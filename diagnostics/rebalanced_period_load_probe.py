"""Check the period and first-gap budgets on capped synthetic replays."""

import argparse
from collections import Counter
from itertools import pairwise
from math import lcm

from rebalanced_potential_probe import rebalanced_potential
from travel_credit_prefix import capped_hits, is_prime
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at
from travel_reuse_overlap_probe import Window, components, replay


def period_stats(periods):
    changes = Counter()
    for left, right, weight in periods:
        changes[left] += weight
        changes[right] -= weight
    load = peak = area = excess = 0
    for left, right in pairwise(sorted(changes)):
        load += changes[left]
        peak = max(peak, load)
        area += (right - left) * load
        excess += (right - left) * max(0, load - 85)
    assert not changes or load + changes[max(changes)] == 0
    assert area == sum((right - left) * weight for left, right, weight in periods)
    at_starts = [sum(w for a, b, w in periods if a <= x < b) for x, _, _ in periods]
    assert peak == max(at_starts, default=0)
    depth = max((sum(a <= x < b for a, b, _ in periods) for x, _, _ in periods), default=0)
    return peak, depth, excess


def component_allowance(growth, debt, requests, by_end):
    keys = {by_end[w.right][0] for w in requests}
    if debt <= 0:
        return 0
    if len(requests) == 2:
        return min(4052, 7 * growth // 4)
    if len(requests) == 3:
        return min(8368, 18 * growth // 5)
    if len(keys) <= 4 and all(w.increment >= 109 and by_end[w.right][1] for w in requests):
        return 2 * growth // 3
    if len(keys) <= 5 and all(w.increment >= 393 and by_end[w.right][1] for w in requests):
        return 5 * growth // 6
    return debt


def check_replay(M, table, potential, cutoff=None):
    requests, costs = replay(M, table, rebalanced=potential)
    hits, _ = capped_hits(M)
    origin, horizon, start = 2 * M - 2, 2 * M - 2, M + 2
    post, by_end, seen = {}, {}, set()
    negative = payment = high_growth = high_count = runs = shortfall = potential_change = 0
    was_high = False
    for (C, residual), hit in zip(costs, hits, strict=True):
        if cutoff is not None and C > cutoff:
            break
        assert C == horizon
        e, gap = increment_at(hit, C), hit - start
        horizon = C + e - 1
        post[C] = 2 * horizon
        key = (e, C % 210, hit % 2)
        long = gap > 10 and is_prime(e)
        reused = long and key in seen
        by_end[2 * horizon] = key, reused
        change = potential[hit % 210, horizon % 210] - potential[start % 210, C % 210]
        net = 0 if 210 % e == 0 else 24 * gap + change - 11 * (e - 1)
        phi = min(24 * gap, max(0, net)) if long and not reused else 0
        assert net - phi == residual
        negative += max(0, -residual)
        payment += phi
        high = phi > 0 and e > 338
        if high:
            high_growth += e - 1
            high_count += 1
            runs += not was_high
            shortfall += 2 * e - gap
            potential_change += change
        was_high = high
        if long:
            seen.add(key)
        start = hit
    assert potential_change <= 1036 * runs
    first_bound = 13887360 + 37 * high_growth + 48 * high_count + 1036 * runs - 24 * shortfall
    old_first_bound = 13887360 + 41 * high_growth
    assert payment <= first_bound <= old_first_bound

    growth_windows = [Window(post[w.left], post[w.right], w.increment, 3 * w.cost)
                      for w in requests if w.right in post]
    growth = horizon - origin
    used = excess = allowance = old_allowance = peak = depth = key_count = count = 0
    for left, right, demand in components(growth_windows):
        rows = [w for w in growth_windows if left <= w.left and w.right <= right]
        periods = []
        for w in rows:
            width = 2 * lcm(210, 2 * w.increment)
            assert w.left <= w.right - width and w.cost <= width
            weight = (60 * w.cost + width - 1) // width
            if not by_end[w.right][1]:
                assert weight <= 46
            elif w.increment >= 393:
                assert weight <= 17
            elif w.increment >= 143:
                assert weight <= 19
            elif w.increment >= 109:
                assert weight <= 20
            periods.append((w.right - width, w.right, weight))
        local_peak, local_depth, local_excess = period_stats(periods)
        local_growth = (right - left) // 2
        debt = demand - 2 * local_growth
        previous = component_allowance(local_growth, debt, rows, by_end)
        period_debt = sum((b - a) * w for a, b, w in periods) - 120 * local_growth
        assert period_debt <= 50 * local_growth + local_excess
        current = min(60 * previous, period_debt)
        assert 60 * debt <= current
        used += local_growth
        excess += local_excess
        allowance += current
        old_allowance += previous
        peak = max(peak, local_peak)
        depth = max(depth, local_depth)
        key_count = max(key_count, len({by_end[w.right][0] for w in rows}))
        count += 1
    unused = growth - used
    assert unused >= 0
    credit_allowance = allowance - 120 * unused - 180 * negative
    exact_debt = sum(w.cost for w in growth_windows) - 2 * growth - 3 * negative
    assert 60 * exact_debt <= credit_allowance <= 60 * (old_allowance - 2 * unused - 3 * negative)
    slack = 54 * M - credit_allowance - 180 * first_bound
    return count, key_count, depth, peak, excess, old_first_bound - first_bound, slack


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lower", type=int)
    parser.add_argument("upper", type=int)
    args = parser.parse_args()
    assert period_stats([(100 * i, 100 * i + 150, 17) for i in range(6)]) == (34, 2, 0)
    assert period_stats([(0, 100, 17)] * 6) == (102, 6, 1700)
    table, potential = residue_tables(), rebalanced_potential()
    starts = range(args.lower + (1 - args.lower) % 6, args.upper + 1, 6)
    results = [(M, check_replay(M, table, potential)) for M in starts if is_prime(M) and is_prime(M - 2)]
    if not results:
        return
    print("Synthetic starts", len(results), "components", sum(row[0] for _, row in results))
    for i, label in enumerate(("keys per component", "depth", "point load", "excess per prefix",
                               "first-payment bound saving"), start=1):
        print("Maximum", label, max((row[i], M) for M, row in results))
    print("Minimum joint budget slack", min((row[6], M) for M, row in results))
    print("Control at M=367264309", check_replay(367264309, table, potential, 734547102))


if __name__ == "__main__":
    main()
