"""Check overlap budgets by trial division on capped replays."""

import argparse
from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction
from itertools import accumulate
from math import lcm
from pathlib import Path
import re

from travel_credit_prefix import capped_hits, is_prime
from rebalanced_potential_probe import rebalanced_potential
from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at


@dataclass(frozen=True)
class Window:
    left: int
    right: int
    increment: int
    cost: int

    @property
    def width(self):
        return self.right - self.left


def replay(record, table, *, scaled=False, adjusted=False, rebalanced=None):
    adjusted = adjusted or rebalanced is not None
    scaled = scaled or adjusted
    hits, _ = capped_hits(record)
    index, horizon = record + 2, 2 * record - 2
    previous = {}
    previous_positive = {}
    windows, costs = [], []
    for hit in hits:
        increment = increment_at(hit, horizon)
        gap = hit - index
        updated = horizon + increment - 1
        long_prime = gap > 10 and is_prime(increment)
        key = (increment, horizon % P, hit % 2)
        old = previous.get(key) if long_prime else None
        first_gap = gap if long_prime and old is None else 0
        net = 0 if scaled else 24 * first_gap
        before = table[index % P, horizon % P][1]
        after = table[hit % P, updated % P][1]
        if rebalanced is not None:
            before = rebalanced[index % P, horizon % P]
            after = rebalanced[hit % P, updated % P]
        elif scaled:
            before, after = 8 * before // 9, 8 * after // 9
        if P % increment:
            net = 24 * gap + after - before - 11 * (increment - 1)
            if adjusted:
                first_payment = 24 * first_gap
                if rebalanced is not None:
                    first_payment = min(first_payment, max(0, net))
                net -= first_payment
                if old is None:
                    old = previous_positive.get(key)
                if net > 0:
                    previous_positive[key] = (horizon, hit)
            if old is not None and net > 0:
                earlier, earlier_hit = old
                assert (hit - earlier_hit) % (2 * increment) == 0
                assert horizon > earlier and (horizon - earlier) % lcm(P, 2 * increment) == 0
                windows.append(Window(earlier, horizon, increment, net))
        elif scaled:
            assert 24 * gap + after - before <= 11 * (increment - 1)
        if long_prime:
            previous[key] = (horizon, hit)
        costs.append((horizon, net))
        index, horizon = hit, updated
    return windows, costs


def pair_margins(windows):
    for j, later in enumerate(windows):
        for earlier in windows[:j]:
            if later.left < earlier.right:
                left = min(earlier.left, later.left)
                yield later.right - left - 2 * (earlier.cost + later.cost), earlier, later


def components(windows):
    ordered = sorted(windows, key=lambda w: w.left)
    if not ordered:
        return
    left, right, cost = ordered[0].left, ordered[0].right, ordered[0].cost
    for window in ordered[1:]:
        if window.left < right:
            right = max(right, window.right)
            cost += window.cost
        else:
            yield left, right, cost
            left, right, cost = window.left, window.right, window.cost
    yield left, right, cost


def margins_for_components(windows, costs):
    for left, right, positive in components(windows):
        enclosed = [value for horizon, value in costs if left < horizon <= right]
        negative = sum(min(0, value) for value in enclosed)
        yield right - left - 2 * (positive + negative), left, right, positive, negative, sum(enclosed)


def prefix_remainders(windows, costs):
    net = covered = count = 0
    for horizon, cost in costs:
        net += cost
        if count < len(windows) and windows[count].right == horizon:
            count += 1
            covered = sum(positive + negative for _, _, _, positive, negative, _ in
                          margins_for_components(windows[:count], costs))
        yield 3 * (net - covered)


def contained_window_margins(windows, costs):
    """Check all contained requests against growth and enclosed negative costs."""
    horizons = [horizon for horizon, _ in costs]
    negative = list(accumulate((max(0, -value) for _, value in costs), initial=0))
    for left in sorted({window.left for window in windows}):
        before = negative[bisect_right(horizons, left)]
        demand = 0
        for window in windows:
            if window.left < left:
                continue
            demand += window.cost
            right = window.right
            supply = negative[bisect_right(horizons, right)] - before
            growth_margin = 2 * (right - left) - 3 * demand
            yield growth_margin, growth_margin + 3 * supply, left, right


def scaled_overlap_summary(limit, controls, table, *, adjusted=False, rebalanced=None):
    twin_starts = {record for record in range(13, limit + 1, 6)
                   if is_prime(record) and is_prime(record - 2)}
    starts = requests = intervals = growth_failures = signed_failures = 0
    least_growth = least_signed = None
    for record in sorted(twin_starts.union(controls)):
        starts += 1
        windows, costs = replay(record, table, scaled=True, adjusted=adjusted, rebalanced=rebalanced)
        requests += len(windows)
        if adjusted and rebalanced is None:
            for window in windows:
                if 3 * window.cost > 2 * window.width:
                    assert (window.increment, window.width) in {(9, 630), (9, 1260), (25, 1050)}
        else:
            assert all(3 * window.cost <= 2 * window.width for window in windows)
        for growth, signed, left, right in contained_window_margins(windows, costs):
            intervals += 1
            growth_failures += growth < 0
            signed_failures += signed < 0
            candidate = (growth, record, left, right)
            least_growth = candidate if least_growth is None else min(least_growth, candidate)
            candidate = (signed, record, left, right)
            least_signed = candidate if least_signed is None else min(least_signed, candidate)
    label = "Rebalanced potential with capped first costs" if rebalanced is not None else (
        "Adjusted costs" if adjusted else "Scaled potential")
    print(f"{label}: {starts=} {requests=} {intervals=} {growth_failures=} {signed_failures=}")
    print(f"Minimum margins (margin, record, left, right): {least_growth=} {least_signed=}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_output", nargs="?")
    parser.add_argument("--scaled-limit", type=int)
    parser.add_argument("--adjusted", action="store_true", help="Separate first gaps and include small repeated costs")
    parser.add_argument("--rebalanced", action="store_true", help="Use the rebalanced potential and cap first costs")
    parser.add_argument("--control", type=int, action="append", default=[])
    args = parser.parse_args()
    table = residue_tables()
    if args.scaled_limit is not None:
        if args.native_output is not None:
            parser.error("supply a native output or a scaled search limit")
        scaled_overlap_summary(args.scaled_limit, args.control, table, adjusted=args.adjusted,
                               rebalanced=rebalanced_potential() if args.rebalanced else None)
        return
    if args.adjusted or args.rebalanced:
        parser.error("--adjusted and --rebalanced require --scaled-limit")
    if args.native_output is None:
        parser.error("supply a native output or a scaled search limit")
    output = Path(args.native_output).read_text()

    pair_match = re.search(r"minimum overlap pair margin=(-?\d+) record=(\d+) horizon=(\d+)", output)
    assert pair_match
    expected, record, right = map(int, pair_match.groups())
    windows, costs = replay(record, table)
    pairs = list(pair_margins(windows))
    assert min(row[0] for row in pairs) == expected
    _, first, second = next(row for row in pairs if row[0] == expected and row[2].right == right)
    left = min(first.left, second.left)
    negative = sum(min(0, value) for horizon, value in costs if left < horizon <= right)
    print(f"Pair at synthetic {record}: {first}, {second}")
    print(f"  union width={right - left}, margin={expected}, negative net cost={negative}, "
          f"margin with those negative terms={expected - 2 * negative}")

    load_match = re.search(r"maximum reuse load=(\d+) scale=(\d+) record=(\d+) horizon=(\d+)", output)
    assert load_match
    expected_load, scale, load_record, cut = map(int, load_match.groups())
    if load_record != record:
        windows, _ = replay(load_record, table)
    rounded = [(w, (2 * scale * w.cost + w.width - 1) // w.width) for w in windows]
    loads = {x: sum(rate for w, rate in rounded if w.left <= x < w.right) for x in {w.left for w in windows}}
    assert max(loads.values()) == expected_load and loads[cut] == expected_load
    exact_load = sum((Fraction(2 * w.cost, w.width) for w in windows if w.left <= cut < w.right), Fraction())
    print(f"Load at synthetic {load_record} horizon={cut}: exact={exact_load}, "
          f"rounded={expected_load}/{scale}")

    component_match = re.search(r"minimum reuse component margin=(-?\d+) record=(\d+) horizon=(\d+)", output)
    if component_match:
        expected_component, component_record, right = map(int, component_match.groups())
        windows, costs = replay(component_record, table)
        rows = list(margins_for_components(windows, costs))
        assert min(row[0] for row in rows) == expected_component
        _, left, _, positive, negative, signed = next(
            row for row in rows if row[0] == expected_component and row[2] == right)
        print(f"Component at synthetic {component_record}: [{left},{right}), "
              f"positive reuse={positive}, negative={negative}, all signed={signed}, "
              f"reuse margin={expected_component}")

    thirds_match = re.search(
        r"minimum two-thirds margin=(-?\d+) record=(\d+) horizon=(\d+) prefix=(\d+)", output)
    if thirds_match:
        expected_thirds, thirds_record, right, prefix = map(int, thirds_match.groups())
        windows, costs = replay(thirds_record, table)
        rows = [(2 * (hi - lo) - 3 * (positive + negative), hi, window.right)
                for j, window in enumerate(windows)
                for _, lo, hi, positive, negative, _ in margins_for_components(windows[:j + 1], costs)]
        assert min(row[0] for row in rows) == expected_thirds
        assert (expected_thirds, right, prefix) in rows
        print(f"Two-thirds margin at synthetic {thirds_record} horizon={right} "
              f"prefix={prefix}: {expected_thirds}")

    remainder_match = re.search(r"maximum triple remainder=(\d+) record=(\d+) hit=(\d+)", output)
    if remainder_match:
        expected_remainder, remainder_record, hit = map(int, remainder_match.groups())
        if expected_remainder:
            windows, costs = replay(remainder_record, table)
            hits, _ = capped_hits(remainder_record)
            rows = list(zip(hits, prefix_remainders(windows, costs)))
            assert max(value for _, value in rows) == expected_remainder
            assert (hit, expected_remainder) in rows
            print(f"Triple remainder at synthetic {remainder_record} hit={hit}: {expected_remainder}")


if __name__ == "__main__":
    main()
