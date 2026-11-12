"""Check the signed boundary on actual and synthetic canonical replays."""

import argparse
from dataclasses import dataclass
from math import gcd

from rebalanced_potential_probe import rebalanced_potential
from travel_credit_prefix import is_prime
from travel_residue_probe import increment_at, next_hit


@dataclass
class Replay:
    horizon: int
    hits: list[int]
    large_gap_growth: int
    max_boundary: int
    max_budget: int
    stop: str


def check_replay(record, potential):
    index, origin = record + 2, 2 * record - 2
    horizon = origin
    residue = potential[index % 210, horizon % 210]
    score = origin_score = 432 * index - 215 * horizon + 18 * residue
    hits = []
    payment = startup = repeat = negative = net_sum = large_growth = 0
    seen_long, seen_positive = set(), set()
    limit = 219 * record - 2400
    max_boundary, max_budget = score, 0

    for _ in range(3000):
        hit = next_hit(index, horizon)
        if hit > horizon:
            assert is_prime(horizon - 1) and is_prime(horizon + 1)
            return Replay(horizon, hits, large_growth, max_boundary, max_budget, "quiet")

        gap, increment = hit - index, increment_at(hit, horizon)
        growth = increment - 1
        assert increment > 1
        next_horizon = horizon + growth

        # Cross-check firstness and the increment against the original recurrence.
        value = index + horizon
        for j in range(index + 1, hit + 1):
            direct = gcd(j if j % 2 == 0 else j - 2, value)
            assert direct == (increment if j == hit else 1)
            value += direct
        assert value - hit == next_horizon

        assert horizon <= 2 * index
        if increment >= 864:
            cofactor = (horizon + (1 if hit % 2 else -1)) // increment
            assert cofactor >= 3 and gap <= 2 * cofactor
            assert 219 * increment - 2809 <= score
        if increment > record:
            assert score > limit
            return Replay(horizon, hits, large_growth, max_boundary, max_budget, "inside record")

        next_residue = potential[hit % 210, next_horizon % 210]
        next_score = 432 * hit - 215 * next_horizon + 18 * next_residue
        raw_cost = 24 * gap + next_residue - residue - 11 * growth
        net = raw_cost if 210 % increment else 0
        change = next_score - score
        assert change <= 18 * net - 17 * growth
        assert change <= 325 * gap + 18863
        if change > 0:
            assert 210 % increment
            if gap <= 10:
                assert increment <= 107
            elif not is_prime(increment):
                assert increment in (49, 77, 121)

        if score <= limit < next_score:
            if record >= 11751795061:
                budget = 180 * payment + 180 * (repeat - negative) - 170 * (horizon - origin)
                assert record < 4 * large_growth and budget > 2169 * record
            return Replay(horizon, hits, large_growth, max_boundary, max_budget, "boundary crossing")

        key = increment, horizon % 210, hit % 2
        long_prime = gap > 10 and is_prime(increment)
        reused = long_prime and key in seen_long
        first = min(24 * gap, max(0, net)) if long_prime and not reused else 0
        residual = net - first
        payment += first
        net_sum += net
        if residual > 0:
            if reused or key in seen_positive:
                repeat += residual
            else:
                startup += residual
            seen_positive.add(key)
        else:
            negative -= residual
        if long_prime:
            seen_long.add(key)
        if growth < 3 * (gap + 1):
            large_growth += growth

        hits.append(hit)
        index, horizon, residue, score = hit, next_horizon, next_residue, next_score
        budget = 180 * payment + 180 * (repeat - negative) - 170 * (horizon - origin)
        assert net_sum == payment + startup + repeat - negative
        assert startup <= 4054512
        assert 10 * (score - origin_score) <= budget + 180 * startup
        assert score <= 2 * record + 865 * large_growth + 20374
        max_boundary, max_budget = max(max_boundary, score), max(max_budget, budget)

    return Replay(horizon, hits, large_growth, max_boundary, max_budget, "event limit")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--synthetic", nargs=2, type=int, metavar=("LOWER", "UPPER"))
    args = parser.parse_args()
    potential = rebalanced_potential()
    records = [1468965061, 2937930211, 5875882249, 11751795061]
    for record, expected in zip(records, records[1:]):
        row = check_replay(record, potential)
        assert (row.stop, row.horizon + 1) == ("quiet", expected)
        print(f"Actual {record} -> {expected}, events={len(row.hits)}, "
              f"growth={row.horizon - (2 * record - 2)}, large-gap growth={row.large_gap_growth}, "
              f"max boundary={row.max_boundary}, max budget={row.max_budget}")

    controls = [69921739, 367264309, 1468999771, 1469100181]
    if args.synthetic:
        lower, upper = args.synthetic
        controls.extend(record for record in range(lower + (1 - lower) % 6, upper + 1, 6)
                        if is_prime(record) and is_prime(record - 2))
    starts = sorted(set(controls))
    runs = [(record, check_replay(record, potential)) for record in starts]
    assert all(row.stop == "quiet" for _, row in runs)
    print(f"Synthetic starts={len(runs)}, events={sum(len(row.hits) for _, row in runs)}, "
          f"maximum budget={max((row.max_budget, record) for record, row in runs)}")


if __name__ == "__main__":
    main()
