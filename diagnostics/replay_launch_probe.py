"""Check first hits from small offsets and test the endpoint condition."""

import argparse
from collections import Counter
from fractions import Fraction
from math import isqrt

from sympy import isprime

from replay_offset_probe import Event, audit, factored_hit, replay
from travel_residue_probe import increment_at


def check_hits(records, label, expected_returns=None):
    counts = Counter()
    peak_offset = (Fraction(0), 0, 0)
    tightest_departure = (Fraction(0), 0, None)
    for record in records:
        events, stop = replay(record)
        counts.update({"starts": 1, stop[0]: 1, "events": len(events)})
        if expected_returns is not None:
            assert stop == ("twin", expected_returns[record])
            audit(events)
        for row in events:
            e, c, x = row.increment, row.horizon, row.offset
            c_after = c + e - 1
            if record * row.next_offset + 4 * (c_after + 1) > record * x + 4 * (c + 1):
                assert row.next_offset >= x or (row.next_offset == x - 2 and record < 2 * (e - 1))
            peak_offset = max(peak_offset, (Fraction(row.next_offset, record), record, row.next_offset))
            if x > 6:
                continue
            assert row.next_offset <= max(28, 2 * isqrt(c + 1) + 6)
            r = row.start + row.gap
            if e < 9:
                if row.next_offset > 6:
                    counts["departures with e < 9"] += 1
                continue
            counts["large hits from X <= 6"] += 1
            assert row.next_offset == 6 * (r % 2) + (2 * e if c_after % 4 else 0)
            if c_after % 4 == 0:
                counts["large hits returning to X <= 6"] += 1
                continue
            parity = "odd" if r % 2 else "even"
            counts[f"departures C % 4 = {c % 4}, {parity} hit"] += 1
            term = c + 1 if r % 2 else c - 1
            strong_residue = 1 if r % 2 else 3
            multiplier = 3 if e % 4 == strong_residue else 1
            assert multiplier * e * e <= term
            margin = Fraction(multiplier * e * e, term)
            if margin > tightest_departure[0]:
                tightest_departure = (margin, record, row)
    if tightest_departure[2] is not None:
        audit([tightest_departure[2]])
    print(label, dict(counts))
    print("Peak X/M", peak_offset)
    print("Closest departure to the cofactor bound", tightest_departure)


def check_local_examples():
    record, offset = 101, 6
    for horizon, expected in ((1600, 3), (10002, 7)):
        start = (horizon + offset) // 2
        hit = factored_hit(start, horizon)
        e = increment_at(hit, horizon)
        assert e == expected and 8 * (horizon + 1) > record * record
        joint = record * offset + 4 * (horizon + 1)
        if horizon == 1600:
            assert joint <= record * record
        else:
            assert joint > record * record
            assert (horizon + 1) % 7 == 0 and offset + 4 * 7 <= record
        audit([Event(start, horizon, hit - start, e, offset, 2 * hit - (horizon + e - 1), False)])
        print("Local first hit", record, start, horizon, hit, e, "joint bound value", joint)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan", action="store_true", help="include both bounded synthetic ranges")
    args = parser.parse_args()
    check_local_examples()
    records = [1468965061, 2937930211, 5875882249, 11751795061, 23503590559, 47007181621, 94014363763]
    check_hits(records[:-1], "Actual segments", dict(zip(records, records[1:])))
    if args.scan:
        for lo, hi in ((13, 2000000), (11751795067, 11751995061)):
            records = (m for m in range(lo, hi + 1, 6) if isprime(m) and isprime(m - 2))
            check_hits(records, f"Synthetic starts in [{lo}, {hi}]")


if __name__ == "__main__":
    main()
