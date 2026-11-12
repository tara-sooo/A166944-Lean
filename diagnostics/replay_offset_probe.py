"""Check offset returns and same-residue segments on bounded replays."""

import argparse
from collections import Counter
from math import gcd
from typing import NamedTuple

from sympy import factorint, isprime, nextprime

from travel_residue_probe import increment_at, next_hit


class Event(NamedTuple):
    start: int
    horizon: int
    gap: int
    increment: int
    offset: int
    next_offset: int
    forced_return: bool


def factored_hit(start, horizon):
    first = horizon + 1
    for term, odd in ((horizon - 1, False), (horizon + 1, True)):
        for prime in factorint(term):
            residue = prime + 2 if odd else 0
            first = min(first, start + 1 + (residue - start - 1) % (2 * prime))
    return first


def replay(record):
    start, horizon = record + 2, 2 * record - 2
    events = []
    for _ in range(3000):
        hit = factored_hit(start, horizon)
        if hit > horizon:
            twin = isprime(horizon - 1) and isprime(horizon + 1)
            return events, ("twin" if twin else "quiet composite", horizon + 1)
        increment, gap = increment_at(hit, horizon), hit - start
        offset = 2 * start - horizon
        next_horizon = horizon + increment - 1
        next_offset = 2 * hit - next_horizon
        assert increment > 1 and offset >= 0 and next_offset >= 0
        if increment > record:
            return events, ("inside record", increment)
        base = 6 * (hit % 2)
        forced = increment >= 5 and (
            3 * increment * increment > increment * (offset + 1) + 4 * (horizon + 1)
        )
        if increment >= 5:
            assert next_offset >= base and (next_offset - base) % (2 * increment) == 0
        if forced:
            assert next_offset == base
        events.append(Event(start, horizon, gap, increment, offset, next_offset, forced))
        start, horizon = hit, next_horizon
    return events, ("event limit", horizon)


def audit(events):
    for row in events:
        hit = row.start + row.gap
        assert next_hit(row.start, row.horizon) == hit
        value = row.start + row.horizon
        for j in range(row.start + 1, hit + 1):
            increment = gcd(j - (2 if j % 2 else 0), value)
            assert increment == (row.increment if j == hit else 1)
            value += increment
        assert value - hit == row.horizon + row.increment - 1


def large_gap(row):
    return row.increment - 1 < 3 * (row.gap + 1)


def summary(starts, label):
    counts = Counter()
    longest = (0, 0, [])
    longest_positive = (0, 0, [])
    biggest_drop = (0, 0, ())
    for record in starts:
        events, stop = replay(record)
        counts.update({"starts": 1, stop[0]: 1, "events": len(events)})
        offset_start = positive_start = 0
        for i, row in enumerate(events):
            if large_gap(row):
                counts["H"] += row.increment - 1
                if row.next_offset <= 6:
                    counts["H ending at X <= 6"] += row.increment - 1
            if row.forced_return:
                counts["forced returns"] += 1
            if row.next_offset <= 6:
                offset_start = i + 1
                biggest_drop = max(biggest_drop, (row.offset - row.next_offset, record, row))
            if row.gap <= 10 or row.next_offset <= row.offset:
                positive_start = i + 1
            if i + 1 - offset_start > longest[0]:
                longest = (i + 1 - offset_start, record, events[offset_start:i + 1])
            if i + 1 - positive_start > longest_positive[0]:
                longest_positive = (i + 1 - positive_start, record, events[positive_start:i + 1])
    audit(longest[2])
    audit(longest_positive[2])
    if biggest_drop[2]:
        audit([biggest_drop[2]])
    print(label, dict(counts))
    print("longest run with X > 6", longest[:2])
    print("longest run of gaps > 10 increasing X", longest_positive)
    print("largest return drop", biggest_drop)


def audit_modular_segments():
    record = 11751887509
    events, _ = replay(record)
    start, end = 11752089043, 11752089463
    segment = [row for row in events if start <= row.start < end]
    assert len(segment) == 14 and segment[0].start == start
    audit(segment)
    last = segment[-1]
    assert last.start + last.gap == end
    assert last.horizon + last.increment - 1 - segment[0].horizon == 420
    assert last.next_offset - segment[0].offset == 420
    print("Synthetic mod-210 segment", record, start, end, "X increase=420")

    # A local first hit at the larger modulus, from an arbitrary start.
    modulus = 30030
    start, horizon, gap, increment = 7274167398, 14479265220, 120120, 120121
    offset = 2 * start - horizon
    local = Event(start, horizon, gap, increment, offset, offset + gap, False)
    audit([local])
    assert gap == increment - 1 and gap % modulus == 0
    print("Local mod-30030 step", local)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan", action="store_true", help="include both bounded synthetic ranges")
    args = parser.parse_args()
    audit_modular_segments()
    records = [1468965061, 2937930211, 5875882249, 11751795061, 23503590559, 47007181621, 94014363763]
    for record, expected in zip(records, records[1:]):
        events, stop = replay(record)
        assert stop == ("twin", expected)
        audit(events)
        growth = sum(row.increment - 1 for row in events if large_gap(row))
        at_return = sum(row.increment - 1 for row in events if large_gap(row) and row.next_offset <= 6)
        print("Actual segment", record, expected, "events", len(events), "H", growth, "H at returns", at_return)
    if args.scan:
        summary((m for m in range(13, 2000001, 6) if isprime(m) and isprime(m - 2)), "Synthetic through 2M")
        summary((m for m in range(11751795067, 11751995062, 6) if isprime(m) and isprime(m - 2)),
                "Synthetic near the finite threshold")


if __name__ == "__main__":
    main()
