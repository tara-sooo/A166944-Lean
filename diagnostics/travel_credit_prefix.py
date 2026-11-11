"""Independently check native prefix totals using Python trial factoring.

Native sieving and Python trial division independently choose all twin-shaped
starts and their first hits. Row/column/eligibility/startup checks are supplied
by funded_summary. Both implementations stop before the first cap/travel
violation and before a 3001st event, exactly as the bounded native search does.
"""

import argparse
import re
import subprocess

from travel_funded_probe import funded_summary
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at, next_hit, odd_prime_divisors


def is_prime(value):
    return value > 2 and list(odd_prime_divisors(value)) == [value]


def capped_hits(record):
    index, horizon = record + 2, 2 * record - 2
    hits = []
    while len(hits) < 3000:
        hit = next_hit(index, horizon)
        if hit > horizon:
            return hits, "quiet"
        increment = increment_at(hit, horizon)
        if increment > record or 2 * (hit - (record + 2)) > record:
            return hits, "cutoff"
        assert increment > 1
        assert all(increment_at(j, horizon) == 1 for j in range(index + 1, hit))
        if hit - index > 10 and not is_prime(increment):
            assert 24 * (hit - index) <= 7 * (increment - 1)
        horizon += increment - 1
        index = hit
        hits.append(hit)
    return hits, "event-limit"


def prefix_summary(limit, multiplier, growth_charge):
    table = residue_tables()
    starts = demands = cutoffs = event_limits = maximum_startup = 0
    for record in range(13, limit + 1, 6):
        if not is_prime(record) or not is_prime(record - 2):
            continue
        starts += 1
        hits, stop = capped_hits(record)
        cutoffs += stop == "cutoff"
        event_limits += stop == "event-limit"
        _, startup, _, _, paid, failure = funded_summary(
            record, table, multiplier, growth_charge, hits=hits)
        assert failure is None, (record, failure)
        demands += paid
        maximum_startup = max(maximum_startup, startup)
    return starts, demands, cutoffs, event_limits, maximum_startup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int)
    parser.add_argument("--multiplier", type=int, default=0)
    parser.add_argument("--growth-charge", type=int, choices=(2, 4), default=4)
    parser.add_argument("--native", help="Optional path to the native executable to compare")
    args = parser.parse_args()
    assert 13 <= args.limit <= 100_000_000 and 0 <= args.multiplier <= 24
    result = prefix_summary(args.limit, args.multiplier, args.growth_charge)
    print("Python trial division (starts, demands, cutoffs, event limits, maximum startup):", result)
    if args.native:
        output = subprocess.check_output([
            args.native, str(args.limit), "--funded", str(args.multiplier),
            "--growth-charge", str(args.growth_charge)], text=True)
        totals = re.search(r"synthetic starts=(\d+) paid demands=(\d+) cutoff stops=(\d+) "
                           r"event-limit stops=(\d+)", output)
        startup = re.search(r"maximum startup=(\d+)", output)
        assert totals is not None and startup is not None, output
        native = tuple(map(int, totals.groups())) + (int(startup.group(1)),)
        assert result == native, (result, native)
        print("Native sieve totals match exactly.")


if __name__ == "__main__":
    main()
