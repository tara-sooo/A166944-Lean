"""Independently replay the native search's reported worst prefixes.

Pass the saved output of --residual-reserve. This verifies its reported
minimum witness by Python trial division, quiet-index checks, and the
allocation row/column/eligibility/startup checks. It does not certify
the native run's global minimality or an unbounded theorem.
"""

import argparse
from math import lcm
from pathlib import Path
import re

from travel_credit_prefix import capped_hits
from travel_credit_windows import replay_ledger
from travel_funded_probe import funded_summary
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at


def reserve_margins(record, multiplier, table):
    hits, _ = capped_hits(record)
    trace = []
    *_, failure = funded_summary(record, table, multiplier, 4, residual=True, hits=hits, trace=trace)
    assert failure is None
    margins = [(record + 2, record, record)]
    for event, first, startup, signed, unused in trace:
        assert signed + unused == startup + multiplier * first
        half_margin = record + 2 * unused - 2 * (24 + multiplier) * first
        signed_margin = record - 2 * (24 * first + signed)
        margins.append((hits[event], half_margin, signed_margin))
    return margins


def middle_margins(record, table):
    hits, _ = capped_hits(record)
    _, requests, sources, _ = replay_ledger(record, table, residual=True, hits=hits)
    capacities = {s.time // 2: s.negative for s in sources if s.negative}
    horizon = 2 * record - 2
    horizons, increments = [], []
    for hit in hits:
        horizons.append(horizon)
        increment = increment_at(hit, horizon)
        increments.append(increment)
        horizon += increment - 1
    margins = []
    for request in requests:
        earlier, later, increment = request.anchor, request.event, request.increment
        assert increments[earlier] == increments[later] == increment
        drift = horizons[later] - horizons[earlier]
        period = lcm(210, 2 * increment)
        assert drift >= period and drift % period == 0
        assert (hits[later] - hits[earlier]) % (2 * increment) == 0
        if later == earlier + 2:
            assert increments[earlier + 1] >= 463
            margins.append((hits[later], capacities.get(earlier + 1, 0) - request.amount))
    return margins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_output")
    args = parser.parse_args()
    output = Path(args.native_output).read_text()
    result = re.search(r"half-reserve checks=(\d+) minimum margin=(-?\d+) record=(\d+) hit=(\d+)", output)
    assert result is not None
    checks, expected, record, hit = map(int, result.groups())
    multiplier_match = re.search(r"multiplier=(\d+)", output)
    assert multiplier_match is not None
    multiplier = int(multiplier_match.group(1))
    assert record >= 50_000_000 and expected >= 0 and checks > 0
    table = residue_tables()
    margins = reserve_margins(record, multiplier, table)
    assert min(half for _, half, _ in margins) == expected
    assert any(u == hit and half == expected for u, half, _ in margins)
    print(f"Python trial replay confirms record={record} hit={hit} half-reserve margin={expected}")
    print(f"Native bounded run reports {checks} checked prefixes. Python replay has {len(margins) - 1} events.")

    signed_result = re.search(r"minimum signed margin=(-?\d+) record=(\d+) hit=(\d+)", output)
    if signed_result:
        signed_margin, signed_record, signed_hit = map(int, signed_result.groups())
        signed_rows = margins if signed_record == record else reserve_margins(signed_record, multiplier, table)
        assert min(signed for _, _, signed in signed_rows) == signed_margin
        assert any(u == signed_hit and signed == signed_margin for u, _, signed in signed_rows)
        print(f"Python trial replay confirms record={signed_record} hit={signed_hit} signed margin={signed_margin}")

    middle_result = re.search(r"minimum one-middle margin=(-?\d+) record=(\d+) hit=(\d+)", output)
    if middle_result:
        middle_margin, middle_record, middle_hit = map(int, middle_result.groups())
        middle_rows = middle_margins(middle_record, table)
        assert min(margin for _, margin in middle_rows) == middle_margin
        assert (middle_hit, middle_margin) in middle_rows
        print(f"Python trial replay confirms record={middle_record} hit={middle_hit} one-middle margin={middle_margin}")


if __name__ == "__main__":
    main()
