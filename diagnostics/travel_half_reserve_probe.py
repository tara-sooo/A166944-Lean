"""Independently replay the native search's worst half-reserve prefix.

Pass the saved output of --residual-reserve. This verifies its reported
minimum witness by Python trial division, quiet-index checks, and the
allocation row/column/eligibility/startup checks. It does not certify
the native run's global minimality or an unbounded theorem.
"""

import argparse
from pathlib import Path
import re

from travel_credit_prefix import capped_hits
from travel_funded_probe import funded_summary
from travel_mod210_probe import residue_tables


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
    hits, _ = capped_hits(record)
    trace = []
    *_, failure = funded_summary(record, residue_tables(), multiplier, 4,
                                residual=True, hits=hits, trace=trace)
    assert failure is None
    margins = [(record, record + 2)]
    for event, first, startup, signed, unused in trace:
        assert signed + unused == startup + multiplier * first
        margins.append((record + 2 * unused - 2 * (24 + multiplier) * first, hits[event]))
    minimum, _ = min(margins)
    assert minimum == expected, (minimum, expected)
    assert (expected, hit) in margins
    print(f"Python trial replay confirms record={record} hit={hit} half-reserve margin={minimum}")
    print(f"Native bounded run reports {checks} checked prefixes; Python replay has {len(trace)} events.")


if __name__ == "__main__":
    main()
