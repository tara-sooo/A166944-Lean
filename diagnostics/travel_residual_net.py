"""Check signed/unused-credit cancellation at every replay prefix.

The margins are bounded integer diagnostics, not Lean certificates for
the original sequence. The global startup bound is the Lean-checked
16170*1478; the actual startup column uses the observed prefix sum.
"""

from math import isqrt

from travel_funded_probe import funded_summary
from travel_mod210_probe import residue_tables


def main():
    table = residue_tables()
    bound = 16170 * 1478
    for label, record in (("actual", 355_723), ("actual", 22_933_441),
                          ("replayed", 45_895_573), ("replayed", 367_232_911),
                          ("synthetic", 23_619_049), ("synthetic", 56_837_371)):
        trace = []
        *_, failure = funded_summary(record, table, 0, 4, residual=True, trace=trace)
        assert failure is None
        penalty = 24 * isqrt(4 * (3 * record + 4)) + 1315
        actual_margin, fixed_margin = record - penalty, record - bound - penalty
        net_peak = 0
        for _, first, startup, signed, unused in trace:
            assert signed + unused == startup
            net = 24 * first + signed
            assert net == 24 * first + startup - unused
            net_peak = max(net_peak, net)
            actual_margin = min(actual_margin, record - net - penalty)
            fixed_margin = min(fixed_margin, record + unused - 24 * first - bound - penalty)
        print(f"{label:10} {record=:10} net_peak={net_peak:8} "
              f"actual_startup_margin={actual_margin:10} fixed_startup_margin={fixed_margin:10}")


if __name__ == "__main__":
    main()
