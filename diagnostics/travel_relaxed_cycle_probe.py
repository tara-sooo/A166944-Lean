"""A positive cycle in the clipped modulo-210 relaxation.

Only the clipped first hit and the increment's gcd with210 are used.
After the first traversal all long-prime phase keys in the cycle have
been seen. The repeated cycle would have no new first-gap funding.
This word is not an actual recurrence path: its two uses of77 violate
the full same-phase horizon congruence.
"""

from math import gcd, lcm

from travel_mod210_probe import P, clipped_hit, residue_tables


STEPS = (
    (9, 5), (1, 3), (13, 7), (9, 25), (10, 7), (10, 5), (6, 3), (7, 77),
    (5, 27), (9, 25), (14, 7), (6, 25), (13, 7), (7, 5), (5, 3), (11, 7),
    (7, 25), (12, 7), (8, 5), (4, 3), (11, 77), (1, 51), (13, 7), (8, 25), (11, 7),
)


if __name__ == "__main__":
    table = residue_tables()
    index, horizon = 98, 84
    full, separating = 0, 0
    uses = []
    for gap, increment in STEPS:
        assert clipped_hit(index % P, horizon % P) == (gap, gcd(increment, P))
        hit, updated = index + gap, horizon + increment - 1
        before = table[index % P, horizon % P][1]
        after = table[hit % P, updated % P][1]
        balance = 24 * gap + after - before - 11 * (increment - 1)
        full += balance
        if P % increment:
            separating += balance
        else:
            assert balance <= 0
        if increment == 77:
            uses.append((hit, horizon))
        index, horizon = hit, updated
    assert (index % P, horizon % P) == (98, 84)
    assert full == 420 and separating == 996
    (r1, c1), (r2, c2) = uses
    assert r1 % 2 == r2 % 2 and c1 % P == c2 % P
    period = lcm(P, 2 * 77)
    assert c2 - c1 == 210 < period == 2310
    print(f"Relaxed cycle: {len(STEPS)} events, travel={index - 98}, growth={horizon - 84}, "
          f"full balance={full}, separating balance={separating}")
    print(f"Two uses of77 have horizon drift={c2 - c1}; an actual same-phase reuse needs {period}.")
