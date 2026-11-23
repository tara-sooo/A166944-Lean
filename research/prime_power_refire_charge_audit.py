#!/usr/bin/env python3
"""Finite direct-gcd checks for the prime-power cell-charge lemma.

This is a regression audit, not a proof of the unbounded W-budget or the
A166944 conjecture. For each fixed odd wheel L, it scans the original parity
gcd at every index in each 2L clock period until the clipped horizon freezes.
"""
from math import gcd


def phi(q: int, C: int) -> int:
    return (C + 2) // (2 * q)


def increment(L: int, n: int, C: int) -> int:
    if n % 2 == 0:
        raw = gcd(n, C - 1)
    else:
        raw = gcd(n - 2, C + 1)
    return gcd(raw, L)


def next_event(L: int, pos: int, C: int):
    # With C fixed, all trigger clocks divide 2L; this checks one complete
    # period using the defining parity-gcd, rather than the residue shortcut.
    for n in range(pos + 1, pos + 2 * L + 1):
        e = increment(L, n, C)
        if e > 1:
            return n, e
    return None


def run_one(L: int, q: int, M: int):
    assert L % q == 0 and q >= 3 and q % 2 == 1
    C0 = 2 * M - 2
    B = ((C0 + 2 * L - 1) // (2 * L)) * (2 * L)
    C, pos = C0, M + 2
    q_events = 0
    total_charge = 0
    max_single_charge = 0

    while C < B:
        found = next_event(L, pos, C)
        if found is None:
            break
        n, e = found
        assert e > 1 and e % 2 == 1 and L % e == 0
        C1 = C + e - 1
        assert C1 <= B, (L, q, M, C, B, n, e, C1)

        # Every q-event advances Phi by its exact charge. For q=3 the even
        # orientation has the one-unit correction described in the note.
        if e % q == 0:
            q_events += 1
            charge = (e // q + 1) // 2
            if q == 3 and n % 2 == 0:
                charge -= 1
            delta = phi(q, C1) - phi(q, C)
            assert delta == charge, (L, q, M, C, n, e, delta, charge)
            total_charge += charge
            max_single_charge = max(max_single_charge, charge)
        else:
            assert phi(q, C1) >= phi(q, C)

        C, pos = C1, n

    W = L // q
    span = phi(q, B) - phi(q, C0)
    assert 0 <= span <= W, (L, q, M, C0, B, span, W)
    assert total_charge <= span <= W, (L, q, M, total_charge, span, W)
    return q_events, total_charge, span


def main():
    # q is the newly added prime-power level; W is coprime to q.
    cases = [
        (3, 1), (3, 5), (3, 7), (3, 35),
        (5, 1), (5, 3), (5, 21),
        (7, 1), (7, 3), (7, 15),
        (9, 1), (9, 5), (9, 7),
        (25, 1), (25, 3),
        (27, 1), (27, 5),
        (49, 1), (49, 3),
        (125, 1), (125, 3),
        (343, 1),
    ]
    starts = list(range(7, 202, 2))
    trajectories = total_q_events = total_charge = max_charge = 0
    for q, W in cases:
        assert gcd(q, W) == 1
        L = q * W
        for M in starts:
            count, charge, span = run_one(L, q, M)
            trajectories += 1
            total_q_events += count
            total_charge += charge
            max_charge = max(max_charge, charge)
    print(
        f"PASS finite direct-gcd audit: {trajectories} trajectories; "
        f"M=7..201 odd; {len(cases)} (q,W) pairs; "
        f"q-events={total_q_events}; aggregate charge={total_charge}; "
        f"max per-trajectory charge={max_charge}."
    )
    print("Finite evidence only; no global average, Cap B, or twin-prime proof.")


if __name__ == "__main__":
    main()
