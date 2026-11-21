#!/usr/bin/env python3
"""A166944 Cap B: finite audit for prime debt and low-offset reset exclusion.

Python 3 stdlib. This is a finite arithmetic certificate + paper deductions,
not a Lean proof and not a proof of Cap B.
"""
from math import gcd, isqrt

MOD = 210
STATES = [(s, c) for s in range(MOD) for c in range(0, MOD, 2)]
INDEX = {key: i for i, key in enumerate(STATES)}
EXCEPTIONAL_INCREMENTS = (9, 25, 27, 33)


def clipped_hit(s, c):
    for gap in range(1, 15):
        r = s + gap
        a = r if r % 2 == 0 else r - 2
        b = c - 1 if r % 2 == 0 else c + 1
        e = gcd(gcd(a, b), MOD)
        if e > 1:
            return r % MOD, gap, e
    return None


def potential():
    edges = []
    for i, (s, c) in enumerate(STATES):
        hit = clipped_hit(s, c)
        if hit is None:
            continue
        r, gap, e0 = hit
        increments = (e0,) + tuple(
            e for e in EXCEPTIONAL_INCREMENTS if gcd(e, MOD) == e0
        )
        for e in increments:
            dst = INDEX[(r, (c + e - 1) % MOD)]
            edges.append((i, dst, gap - (e - 1)))
    assert len(STATES) == 22050 and len(edges) == 58232
    V = [0] * len(STATES)
    for it in range(1, 100):
        new = V.copy()
        for i, j, weight in edges:
            if new[i] < weight + V[j]:
                new[i] = weight + V[j]
        if new == V:
            break
        V = new
    else:
        raise AssertionError('potential failed to stabilize')
    assert it == 19 and min(V) == 0 and max(V) == 29
    assert all(weight + V[j] <= V[i] for i, j, weight in edges)
    return V


def inert(c):
    return gcd(c - 1, MOD) == gcd(c + 1, MOD) == 1


def noninert_potential_upper(p, V):
    """All hypothetical p hits strictly before a 3,5,7 clipped hit."""
    best = -100000
    for s, c in STATES:
        if inert(c):
            continue
        hit = clipped_hit(s, c)
        assert hit is not None
        for gap in range(1, hit[1]):
            r = (s + gap) % MOD
            v2 = V[INDEX[(r, (c + p - 1) % MOD)]]
            best = max(best, gap - (p - 1) + v2 - V[INDEX[(s, c)]])
    return best


def reset_potential_upper(p, V):
    """All residue candidates with X>=0 and X' in {0,6}.

    Event parity is enforced. C mod 420 is sufficient because s and r
    contain C/2. CRT conditions p | C +/- 1 are intentionally ignored,
    making this search a strict overapproximation of real first hits.
    """
    best = -100000
    for C in range(0, 420, 2):
        c = C % MOD
        if not inert(c):
            continue
        for newX in (0, 6):
            for oldX in range(0, p + 6, 2):
                gap = (newX - oldX + p - 1) // 2
                if gap <= 0 or 2 * gap != newX - oldX + p - 1:
                    continue
                s = (C + oldX) // 2
                r = s + gap
                if (r % 2 == 0) != (newX == 0):
                    continue
                before = V[INDEX[(s % MOD, c)]]
                after = V[INDEX[(r % MOD, (c + p - 1) % MOD)]]
                best = max(best, gap - (p - 1) + after - before)
    return best


def small_prime_envelopes(V):
    """Residues of pre-event C that can support positive prime debt."""
    out = {}
    for p in (11, 13, 17, 19, 23, 29):
        positive_c = set()
        highest = 0
        for s, c in STATES:
            hit = clipped_hit(s, c)
            maxgap = min(2 * p, hit[1] - 1 if hit else 2 * p)
            for gap in range(1, maxgap + 1):
                r = (s + gap) % MOD
                score = gap - (p - 1) + V[INDEX[(r, (c + p - 1) % MOD)]] - V[INDEX[(s, c)]]
                if score > 0:
                    positive_c.add(c)
                    highest = max(highest, score)
        out[p] = (len(positive_c), highest)
    return out


def primes_through(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\x00' * ((n-p*p)//p + 1)
    return (p for p in range(11, n + 1) if sieve[p])


def first_use_upper(M):
    K = (7 * M - 1) // 4
    U = 2 * K + 1
    bound = 0
    count = 0
    for p in primes_through(isqrt(2 * U) + 31):
        gap_upper = min(2 * p, 2 * U // p)
        debt = max(0, gap_upper - p + 30)
        if debt:
            count += 1
            bound += debt
    return K, U, count, bound


def is_prime(n):
    if n < 2:
        return False
    for q in range(2, isqrt(n) + 1):
        if n % q == 0:
            return False
    return True


def offset_ledger_control(M, steps, V):
    """Direct true-gcd events; verify the global signed offset ledger."""
    s, C = M + 2, 2 * M - 2
    startX = 2 * s - C
    growth_down = Bbig = Btotal = surcharge = large_credit = 0
    for _ in range(steps):
        hit = None
        for r in range(s + 1, min(C, s + isqrt(4 * (C + 1))) + 1):
            e = gcd(r, C - 1) if r % 2 == 0 else gcd(r - 2, C + 1)
            if e > 1:
                hit = (r, e)
                break
        assert hit is not None, (M, s, C)
        r, e = hit
        Cnext = C + e - 1
        dx = 2 * (r - s) - (e - 1)
        if dx < 0:
            growth_down += e - 1
        net = (r - s) - (e - 1) + V[INDEX[(r % MOD, Cnext % MOD)]] - V[INDEX[(s % MOD, C % MOD)]]
        if e >= 11 and is_prime(e) and net > 0:
            Btotal += net
            if e >= 61:
                Bbig += net
                large_credit += e - 59
                assert dx >= e - 57
            else:
                surcharge += 59 - e
        s, C = r, Cnext
    endX = 2 * s - C
    assert 2 * Bbig + large_credit <= endX - startX + growth_down
    assert 2 * Btotal + large_credit <= endX - startX + growth_down + surcharge
    return endX, growth_down, Bbig, large_credit, Btotal, surcharge


def main():
    V = potential()
    inert_residues = [c for c in range(0, MOD, 2) if inert(c)]
    assert inert_residues == [0,12,18,30,42,60,72,102,108,138,150,168,180,192,198]
    assert all(V[INDEX[(s, c)]] == 0 for c in inert_residues for s in range(MOD))
    print('PASS: 22050 mod-210 states, 58232 edges, 19 relaxations, V range 0..29')
    print('PASS: all 15 inert-horizon residue states have V=0')

    # For p>=43, a noninert horizon permits a clipped hit by gap 14;
    # a prior prime p hit has g<=13 and b<=13-(p-1)+29<=0.
    max_noninert = {p: noninert_potential_upper(p, V) for p in (31,37,41)}
    assert max_noninert == {31:-2, 37:-7, 41:-10}, max_noninert
    print('PASS: noninert p=31,37,41 upper debt:', max_noninert)

    # For prime p>=67, X'<=6 gives g <= (p+5)/2 and
    # b <= (65-p)/2 < 0. The five remaining primes 43..61 are finite.
    max_reset = {p: reset_potential_upper(p, V) for p in (43,47,53,59,61)}
    assert max_reset == {43:-2,47:-2,53:-1,59:-8,61:-15}, max_reset
    print('PASS: p=43..61 low-offset reset upper debt:', max_reset)
    print('PAPER: every positive-debt prime p>=43 exits with X\' >= 2p')
    print('PAPER: every positive-debt prime p>=61 has Delta X >= p-57 >= 4')

    # For each small prime, any positive-debt pre-horizon C belongs to
    # at most nu residue classes mod 210. Together with p | C +/- 1,
    # this gives exactly <= 2*nu admissible classes mod 210*p.
    small = small_prime_envelopes(V)
    expected_small = {11:(43,41),13:(41,42),17:(31,46),
                      19:(32,49),23:(28,52),29:(17,58)}
    assert small == expected_small, small
    print('PASS: small-prime (horizon classes mod 210, max debt):', small)

    M = 45895573
    K, U, nprime, Bfirst = first_use_upper(M)
    assert (K,U,nprime,Bfirst) == (80317252,160634505,2052,12241507)
    print(f'PASS: first-use envelope M={M}: K={K}, U={U}, '
          f'{nprime} positive-prime candidates, budget={Bfirst}')
    controls = {
        45895573: (37, (6,1154,144,184,216,54)),
        5875882249: (26, (60276,296,15091,30052,15106,30)),
    }
    for M, (steps, expected) in controls.items():
        got = offset_ledger_control(M, steps, V)
        assert got == expected, (M, got, expected)
        print(f'PASS: actual-gcd offset ledger M={M}, steps={steps}: {got}')
    print('Cap B and the global repeated-prime debt bound remain open.')


if __name__ == '__main__':
    main()
