#!/usr/bin/env python3
"""Finite exact integer checks for large-prime clock support intersections.

The paper theorem is universal; this script exhaustively checks small finite
ranges, sharp examples, and the special delta=2 counterexample. Standard
library only. No twin-prime infinitude or Cap B proof.
"""
from math import gcd, isqrt


def spf_sieve(limit):
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def factors(n, spf):
    result = set()
    while n > 1:
        p = spf[n]
        result.add(p)
        while n % p == 0:
            n //= p
    return result


def test_all_pair_states():
    limit = 10000 + 4 * 31 + 2
    spf = spf_sieve(limit + 3)
    active = {
        c: (factors(c - 1, spf) | factors(c + 1, spf)) - {2}
        for c in range(2, limit + 1, 2)
    }
    total = 0
    twins = 0
    for P in (7, 11, 17, 31):
        count = 0
        two = 0
        for C in range(2, 10001, 2):
            for delta in range(4, 4 * P - 2, 2):
                Cnew = C + delta
                common = {p for p in active[C] & active[Cnew] if p >= P}
                n = delta // 2
                assert common <= {n - 1, n, n + 1}
                assert len(common) <= 2
                if len(common) == 2:
                    assert common == {n - 1, n + 1}
                    assert n % 2 == 0
                    assert (C + 1) % (n - 1) == 0
                    assert (C - 1) % (n + 1) == 0
                    assert (Cnew - 1) % (n - 1) == 0
                    assert (Cnew + 1) % (n + 1) == 0
                    two += 1
                count += 1
        print(f'PASS P={P}: {count} exact horizon pairs, twin overlaps={two}')
        total += count
        twins += two
    assert (total, twins) == (600000, 108)


def test_sharp_examples():
    C, Cnew = 846, 870
    assert gcd(430, C - 1) == 5
    assert (C - 1) % 13 == 0 and (C + 1) % 11 == 0
    assert (Cnew + 1) % 13 == 0 and (Cnew - 1) % 11 == 0
    assert Cnew - (C + 5 - 1) == 20

    P, C, Cnew = 7, 456, 482
    assert Cnew - C == 4 * P - 2
    assert gcd(230, C - 1) == 5
    assert (C - 1) % (7 * 13) == 0
    assert (Cnew + 1) % 7 == 0 and (Cnew - 1) % 13 == 0

    C, Cnew = 85084, 85086
    assert gcd(42546, C - 1) == 3 and Cnew == C + 2
    assert all((C + 1) % p == (Cnew - 1) % p == 0
               for p in (7, 11, 13, 17))
    print('PASS opposite-side twin, sharp endpoint, exact delta=2 exception')


if __name__ == '__main__':
    test_all_pair_states()
    test_sharp_examples()
    print('PASS finite exact capacity tests; global localization remains OPEN')
