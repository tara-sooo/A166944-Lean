#!/usr/bin/env python3
"""A166944 arithmetic audit: offset direction and synthetic reset obstruction.

Finite, standard-library-only checks.  None of the synthetic starting values
is asserted to be an attained A166944 maximum.  This is NOT a proof of Cap B.
"""
from math import gcd, isqrt

M = 404_983
RESET_STEPS = (
    (2, 5), (1, 3), (119, 239), (1, 9), (2, 5), (4, 3),
    (8, 23), (4, 9), (6, 13), (5, 5), (1, 3), (3, 7),
    (6, 13), (14, 29), (1, 9), (5, 5), (1, 3), (9, 19),
    (11, 29), (2, 5), (1, 3), (1, 3), (5, 5), (1, 9),
    (2, 5), (4, 3), (5, 11), (1, 3),
)


def is_prime(n):
    if n < 2:
        return False
    return all(n % p for p in range(2, isqrt(n) + 1))


def hit(n, c):
    return gcd(n, c - 1) if n % 2 == 0 else gcd(n - 2, c + 1)


def actual_at(k):
    dvalue, D = 1, 2
    for n in range(3, k + 1):
        dvalue = hit(n, D)
        D += dvalue - 1
    return dvalue, D


def check_long_reset():
    assert is_prime(M) and is_prime(M - 2)
    s, C = M + 2, 2 * M - 2
    for idx, (gap, increment) in enumerate(RESET_STEPS, 1):
        r = s + gap
        assert r <= C
        for j in range(s + 1, r):
            assert hit(j, C) == 1, (idx, j, C)
        assert hit(r, C) == increment, (idx, r, C, increment)
        s, C = r, C + increment - 1
        assert 2 * s - C in (0, 6)
    T = s - (M + 2)
    G = C - (2 * M - 2)
    assert (s, C, T, G, 2 * s - C) == (405_210, 810_414, 225, 450, 6)
    assert G == 2*T + 6-(2*s-C)
    d_real, D_real = actual_at(M + 2)
    assert (d_real, D_real) == (1, 713_832)
    print('PASS: twin-prime-shaped synthetic M=404983: 28 exact first hits,')
    print('      X always 0 or 6; T=225, G=450; true d(M+2)=1 (not a record).')


def check_short_counterexamples():
    for m, end, horizon, growth in ((349, 474, 828, 132),
                                     (601, 738, 1428, 228),
                                     (823, 978, 1950, 306)):
        assert is_prime(m) and is_prime(m - 2)
        s, C = m+2, 2*m-2
        cutoff = (7*m-1)//4
        while True:
            next_hit = next((j for j in range(s+1, C+1) if hit(j,C)>1), None)
            if next_hit is None or next_hit>cutoff:
                break
            e = hit(next_hit,C)
            s,C = next_hit,C+e-1
        assert (s,C,C-(2*m-2)) == (end,horizon,growth)
        assert is_prime(C-1) and is_prime(C+1)
        assert s<cutoff<=C
        assert 4*s<=7*m-1
        assert 1000*C>2335*m
        print(f'PASS: synthetic M={m}, quiet before K={cutoff}, '
              f'G={growth}; numerical cutoff endpoint valid although sample 2335 fails.')


def check_exact_offset_threshold():
    for m in range(9, 1000, 2):
        k=(7*m-1)//4
        z=1165*m-(1500 if m%4==1 else 500)
        assert 2000*k-2335*m==z
        for D in range(2*m-2, 4*m, 2):
            assert (1000*D<=2335*m)==(1000*(2*k-D)>=z)
    print('PASS: fixed-sample <=> exact offset lower bound for both odd M mod 4 cases.')

if __name__ == '__main__':
    check_long_reset()
    check_short_counterexamples()
    check_exact_offset_threshold()
    print('Cap B for genuine large canonical records remains OPEN.')
