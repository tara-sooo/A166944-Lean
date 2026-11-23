#!/usr/bin/env python3
"""Exact inverse map for the original parity-specific squarefree clipped GCD.

Run: python3 research/exact_inverse_gcd_fold_audit.py
All numerical checks are finite; the lemmas in the companion note are paper arguments.
"""
from collections import defaultdict
from math import gcd, isqrt


def clipped_rad(n: int, B: int) -> int:
    value = 1
    for p in range(3, B + 1, 2):
        if all(p % j for j in range(3, isqrt(p) + 1, 2)) and n % p == 0:
            value *= p
    return value


def spec(n: int, B: int):
    sigma = 1 if n % 2 == 0 else -1
    a = n if n % 2 == 0 else n - 2
    return clipped_rad(a, B), sigma


def forward(n: int, c: int, B: int):
    A, sigma = spec(n, B)
    d = gcd(A, c - sigma)
    return c + d - 1


def inverse_candidates(n: int, y: int, B: int):
    A, sigma = spec(n, B)
    D = gcd(A, y + 1 - sigma)
    return sorted(
        (y - d + 1, d)
        for d in range(1, D + 1)
        if D % d == 0 and y - d + 1 >= 2
        and gcd(A, y + 1 - sigma - d) == d
    )


def check_exact_inverse():
    tested = 0
    for n in range(5, 226):
        actual = defaultdict(list)
        for c in range(2, 1002, 2):
            actual[forward(n, c, 53)].append(c)
            tested += 1
        for y in range(2, 1400, 2):
            expected = sorted(actual[y])
            calculated = [c for c, d in inverse_candidates(n, y, 53)
                          if 2 <= c <= 1000]
            assert expected == calculated, (n, y, expected, calculated)
    print('INVERSE_FORMULA_PASS', 'test_inputs', tested,
          'n_range', '5..225', 'input_even_C', '2..1000')


def check_fold_and_moments():
    for n in (15, 30, 42, 105, 210, 462):
        B = 53
        A, sigma = spec(n, B)
        # Since F(c+2A)=F(c)+2A, the induced map of A even
        # classes modulo 2A is a finite function with mean preimage count 1.
        counts = [0] * A
        for k in range(A):
            c = 2 * (k + 10 * A)
            y = forward(n, c, B)
            counts[(y // 2) % A] += 1
        assert sum(counts) == A
        squares = sum(z * z for z in counts)
        max_branch = max(counts)
        prime_factors = [p for p in range(3, B + 1, 2)
                         if A % p == 0 and all(p % j for j in range(3, isqrt(p) + 1, 2))]
        # The upper bound on average square of inverse multiplicity
        # is prod_(p|A) (1+3/p).
        majorant = 1.0
        for p in prime_factors:
            majorant *= 1 + 3 / p
        assert squares / A <= majorant + 1e-10, (n, squares, A, majorant)
        print('PERIODIC_PREIMAGE_PASS', 'n', n, 'A', A, 'average', 1,
              'second_moment', round(squares / A, 8),
              'bound', round(majorant, 8), 'max_branch', max_branch)
    assert inverse_candidates(30, 30, 53) == [(16, 15), (26, 5), (28, 3), (30, 1)]
    print('PRIME_FOLD_PASS', 'n', 30, 'Y', 30, 'predecessors', [16, 26, 28, 30])


def check_general_merger_identity():
    for n in (15, 30, 42, 105, 210):
        B = 53
        w = {c: 1 + (c // 2 % 13) for c in range(2, 700, 2)}
        out = defaultdict(int)
        for c, count in w.items():
            out[forward(n, c, B)] += count
        lhs = sum(t * t for t in out.values()) - sum(t * t for t in w.values())
        rhs = 0
        for y in out:
            prevs = inverse_candidates(n, y, B)
            for j in range(len(prevs)):
                for k in range(j + 1, len(prevs)):
                    rhs += 2 * w.get(prevs[j][0], 0) * w.get(prevs[k][0], 0)
        assert lhs == rhs, (n, lhs, rhs)
        print('GENERAL_MERGER_PASS', 'n', n, 'exact_l2_increase', lhs)


def check_bilinear_merger():
    # For a prime-only clock A_n=q, the ONLY nontrivial merger is
    # between pre-states y and y-q+1 at output y == sigma-1 mod q.
    n, B = 34, 53  # n-2? even n=34 => A=17
    A, sigma = spec(n, B)
    assert A == 17
    w = {c: (c // 2) % 7 + 1 for c in range(2, 400, 2)}
    out = defaultdict(int)
    for c, m in w.items():
        out[forward(n, c, B)] += m
    delta = sum(m * m for m in out.values()) - sum(m * m for m in w.values())
    paired = 2 * sum(w.get(y, 0) * w.get(y - A + 1, 0)
                     for y in out if (y + 1 - sigma) % A == 0)
    assert delta == paired, (delta, paired)
    print('BILINEAR_FOLD_PASS', 'q', A, 'exact_l2_increase', delta)


if __name__ == '__main__':
    check_exact_inverse()
    check_fold_and_moments()
    check_general_merger_identity()
    check_bilinear_merger()
