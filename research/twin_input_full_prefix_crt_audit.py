#!/usr/bin/env python3
"""Exact full-prefix CRT compatibility and twin-input cutoff residue audit.
Python 3 standard library. Paper theorem checks, NOT Cap B or twin prime proof.
"""
from math import gcd, lcm, isqrt


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def test(r, C):
    return gcd(r if r % 2 == 0 else r - 2,
               C - 1 if r % 2 == 0 else C + 1)


def prefix(M, T):
    """Exact original gcd from the artificial canonical-shaped input M."""
    assert M % 2 == 1
    C = 2 * M - 2
    G = 0
    residuals, increments = [], []
    for t in range(1, T + 1):
        r = M + 2 + t
        index = M + t + 2 if r % 2 == 0 else M + t
        residual = 2*t + (7 if r % 2 == 0 else 1) - G
        e = test(r, C)
        assert e == gcd(index, abs(residual)), (M, t, e, residual)
        residuals.append(residual)
        increments.append(e)
        G += e - 1
        C += e - 1
    return residuals, increments, C


def periodic_prefix_lift(M, T, B=59):
    """Preserves every intermediate gcd, not only a sampled event list."""
    R, e, C = prefix(M, T)
    assert all(x != 0 for x in R)
    P = 2
    for r in R:
        P = lcm(P, abs(r))
    R1, e1, C1 = prefix(M + P, T)
    assert (R1, e1, C1 - C) == (R, e, 2*P)
    Q = 1
    for q in range(2, B + 1):
        if prime(q):
            Q *= q
    # The lifted starting values remain coprime to every prime <= B.
    huge_M = M + P*Q
    R2, e2, C2 = prefix(huge_M, T)
    assert (R2, e2, C2 - C) == (R, e, 2*P*Q)
    assert all(huge_M % q not in (0, 2)
               for q in range(2, B + 1) if prime(q))
    print('CRT prefix M', M, 'T', T, 'nonunit hits', sum(x > 1 for x in e),
          'lift modulus bits', P.bit_length(), 'PASS')


def cutoff_index_sieve(M, radius=8):
    K = (7*M - 1)//4
    zeta = 7*M - 1 - 4*K
    assert zeta in (0, 2)
    # General identity 7M=4*(r-2*(r odd))+A.
    for delta in range(-radius, radius + 1):
        r = K + delta
        if r < 3:
            continue
        index = r if r % 2 == 0 else r - 2
        A = 1 + zeta - 4*delta + 8*(r % 2)
        assert 7*M == 4*index + A
        for q in (3, 5, 7, 11, 13, 17, 19, 23, 29):
            if index % q == 0:
                assert (7*M-A) % q == 0
                if prime(M) and prime(M-2) and M > q+2 and q != 7:
                    assert A % q not in (0, 14 % q)
    # The cutoff itself can never have 7 as an increment factor,
    # for ANY odd M, regardless of input primality.
    assert (K if K % 2 == 0 else K - 2) % 7 != 0
    if prime(M) and prime(M-2) and M >= 7:
        if K % 2 == 1 or M % 24 != 7:
            assert (K if K % 2 == 0 else K-2) % 3 != 0
        if M % 24 == 7:
            assert K % 2 == 0 and K % 3 == 0
            assert all((K-1) % q != 0 for q in (3, 5, 7))


def trace_to_cutoff(M):
    K = (7*M - 1)//4
    C = 2*M - 2
    hits = []
    for r in range(M + 3, K + 1):
        e = test(r, C)
        if e > 1:
            hits.append((r, e))
            C += e - 1
    return K, C, hits


def local_twin_witness(M, p, q, C):
    """Locally exact BAD crossing, but NOT reachable from the canonical start."""
    assert prime(M) and prime(M-2) and M > 1000
    K = (7*M-1)//4
    assert K % 2 == 0
    s, H = K - 1, C - (p - 1)
    assert 2*M-2 <= H <= 2*s and C <= 2*K
    assert test(K, H) == p and test(K+1, C) == q
    T, G = s-(M+2), H-(2*M-2)
    # Even the W potential with arbitrary endpoints 0<=W<=32 permits this.
    assert 9*G - 4*T >= 32
    real_K, real_C, hits = trace_to_cutoff(M)
    assert real_K == K and real_C != C
    assert prime(real_C-1) and prime(real_C+1)
    print('TWIN-COMPATIBLE ARTIFICIAL BAD crossing M', M,
          'p->q', p, q, 'local C', C, 'actual C', real_C,
          'actual event count', len(hits), 'PASS')


def main():
    for M,T in ((100549, 750), (101119, 1500), (45895573, 1600)):
        assert prime(M) and prime(M-2)
        periodic_prefix_lift(M, T)
        cutoff_index_sieve(M, 25)
    for M in range(7, 200000, 2):
        cutoff_index_sieve(M, 0)
        if prime(M) and prime(M-2):
            cutoff_index_sieve(M, 8)
    local_twin_witness(101119, 3, 11, 236004)
    local_twin_witness(100549, 5, 3, 241340)
    print('PASS: exact all-prefix CRT lifts and prime-index barriers')


if __name__ == '__main__':
    main()
