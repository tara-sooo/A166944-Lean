#!/usr/bin/env python3
"""Independent direct n-by-n MIN clipped gcd wheel and weighted reset moment.
Run: python3 research/min_reset_weighted_moments_literal.py 256 512 1024
"""
from collections import defaultdict
from math import gcd, isqrt
import sys


def primes(B):
    return [p for p in range(3, B + 1, 2) if all(p % d for d in range(3, isqrt(p) + 1, 2))]


def trajectory(t, c, end, ps):
    events = []
    for n in range(t + 1, end + 1):
        r = gcd(n, c - 1) if n % 2 == 0 else gcd(n - 2, c + 1)
        p = next((p for p in ps if r % p == 0), None)
        if p:
            c += p - 1
            events.append((n, c, p))
    return events


def audit(X):
    B = isqrt(7 * X)
    if B * B < 7 * X:
        B += 1
    Kmax = (7 * (2 * X - 1) - 1) // 4
    ps = primes(B)
    fibres = defaultdict(list)
    Hpre = Hpost = E = 0
    for M in range(X + 1, 2 * X, 2):
        es = trajectory(M + 2, 2 * M - 2, (7 * M - 1) // 4, ps)
        hit = False
        for n, c, p in es:
            if p >= 11:
                if not hit:
                    Hpre += 1
                else:
                    Hpost += 1
            if not hit and p >= 11 and 2 * n - c == (6 if n % 2 else 0):
                hit = True
                fibres[(n, c)].append(M)
                E += c - (2 * M - 2)
    W2 = sum(len(m) ** 2 for m in fibres.values())
    U2 = WU = U_sum = 0
    for (n, c), ms in fibres.items():
        U = sum(p >= 11 for _, _, p in trajectory(n, c, Kmax, ps))
        WU += len(ms) * U
        U2 += U * U
        U_sum += U
    assert WU == Hpost, (WU, Hpost)
    assert W2 <= sum(map(len, fibres.values())) + E // 2
    assert E <= (B + 33) * Hpre
    U2all = 0
    for n in range(X + 3, Kmax):
        c = 2 * n - (6 if n % 2 else 0)
        U = sum(p >= 11 for _, _, p in trajectory(n, c, Kmax, ps))
        U2all += U * U
    assert U2 <= U2all
    print('RESET_WEIGHTED_LITERAL_PASS', f'X={X}', f'B={B}', f'atoms={len(fibres)}',
          f'covered={sum(map(len, fibres.values()))}', f'Hpre={Hpre}', f'Hpost={Hpost}',
          f'entranceGain={E}', f'fibreL2={W2}', f'atomU2={U2}', f'allTimeU2={U2all}')


if __name__ == '__main__':
    for X in map(int, sys.argv[1:] or (256, 512)):
        audit(X)
