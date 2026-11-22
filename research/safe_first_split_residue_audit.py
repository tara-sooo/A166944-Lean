#!/usr/bin/env python3
"""Exact arithmetic certificate of safe-first-p candidate classes and energy.
No probabilistic independence, no universal twin-prime result.
Uses only Python 3 standard library.
"""
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def verify():
    tested = 0
    for p in range(11, 2001, 2):
        if not prime(p):
            continue
        J = (p - 8) // 12  # safe G=2j, j in 0..J
        possible = {
            m for m in range(p)
            if any((2*m-3+2*j) % p == 0 or
                   (2*m-1+2*j) % p == 0
                   for j in range(J+1))
        }
        exact = {
            m for m in range(p)
            if any((2*m-3+2*k) % p == 0
                   for k in range(J+2))
        }
        assert possible == exact
        assert len(possible) == J + 2
        # Each M residue is distinct; its minimal compatible OLD growth
        # is the smallest h=2j making a terminal p clock active.
        minima = sorted(
            min(2*j for j in range(J+1)
                if (2*m-3+2*j) % p == 0 or
                   (2*m-1+2*j) % p == 0)
            for m in possible
        )
        assert minima == [0, 0] + list(range(2, 2*J+1, 2))
        for b in range(1, len(minima)+1):
            assert sum(minima[:b]) >= max(0,b-2)*max(0,b-1)
        tested += 1
    assert tested == 299
    print('PASS', tested,
          'odd primes p in [11,2000]: exact safe clock residue count')
    print('PASS minimal old growth packing per complete p-residue block')
    print('No global dyadic average or twin-prime infinitude proved')

if __name__ == '__main__':
    verify()
