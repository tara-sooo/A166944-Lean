#!/usr/bin/env python3
"""Independent n-by-n original GCD oracle for MIN-prime donor renewal classification."""
from collections import Counter
from math import gcd, isqrt


def primes_le(B):
    return [p for p in range(3, B + 1, 2) if all(p % r for r in range(3, isqrt(p) + 1, 2))]


def audit(X):
    B = isqrt(7 * X)
    B += B*B < 7*X
    ps = primes_le(B)
    result = Counter()
    for M in range(X + 1, 2*X, 2):
        C = 2*M - 2
        s = M + 2
        K = (7*M - 1)//4
        es = []
        last = {}
        for n in range(s + 1, K + 1):
            raw = gcd(n, C-1) if n % 2 == 0 else gcd(n-2, C+1)
            fac = [p for p in ps if raw % p == 0]
            if not fac: continue
            p = min(fac)
            curr = len(es)
            if p >= 11:
                if p not in last:
                    result['F'] += 1
                else:
                    result['R'] += 1
                    prev = last[p]
                    intermediate = es[prev+1:]
                    donors = [r for tm, r in intermediate if r >= 11]
                    low_g = sum(r-1 for tm, r in intermediate if r <= 7)
                    m = len(donors)
                    assert low_g <= 34 * (m+1)
                    c = (1 if n % 2 == 0 else -1) if es[prev][0] % 2 == 0 else (3 if n % 2 == 0 else 1)
                    E = sum(r-1 for tm, r in intermediate)
                    assert (E-c) % p == 0
                    result['m0' if m==0 else 'm1' if m==1 else 'm2' if m==2 else 'm3'] += 1
                    assert m>0 or p<=31
                    if 2*p >= B:result['topR'] += 1
                    if m == 1 and 2*p > B+68:
                        assert -4 <= p-donors[0] <= 68
                        result['nearTop'] += 1
                last[p] = curr
            C += p - 1
            es.append((n,p))
            result['events'] += 1
            assert C<=2*n
        result['growth'] += C-(2*M-2)
    assert result['R'] == sum(result[k] for k in ('m0','m1','m2','m3'))
    print('MIN_DONOR_LITERAL_PASS X=',X,'B=',B,dict(result))

if __name__ == '__main__':
    for x in (256,512,1024):audit(x)
