#!/usr/bin/env python3
"""Independent literal integer-by-integer GCD verification of controlled squarefree wheel."""
from math import gcd, isqrt, prod


def primes_le(B):
    return [p for p in range(3, B + 1, 2) if all(p % r for r in range(3, isqrt(p) + 1, 2))]


def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def next_clock(t, C, ps, K):
    value = K + 1
    for p in ps:
        if (C - 1) % p == 0:
            r = 0
        elif (C + 1) % p == 0:
            r = p + 2
        else:
            continue
        delta = (r - t) % (2 * p) or 2 * p
        value = min(value, t + delta)
    return value


def choose(policy, n, C, factors, K, ps):
    if policy == 'PRODUCT':
        return prod(factors)
    if policy == 'MIN':
        return factors[0]
    if policy == 'MAX':
        return factors[-1]
    candidates = []
    for mask in range(1, 1 << len(factors)):
        d = prod(factors[i] for i in range(len(factors)) if mask & (1 << i))
        after = C + d - 1
        assert after <= 2 * n
        if policy == 'MIN_ACTIVE':
            ac = sum((after - 1) % p == 0 or (after + 1) % p == 0 for p in ps)
            candidates.append(((ac, d), d))
        elif policy == 'MAX_WAIT':
            wait = next_clock(n, after, ps, K) - n
            candidates.append(((-wait, d), d))
        else:
            raise ValueError(policy)
    return min(candidates)[1]


def audit(X):
    B = isqrt(7 * X)
    B += B * B < 7 * X
    ps = primes_le(B)
    for policy in ('PRODUCT', 'MIN', 'MAX', 'MIN_ACTIVE', 'MAX_WAIT'):
        events = ownerR = ownerF = growth = good = bad = 0
        for M in range(X + 1, 2 * X, 2):
            C, s = 2 * M - 2, M + 2
            K = (7 * M - 1) // 4
            seen = set()
            last = s
            for n in range(s + 1, K + 1):
                raw = gcd(n, C - 1) if n % 2 == 0 else gcd(n - 2, C + 1)
                factors = [p for p in ps if raw % p == 0]
                if not factors:
                    continue
                d = choose(policy, n, C, factors, K, ps)
                C += d - 1
                assert C <= 2 * n and C % 2 == 0
                last = n
                events += 1
                growth += d - 1
                owner = next((p for p in ps if p >= 11 and d % p == 0), None)
                if owner:
                    if owner in seen:
                        ownerR += 1
                    else:
                        ownerF += 1
                        seen.add(owner)
            both = prime(C - 1) and prime(C + 1)
            good += both
            bad += not both
            assert both or K - last < 2 * B
        print('GREEDY_LITERAL_PASS', 'X=', X, 'policy=', policy, 'good=',good,'bad=',bad,
              'events=',events,'growth=',growth,'ownerF=',ownerF,'ownerR=',ownerR)


if __name__ == '__main__':
    for X in (256, 512, 1024):
        audit(X)
