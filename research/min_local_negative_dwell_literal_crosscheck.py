"""Literal tick gcd versus factor-calendar MIN, with exact integer dwell packing."""
from collections import defaultdict
from math import gcd, isqrt
import sys


def audit(R):
    T = isqrt(2 * R + 1)
    T += T * T < 2 * R + 1
    lo, hi = 6 * ((R + 5) // 6), 6 * (2 * R // 6)
    spf = list(range(2 * R + 2))
    for p in range(2, isqrt(2 * R + 1) + 1):
        if spf[p] == p:
            for n in range(p * p, len(spf), p):
                if spf[n] == n:
                    spf[n] = p

    def factors(n):
        while n > 1:
            p = spf[n]
            yield p
            while n % p == 0:
                n //= p

    def literal(A):
        x, n = A, 3 - A // 2
        dw = defaultdict(int)
        for _ in range(T):
            dw[x] += 1
            n += 1
            g = gcd(n, x + 1) if n % 2 == 0 else gcd(n - 2, x - 1)
            if g > 1:
                x -= spf[g] - 1
            assert n + x // 2 >= 0
        return x, dict(dw)

    def calendar(A):
        x, n = A, 3 - A // 2
        end = n + T
        dw = defaultdict(int)
        while n < end:
            candidates = [( (-n) % (2*p) or 2*p, p) for p in factors(x + 1)]
            candidates += [((p + 2 - n) % (2*p) or 2*p, p) for p in factors(x - 1)]
            wait, p = min(candidates)
            dw[x] += min(wait, end - n)
            if n + wait > end:
                return x, dict(dw)
            n += wait
            x -= p - 1
            assert n + x // 2 >= 0
        return x, dict(dw)

    groups = defaultdict(list)
    roots = ticks = visits = 0
    for A in range(lo, hi + 1, 6):
        y, dw = literal(A)
        assert (y, dw) == calendar(A)
        assert sum(dw.values()) == T
        assert A - y <= 2 * T + 6
        roots += 1
        ticks += T
        for x, count in dw.items():
            assert x <= A
            C = min(T, 2 * min(spf[x - 1], spf[x + 1]))
            assert 0 < count <= C
            groups[x].append((A - x, count))
            visits += 1
    total_capacity = total_gain = packing_checks = 0
    for x, group in groups.items():
        C = min(T, 2 * min(spf[x - 1], spf[x + 1]))
        m = sum(w for _, w in group)
        G6 = sum(w * (g + 6) for g, w in group)
        assert C * G6 >= 3 * m * m
        total_capacity += C
        total_gain += G6
        cum = 0
        for d, w in sorted(group):
            cum += w
            assert cum <= C * (1 + d // 6)
            packing_checks += 1
    assert 3 * ticks * ticks <= total_capacity * total_gain
    return dict(R=R, roots=roots, ticks=ticks, visits=visits,
                positions=len(groups), packing_checks=packing_checks)


if __name__ == '__main__':
    for R in map(int, sys.argv[1:] or ['12000', '48000']):
        print(audit(R))
