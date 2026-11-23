#!/usr/bin/env python3
"""Independent integer-by-integer checks of the four-prime LOW7+q process.
Run: python3 research/low7_onehigh_literal_oracle.py
The general q>=109 proof is mathematical and does not rely on random tests.
"""
from math import gcd


def squarefree_clip(raw, ps):
    out = 1
    for p in ps:
        if raw % p == 0:
            out *= p
    return out


def literal(start_t, start_c, primes, bound=3000):
    t, c = start_t, start_c
    events = []
    for n in range(t + 1, t + bound + 1):
        if all((c - 1) % p and (c + 1) % p for p in primes):
            return events
        raw = gcd(n, c - 1) if n % 2 == 0 else gcd(n - 2, c + 1)
        d = squarefree_clip(raw, primes)
        if d > 1:
            c += d - 1
            events.append((n, d, c))
    raise AssertionError(('not stopped', start_t, start_c, primes))


def event_jump(t, c, primes):
    out = []
    for _ in range(200):
        hits = []
        for p in primes:
            if (c - 1) % p == 0:
                residue = 0
            elif (c + 1) % p == 0:
                residue = p + 2
            else:
                continue
            g = (residue - t) % (2 * p) or 2 * p
            hits.append((g, p))
        if not hits:
            return out
        g = min(g for g, _ in hits)
        d = 1
        for h, p in hits:
            if h == g:
                d *= p
        t += g
        c += d - 1
        out.append((t, d, c))
    raise AssertionError(('jump guard', t, c))


def main():
    cases = 0
    for q in (11, 13, 23, 29, 31, 53, 107, 109, 211):
        primes = (3, 5, 7, q)
        for m in range(7, 205, 2):
            a = literal(m + 2, 2 * m - 2, primes)
            b = event_jump(m + 2, 2 * m - 2, primes)
            assert a == b, (q, m, a, b)
            if q >= 109:
                assert sum(d % q == 0 for _, d, _ in a) <= 1
                assert (a[-1][0] - (m + 2) if a else 0) <= 2 * q + 112
            cases += 1
    actual = literal(5563, 5458, (3, 5, 7, 107))
    assert actual[:4] == [
        (5564, 107, 5564), (5567, 105, 5668),
        (5568, 3, 5670), (5673, 107, 5776)]
    print('LOW7_ONEHIGH_LITERAL_PASS cases=', cases, 'q107_sharp_witness=', actual[:4])


if __name__ == '__main__':
    main()
