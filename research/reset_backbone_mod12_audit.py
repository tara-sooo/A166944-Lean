#!/usr/bin/env python3
"""A166944: exact aligned-reset prime clocks and 12-wheel reload audit.

Standard library only; no Cap B or twin-prime infinitude theorem.
See 2026-11-22-reset-backbone-mod12-recharge-and-sentinel.md.
"""
from collections import Counter
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def factors(n):
    out = []
    d = 3
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 2
    if n > 1:
        out.append(n)
    return out


def event(r, C):
    return gcd(r if r % 2 == 0 else r - 2,
               C - 1 if r % 2 == 0 else C + 1)


def clock(s, C):
    x = 2 * s - C
    assert (s % 2 == 0 and x == 0) or (s % 2 == 1 and x == 6)
    assert C % 4 == 0
    clocks = []
    sentinels = []
    for sign in (-1, 1):
        for q in factors(C + sign):
            if sign == -1:  # even target
                k = (5 if q == 5 and x == 6 else 1) if q % 4 == 1 else 3
                g = (k * q - x - 1) // 2
                assert (s + g) % 2 == 0
                if q % 4 == 3:
                    sentinels.append(q)
            else:  # odd target
                k = -1 if q == 3 and x == 0 else (1 if q % 4 == 1 else 3)
                g = (k * q - x + 5) // 2
                assert (s + g) % 2 == 1
            assert g > 0
            clocks.append((g, q, sign))
    assert sentinels
    return min(g for g, _, _ in clocks), min(sentinels)


def reset_mode(s, C, r, e):
    x = 2 * s - C
    if e < 9 or not ((x == 0 and s % 2 == 0) or (x == 6 and s % 2 == 1)):
        return None
    g = r - s
    u = 2 * g + x + (1 if r % 2 == 0 else -5)
    assert u > 0 and u % e == 0
    k = u // e
    assert k in (1, 3)
    if k == 1:
        assert e % 4 == 1 and (prime(e) or e in (9, 25))
        gap, q = clock(s, C)
        assert g == gap
        if prime(e):
            assert e <= 3 * q - (4 if r % 2 == 0 else 8)
    else:
        assert prime(e)
    return k


def check_12_reload():
    for p in range(13, 500, 12):
        if not prime(p):
            continue
        for first in (0, 1):
            for later in (0, 1):
                after = 0 if first == 0 else -2
                target = 1 if later == 0 else -1
                min_growth = next(R for R in range(12, 12 * (12 * p + 1), 12)
                                  if (after + R - target) % p == 0)
                expected = (p - 1 if (first, later) == (0, 1)
                            else 9 * p + 3 if (first, later) == (1, 0)
                            else 11 * p + 1)
                assert min_growth == expected
    # One-separator, p, q, p, where both keys are primes 1 mod 12.
    for p in range(13, 250, 12):
        if not prime(p):
            continue
        for q in range(13, 5000, 12):
            if q == p or not prime(q):
                continue
            for first in (0, 1):
                for later in (0, 1):
                    after = 0 if first == 0 else -2
                    target = 1 if later == 0 else -1
                    if (after + q - 1 - target) % p == 0:
                        assert (first, later) != (0, 1)
                        assert q >= (9 * p + 4 if (first, later) == (1, 0)
                                     else 11 * p + 2)
    print("12-wheel reload and one-separator residue tests PASS")


def run(s0, C0, end):
    C = C0
    last_s, last_C = s0, C0
    events = 0
    chain = []
    stats = Counter()
    for r in range(s0 + 1, end + 1):
        e = event(r, C)
        if e > 1:
            events += 1
            k = reset_mode(last_s, last_C, r, e)
            if k == 1:
                g = r - last_s
                if chain:
                    prior_s, prior_C, prior_r, prior_e, prior_g = chain[-1]
                    assert prior_r == last_s
                    assert prime(prior_e) or prime(e)
                    if prior_g > 6 and g > 6:
                        assert prior_C % 3 == 0 and last_C % 3 == 0
                        assert prior_e % 12 == 1
                if not prime(e):
                    stats["composite_" + str(e)] += 1
                chain.append((last_s, last_C, r, e, g))
                stats["resets"] += 1
            else:
                if chain:
                    stats["runs"] += 1
                    stats["longest"] = max(stats["longest"], len(chain))
                chain = []
            last_s, last_C = r, C + e - 1
            C += e - 1
    if chain:
        stats["runs"] += 1
        stats["longest"] = max(stats["longest"], len(chain))
    return C, events, dict(stats)


def main():
    count = 0
    for s in range(13, 20113):
        C = 2 * s - (6 if s % 2 else 0)
        g, sentinel = clock(s, C)
        assert sentinel % 4 == 3 and (C - 1) % sentinel == 0
        assert event(s + g, C) > 1
        for j in range(1, g):
            assert event(s + j, C) == 1
        count += 1
    assert count == 20100
    # The two sharp 3 mod 4 sentinel examples, with q=7.
    for s, C, r, e in [(63, 120, 68, 17), (399, 792, 405, 13)]:
        g, q = clock(s, C)
        assert q == 7 and r == s + g and event(r, C) == e
        assert e == 3 * q - (4 if r % 2 == 0 else 8)
    # A composite nine at an odd reset is followed by an immediate three.
    assert clock(43, 80)[0] == 4 and event(47, 80) == 9
    assert event(48, 88) == 3
    check_12_reload()
    C, n, stats = run(2, 2, 2500000)
    assert C == 2860770 and n == 249
    assert stats == {"resets": 26, "runs": 18, "longest": 3,
                     "composite_9": 7, "composite_25": 3}, stats
    print("Actual A166944 n<=2,500,000:", n, "nonunit events after n=2", stats)
    for M in (367, 100549, 101119):
        K = (7 * M - 1) // 4
        C, n, stats = run(M + 2, 2 * M - 2, K)
        print("Artificial canonical-shaped M=", M, "K=", K,
              "events=", n, "terminal C=", C, "aligned modes=", stats)
    print("PASS: exact clocks, sentinel, 12-wheel, and composite-spacing audits")


if __name__ == "__main__":
    main()
