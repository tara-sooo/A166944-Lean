#!/usr/bin/env python3
"""Independent literal per-n MIN wheel: height identity, reset coalescence, far donors.
No external packages. Run: python3 research/min_prime_gap_height_literal_oracle.py
"""
from collections import Counter
from math import gcd, isqrt


def primes_to(b):
    return [p for p in range(3, b + 1, 2)
            if all(p % d for d in range(3, isqrt(p) + 1, 2))]


def events(M, B):
    ps = primes_to(B)
    C = 2 * M - 2
    out = []
    for n in range(M + 3, (7 * M - 1) // 4 + 1):
        raw = gcd(n if n % 2 == 0 else n - 2,
                  C - 1 if n % 2 == 0 else C + 1)
        p = next((p for p in ps if raw % p == 0), None)
        if p is None:
            continue
        C += p - 1
        h = 2 * n - C
        assert h >= 0
        assert (h if n % 2 == 0 else h - 6) % (2 * p) == 0
        out.append((n, p, h, C))
    return out


def audit(X):
    B = isqrt(7 * X)
    B += B * B < 7 * X
    resets = Counter()
    top = 0
    for M in range(X + 1, 2 * X, 2):
        for n, p, h, C in events(M, B):
            if 2 * p >= B:
                top += 1
                if h == (0 if n % 2 == 0 else 6):
                    resets[n, C] += 1
    ans = (top, sum(resets.values()), len(resets),
           max(resets.values(), default=0))
    expected = {256: (87, 15, 6, 4),
                512: (137, 124, 15, 29),
                1024: (153, 143, 18, 46)}
    assert ans == expected[X], (X, ans, expected[X])
    print("MIN_LITERAL_RESET_PASS", "X=", X, "B=", B, "stats=", ans)


def witness():
    X, M, q = 65536, 97289, 197
    B = isqrt(7 * X)
    B += B * B < 7 * X
    e = events(M, B)
    hits = [j for j, (_, p, _, _) in enumerate(e) if p == q]
    assert len(hits) >= 2
    a, b = hits[:2]
    assert (e[a][0], e[b][0], e[a][2], e[b][2]) == (97517, 97712, 6, 0)
    high = [p for _, p, _, _ in e[a + 1:b] if p >= 11]
    low = sum(p - 1 for _, p, _, _ in e[a + 1:b] if p <= 7)
    G = sum(p - 1 for _, p, _, _ in e[a + 1:b])
    assert high == [101, 83, 11] and low == 8 and G == 200
    assert all(abs(q - r) > 68 for r in high)
    assert G % q == 3
    print("MIN_FAR_DONOR_LITERAL_PASS", "M=", M, "q=", q,
          "times=", (e[a][0], e[b][0]), "donors=", high, "gain=", G)


if __name__ == "__main__":
    for X in (256, 512, 1024):
        audit(X)
    witness()
