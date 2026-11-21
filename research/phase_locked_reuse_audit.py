"""Exact integer checks for phase-locked first-hit prime reuse.

No external libraries and no claimed proof of Cap B or twin primes.
The synthetic chain is not attained from the original A166944 initial value.
"""
from math import gcd, isqrt

W = 420


def min_middle(p, sign):
    """Smallest q > 1 with q = 1 (mod 420) and q = sign (mod p)."""
    assert p > 3 and p % W == 1
    if sign == 2:
        return (W - 1) * p + 2
    if sign == 4:
        return (W - 3) * p + 4
    raise ValueError(sign)


def check_modular_minima():
    for p in (421, 2521, 3361, 5881, 10921):
        for sign in (2, 4):
            lower = min_middle(p, sign)
            assert lower % W == 1 and lower % p == sign
            assert all(q % p != sign for q in range(1, lower, W))
        assert min_middle(p, 2) == 419 * p + 2
    print("CRT middle-increment minima PASS")


def hit(r, C):
    return gcd(r if r % 2 == 0 else r - 2,
               C - 1 if r % 2 == 0 else C + 1)


def synthetic_exact_triple():
    M = 9_801_898_053_991
    s, C = M + 2, 2 * M - 2
    events = (421, 176401, 421)
    seen = []
    for e in events:
        assert e % 420 == 1 and s % 2 == 1
        g = (e - 1) // 2
        assert C == 2 * s - 6 and C % 420 == 0
        for r in range(s + 1, s + g + 1):
            d = hit(r, C)
            assert d == (e if r == s + g else 1), (r, d)
        seen.append((s, C, s + g, e, g))
        assert g*g <= 4 * (C+1)
        s += g
        C += e - 1
    assert seen[2][1] - seen[0][1] == 420 * 421
    assert seen[2][2] - seen[0][2] == 210 * 421
    assert events[1] == min_middle(events[0], 2)
    print("Synthetic exact gcd chain PASS:", seen)


def cutoff_bounds():
    M = 45_895_573
    K = (7 * M - 1) // 4
    R = isqrt(2 * K + 1)
    pmax = (4 * R - 1) // 419
    assert (K, R, pmax) == (80_317_252, 12_674, 120)
    p = 421
    q = 419 * p + 2
    middle_gap = (q - 1) // 2
    assert middle_gap == 88_200
    assert middle_gap > 2 * R
    assert (419 * p + 1)**2 > 16 * (2 * K + 1)
    p_broad = isqrt(M) + 1
    separators = (419 * p_broad + 1 + (4 * R-1)) // (4 * R)
    assert separators == 56
    print("Official cutoff:", {"M": M, "K": K, "R": R,
          "max permissible p in neutral pqp": pmax,
          "minimum intervening events if p>=sqrt(M)": separators})


def check_original_recurrence(limit=2_500_000):
    D = 1
    last = []
    patterns = w6 = 0
    for n in range(2, limit+1):
        e = hit(n, D)
        if e > 1:
            last.append((n, e, D))
            if len(last)>3:
                last.pop(0)
            if len(last)==3 and last[0][1]==last[2][1] and last[0][1]>=5:
                patterns += 1
                (r1,p,C1),(r2,q,C2),(r3,_,C3) = last
                if p>3 and p%6==1 and q%6==1 and q!=p:
                    w6 += 1
                    assert q>=3*p+4, (r1,r2,r3,p,q)
        D += e-1
    assert (patterns,w6)==(7,1), (patterns,w6)
    print("Original recurrence up to",limit,"three-event p,q,p",patterns,
          "with W=6",w6)


if __name__ == "__main__":
    check_modular_minima()
    synthetic_exact_triple()
    cutoff_bounds()
    check_original_recurrence()
    print("PASS")
