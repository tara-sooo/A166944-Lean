"""Exact 420-wheel CRT phase graph and phase-switch count audit (Python 3).

Validates the original A166944 recurrence and an explicitly synthetic
first-hit path. Modular sharpness examples are not genuine path claims.
"""
from math import gcd
from collections import defaultdict

W = 420
INERT = {a for a in range(210) if gcd(a-1, 210) == 1
         and gcd(a+1, 210) == 1}
assert len(INERT) == 15


def residue(p, C, r):
    """CRT class of the pre-hit horizon C modulo 420*p."""
    assert p > 7 and gcd(p, W) == 1
    alpha = C % W
    sign = 1 if r % 2 == 0 else -1
    x = alpha + W * (((sign-alpha)*pow(W, -1, p)) % p)
    assert x % W == alpha and x % p == sign % p
    return x


def min_growth(p, C1, r1, C2, r2):
    """Least strictly positive congruence-compatible horizon increase."""
    period = W*p
    step = (residue(p, C2, r2) - residue(p, C1, r1)) % period
    return step or period


def factor_keys(n):
    out = []
    f = 3
    while f*f <= n:
        if n % f == 0:
            if f > 7:
                out.append(f)
            while n % f == 0:
                n //= f
        f += 2
    if n > 7:
        out.append(n)
    return out


def actual_events(limit=2_500_000):
    D = 1
    events = []
    for r in range(2, limit+1):
        e = gcd(r if r%2 == 0 else r-2,
                D-1 if r%2 == 0 else D+1)
        if e > 1:
            events.append((r, e, D))
        D += e-1
    return events, D


def audit_actual():
    events, D = actual_events()
    print("Original recurrence events", len(events), "D(end)", D)
    windows = ((2, 30000), (10000, 500000), (2, 1000000),
               (1000000, 2500000), (2, 2500000))
    for u, v in windows:
        prefix = lambda n: sum(e-1 for r,e,C in events if r <= n)
        growth = prefix(v)-prefix(u)
        sub = [(r,e,C) for r,e,C in events if u < r <= v]
        switches = sum((e-1)%W != 0 for r,e,C in sub)
        by_prime = defaultdict(list)
        for r,e,C in sub:
            for p in factor_keys(e):
                assert C%p == (1 if r%2 == 0 else p-1)
                by_prime[p].append((r,C))
        for p,hits in by_prime.items():
            for (r1,C1),(r2,C2) in zip(hits,hits[1:]):
                delta = C2-C1
                edge = min_growth(p,C1,r1,C2,r2)
                assert delta >= edge and (delta-edge)%(W*p) == 0
            n = len(hits)
            assert n <= 2*(switches+1)+2*(growth//(W*p))
            if all(r%2 == 1 for r,C in hits):
                assert n <= switches+1+growth//(W*p)
            inert_hits = sum(C%210 in INERT for r,C in hits)
            assert inert_hits <= 60*(growth//(W*p)+1)
        print("actual window",u,v,"growth",growth,
              "wheel switches",switches,"prime keys",len(by_prime),"PASS")
    assert min_growth(13,12,15,300,156) == 288
    print("Actual p=13 phase-changing return: exact CRT minimum 288")


def audit_neutral():
    p = 421
    M = 9_801_898_053_991  # synthetic, NOT attained from a(1)=2
    s,C = M+2, 2*M-2
    hits = []
    for e,g in ((421,210),(176401,88200),(421,210)):
        for r in range(s+1,s+g+1):
            val = gcd(r if r%2 == 0 else r-2,
                      C-1 if r%2 == 0 else C+1)
            assert val == (e if r == s+g else 1), (r,val)
        hits.append((s+g,C))
        C += e-1
        s += g
    (r1,C1),(r2,C2) = hits[0],hits[2]
    assert C2-C1 == W*p == min_growth(p,C1,r1,C2,r2)
    assert r2-r1 == 210*p
    print("Synthetic odd-hit p=421 exact one-lap phase return PASS")


def audit_three_hit_phase_return():
    p = 421
    C1 = 420
    C2 = C1+12*p
    C3 = C1+418*p+2
    assert [C%420 for C in (C1,C2,C3)] == [0,12,0]
    assert [C%p for C in (C1,C2,C3)] == [p-1,p-1,1]
    assert C3-C1 == 418*p+2
    assert min_growth(p,C1,11,C2,13) == 12*p
    assert min_growth(p,C2,13,C3,14) == 406*p+2
    print("Three-hit first-last phase return: CRT coefficient 418 sharp")


if __name__ == "__main__":
    audit_actual()
    audit_neutral()
    audit_three_hit_phase_return()
    print("PASS")
