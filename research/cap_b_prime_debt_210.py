#!/usr/bin/env python3
"""Finite arithmetic certificate for the A166944 Cap B prime-debt reduction.

This is not a proof of Cap B. It verifies a 210-residue potential certificate.
Python 3 standard library only. Paper proof: research/2026-11-21-prime-debt-mod210.md
"""
from math import gcd

N = 210
EXCEPTIONS = (9, 25, 27, 33)
STATES = [(s, c) for s in range(N) for c in range(0, N, 2)]
INDEX = {state: i for i, state in enumerate(STATES)}


def clipped_hit(s, c):
    """The first 210-clipped nonunit gcd event, if one exists."""
    # A factor among 3, 5, 7 produces a hit within at most 2*7 indices.
    for gap in range(1, 15):
        r = s + gap
        n = r if r % 2 == 0 else r - 2
        z = c - 1 if r % 2 == 0 else c + 1
        e = gcd(gcd(n, z), N)
        if e > 1:
            return (r % N, gap, e)
    return None


def make_edges():
    edges = []
    hits = {}
    for s, c in STATES:
        step = clipped_hit(s, c)
        if step is None:
            continue
        r_mod, gap, e = step
        hits[e] = hits.get(e, 0) + 1
        # Actual increments 9,25,27,33 have clipped gcd 3 or 5.
        for actual_e in (e,) + tuple(x for x in EXCEPTIONS if gcd(x, N) == e):
            after = (r_mod, (c + actual_e - 1) % N)
            edges.append((INDEX[(s,c)], INDEX[after],
                          gap - (actual_e - 1), actual_e))
    assert hits == {3:11774,5:4010,7:2210,15:546,21:258,35:90,105:12}, hits
    assert len(edges) == 58232, len(edges)
    return edges


def potential(edges):
    V = [0] * len(STATES)
    for iteration in range(1, 100):
        nxt = V.copy()
        for src, dst, weight, _ in edges:
            nxt[src] = max(nxt[src], weight + V[dst])
        if nxt == V:
            break
        V = nxt
    else:
        raise AssertionError("Potential relaxation did not converge")
    # These assertions make the finite certificate independently checkable.
    assert iteration == 19, iteration
    assert min(V) == 0 and max(V) == 29
    assert all(weight + V[dst] <= V[src] for src,dst,weight,e in edges)
    canonical_max = max(V[INDEX[((m+2)%N,(2*m-2)%N)]]
                        for m in range(1, N+1, 6))
    assert canonical_max == 27, canonical_max
    return V


def is_prime(n):
    if n < 2:
        return False
    f = 2
    while f*f <= n:
        if n % f == 0:
            return False
        f += 1
    return True


def check_composite_tail():
    """Finite diagnostic. The general tail is covered by three paper cases."""
    exceptions = {9, 15, 21, 25, 27, 33, 35}
    for e in range(9, 10001, 2):
        if is_prime(e) or e in exceptions:
            continue
        p = next(q for q in range(3, e+1, 2) if e % q == 0)
        assert e-1-2*p >= 29, (e,p)


def actual_first_hit(s, C):
    """Unclipped first-gcd event, for known finite canonical controls."""
    for r in range(s+1, C+1):
        e = gcd(r, C-1) if r%2 == 0 else gcd(r-2, C+1)
        if e > 1:
            return r,e
    return None


def check_control(M, count, V):
    s,C = M+2,2*M-2
    T = G = prime_debt = 0
    v0 = V[INDEX[(s%N,C%N)]]
    for _ in range(count):
        hit = actual_first_hit(s,C)
        assert hit is not None
        r,e = hit
        assert e%2 == 1 and e <= M and r<=C
        g = r-s
        Cnext = C+e-1
        before = V[INDEX[(s%N,C%N)]]
        after = V[INDEX[(r%N,Cnext%N)]]
        net = g-(e-1)+after-before
        if e in (3,5,7) or not is_prime(e):
            assert net<=0, (M,s,C,r,e,net)
        else:
            prime_debt += max(0,net)
        T += g
        G += e-1
        s,C = r,Cnext
    assert T+V[INDEX[(s%N,C%N)]] <= G+v0+prime_debt
    return T,G,prime_debt,v0


def main():
    edges = make_edges()
    V = potential(edges)
    check_composite_tail()
    controls = {
        5419: (9, (75,54,13,9)),
        45895573: (37, (957,1914,216,0)),
        5875882249: (26, (45417,30564,15106,27)),
    }
    for M,(count,expected) in controls.items():
        got = check_control(M,count,V)
        assert got == expected,(M,got,expected)
        print(f"M={M}: {count} events; T={got[0]}, G={got[1]}, "
              f"prime>=11 debt={got[2]}, V0={got[3]}")
    print(f"PASS: {len(STATES)} states, {len(edges)} edges, "
          f"max V={max(V)}, max canonical V=27")
    print("Cap B and the global prime-debt bound remain open.")


if __name__ == "__main__":
    main()
