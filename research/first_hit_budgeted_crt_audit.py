#!/usr/bin/env python3
"""Exact finite CRT + budgeted first-hit wheel audit for A166944.

Requires only Python 3 standard library.
Theorems: research/2026-11-22-budgeted-first-hit-crt-anti-resonance.md
Finite certificates, NOT a proof of Cap B or infinite twin primes.
"""
from math import gcd, lcm
from bisect import bisect_right
from functools import lru_cache
from collections import Counter, defaultdict


def exact_events(limit=2_500_000):
    C, out = 1, []
    for n in range(2, limit+1):
        e = gcd(n if n % 2 == 0 else n-2, C-1 if n % 2 == 0 else C+1)
        if e > 1:
            C += e-1
            out.append((n,e,C))
    assert (len(out),C) == (250,2_860_770)
    return out


def factors(n):
    out, p = [], 3
    while p*p <= n:
        if n%p == 0:
            out.append(p)
            while n%p == 0: n//=p
        p+=2
    if n>1: out.append(n)
    return out


def crt(mods):
    x, P=0, 1
    for p,r in mods:
        assert gcd(p,P)==1
        x += P*((r-x)*pow(P,-1,p)%p)
        P*=p
    return x,P


@lru_cache(None)
def odd_lcm(h):
    assert h>=0 and h%2==0
    q=1
    for z in range(1,h+2,2): q=lcm(q,z)
    return q


def truncated_replay(u,C,v,h):
    """Small-factor overapproximation; matches true path IF true growth <= h."""
    modulus=odd_lcm(h)
    x=C
    hits=[]
    for n in range(u+1,v+1):
        first = n if n%2==0 else n-2
        second = x-1 if n%2==0 else x+1
        e=gcd(gcd(first,second),modulus)
        if e>1:
            hits.append((n,e))
            x+=e-1
    return x-C,hits


def next_factor_hit(s,C):
    """Exact first-hit clock, factoring each odd horizon neighbor."""
    hits=[]
    for p in factors(C-1):
        hits.append(s+((-s)%(2*p) or 2*p))
    for p in factors(C+1):
        hits.append(s+((p+2-s)%(2*p) or 2*p))
    r=min(hits)
    e=gcd(r if r%2==0 else r-2,C-1 if r%2==0 else C+1)
    assert e>1
    return r,e


def clock_replay(u,C,v):
    hits=[]
    while True:
        r,e=next_factor_hit(u,C)
        if r>v: return hits,C
        C+=e-1
        u=r
        hits.append((r,e))


def analyze_pairs(events):
    D={n:C for n,e,C in events}
    by_prime=defaultdict(list)
    for n,e,C in events:
        for p in factors(e):
            if p>=5: by_prime[p].append(n)
    intervals=[]
    for p,ns in by_prime.items():
        for a,b in zip(ns,ns[1:]):intervals.append((p,a,b))
    assert len(by_prime)==45 and len(intervals)==125
    stats=Counter()
    for i,(p,a,b) in enumerate(intervals):
        for q,c,d in intervals[i+1:]:
            u,v=max(a,c),min(b,d)
            if u>=v:continue
            H=D[v]-D[u]
            cap=2*(v-u)+2*u-D[u]
            residues=[]
            for key,first,last in ((p,a,b),(q,c,d)):
                tau=(0 if first%2==last%2
                       else 2 if first%2 else -2)
                fringe=(D[u]-D[first])+(D[last]-D[v])
                residues.append((key,(tau-fringe)%key))
            h0,P=crt(residues)
            assert H%P==h0 and H%2==0 and H<=cap
            he=h0+(P if h0%2 else 0)
            assert H%(2*P)==he
            stats['overlapping_pairs']+=1
            if P>cap:stats['CRT_rigid']+=1
            if h0<H:stats['nonminimal_unadjusted']+=1
            if v-u>2000:continue
            for h in range(he,min(cap,128)+1,2*P):
                stats['candidate_tested']+=1
                report,_=truncated_replay(u,D[u],v,h)
                if report==h:stats['candidate_survived']+=1
                else:stats['candidate_rejected']+=1
            if H<=128:
                assert truncated_replay(u,D[u],v,H)[0]==H
    expected=Counter({'overlapping_pairs':968,'CRT_rigid':334,
        'nonminimal_unadjusted':525,'candidate_tested':522,
        'candidate_survived':386,'candidate_rejected':136})
    assert stats==expected,(stats,expected)
    print('CRT pair scan:',dict(stats))
    return events


def examples(events):
    D={n:C for n,e,C in events}
    assert (D[60],D[66],D[150],D[343])==(100,132,300,658)
    assert crt([(5,3),(11,3)])==(3,55)
    s,C,v=66,132,150
    assert 2*(v-s)+2*s-C==168
    assert truncated_replay(s,C,v,58)==(6,[(79,7)])
    hits,finish=clock_replay(s,C,v)
    assert (hits,finish-C)==(
        [(79,7),(141,139),(150,25)],168)
    assert truncated_replay(s,C,v,168)==(168,hits)
    print('Genuine [66,150]: CRT H=58 (mod110); wheel58=6;',
          'first-hit clocks force H=168')
    hits,finish=clock_replay(356873,713458,356883)
    assert hits==[(356874,3),(356883,7)]
    assert finish-713458==8
    assert truncated_replay(356873,713458,356883,8)==(8,hits)
    print('Genuine 12-key core: H=8, C mod210=',713458%210,
          ', hits=',hits)


def residue_census():
    counts=Counter()
    for s in range(630):
        for C in range(0,630,2):
            H,_=truncated_replay(s,C,s+10,8)
            counts[H if H<=8 else '>8']+=1
            if C%210==0:
                assert H==0
    expected=Counter({'>8':49404,4:38873,0:31590,
                      2:30664,6:26156,8:21763})
    assert counts==expected and sum(counts.values())==198450
    print('Universal 630x315 B=8, L=10 residue census:',dict(counts))


def actual_interval_spotchecks(events):
    times=[n for n,e,C in events]
    horizons=[C for n,e,C in events]
    def D_at(n):
        i=bisect_right(times,n)-1
        return horizons[i] if i>=0 else 1
    checked=0
    for s in range(1000,2_500_000-100,322):
        for L in (10,23,100):
            v=s+L
            C=D_at(s)
            H=D_at(v)-C
            if H<=8:
                assert truncated_replay(s,C,v,8)[0]==H
                checked+=1
    assert checked==23261,checked
    rough_checks=0
    for s in range(10000,2_500_000-250,239):
        for L in (90,150,230):
            C=D_at(s)
            v=s+L
            V=D_at(v)
            if V-C>8:continue
            k=bisect_right(times,v)-1
            r=times[k]
            if r<=s:
                roughC,last=C,s
            else:
                roughC,last=V,r
            assert last-s<=72
            assert gcd(roughC-1,315)==gcd(roughC+1,315)==1
            rough_checks+=1
    assert rough_checks==31204,rough_checks
    print('Actual bounded-growth windows:',checked,
          '; h=8 terminal-roughness windows:',rough_checks)


if __name__=='__main__':
    events=exact_events()
    analyze_pairs(events)
    examples(events)
    residue_census()
    actual_interval_spotchecks(events)
    print('PASS: exact finite first-hit + CRT-wheel certificates; Cap B remains open')
