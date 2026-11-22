#!/usr/bin/env python3
"""A166944 two-speed reset theorem: exact integer-gcd audit.

The algebraic proof is in research/2026-11-22-two-speed-reset-prime-fuel.md.
This program tests concrete trajectories. It does NOT prove Cap B or twin-prime infinitude.
"""
from collections import Counter
from math import gcd


def gcd_event(n, C):
    return gcd(n if n % 2 == 0 else n-2,
               C-1 if n % 2 == 0 else C+1)


def check_step(n, C, e):
    x = 2*(n-1)-C
    z = x+3 if n % 2 == 0 else x-3
    assert e == gcd(n if n%2==0 else n-2, abs(z))
    after = x+3-e
    assert after == 2*n-(C+e-1)
    if n>=3 and e>1 and z:
        assert abs(z)%e==0
        if abs(z)>e:
            assert abs(z)//e>=3
            if x>=10:
                assert 3*after>=2*x+6
        elif z>0:
            assert after == (0 if n%2==0 else 6)
        if e>=5:
            for p in range(5,e+1,2):
                if e%p==0 and all(p%f for f in range(3,int(p**0.5)+1,2)):
                    assert (C+e-1-1)%p and (C+e-1+1)%p
    return after


def check_next_from_reset(s, C, r, e):
    x=2*s-C
    assert x in (0,6) and e>=9
    g=r-s
    c=x+1 if r%2==0 else x-5
    u=2*g+c
    assert u>0 and u%e==0
    k=u//e
    assert k in (1,3), (s,C,r,e,x,g,k)
    assert g<=2*e
    after=2*r-(C+e-1)
    assert after==((k-1)*e+(0 if r%2==0 else 6))
    return k


def actual_prefix(N=2_500_000):
    C=1
    prev=None
    counts=Counter()
    exemplar=None
    for n in range(2,N+1):
        e=gcd_event(n,C)
        if n>=3:
            after=check_step(n,C,e)
        else:
            after=2*n-(C+e-1)
        if n>=3 and e>1:
            counts['events']+=1
            z=2*(n-1)-C+(3 if n%2==0 else -3)
            if z and abs(z)==e: counts['primitive']+=1
            elif z: counts['proper']+=1
            else: counts['zero']+=1
            if prev is not None:
                s, prior_C=prev
                if 2*s-prior_C in (0,6) and e>=9:
                    k=check_next_from_reset(s,prior_C,n,e)
                    counts['speed'+str(k)]+=1
                    if k==3 and exemplar is None:
                        exemplar=(s,n,e,n-s,2*s-prior_C,after)
            prev=(n,C+e-1)
        C+=e-1
    assert C==2_860_770 and counts == Counter({
        'events':249,'primitive':98,'proper':151,'speed1':36,'speed3':10
    }), counts
    assert exemplar==(318,340,17,22,6,34)
    print('ACTUAL 2.5m:',dict(counts),'first three-speed',exemplar)


def synthetic(M):
    s0=M+2
    K=(7*M-1)//4
    C=2*M-2
    prev=(s0,C)
    tally=Counter()
    for n in range(s0+1,K+1):
        e=gcd_event(n,C)
        after=check_step(n,C,e)
        if e>1:
            s,olderC=prev
            if 2*s-olderC in (0,6) and e>=9:
                tally[str(check_next_from_reset(s,olderC,n,e))]+=1
            prev=(n,C+e-1)
        C+=e-1
    expected = {
        367: {'1':6,'3':1},
        100549: {'1':1,'3':1},
        101119: {'1':2,'3':2},
    }
    assert dict(tally)==expected[M], (M,tally)
    print('SYNTHETIC canonical M=',M, 'reset large-speed split',dict(tally),
          'terminal horizon',C)


if __name__=='__main__':
    actual_prefix()
    for M in (367,100549,101119):
        synthetic(M)
    print('PASS finite integer checks. No unbounded conclusion or new Lean compilation.')
