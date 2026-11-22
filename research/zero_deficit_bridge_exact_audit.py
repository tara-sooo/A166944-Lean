#!/usr/bin/env python3
"""Exact modulo-30 certificate: every EVEN X=0 state reaches X=6 <=7 steps.
Uses the original A166944 parity gcd clipped by an odd wheel.
Only a local theorem, not proof of Cap B or twin-prime infinitude.
"""
from math import gcd
from collections import Counter

def bridge(n0, L):
    assert n0>=30 and n0%2==0 and L%2==1
    C=2*n0
    growth=0
    events=[]
    for k in range(1,8):
        n=n0+k
        x=2*(n-1)-C
        raw=gcd(n,C-1) if n%2==0 else gcd(n-2,C+1)
        e=gcd(raw,L)
        if e>1:events.append((k,e))
        growth+=e-1
        C+=e-1
        assert 2*n-C==x+3-e
        if 2*n-C==6:
            assert k in (3,5,7) and growth==2*k-6
            assert n%2==1 and C==2*(n-2)-2
            assert all(v in (3,5) for _,v in events)
            return k,growth,events
    raise AssertionError((n0,L,events))

def run():
    expected={
        1:{3:15}, 3:{3:10,5:5},
        5:{3:12,5:3}, 15:{3:8,5:5,7:2},
    }
    for L,hist_expected in expected.items():
        hist=Counter(bridge(30000+r,L)[0] for r in range(0,30,2))
        assert dict(hist)==hist_expected,(L,hist)
        print(f'L={L:>3}: lengths {dict(sorted(hist.items()))}')
    for L in (15,105,1155,15015,315315):
        for n0 in range(30000,30420,2):
            k,b,events=bridge(n0,L)
            assert (k,b) in ((3,0),(5,4),(7,8))
    full={r:bridge(30000+r,315315) for r in range(0,30,2)}
    assert [r for r,(k,_,_) in full.items() if k==7]==[8,16]
    assert [r for r,(k,_,_) in full.items() if k==5]==[4,10,18,22,28]
    print('Full-gcd bridge length7 residues: 8,16; length5: 4,10,18,22,28')
    print('PASS finite complete mod30 certificate and regeneration identity')

if __name__=='__main__':
    run()
