#!/usr/bin/env python3
"""Independent literal per-integer source/q-deleted shadow and shifted-clock oracle.

Tests actual next q event against first q hit on ghost trajectory and measures
counterfactual phase shifts (never treated as genuine q dynamics).
"""
from math import gcd, isqrt
import sys

def primes_le(B):
    return [n for n in range(3,B+1,2) if all(n%p for p in range(3,isqrt(n)+1,2))]

def clipped(n,C,ps,omit=0):
    a,b=(n,C-1) if n%2==0 else (n-2,C+1)
    raw=gcd(a,b)
    d=1
    for p in ps:
        if p!=omit and raw%p==0: d*=p
    return d

def audit(X):
    B=isqrt(7*X)
    if B*B<7*X:B+=1
    ps=primes_le(B)
    stats={b:dict(first=0,tagged=0,returns=0,protected=0,unprotected=0,shifts=0.,shift_count=0) for b in (1,2)}
    for M in range(X+1,2*X,2):
        K=(7*M-1)//4
        C=2*M-2
        qhits={}
        for n in range(M+3,K+1):
            d=clipped(n,C,ps)
            if d>1:
                C+=d-1
                for q in ps:
                    if q>=11 and d%q==0:
                        qhits.setdefault(q,[]).append((n,C))
        for q,hits in qhits.items():
            b=2 if 2*q>=B else (1 if 4*q>=B else 0)
            if b==0:continue
            z=stats[b]
            for j,(n0,C0) in enumerate(hits):
                z['tagged']+=1
                if j==0:z['first']+=1
                C=C0;G=0;nevents=0;nextq=0;rotations=set()
                for n in range(n0+1,K+1):
                    even=(n%2==0 and n%q==0)
                    odd=(n%2==1 and (n-2)%q==0)
                    if even or odd:
                        a=(C-1)%q if even else (C+1)%q
                        if nevents>0:rotations.add(a)
                        if a==0 and nextq==0:nextq=n
                    d=clipped(n,C,ps,omit=q)
                    if d>1:
                        C+=d-1;G+=d-1;nevents+=1
                observed=hits[j+1][0] if j+1<len(hits) else 0
                assert nextq==observed,(X,M,q,j,nextq,observed)
                ret=(nextq>0)
                z['returns']+=ret
                threshold=q-1 if n0%2==0 else q+1
                if G<threshold:
                    assert not ret
                    z['protected']+=1
                else:z['unprotected']+=1
                z['shifts']+=len(rotations)/q
                z['shift_count']+=len(rotations)
    for b,z in stats.items():
        print(f'LITERAL_PHASE_RACE_PASS X={X} B={B} band={b} first={z["first"]} tagged={z["tagged"]} returns={z["returns"]} protected={z["protected"]} unprotected={z["unprotected"]} shiftedPhaseExpected={z["shifts"]:.9f} shiftedWinningPhaseMean={z["shift_count"]/z["tagged"] if z["tagged"] else 0:.8f}')

if __name__=='__main__':
    for x in map(int,sys.argv[1:] or ['256','512','1024']):audit(x)