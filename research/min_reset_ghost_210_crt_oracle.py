#!/usr/bin/env python3
"""Exact LOW7-MIN reset-prefix ghost, checked against literal parity-GCD."""
from collections import Counter
from math import gcd
LOW=(3,5,7)

def ghost(r):
    t=r;c=2*r-(6 if r&1 else 0);gains=[0]
    for _ in range(100):
        candidates=[]
        for p in LOW:
            residue=0 if (c-1)%p==0 else (p+2 if (c+1)%p==0 else -1)
            if residue<0:continue
            gap=(residue-t)%(2*p) or 2*p
            candidates.append((gap,p))
        if not candidates:return gains
        gap,p=min(candidates)
        t+=gap;c+=p-1;gains.append(gains[-1]+p-1)
    raise AssertionError('LOW7 ghost nonterminating')

def literal(r):
    n=r+420;c=2*n-(6 if n&1 else 0);base=c;gains=[0]
    for t in range(n+1,n+211):
        raw=gcd(t if t%2==0 else t-2,c-1 if t%2==0 else c+1)
        p=next((p for p in LOW if raw%p==0),None)
        if p is not None:
            c+=p-1;gains.append(c-base)
    return gains

def main():
    D=0;max_d=max_gain=max_events=0;words=Counter()
    for r in range(210):
        g=ghost(r);ind=literal(r)
        assert g==ind,(r,g,ind)
        offsets={e+a for e in g for a in (-1,1)}
        D+=len(offsets);max_d=max(max_d,len(offsets))
        max_gain=max(max_gain,max(g));max_events=max(max_events,len(g)-1)
        words[tuple(g)]+=1
    assert (D,max_d,max_gain,max_events,len(words))==(1195,16,32,9,36)
    print('RESET_GHOST_CRT_PASS classes=210 D=1195 maxOffsets=16 maxGrowth=32 maxEvents=9 distinctWords=36 literal_verified=210')

if __name__=='__main__':main()
