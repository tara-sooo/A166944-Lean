#!/usr/bin/env python3
"""Exact q-deleted shadow first-return equivalence vs original literal one-step clipped GCD.
The q-deleted trajectory agrees with the original UNTIL its first subsequent q hit.
Usage: python3 research/independent_prime_deleted_shadow.py [256 512 1024]
"""
from collections import defaultdict
from math import gcd, isqrt
import sys

def primes(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]

def run(X):
    B=isqrt(7*X)+(isqrt(7*X)**2!=7*X)
    ps=primes(B)
    starts=events=shadows=returned=never=shadow_steps=0
    for M in range(X+1,2*X,2):
        C=2*M-2;K=(7*M-1)//4;starts+=1
        hits=defaultdict(list)
        for n in range(M+3,K+1):
            g=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
            d=1
            support=[]
            for p in ps:
                if g%p==0:
                    d*=p
                    if p>=19:support.append(p)
            for p in support:hits[p].append((n,C+d-1))
            C+=d-1
        for q,occ in hits.items():
            events+=len(occ)
            for k,(time,post) in enumerate(occ):
                target=occ[k+1][0] if k+1<len(occ) else None
                Cshadow=post
                found=None
                for n in range(time+1,K+1):
                    shadow_steps+=1
                    raw=gcd(n if n%2==0 else n-2,Cshadow-1 if n%2==0 else Cshadow+1)
                    if raw%q==0:
                        found=n
                        break
                    d=1
                    for p in ps:
                        if p!=q and raw%p==0:d*=p
                    Cshadow+=d-1
                if found!=target:
                    raise AssertionError(f'SHADOW_MISMATCH X={X} M={M} q={q} after={time} shadow={found} full={target}')
                shadows+=1;returned+=found is not None;never+=found is None
    print(f'PRIME_DELETED_SHADOW_PASS X={X} B={B} starts={starts} qHits={events} qPostTests={shadows} repeatReturns={returned} noReturn={never} literalShadowSteps={shadow_steps}')

if __name__=='__main__':
    for X in map(int,sys.argv[1:] or ['256','512','1024']):run(X)
