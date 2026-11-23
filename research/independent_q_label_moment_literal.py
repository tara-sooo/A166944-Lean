#!/usr/bin/env python3
"""Independent literal single-integer-step original GCD; checks (M,q) hit-count moment.
Usage: python3 research/independent_q_label_moment_literal.py [256 512 1024]
"""
from math import gcd, isqrt
from collections import Counter
import sys

def primes(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]

def audit(X):
    B=isqrt(7*X)+(isqrt(7*X)**2!=7*X)
    P=primes(B)
    H=F=Z=T=0
    tail=Counter()
    best=(0,None,None)
    for M in range(X+1,2*X,2):
        C=2*M-2
        N=Counter()
        for n in range(M+3,(7*M-1)//4+1):
            raw=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
            d=1
            high=False
            for q in P:
                if raw%q==0:
                    d*=q
                    if q>=19:
                        N[q]+=1
                        high=True
            T+=high
            C+=d-1
        for q,v in N.items():
            H+=v;F+=1;Z+=v*v
            tail[v]+=1
            if v>best[0]:best=(v,M,q)
    expected={256:(163,128),512:(265,265),1024:(640,577),4096:(5391,4823)}
    assert (H,F)==expected.get(X,(H,F)),(X,H,F)
    print(f'LITERAL_LABEL_MOMENT_PASS X={X} B={B} H={H} F={F} Z={Z} return_pairs={(Z-H)//2} maxN={best[0]} atM={best[1]} atQ={best[2]}')
    return H,F,Z

if __name__=='__main__':
    for arg in sys.argv[1:] or ('256','512','1024'):
        audit(int(arg))
