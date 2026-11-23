#!/usr/bin/env python3
"""Independent integer-by-integer parity-GCD verifier for reset first-high labels.
Run: python3 research/min_reset_first_three_high_literal.py 256 1024
"""
from math import gcd, isqrt
import sys


def primes(b):
    return [p for p in range(3,b+1,2)
            if all(p%d for d in range(3,isqrt(p)+1,2))]


def first_three(n, end, ps):
    c=2*n-(6 if n%2 else 0)
    events=[]
    low_since_high=0
    for t in range(n+1,end+1):
        raw=gcd(t if t%2==0 else t-2,c-1 if t%2==0 else c+1)
        p=next((p for p in ps if raw%p==0),0)
        if p==0:continue
        c+=p-1
        if p>=11:
            events.append((p,t,low_since_high))
            low_since_high=0
            if len(events)==3:break
        elif events:
            low_since_high+=p-1
    return events


def audit(X):
    b=isqrt(7*X)
    if b*b<7*X:b+=1
    end=(7*(2*X-1)-1)//4
    lo=max(37,(b+1)//2)
    ps=primes(b)
    one=two=three=0
    witness=None
    for n in range(X+3,end+1):
        e=first_three(n,end,ps)
        if e and e[0][0]>=lo:
            one+=1
            if len(e)>=2 and e[1][0]>=lo:two+=1
            if len(e)>=3 and e[2][0]==e[0][0]:
                three+=1
                if witness is None:witness=(n,e)
    if X==256:assert (one,two,three)==(29,0,0)
    if X==1024:
        assert (one,two,three)==(295,27,1)
        assert witness[0]==1271
        assert tuple(p for p,t,g in witness[1])==(43,29,43)
    print("RESET_THREE_LITERAL_PASS",X,"B",b,
          "firstTop",one,"firstTwoTop",two,"q-r-qTop",three,
          "example",witness)


if __name__=="__main__":
    for x in map(int,sys.argv[1:] or (256,1024)):
        audit(x)
