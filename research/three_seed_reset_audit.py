#!/usr/bin/env python3
"""Exhaustive finite audit of odd-time 3-seed normalization after high-GCD resets."""
from collections import Counter
from math import gcd

PRIMES=(3,5,7,11)
L=2*3*5*7*11

def step_gcd(n,c):
    return gcd(n if n%2==0 else n-2, c-1 if n%2==0 else c+1)

def low_trace(t,z):
    c=2*t-z
    e=count=0
    maxz=z
    while True:
        clocks=[]
        for p in PRIMES:
            if (c-1)%p==0:r=0
            elif (c+1)%p==0:r=p+2
            else:continue
            clocks.append(((r-t)%(2*p) or 2*p,p))
        if not clocks:return count,e,maxz
        dt=min(v for v,p in clocks)
        d=1
        for v,p in clocks:
            if v==dt:d*=p
        n=t+dt
        raw=step_gcd(n,c)
        check=1
        for p in PRIMES:
            if raw%p==0:check*=p
        assert check==d
        c+=d-1;t=n;e+=d-1;count+=1
        maxz=max(maxz,2*t-c)
        assert 0<=2*t-c and e<=1156 and count<=22

def even_to_odd(t):
    assert t%2==0
    c=2*t
    pattern=[]
    for n in (t+1,t+2,t+3):
        raw=step_gcd(n,c)
        d=1
        for p in (3,5):
            if raw%p==0:d*=p
        assert raw in (1,3,5)
        pattern.append(d)
        c+=d-1
    return tuple(pattern),2*(t+3)-c

def main():
    patterns=Counter(even_to_odd(t) for t in range(4*L,4*L+30,2))
    assert patterns=={((1,1,1),6):8,((3,3,1),2):5,((1,5,1),2):1,((1,5,3),0):1},patterns
    print("THREE_STEP_PASS",sorted(patterns.items()))
    for z in (0,2,6):
        vals=[low_trace(4*L+r,z) for r in range(1,L,2)]
        bounds=tuple(max(v[i] for v in vals) for i in range(3))
        assert bounds=={0:(17,100,146),2:(19,98,146),6:(18,98,146)}[z],(z,bounds)
        print("ODD_SEED_PASS",z,"states",len(vals),"max_events_growth_deficit",bounds)
    assert low_trace(10394,2*2887)[:2]==(2,1156)
    print("CHARGED_WORST_CASE_PASS")

if __name__=="__main__":
    main()
