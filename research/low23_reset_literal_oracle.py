#!/usr/bin/env python3
"""Independent literal one-step original parity-GCD oracle for restricted reset wheel.
Checks exactly the original n-even/n-odd gcd, without event clocks.
"""
from math import gcd
from random import Random

PRIMES=[3,5,7,11,13,17,19,23]
WITNESSES={
17:[(164569,40,None,316,None),(221683,None,239,None,None),(115729,None,None,None,4)],
19:[(8264689,56,388,568,None),(489878,None,None,None,5),(2392753,None,None,None,None)],
23:[(175438762,88,533,946, None),(7491793,75,599,820,6),(163925126,None,None,None,6),
    (74662603,None,None,None,None),(160467553,None,None,None,None)]
}

def literal(q,r):
    primes=[p for p in PRIMES if p<=q]
    P=1
    for p in primes:P*=p
    L=2*P
    t=5*L+r; z=6 if t%2 else 0; c=2*t-z
    t0,c0=t,c; nevents=0; qhits=0; max_prefix=0; max_active_z=0; last_plateau=t
    for k in range(2000):
        active=any((c-1)%p==0 or (c+1)%p==0 for p in primes)
        if not active:return (nevents,t-t0,c-c0,qhits,max_prefix,max_active_z)
        n=t+1
        raw=gcd(n if n%2==0 else n-2,c-1 if n%2==0 else c+1)
        d=1
        for p in primes:
            if raw%p==0:d*=p
        if d!=1:
            max_prefix=max(max_prefix,2*(last_plateau-t0)-(c-c0))
            max_active_z=max(max_active_z,2*last_plateau-c)
            nevents+=1
            qhits+=(d%q==0)
            c+=d-1
            last_plateau=n
        t=n
    raise RuntimeError(f'Exceeded 2000 steps, q={q}, r={r}')

def main():
    rng=Random(20261123)
    for q in [17,19,23]:
        P=1
        for p in PRIMES:
            if p<=q:P*=p
        L=2*P
        for r,e,t,g,h in WITNESSES[q]:
            got=literal(q,r)
            assert e is None or got[0]==e,(q,r,got,e)
            assert t is None or got[1]==t,(q,r,got,t)
            assert g is None or got[2]==g,(q,r,got,g)
            assert h is None or got[3]==h,(q,r,got,h)
            print('LITERAL_WITNESS',q,r,got)
        mx=[0]*6
        for j in range(1000):
            r=rng.randrange(L)
            got=literal(q,r)
            mx=[max(a,b) for a,b in zip(mx,got)]
            if q==17:
                assert got[0]<=40 and got[1]<=239 and got[2]<=316 and got[3]<=4
            elif q==19:
                assert got[0]<=56 and got[1]<=388 and got[2]<=568 and got[3]<=5
            else:
                assert got[0]<=88 and got[1]<=599 and got[2]<=946 and got[3]<=6
        print('LITERAL_RESET_SLICE_PASS q=',q,'1000 random states plus extrema, max observed',mx)
if __name__=='__main__':main()
