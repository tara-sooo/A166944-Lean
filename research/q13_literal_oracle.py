#!/usr/bin/env python3
"""Independent one-step literal-GCD oracle for 5-prime-only 13 renewal event states.
The exhaustive graph is in q13_renewal_graph_full.cpp; this checks selected extremal
nodes and random legal post-13 states, independently of its event-jump algorithm.
"""
from math import gcd
from random import Random
P = 3*5*7*11*13
L = 2*P
primes = (3,5,7,11,13)
times = [t for t in range(L) if (t%2==0 and t%13==0) or (t%2==1 and (t-2)%13==0)]
assert len(times)==2310

def state(index):
    ti, j=divmod(index,1155)
    r=times[ti]
    k0=12 if r%2 else 0
    return 5*L+r, 5*L+2*(k0+13*j)

def run_direct(t,c):
    t0,c0=t,c
    n13=0;events=0
    while True:
        if all((c-1)%p and (c+1)%p for p in primes):
            return n13,events,t-t0,c-c0
        n=t+1
        raw=gcd(n if n%2==0 else n-2, c-1 if n%2==0 else c+1)
        d=1
        for p in primes:
            if raw%p==0: d*=p
        if d!=1:
            n13+=(d%13==0)
            events+=1
            c+=d-1
        t=n
        if t-t0>400:raise RuntimeError('direct path unexpectedly long',t0,c0,t,c)

def run_jump(t,c):
    t0,c0=t,c
    n13=0;events=0
    while True:
        options=[]
        for p in primes:
            if (c-1)%p==0:r=0
            elif (c+1)%p==0:r=p+2
            else: continue
            delta=(r-t)%(2*p) or 2*p
            options.append((delta,p))
        if not options:return n13,events,t-t0,c-c0
        dt=min(a for a,p in options)
        d=1
        for a,p in options:
            if a==dt:d*=p
        n13+=(d%13==0)
        t+=dt;c+=d-1;events+=1
        if t-t0>400:raise RuntimeError('jump path unexpectedly long',t0,c0,t,c)

def main():
    rng=Random(20261123)
    ids=[2499578,1491074]+[rng.randrange(len(times)*1155) for _ in range(1500)]
    maxima=[0,0,0,0]
    for idx in ids:
        t,c=state(idx)
        a=run_direct(t,c);b=run_jump(t,c)
        assert a==b,(idx,a,b)
        maxima=[max(x,y) for x,y in zip(maxima,a)]
        assert a[0]<=5 and a[1]<=40 and a[2]<=222 and a[3]<=1406
        if idx in (2499578,1491074):print('EXTREME_LITERAL_PASS',idx,'start',t,c,'future13,events,elapsed,growth',a)
    for j in range(1200):
        t=L*5+rng.randrange(L)
        c=L*5+2*rng.randrange(P)
        a=run_direct(t,c);b=run_jump(t,c)
        assert a==b, (j,t,c,a,b)
        assert a[0]<=6 and a[1]<=63 and a[2]<=381 and a[3]<=17576, (t,c,a)
    print('Q13_LITERAL_ORACLE_PASS',len(ids),'post13_states_and_1200_arbitrary_states',
          'max_observed_post13_13_events_elapsed_growth',maxima)
if __name__=='__main__':main()
