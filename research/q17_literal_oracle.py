#!/usr/bin/env python3
"""Independent literal, one-step odd/even GCD check of the complete q=17 low wheel.
The exhaustive finite transition graph is separately checked by q17_full_dfs.cpp.
"""
from math import gcd
from random import Random

PRIMES=(3,5,7,11,13,17)
P=1
for p in PRIMES:P*=p
L=2*P
Q=17
TIMES=[t for t in range(L) if (t%2==0 and t%Q==0) or (t%2==1 and (t-2)%Q==0)]
assert len(TIMES)==30030
N=len(TIMES)*(P//Q)
assert N==450900450

def post_state(index):
    ti,j=divmod(index,P//Q)
    t=TIMES[ti]
    k0=Q-1 if t%2 else 0
    c=2*(k0+Q*j)
    return t+5*L, c+5*L

def literal(t,c,max_elapsed=900):
    n17=events=0
    begin=t,c
    while True:
        if all((c-1)%p and (c+1)%p for p in PRIMES):
            return n17,events,t-begin[0],c-begin[1]
        n=t+1
        g=gcd(n if n%2==0 else n-2,c-1 if n%2==0 else c+1)
        d=1
        for p in PRIMES:
            if g%p==0:d*=p
        if d>1:
            events+=1
            n17+=d%17==0
            c+=d-1
        t=n
        if t-begin[0]>max_elapsed:
            raise AssertionError(('unexpectedly long',begin,t,c,events,n17))

def jump(t,c):
    t0,c0=t,c
    events=n17=0
    while True:
        options=[]
        for p in PRIMES:
            if (c-1)%p==0:r=0
            elif (c+1)%p==0:r=p+2
            else:continue
            delay=(r-t)%(2*p) or 2*p
            options.append((delay,p))
        if not options:return n17,events,t-t0,c-c0
        delay=min(v for v,p in options)
        d=1
        for v,p in options:
            if v==delay:d*=p
        t+=delay;c+=d-1;events+=1;n17+=d%17==0
        assert t-t0<=900

def main():
    rng=Random(20261123)
    witness={
        'max_return_depth':432334160,
        'max_events':233618750,
        'max_elapsed':64504807,
        'max_growth':81973026,
    }
    seen={}
    for name,index in witness.items():
        t,c=post_state(index)
        a=literal(t,c);b=jump(t,c)
        assert a==b,(name,a,b)
        assert a[0]<=7 and a[1]<=62 and a[2]<=354 and a[3]<=23224
        print('Q17_EXTREME_LITERAL_PASS',name,index,'q17_events,total_events,elapsed,growth',a)
        seen[name]=a
    assert seen['max_return_depth'][0]==7
    assert seen['max_events'][1]==62
    assert seen['max_elapsed'][2]==354
    assert seen['max_growth'][3]==23224
    n=3000
    for j in range(n):
        t,c=post_state(rng.randrange(N))
        a=literal(t,c);b=jump(t,c)
        assert a==b,(j,t,c,a,b)
        assert a[0]<=7 and a[1]<=62 and a[2]<=354 and a[3]<=23224
    arbitrary=1500
    for j in range(arbitrary):
        t=5*L+rng.randrange(L)
        c=5*L+2*rng.randrange(P)
        a=literal(t,c);b=jump(t,c)
        assert a==b,(j,t,c,a,b)
        assert a[0]<=8 and a[1]<=126 and a[2]<=769 and a[3]<=296054
    print('Q17_INDEPENDENT_LITERAL_PASS',len(witness),'extremes',n,'post-q17',arbitrary,'arbitrary-start states')
if __name__=='__main__':main()
