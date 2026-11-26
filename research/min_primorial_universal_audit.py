"""Universal offset ray: exact clocks and doubling/record criteria.
Run: python min_primorial_universal_audit.py [horizon cap, default 10^15]
Requires sympy. Finite computations only, no asymptotic extrapolation.
"""
from math import isqrt, gcd
from collections import Counter
from functools import lru_cache
from sys import argv
from sympy import factorint, isprime

@lru_cache(None)
def primes(n):
    return tuple(sorted(int(p) for p in factorint(n)))

def step(u,v,S=None):
    choices=[]
    for e in (1,-1):
        for p in primes(u-e):
            if S is not None and p>S: continue
            w=((0 if e==1 else p+2)-v)%(2*p) or 2*p
            choices.append((w,p,e))
    return min(choices) if choices else None

def main(cap):
    u,v=4,5; record=0; prior_double=None
    rows=[]; stats=Counter(); records=[]; doubles=[]; exceptions=[]
    maxd=0; maxgap=(0,0); rawchecks=0
    while u<=cap:
        i=len(rows); w,p,e=step(u,v); d=2*v-u; L=u+3-v
        U,V=u+p-1,v+w; D=2*V-U; twin=isprime(u-1) and isprime(u+1)
        assert 0<=d<=u+2 and 2<=L and V<=u+3 and 0<=D<=U+2
        assert u+3-V+p-1==U+3-V and U+3-V>=p-1
        if p>=5 and e==1:
            assert V<=u-p-1 and L>=p+5
        if p>=5 and e==-1 and not isprime(u+1):
            # At u+3 the least plus factor would win the tie. A selected
            # nonleast factor must fire earlier, not every composite label.
            if p!=min(primes(u+1)):
                assert V<=u+3-2*p and L>=2*p+1
        if 3*p>u+1 and u>=6:
            assert p==u+1 and V==u+3 and U==2*u and D==6
        if twin and u>=6:
            assert p==u+1 and V==u+3 and U==2*u and D==6
            assert p>record
        if p==u+1 and u>=6:
            doubles.append((i,u,d,p,w,bool(twin)))
            if not twin:
                q=min(primes(u-1)); assert q*q<=u-1
                assert L<=q+4 and d>=u-2*q-2
                assert q>=5 and u%6==0
                if prior_double is not None:
                    j,X=prior_double
                    # Exact squared version of potential difference bound:
                    # sqrt(2v+1) <= sqrt(X+7)+2(i-j-1).
                    n=i-j-1; A=2*v+1; B=X+7; c=2*n
                    if A>B+c*c: assert (A-B-c*c)**2<=4*c*c*B
                exceptions.append((i,u,d,L,q))
            prior_double=(i,U)
        if not twin:
            q=min(min(primes(u-1)),min(primes(u+1)))
            assert q*q<=u+1 and w<=2*q
            if p*p>u+1:stats['non_twin_above_sqrt']+=1
            if p-1>d+4*isqrt(u+1):raise AssertionError('large jump without twin')
        else:stats['twins']+=1
        if p>record:
            records.append((i,u,v,p,record,bool(twin)))
            if not twin:stats['non_twin_records']+=1
            record=p
        assert p<=U-3
        if u<=100000:
            for n in range(v+1,V+1):
                g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                assert (g==1) if n<V else (min(primes(g))==p)
                rawchecks+=1
        rows.append((u,v,p,w));maxd=max(maxd,D);maxgap=max(maxgap,(w,u))
        u,v=U,V
    # For selected S, the first omitted universal label occurs at a known
    # record. Verify the predicted prefix and any rough-stop criterion.
    thresholds={5,7,10,20,30,50,100,200,500,1000,2000}
    thresholds.update(10**k for k in range(2,len(str(cap))))
    for i,h,t,p,r,tw in records:
        if p>10: thresholds.update((p-3,p-2,p-1,p))
    checked=rough=boundary=0
    for S in sorted(thresholds):
        if S<5:continue
        item=next((x for x in records if x[3]>S),None)
        if item is None:continue
        i,h,t,p,r,tw=item
        if h>S*S-2:continue
        a,b=4,5
        for j in range(i):
            x=step(a,b,S);assert x is not None
            w0,p0,e0=x
            assert (a,b,p0,w0)==rows[j]
            a+=p0-1;b+=w0
        assert (a,b)==(h,t)
        x=step(a,b,S)
        if tw and S<=h-2:
            assert x is None;rough+=1
        if tw and h-1<=S<=h:
            assert x is not None and x[1]==h-1;boundary+=1
        checked+=1
    print('cap',cap,'events',len(rows),'post',u,v,'stats',dict(stats),'records',len(records),'doubles',len(doubles),'non_twin_doubles',exceptions,'maxd',maxd,'rawchecks',rawchecks)
    print('cutoff checks',checked,'rough',rough,'one-prime boundary',boundary)
    print('last records',records[-8:])
    print('last doubles',doubles[-8:])
    print('max wait',maxgap)
    # A non-twin doubling can occur in the local state space. This is NOT
    # claimed reachable from the distinguished initial state (4,5).
    assert step(66,67)==(2,67,-1) and not isprime(65)
    print('local non-twin doubling control', (66,67),step(66,67))

if __name__=='__main__':main(int(argv[1]) if len(argv)>1 else 10**15)
