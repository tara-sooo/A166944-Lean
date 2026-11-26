"""Finite arithmetic certificate and local false-double ancestry audit.
Run: python min_primorial_lag_barrier_audit.py [reverse cap, default 100000]
Dependencies: numpy, sympy, sibling min_primorial_record_supply_audit.py.
The finite checks are not a proof of global reachability or twin infinitude.
"""
from math import prod, gcd
from functools import lru_cache
from collections import Counter
from sys import argv
import numpy as np
from sympy import primerange, nextprime, isprime
from min_primorial_record_supply_audit import spf_table, factors


def small_clock(u,v,ps):
    c=[((s-v-1)%(2*p)+1,p) for p in ps for e,s in ((1,0),(-1,p+2)) if (u-e)%p==0]
    return min(c) if c else None


def small_certificate():
    ps=(3,5,7,11); Q=2*prod(ps); V=np.arange(Q,dtype=np.int64)
    # Scaled reward 13*(delta_d)-48*(delta_u) = 26*w-61*(p-1).
    dp=np.zeros((Q//2+1,Q),dtype=np.int32)
    for u in range(Q-2,-1,-2):
        w=np.full(Q,10000,dtype=np.int64); pp=np.zeros(Q,dtype=np.int64)
        for p in ps:
            for e,s in ((1,0),(-1,p+2)):
                if (u-e)%p:continue
                ww=(s-V-1)%(2*p)+1
                b=(ww<w)|((ww==w)&(p<pp)); w[b]=ww[b];pp[b]=p
        for p in ps:
            b=pp==p
            if not np.any(b):continue
            assert u+p-1<=Q
            dp[u//2,b]=np.maximum(0,26*w[b]-61*(p-1)+dp[(u+p-1)//2,(V[b]+w[b])%Q])
    B=int(dp.max()); I=max(int(dp[(12*k%Q)//2,(6*k+3)%Q]) for k in range(Q//6))
    assert B==56 and I==24
    assert 61-9*13==-56
    def witness(u,v):
        path=[]; val=0
        while dp[u//2,v%Q]>0:
            w,p=small_clock(u,v,ps);reward=26*w-61*(p-1)
            assert dp[u//2,v%Q]==reward+dp[(u+p-1)//2,(v+w)%Q]
            path.append((p,w,reward));val+=reward;u+=p-1;v+=w
        return path,val
    i,v=map(int,np.unravel_index(dp.argmax(),dp.shape))
    k=max(range(Q//6),key=lambda k:dp[(12*k%Q)//2,(6*k+3)%Q])
    print('finite certificate',Q,'states',(Q//2+1)*Q,'B',B,'I',I,'max witness',(2*i,v,witness(2*i,v)),'seed witness',(k,witness(12*k%Q,(6*k+3)%Q)),flush=True)
    # Independent scalar recurrence check on every state, using exact clocks.
    # The row Q is a terminal wall; v is a periodic residue.
    for u in range(0,Q+1,2):
        for v in range(Q):
            x=small_clock(u,v,ps)
            rhs=0 if x is None else max(0,26*x[0]-61*(x[1]-1)+int(dp[(u+x[1]-1)//2,(v+x[0])%Q]))
            assert int(dp[u//2,v])==rhs
    print('independent scalar recurrence checks',(Q//2+1)*Q,flush=True)


def reverse_audit(cap):
    a=spf_table(cap+10)
    @lru_cache(None)
    def clocks(u):
        return tuple((p,0 if e==1 else p+2) for e in (1,-1) for p in factors(u-e,a))
    def prevs(u,v):
        if not u//2<=v<=u+1:return
        g=gcd(u,v) if v%2==0 else gcd(u+2,v-2)
        while g%2==0:g//=2
        for p in factors(g,a):
            x=u-p+1
            if x<12 or v>x+3:continue
            fs=clocks(x)
            if min((q for q,s in fs if (v-s)%(2*q)==0),default=0)!=p:continue
            b=max(v-1-(v-1-s)%(2*q) for q,s in fs)
            for t in range(max(x//2,b),min(x+1,v-1)+1):yield x,t
    visited=0
    def depth(u,v):
        nonlocal visited
        visited+=1
        assert not (u%12==0 and v==u//2+3), ('reachable false double',u,v)
        return max((1+depth(x,t) for x,t in prevs(u,v)),default=0)
    counts=Counter();mx=(-1,0,0)
    for u in range(12,cap+1,6):
        if a[u+1] or a[u-1]==0:continue
        q=a[u-1]
        for v in range(u-q-1,u+2):
            z=depth(u,v);counts[z]+=1;mx=max(mx,(z,u,v))
    print('reverse cap',cap,'candidates',sum(counts.values()),'zero predecessors',counts[0],'max depth',mx,'nodes checked',visited,flush=True)
    # Recover one deepest path using the same exact reverse recursion.
    d,u,v=mx;path=[(u,v)]
    while d>0:
        x,t=next((x,t) for x,t in prevs(u,v) if depth(x,t)==d-1)
        path.append((x,t));u,v=x,t;d-=1
    path.reverse()
    print('deepest ancestor first/last',path[:3],path[-3:],'length',len(path)-1,flush=True)
    # Independently confirm all edges using the full forward clock selection.
    for (u,v),(U,V) in zip(path,path[1:]):
        w,p=min(((s-v-1)%(2*p)+1,p) for p,s in clocks(u))
        assert (u+p-1,v+w)==(U,V)


def local_construction(ps):
    # Small explicit examples of the constant-lag CRT construction. For the
    # arbitrary-length theorem use recursively separated primes in the note.
    L=3+2*prod(ps); E=[0]
    for p in ps:E.append(E[-1]+p-1)
    R,M=0,2
    for q in primerange(3,L+5):
        q=int(q)
        if q in ps:
            j=ps.index(q);a=(1-E[j])%q
            assert all((a+g)%q not in (1,q-1) for i,g in enumerate(E) if i!=j)
        else:
            excluded={(e-g)%q for g in E for e in (1,-1)}
            a=next(a for a in range(q) if a not in excluded)
        R+=M*((a-R)*pow(M,-1,q)%q);M*=q
    q=int(nextprime(L+4));a=(1-E[-1])%q
    R+=M*((a-R)*pow(M,-1,q)%q);M*=q
    assert gcd(R+E[-1]+1,M)==1
    # Dirichlet proves the progression contains arbitrarily large primes.
    # This finite search just checks two examples; for >64-bit results
    # SymPy uses a probable-prime test, not a primality certificate.
    for k in range(1,100000):
        u0=R+k*M;upper=u0+E[-1]+1
        if u0>2*L and isprime(upper):break
    else:raise AssertionError('finite search cap')
    u=u0;v=u+3-L
    for p in ps:
        w=p-1
        for n in range(v+1,v+w+1):
            g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
            if n<v+w:assert g==1
            else:assert g%p==0 and all(g%int(a) for a in primerange(3,p))
        u+=p-1;v+=w;assert u+3-v==L
    assert (u-1)%q==0 and u-1>q and isprime(u+1)
    for n in range(v+1,u+4):
        g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
        assert g==(u+1 if n==u+3 else 1)
    print('constant lag',ps,'L',L,'forced lower factor',q,'upper digits',len(str(upper)),'search k',k,'terminal center',u,flush=True)


def lag_cuts():
    # Direct residue proof audit for the exact lag maps on the first several periods.
    for p in primerange(3,100):
        p=int(p)
        for L in range(2,8*p+3):
            for s0 in (0,(p+4)%(2*p)):
                s=L-1-(L-1-s0)%(2*p)
                if s<0:continue
                L2=s+p-1
                assert L2>=p-1 and L<=2*L2+2
                for j in range(0,5*2*p,2*p):
                    if L>=j+2:assert L2>=j+2
    print('lag residue checks passed',flush=True)

if __name__=='__main__':
    small_certificate()
    lag_cuts()
    reverse_audit(int(argv[1]) if len(argv)>1 else 100000)
    local_construction((7,))
    local_construction((7,13))
