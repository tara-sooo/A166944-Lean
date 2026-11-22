#!/usr/bin/env python3
"""A166944 permutation-energy, exact CRT, and overlap-depth audit.

Uses Python 3 stdlib. Finite audit plus exact arithmetic identities; not
a proof of Cap B or infinitude of twin primes.
"""
from itertools import permutations, product
from math import gcd, isqrt, prod
from collections import defaultdict

def prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    return all(n % q for q in range(3,isqrt(n)+1,2))

def crt(modres):
    x,m=0,1
    for p,res in modres:
        assert gcd(m,p)==1
        x+=m*((res-x)*pow(m,-1,p)%p)
        m*=p
    return x,m

def event_list(N=2500000):
    C=1;out=[]
    for n in range(2,N+1):
        e=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
        if e>1:
            out.append((n,e,C+e-1))
            C+=e-1
    assert len(out)==250 and C==2860770
    return out

def factors(n):
    out=[];d=3
    while d*d<=n:
        if n%d==0:
            if d>=5:out.append(d)
            while n%d==0:n//=d
        d+=2
    if n>=5:out.append(n)
    return out

def weighted_energy(A,B,w):
    def prefix(seq):
        z=0;out={}
        for p in seq:out[p]=z;z+=w[p]
        return out
    a,b=prefix(A),prefix(B)
    delta={p:b[p]-a[p] for p in A}
    inversions=[(p,q) for i,p in enumerate(A)
                for q in A[i+1:] if B.index(q)<B.index(p)]
    W=sum(w.values())
    E=sum(w[p]*delta[p]**2 for p in A)
    J=sum(w[p]*w[q]*(delta[p]-delta[q]) for p,q in inversions)
    lo=sum(w[p]*w[q]*(w[p]+w[q]) for p,q in inversions)
    assert sum(w[p]*delta[p] for p in A)==0
    assert E==J and E>=lo
    assert E<=W*max(delta.values())*(-min(delta.values()))
    assert 3*E<=W**3-sum(x**3 for x in w.values())
    if tuple(B)==tuple(reversed(A)):
        assert 3*E==W**3-sum(x**3 for x in w.values())
    return W,delta,E,lo

def permutation_sweep():
    checked=0
    for k in range(2,6):
        A=list(range(k))
        for ww in product(range(1,5),repeat=k):
            w=dict(enumerate(ww))
            for B in permutations(A):
                weighted_energy(A,B,w);checked+=1
    assert checked==129440
    print("129440 weighted permutations PASS")

def common_core(first,last,D):
    keys=sorted(first)
    u=max(first[p][0] for p in keys)
    v=min(last[p][0] for p in keys)
    assert u<v
    x=2*u-D[u]
    mods=[]
    for p in keys:
        f,l=first[p],last[p]
        fringe=(D[u]-f[1])+(l[1]-D[v])
        tau=0 if f[0]%2==l[0]%2 else (2 if f[0]%2 else -2)
        mods.append((p,(tau-fringe)%p))
    h,P=crt(mods)
    actual=D[v]-D[u]
    cap=2*(v-u)+x
    assert 0<=h<=actual<=cap and (actual-h)%P==0
    return u,v,h,P,cap,actual

def actual_reuse():
    ev=event_list()
    D={n:C for n,e,C in ev}
    uses=defaultdict(list)
    for i,(n,e,C) in enumerate(ev):
        for p in factors(e):uses[p].append(i)
    dif=[0]*(len(ev)+1)
    intervals=[]
    for p,ix in uses.items():
        for a,b in zip(ix,ix[1:]):
            T=ev[b][2]-ev[a][2]
            assert T>=2*(p-1)
            dif[a+1]+=1;dif[b+1]-=1
            intervals.append((p,a,b,T))
    d=[];cur=0
    for i in range(len(ev)):
        cur+=dif[i];d.append(cur)
    sumT=sum(item[3] for item in intervals)
    integral=sum(d[i]*(ev[i][1]-1) for i in range(len(ev)))
    assert len(uses)==45 and len(intervals)==125
    assert (sumT,integral,max(d))==(30879800,30879800,12)
    peak=next(i for i,(n,e,C) in enumerate(ev) if n==356874)
    assert d[peak]==12
    chosen=[(p,a,b) for p,a,b,T in intervals if a<peak<=b]
    first={p:(ev[a][0],ev[a][2]) for p,a,b in chosen}
    last={p:(ev[b][0],ev[b][2]) for p,a,b in chosen}
    assert tuple(sorted(first))==(5,7,11,13,17,19,29,31,37,47,149,313)
    assert common_core(first,last,D)==(
         356873,356883,8,117868154539690555,308,8)
    # Another exact four-key bridge
    keys=(5,13,149,313)
    first={p:(ev[uses[p][0]][0],ev[uses[p][0]][2]) for p in keys}
    last={p:(ev[uses[p][-1]][0],ev[uses[p][-1]][2]) for p in keys}
    assert common_core(first,last,D)==(
         356857,357004,300,3031405,598,300)
    print("Authentic factor returns 125; growth charged",sumT,
          "maximum depth 12; 12-key core H=8 PASS")
    # Authentic inverted 7,13...13,7
    p,q=7,13
    W,delta,E,lo=weighted_energy([p,q],[q,p],{p:6,q:12})
    assert (W,delta,E,lo)==(18,{7:12,13:-6},1296,1296)
    h,P=crt([(7,(-18-12)%7),(13,(2-18+6)%13)])
    assert (h,P)==(68,91)
    print("Authentic 7,13 reversal inversion-energy equality PASS")

def twelve_wheel_and_synthetic():
    p,q,r=421,2521,2497753861
    assert all(prime(t) and t%420==1 for t in (p,q,r))
    W=p+q-2
    h,P=crt([(12,0),(p,(-W-(q-1))%p),
                      (q,(-W+(p-1))%q)])
    assert (h,P,2*W+h)==(1479828,12736092,1485708)
    M=500113
    assert prime(M) and prime(M-2)
    K=(7*M-1)//4
    Gcap=2*K-(2*M-2)
    assert (K,Gcap)==(875197,750170) and 2*W+h>Gcap
    H=r-1
    assert (H-h)%P==0 and r%420==1
    # Selected prime factors activate only at their desired event states.
    word=[p,q,r,q,p]
    shifts=[0]
    for e in word[:-1]:shifts.append(shifts[-1]+e-1)
    n0,mod=crt([(p,0),(q,-(p-1)),(r,-(p-1)-(q-1))])
    for key,expected in ((p,[0,4]),(q,[1,3]),(r,[2])):
        positions=[i for i,sh in enumerate(shifts)
                   if (n0+sh)%key in (0,2)]
        assert positions==expected
        assert all((n0+shifts[i])%key==0 for i in expected)
    for pp in range(13,1200,12):
        if not prime(pp):continue
        for a in (0,1):
            for b in (0,1):
                tau=0 if a==b else (2 if a else -2)
                expected=12*pp if a==b else (10*pp+2 if a else 2*pp-2)
                assert expected%12==0 and (expected-tau)%pp==0
                assert not any((x-tau)%pp==0 for x in range(12,expected,12))
    print("12-wheel CRT min=1479828 excludes twin-start M=500113;",
          "artificial inverse prime clocks PASS")

if __name__=="__main__":
    permutation_sweep()
    actual_reuse()
    twelve_wheel_and_synthetic()
    print("PASS: finite audit; global Cap B and twin-prime infinitude OPEN")
