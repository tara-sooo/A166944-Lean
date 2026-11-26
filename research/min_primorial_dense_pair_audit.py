"""Finite arithmetic audit: dense source-only pair sieve and singular-return pairs.
Run: python min_primorial_dense_pair_audit.py 100000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
The asymptotic sieve and transport estimates are paper deductions.
"""
from collections import Counter
from itertools import product
from math import prod
from sys import argv
from sympy import primerange
from min_primorial_record_supply_audit import spf_table, step, factors


def local():
    count=0
    for p in map(int,primerange(7,200)):
        for e,E,ell in product((-1,1),range(0,24,2),(7,11,13,17,19,23)):
            if p==ell:continue
            D=p+E-1
            roots={k for k in range(ell) if k*(p*k+2*e)*(p*k+e+D-1)*(p*k+e+D+1)%ell==0}
            nu=2*(D%ell==0)+((D-2)%ell==0)+((D+2)%ell==0)
            assert len(roots)==4-nu
            assert len({k for k in range(ell) if k*(p*k+2*e)%ell==0})==2
            count+=1
    print('local root comparisons',count,flush=True)


def strip(cap,D0):
    B=max(3,D0//2);Q=2*prod(map(int,primerange(3,B+1)))
    a=spf_table(cap+10); L=D0//2+1; N=(cap//2-5)*L
    def idx(u,d):return (u//2-6)*L+d//2
    def state(i):return 2*(i//L+6),2*(i%L)
    valid=[False]*N; singular=[False]*N; succ=[-1]*N;lab=[0]*N;sgn=[0]*N;wait=[0]*N
    for u in range(12,cap+1,2):
        for d in range(0,min(D0,u+2)+1,2):
            i=idx(u,d);v=(u+d)//2;valid[i]=True;singular[i]=(d==(0 if v%2==0 else 6))
            w,p,e=step(u,v,a);U=u+p-1;V=v+w;dd=2*V-U
            if p>u//2+1 or U>cap or not 0<=dd<=D0:continue
            j=idx(U,dd);succ[i]=j;lab[i]=p;sgn[i]=e;wait[i]=w
            assert j>i
    # First singular destination and final event source, for every local vertex.
    end=[-1]*N;last=[-1]*N;span=[0]*N
    for i in range(N-1,-1,-1):
        j=succ[i]
        if j<0:continue
        if singular[j]:end[i]=j;last[i]=i
        elif end[j]>=0:end[i]=end[j];last[i]=last[j];span[i]=span[j]+lab[i]-1
        if end[i]>=0:
            assert span[i]<=Q and state(last[i])[0]-state(i)[0]==span[i]
    # Count actual ordered pair source states once, then test induced starts.
    c=Counter();thresholds=sorted({max(17,2*D0+2),max(31,2*D0+2),max(61,2*D0+2)})
    pairs={T:set() for T in thresholds};sources={T:set() for T in thresholds}
    for i in range(N):
        j=succ[i]
        if j<0 or not singular[j] or end[j]<0:continue
        k=last[j];p,r=lab[i],lab[k];x,d=state(i);y,dd=state(k);E=y-x-p+1
        assert E==span[j] and 0<=E<=Q and E%2==0
        for T in thresholds:
            if min(p,r)<T:continue
            assert wait[i]*4>=p and wait[k]*4>=r
            assert all(8*q>=p for q in factors(x-1,a)+factors(x+1,a))
            assert all(8*q>=r for q in factors(y-1,a)+factors(y+1,a))
            assert (p-1)**2<=64*(x+1) and (r-1)**2<=64*(y+1)
            e=sgn[i];z=(x-e)//p;D=p+E-1
            assert x==p*z+e and y==x+D
            for ell in map(int,primerange(7,(min(p,r)-1)//8+1)):
                assert z*(p*z+2*e)*(p*z+e+D-1)*(p*z+e+D+1)%ell
                c['rough_checks']+=1
            pairs[T].add(i);c['pair_checks']+=1
    for i in range(N):
        if not singular[i] or end[i]<0:continue
        for T in thresholds:
            if last[i] in pairs[T]:sources[T].add(i)
    for T in thresholds:
        assert len(sources[T])<=(Q+2)*len(pairs[T])
    print('strip',D0,'cap',cap,'vertices',sum(valid),'edges',sum(j>=0 for j in succ),'Q',Q,'pair counts',[(T,len(pairs[T]),len(sources[T])) for T in thresholds],dict(c),flush=True)

if __name__=='__main__':
    local()
    for D in (6,12,24):strip(int(argv[1]) if len(argv)>1 else 100000,D)
