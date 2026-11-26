"""Efficient candidate graph and actual prefix traffic. Stdlib only.
Run: python min_simple_efficient_graph_audit.py 1000 10000 100000 1000000
"""
from collections import Counter
from math import isqrt
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R,C=16):
    lo=R+(R%2); V=(2*R-lo+1)//2
    a=spf(2*R+1); adj=[[] for _ in range(V)]; qvals=[0]*V
    din=[0]*V; dtin=[0]*V; dtout=[0]*V; T=max(7,isqrt(R)//4)
    for i in range(V):
        u=lo+2*i; fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:continue
        q=min(fs[0],gs[0]);qvals[i]=q
        for p in fs+gs:
            U=u+p-1
            if p<=C*q and U<2*R:
                j=(U-lo)//2;adj[i].append(j);din[j]+=1
                assert j>i and (U%p==0 or (U+2)%p==0)
                if p>=T:dtin[j]+=1;dtout[i]+=1
    dout=list(map(len,adj)); assert sum(din)==sum(dout)
    seeds=list(range(6*((R+5)//6),3*R//2+1,6))
    f=[0]*V
    for X in seeds:f[(X-lo)//2]=1
    g=f.copy(); marked=[0]*V; exact=[0]*V; actual=[(X,X//2+3) for X in seeds]
    print(f'R={R} V={V} seeds={len(seeds)} C={C} T={T} edges={sum(din)} maxdeg={max(din)},{max(dout)}')
    print('degree moments in/out, orders 1,2,4',[(sum(x**k for x in din),sum(x**k for x in dout)) for k in (1,2,4)])
    print('marked degrees in/out, orders 1,2,4',[(sum(x**k for x in dtin),sum(x**k for x in dtout)) for k in (1,2,4)])
    for h in range(1,17):
        nf=[0]*V;nm=[0]*V
        for i,js in enumerate(adj):
            if f[i]:
                for j in js:
                    nf[j]+=f[i];nm[j]+=f[i] if 2*(j-i)+1>=T else marked[i]
        f,marked=nf,nm
        assert all(0<=m<=b for m,b in zip(marked,f))
        for i,b in enumerate(f):g[i]+=b
        na=[]
        for u,v in actual:
            i=(u-lo)//2
            if not qvals[i]:continue
            fs,gs=factors(u-1,a),factors(u+1,a)
            w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs]);U=u+p-1
            if U<2*R and p<=C*qvals[i]:
                assert (U-lo)//2 in adj[i];na.append((U,v+w))
        actual=na; counts=Counter((u-lo)//2 for u,v in actual)
        for i,b in counts.items():assert b<=f[i];exact[i]+=b
        if h in (1,2,4,8,16):
            print('depth',h,'paths',sum(f),'marked',sum(marked),'max',max(f),'energy',sum(x*x for x in f),'actual',len(actual),'actual_max',max(counts.values(),default=0),'actual_energy',sum(x*x for x in counts.values()))
    assert all(b<=c for b,c in zip(exact,g))
    print('prefix through depth 16, candidate energy',sum(x*x for x in g),'actual arrivals energy',sum(x*x for x in exact))

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
