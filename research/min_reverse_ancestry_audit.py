#!/usr/bin/env python3
"""Exact target-specific MIN reverse ancestry, plus a time-free relaxation."""
from collections import Counter, defaultdict
from functools import lru_cache
from math import isqrt, log, ceil, gcd
import sys


def audit(X):
    assert X >= 256 and X % 4 == 0
    B = isqrt(7*X-1)+1
    Q = ceil(B/log(B)**(2/3))
    N = X//2
    Kmax = (7*(2*X-1)-1)//4
    lo = 2*X
    spf = list(range(7*X+4))
    for p in range(2,isqrt(len(spf)-1)+1):
        if spf[p] == p:
            for z in range(p*p,len(spf),p):
                if spf[z] == z: spf[z] = p
    P = sum(spf[p]==p for p in range(11,B+1))
    m = 2*P
    z = isqrt(isqrt(B))
    @lru_cache(None)
    def factors(z):
        out=[]
        while z>1:
            p=spf[z]
            if p>B: break
            if p>2: out.append(p)
            while z%p==0: z//=p
        return tuple(out)
    @lru_cache(None)
    def clocks(C):
        return tuple((p,0) for p in factors(C-1))+tuple((p,p+2) for p in factors(C+1))
    def hit(t,C,K):
        return min(((t+1+(r-t-1)%(2*p),p) for p,r in clocks(C)), default=(K+1,0))
    def root(t,C,T):
        M=t-2
        return int(X<=M<2*X and M%2==1 and C==2*M-2 and (7*M-1)//4>=T)
    @lru_cache(None)
    def reverse_edges(t,C):
        """(p, pre-horizon, earliest allowable predecessor time)."""
        out=[]
        for p in factors(C+(2 if t%2 else 0)):
            r=p+2 if t%2 else 0
            if (t-r)%(2*p): continue
            D=C-p+1
            if D<lo: continue
            cs=clocks(D)
            if min((q for q,r0 in cs if (t-r0)%(2*q)==0),default=B+1)!=p: continue
            L=max(t-1-(t-1-r0)%(2*q) for q,r0 in cs)
            assert t-2*p<=L<t
            out.append((p,D,max(L,X+3)))
        return tuple(out)
    @lru_cache(None)
    def previous_states(D,L,t):
        # Root and any previous post-event clock. Union prevents double counts
        # when a physical state has more than one possible last label.
        times=set()
        if D%4==0 and L <= D//2+3 < t: times.add(D//2+3)
        for side in (0,2):
            for p in factors(D+side):
                r=0 if side==0 else p+2
                u=L+(r-L)%(2*p)
                times.update(range(u,t,2*p))
        return tuple(sorted(times))
    def reverse_weight(q,C,t):
        T=t
        @lru_cache(None)
        def F(u,D,k):
            if k<0 or D<lo or u<X+3: return 0
            ans=root(u,D,T)
            for p,H,L in reverse_edges(u,D):
                if k>=int(p>7):
                    ans+=sum(F(v,H,k-int(p>7)) for v in previous_states(H,L,u))
            return ans
        ans=long=0
        for p,D,L in reverse_edges(t,C):
            if p==q:
                for u in previous_states(D,L,t):
                    f=F(u,D,m-1);ans+=f
                    if t-u>2*z: long+=f
        return ans,long,F.cache_info().currsize
    def relaxed(q,C):
        # Any history with <=m HIGH steps and unlimited LOW steps, ignoring time.
        # Store maximum remaining HIGH budget at each horizon (monotonicity).
        D=C-q+1; best={D:m-1}; stack=[D]; roots=set()
        while stack:
            u=stack.pop(); k=best[u]
            if lo<=u<=4*X-4 and u%4==0: roots.add(u)
            for p in set(factors(u)+factors(u+2)):
                v=u-p+1; h=k-int(p>7)
                if v>=lo and h>=0 and h>best.get(v,-1): best[v]=h;stack.append(v)
        return len(roots),len(best)
    counts=Counter(); ts=defaultdict(Counter); longs=defaultdict(Counter); checks=0; total=0
    for M in range(X+1,2*X,2):
        t,C,K=M+2,2*M-2,(7*M-1)//4; j=0
        while j<m:
            u,p=hit(t,C,K)
            if X<=1024:
                literal=None
                for v in range(t+1,K+1):
                    g=gcd(v if v%2==0 else v-2,C-1 if v%2==0 else C+1)
                    fs=factors(g)
                    if fs: literal=(v,min(fs));break
                assert (None if u>K else (u,p))==literal;checks+=1
            if u>K: break
            d=u-t;t=u;C+=p-1;assert C<=2*t
            if p>7:
                j+=1
                if p>=Q:
                    counts[p,C]+=1;ts[p,C][t]+=1;total+=1
                    if d>2*z: longs[p,C][t]+=1
    # Full verification of every reached key at small X; top 8 otherwise.
    targets=counts.most_common(None if X<=1024 else 8)
    maxrel=0; states=0; num=0; maxratio=0.0; top=None
    for (q,C),w in targets:
        # Enumerate ALL possible last event times, not just reached times.
        # Its side is determined by q|C or q|C+2.
        r=0 if C%q==0 else q+2
        assert C%q==0 or (C+2)%q==0
        start=max(X+4,(C+1)//2)
        if r: start=max(start,(C+1)//2)
        mass=0
        for t in range(start+(r-start)%(2*q),Kmax+1,2*q):
            val,long,n=reverse_weight(q,C,t);states+=n;num+=1
            assert long==longs[q,C][t],(X,q,C,t,long,longs[q,C][t])
            assert val==ts[q,C][t],(X,q,C,t,val,ts[q,C][t])
            mass+=val
        assert mass==w
        rel,size=relaxed(q,C);assert rel>=w
        maxrel=max(maxrel,rel);maxratio=max(maxratio,rel/w)
        if top is None: top=(q,C,w,rel,size,sum(longs[q,C].values()))
    print(f'X={X} B={B} P={P} Q={Q} large_events={total} keys={len(counts)} literal_checks={checks} targets={len(targets)} reverse_times={num} memo_states={states} top(q,C,W,relaxed,vertices,long)={top} max_relaxed={maxrel} max_ratio={maxratio:.6f}',flush=True)

if __name__=='__main__':
    sys.setrecursionlimit(100000)
    for x in map(int,sys.argv[1:]): audit(x)
