#!/usr/bin/env python3
from collections import defaultdict
from fractions import Fraction
from math import isqrt, prod
import sys

LOW=(3,5,7)

def primes(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]

def clock(M,G,s,p):
    C=2*M-2+G
    if (C-1)%p==0: r=0
    elif (C+1)%p==0: r=p+2
    else: return None
    return s+1+(r-(M+2+s)-1)%(2*p)

def hit(M,G,s,pool,T):
    return min(((v,p) for p in pool if (v:=clock(M,G,s,p)) is not None and v<=T),default=(T+1,0))

def run(M,pool,T):
    G=s=0; w=[]
    while True:
        v,p=hit(M,G,s,pool,T)
        if not p: return tuple(w)
        w.append((v,p)); G+=p-1; s=v

def prefix_cells(sources,pool,T):
    cells=[defaultdict(list) for _ in range(3)]
    for M in sources:
        w=run(M,pool,T); seen=set(LOW); key=(M%210,); nd=0
        firsts=[i for i,(_,p) in enumerate(w) if p not in LOW and p not in [q for _,q in w[:i]]]
        for k in range(3):
            if k>len(firsts): break
            end=0 if k==0 else firsts[k-1]+1
            nxt=w[firsts[k]] if k<len(firsts) else None
            key=(M%210,tuple((w[i][1],M%w[i][1]) for i in firsts[:k]))
            cells[k][key].append((M,w[:end],nxt))
    return cells

def reconstruct(M,key,T):
    known=list(LOW); G=s=0; w=[]
    for p,a in key[1]:
        assert M%p==a
        known.append(p)
        while True:
            v,q=hit(M,G,s,known,T); assert q
            w.append((v,q)); G+=q-1; s=v
            if q==p:break
    return tuple(w),known,G,s

def allowed(M,w,pool):
    A={p:({M%p} if p in LOW else set(range(p))) for p in pool};G=s=0
    for v,q in w:
        for p in pool:
            for a in tuple(A[p]):
                z=clock(a if a%2 else a+p,G,s,p)
                if p==q and z!=v or p!=q and z is not None and (z,p)<(v,q): A[p].remove(a)
        G+=q-1;s=v
    return A

def interventions(M,known,G,s,pool,T):
    unseen=[p for p in pool if p not in known]; R={p:{} for p in unseen};steps=0
    while True:
        v,q=hit(M,G,s,known,T)
        for p in unseen:
            for a in {(3-G)*pow(2,-1,p)%p,(1-G)*pow(2,-1,p)%p}:
                if a in R[p]:continue
                z=clock(a if a%2 else a+p,G,s,p)
                if z is not None and z<=T and (z,p)<(v,q): R[p][a]=(z,p)
        if not q: return R,steps+1
        G+=q-1;s=v;steps+=1

def audit(sources,pool,T,full=False):
    pmax=pool[-1];X=len(sources)*2
    bylow=defaultdict(list)
    for M in sources: bylow[M%210].append(M)
    for k,cells in enumerate(prefix_cells(sources,pool,T)):
        cnt=singleton=bigD=largeProduct=actualNone=checks=shadow=0; expectedNone=0.0; maxPlateau=0
        for key,rows in cells.items():
            M=rows[0][0]; w,known,G,s=reconstruct(M,key,T);A=allowed(M,w,pool)
            R,steps=interventions(M,known,G,s,pool,T);shadow+=steps;maxPlateau=max(maxPlateau,steps)
            if full: assert len(rows)==prod(len(A[p]) for p in pool)
            else: assert {m for m in bylow[key[0]] if all(m%p in A[p] for p in pool)}=={r[0] for r in rows}
            D=prod(known); n=len(rows);cnt+=n;singleton+=n==1;bigD+=n*(D>pmax);largeProduct+=n*(2*D>=X)
            survival=prod((Fraction(len(A[p])-len(A[p]&R[p].keys()),len(A[p])) for p in R),start=Fraction(1))
            none=0
            for m,actual,next_ in rows:
                assert actual==w
                assert all(m%p in A[p] for p in pool)
                candidates=[R[p][m%p] for p in R if m%p in R[p]]
                got=min(candidates,default=None); assert got==next_,(m,k,got,next_)
                none+=got is None;checks+=1
            if full: assert n*survival==none,(key,n,survival,none)
            actualNone+=none;expectedNone+=float(n*survival)
        print(f'full={int(full)} X={X} pmax={pmax} k={k} roots={cnt} cells={len(cells)} singleton={singleton} D>pmax_roots={bigD} 2D>=X_roots={largeProduct} actualNoNew={actualNone} CRT_conditionalNoNew={expectedNone:.6f} nextChecks={checks} shadowPlateaus={shadow} maxPlateaus={maxPlateau}',flush=True)

if __name__=='__main__':
    for arg in sys.argv[1:]:
        if arg=='full':
            pool=primes(13);audit(range(1,2*prod(pool),2),pool,300,True)
        else:
            X=int(arg);audit(range(X+1,2*X,2),primes(isqrt(7*X-1)+1),3*X//4-3)
