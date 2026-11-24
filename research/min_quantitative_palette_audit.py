#!/usr/bin/env python3
from math import isqrt, factorial
from itertools import combinations
from functools import lru_cache
import sys


def bounds(k,L,g):
    d=k+1; H=(L+2)*g; A=factorial(d)*H**d
    D=factorial(d)*A**d; Z=2*d*H*D
    n=g*(Z+3); U=D*(n*(L+2)+Z)
    return n,max(A,(k+1)*U+2)


def exact_word(P):
    # No LOW labels: each state records cumulative gain and the assigned
    # initial-horizon residues (None for a prime not yet used).
    @lru_cache(None)
    def go(G, residues):
        best=()
        for i,p in enumerate(P):
            for s in (-1,1):
                a=(-G-s)%p
                if residues[i] is not None and residues[i]!=a: continue
                R=residues[:i]+(a,)+residues[i+1:]
                w=((p,s),)+go(G+p-1,R)
                if len(w)>len(best): best=w
        return best
    w=go(0,(None,)*len(P));return w,go.cache_info().currsize


def check_narrow(w,L=2):
    # Check every contiguous segment satisfying the stated narrow-band test.
    checks=zero=0
    for a in range(len(w)):
        for b in range(a+1,len(w)+1):
            sub=w[a:b]; ps=[p for p,s in sub]; p=min(ps); W=max(ps)-p;m=len(ps)
            if p<=m*(W+L+2)+2 or any(q+2 in ps for q in ps):continue
            checks+=1
            where=[i for i,q in enumerate(ps) if q==p]
            assert len(where)<=2
            if len(where)==2:
                i,j=where;assert j==i+2 and ps[i+1]==p+4 and sub[i][1]==1 and sub[j][1]==-1
                zero+=1
            assert m<=3**len(set(ps))-1
    return checks,zero


def run(lo,hi):
    P=[p for p in range(max(3,lo),hi+1) if p%2 and all(p%d for d in range(3,isqrt(p)+1,2))]
    for k in (3,4):
        best=(); bp=(); states=checks=twice=0;count=0
        for palette in combinations(P,k):
            w,n=exact_word(palette);states+=n;count+=1
            c,z=check_narrow(w);checks+=c;twice+=z
            if len(w)>len(best):best,bp=w,palette
        print(f'lo={lo} hi={hi} k={k} palettes={count} states={states} maxlen={len(best)} palette={bp} word={best} narrow_checks={checks} twice={twice}',flush=True)


if __name__=='__main__':
    for arg in sys.argv[1:]:
        lo,hi=map(int,arg.split(':'));run(lo,hi)
    for k,g in [(3,8),(4,32)]:
        n,p=bounds(k,210,g);print(f'k={k} g={g} n={n} p={p}')
