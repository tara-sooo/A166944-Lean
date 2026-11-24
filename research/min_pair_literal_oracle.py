#!/usr/bin/env python3
from math import gcd, isqrt
from bisect import bisect_left
from collections import defaultdict
import sys

def run(X):
    B=isqrt(7*X-1)+1
    spf=list(range(7*X+4))
    for p in range(2,isqrt(len(spf)-1)+1):
        if spf[p]==p:
            for n in range(p*p,len(spf),p):
                if spf[n]==n: spf[n]=p
    bands=[B]
    while bands[-1]<X: bands.append(2*bands[-1])
    paths=[]; total=0; R=0
    for M in range(X+1,2*X,2):
        t,C,K=M+2,2*M-2,(7*M-1)//4; states=[]
        while True:
            hit=None
            for u in range(t+1,K+1):
                g=gcd(u if u%2==0 else u-2,C-1 if u%2==0 else C+1)
                if g>1 and spf[g]<=B:
                    hit=(u,spf[g]);break
            states.append((C,t,hit))
            if hit is None: break
            r=min(spf[C-1],spf[C+1]);R+=r;total+=1
            t,p=hit;C+=p-1
        paths.append(states)
    out=[defaultdict(int) for _ in bands]
    for i,aa in enumerate(paths):
        for j in range(i+1,len(paths)):
            bb=paths[j];v=out[bisect_left(bands,2*(j-i))];a={C:(t,h,k) for k,(C,t,h) in enumerate(aa)};b={C:(t,h,k) for k,(C,t,h) in enumerate(bb)};met=False
            for C in sorted(a.keys()&b.keys()):
                t,h,k=a[C];u,g,l=b[C]
                if t==u and not met:
                    met=True;v['F']+=2
                    if k and l and aa[k-1][0]==bb[l-1][0]:v['sameLabel']+=2
                if h is None or g is None:continue
                r=2*min(spf[C-1],spf[C+1]);v['E']+=r
                if t==u:continue
                v['G']+=r
                if h[1]!=g[1]:v['Gdiff']+=r
                elif h[0]==g[0]:v['Gmerge']+=r
                elif h[0]-t==g[0]-u:v['Gparallel']+=r
                else:v['Gchange']+=r
    print(f'X={X} events={total} R={R}')
    for hi,v in zip(bands,out):print(hi,dict(v))

if __name__=='__main__':
    for X in map(int,sys.argv[1:]):run(X)
