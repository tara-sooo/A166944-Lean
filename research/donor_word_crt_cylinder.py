#!/usr/bin/env python3
"""Exact original parity-GCD event-word CRT cylinders, no distribution assumption.
Run: python3 research/donor_word_crt_cylinder.py 256 1024 4096
"""
from collections import defaultdict
from math import gcd, isqrt
import sys

def primes(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]

def trace(M,B):
    ps=primes(B); n=M+2; C=2*M-2; K=(7*M-1)//4;out=[]
    while n<K:
        best=K+1
        for p in ps:
            if (C-1)%p==0:r=0
            elif (C+1)%p==0:r=p+2
            else:continue
            g=(r-n)%(2*p) or 2*p
            if n+g<best:best=n+g
        if best>K:break
        raw=gcd(best if best%2==0 else best-2,C-1 if best%2==0 else C+1)
        d=1
        for p in ps:
            if raw%p==0:d*=p
        if d==1:raise AssertionError('zero event')
        out.append((d,best%2,best))
        C+=d-1;n=best
    return out

def audit(X):
    B=isqrt(7*X)+(isqrt(7*X)**2<7*X)
    groups=[defaultdict(list) for _ in range(5)]
    for M in range(X+1,2*X,2):
        tr=trace(M,B)
        # Source-free TIME-GAIN congruence: p | G - (2*delta + 7/1).
        gain = 0
        for d, parity, t in tr:
            delta = t - (M + 2)
            clock_offset = 7 if parity == 0 else 1
            for p in primes(B):
                if d % p == 0:
                    assert (gain - (2 * delta + clock_offset)) % p == 0, (X,M,d,p,delta,gain)
            gain += d - 1
        for depth in range(1,5):
            if len(tr)>=depth:
                key=tuple((d,parity) for d,parity,_ in tr[:depth]); groups[depth][key].append(M)
    for depth in range(1,5):
        peak=0; worst=None; nontrivial=0; total=0
        for key,starts in groups[depth].items():
            residues={}; total+=len(starts)
            G=0
            for d,parity in key:
                k=3 if parity==0 else 1
                r=d
                for p in primes(B):
                    if r%p==0:
                        if p not in residues:
                            residues[p]=((k-G)*pow(2,-1,p))%p
                        else:assert residues[p]==((k-G)*pow(2,-1,p))%p,(X,depth,key,p)
                        while r%p==0:r//=p
                assert r==1
                G+=d-1
            P=1
            for p in residues:P*=p
            first=starts[0]%P
            assert all(m%P==first for m in starts),(X,depth,key,P,starts)
            bound=(X//2-1)//P+1
            assert len(starts)<=bound,(X,depth,key,len(starts),bound,P)
            if len(starts)>1 and P>1: nontrivial+=1
            if len(starts)>peak:peak=len(starts);worst=(key,P,bound,starts[:7])
        print('CRT_CYLINDER_PASS',f'X={X}',f'B={B}',f'depth={depth}',f'groups={len(groups[depth])}',f'tags={total}',f'with_multi_source_Pgt1={nontrivial}',f'peak={peak}',f'worst={worst}')
    untyped=defaultdict(list)
    for key,starts in groups[1].items(): untyped[key[0][0]].extend(starts)
    for d, starts in untyped.items():
        p=next((p for p in primes(B) if d%p==0),None)
        if p and len({m%p for m in starts})>1:
            print('PARITY_OMISSION_COUNTEREXAMPLE',f'X={X}',f'd={d}',f'p={p}',f'number_of_M_residues={len({m%p for m in starts})}',f'example={starts[:10]}')
            break
if __name__=='__main__':
    for x in map(int,sys.argv[1:] or ['256','1024']):audit(x)
