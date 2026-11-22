#!/usr/bin/env python3
"""Exact old wheel split residues and dense-prime complete-lift certificates.

Python 3 standard library. Independent finite integer checks for the paper
growth-adaptive insertion lemma; NO Cap B or twin-prime infinity proof.
"""
from math import gcd

def grow(m,L):
    c=2*m-2
    for n in range(m+3,(7*m-1)//4+1):
        h=gcd(n,c-1) if n%2==0 else gcd(n-2,c+1)
        c+=gcd(h,L)-1
    return c-(2*m-2)

def split_residue(L,a,p):
    m=20*L+a;h=0;res=set();last=0
    for t in range(1,6*L+2*p+11):
        if t%2:
            b=m+t+2;f=2*t+7-h;k=2
        else:
            b=m+t;f=2*t+1-h;k=0
        if f%p==0:res.add((-t-k)%p)
        e=gcd(gcd(b,abs(f)),L)
        if e>1:last=t
        h+=e-1
    return h,last,res

def main():
    totals=eligible,outside=0
    for L in (15,21,35,45,63,105,135,315):
        for p in (43,53,67,79,101,127,149,181,211,257):
            if L%p==0:continue
            for a in range(1,2*L,2):
                totals+=1
                h,last,res=split_residue(L,a,p)
                if p>6*h+7:
                    eligible+=1
                    outside+=p<=12*L+7
                    assert len(res)==2,(L,a,p,h,last,len(res))
    assert (totals,eligible,outside)==(7340,5988,5958)
    print('PASS exact split residue classes:',totals,eligible,outside)
    L=315;a=1
    for p,expected in (
        (101,[(25201,108),(38431,108)]),
        (211,[(22051,210),(110881,210)])):
        found=[]
        for k in range(p):
            m=20*L+a+2*L*k
            old=grow(m,L);new=grow(m,L*p)
            assert old==0
            if new-old:found.append((m,new-old))
        assert found==expected,(p,found)
        print('PASS natural-cutoff dense prime',p,'divergent lifts',found)

if __name__=='__main__':
    main()
