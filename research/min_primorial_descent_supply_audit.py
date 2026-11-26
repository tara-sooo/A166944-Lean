"""Finite audit of lag-floor supply constraints for arbitrary reset prefixes.
Run: python min_primorial_descent_supply_audit.py [seed limit, default 100000]
Requires the sibling min_primorial_record_supply_audit.py and SymPy.
The upper-bound sieve and asymptotic support conclusions are paper results.
"""
from collections import Counter
from math import prod
from sys import argv
from min_primorial_record_supply_audit import spf_table, factors, step


def audit(R):
    a=spf_table(4*R+10000)
    seeds=events=descents=checks=0
    worst={k:(0,1,None) for k in (7,1000,10000)}
    max_support=(0,None)
    for r in range(7,R+1,6):
        seeds+=1; X=2*r-2; u=X;v=r+2; counts=Counter(); m=0
        while True:
            w,p,e=step(u,v,a)
            if p>r:break
            L=u+3-v; U,V=u+p-1,v+w; L2=U+3-V
            assert L>=2 and L2>=2
            if L2<L:
                descents+=1; counts[p]+=1
                assert w>=p and L-L2<=p+1
                fs=factors(u-1,a)+factors(u+1,a)
                assert all(2*q>=p for q in fs)
                assert p*p<=4*(u+1)
            D=X//2-L2
            Q=2*prod(counts)
            assert D<Q
            for z in (3,7,13,31):
                Q=2*prod(p0 for p0 in counts if p0<=z)
                budget=sum(n*(p0+Q) for p0,n in counts.items() if p0>z)
                assert budget>=D-Q+1
                checks+=1
            for k,(num,den,row) in worst.items():
                if r>=k and D*den>num*X:worst[k]=(D,X,(r,U,V,len(counts)))
            if len(counts)>max_support[0]:max_support=(len(counts),(r,U,V))
            u,v=U,V;events+=1;m+=1
            assert m<100000
    print('seed limit',R,'seeds',seeds,'pre-record events',events,'lag descents',descents,'subset budget checks',checks)
    print('max relative lag decrease by seed cutoff',worst)
    print('max descending-label support',max_support)

if __name__=='__main__':audit(int(argv[1]) if len(argv)>1 else 100000)
