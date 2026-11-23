#!/usr/bin/env python3
"""Independent per-integer recurrence and all-q donor-word modular-rank oracle.
Run: python3 research/donor_rank_literal_oracle.py 256 512 1024
"""
from collections import Counter, defaultdict
from math import gcd, isqrt
import sys

def prime_list(B):
    return [p for p in range(3,B+1,2) if not any(p%i==0 for i in range(3,isqrt(p)+1,2))]

def audit(X):
    sq=isqrt(7*X);B=sq+(sq*sq<7*X);ps=prime_list(B)
    stats=[Counter() for _ in range(3)]
    for M in range(X+1,2*X,2):
        C=2*M-2;K=(7*M-1)//4;events=[];last={}
        for n in range(M+3,K+1):
            raw=gcd(n,C-1) if n%2==0 else gcd(n-2,C+1)
            d=1;hi=[]
            for p in ps:
                if raw%p==0:
                    d*=p
                    if p>=11:hi.append(p)
            if d==1:continue
            for q in hi:
                if q in last:
                    i=last[q];band=0 if 4*q<B else 1 if 2*q<B else 2;z=stats[band];z['total']+=1
                    m=0;low=0;E=0;coeff=defaultdict(int);occ=Counter();nonlinear=False
                    for dt,dd,hh in events[i+1:]:
                        E+=dd-1
                        if not hh:
                            low+=dd-1
                        else:
                            m+=1
                            if len(hh)!=1:
                                nonlinear=True
                            else:
                                r=hh[0];a=dd//r
                                assert 105%a==0,(dd,r)
                                coeff[r]+=a;occ[r]+=1
                    if m==0:z['zero']+=1
                    elif nonlinear:z['nonlinear']+=1
                    else:
                        z['linear']+=1
                        c=1 if events[i][0]%2==1 and n%2==1 else 3 if events[i][0]%2==1 else -1 if n%2==1 else 1
                        assert (E-c)%q==0,(M,q,n,E,c)
                        assert (sum(a*r for r,a in coeff.items())+low-m-c)%q==0
                        if any(occ[r]==1 for r in coeff):z['singleton']+=1
                        if any(a%q for a in coeff.values()):z['nontrivial']+=1
                        else:z['degenerate']+=1
                        if 105*m<q:z['short']+=1
                last[q]=len(events)
            events.append((n,d,hi))
            C+=d-1
    print('LITERAL_DONOR_RANK_PASS',f'X={X}',f'B={B}',*(f'band{i}='+str(dict(z)) for i,z in enumerate(stats)))
if __name__=='__main__':
    for X in map(int,sys.argv[1:] or ['256','512']):audit(X)
