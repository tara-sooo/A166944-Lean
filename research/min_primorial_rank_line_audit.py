"""Rank-line local construction and exact reachable-state scan.
Run: python min_primorial_rank_line_audit.py 1000000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
"""
from collections import Counter, defaultdict
from math import gcd
from sys import argv
from sympy import primerange, isprime
from min_primorial_record_supply_audit import spf_table, step, factors


def construct(ps):
    es=[0]
    for p in ps:es.append(es[-1]+p-1)
    C=2*max(ps)+8
    T,M=0,2
    for q in map(int,primerange(3,C+1)):
        if q in ps:
            j=ps.index(q);r=(1-es[j])*pow(3,-1,q)%q
            assert all((3*r+es[i])%q not in (1,q-1) for i in range(len(ps)) if i!=j)
            assert (r+es[-1]//3+1)%q
        elif q==3:r=next(r for r in range(q) if (r+es[-1]//3+1)%q)
        elif q==5:
            r=(3-es[-1]//3)%5
            assert all((3*r+es[i])%q not in (1,q-1) for i in range(len(ps)))
        else:
            r=next(r for r in range(q) if all((3*r+g)%q not in (1,q-1) for g in es[:-1]) and (r+es[-1]//3+1)%q)
        T+=M*((r-T)*pow(M,-1,q)%q);M*=q
    assert gcd(T+es[-1]//3+1,M)==1
    for j in range(1,10000):
        t=T+j*M;P=t+es[-1]//3+1
        if P>max(ps) and isprime(P):break
    else:raise RuntimeError('search cap')
    u,v=3*t,2*t; out=[]
    for p in (*ps,5,int(P)):
        w=2*(p-1)//3 if p in ps else 1
        for n in range(v+1,v+w+1):
            g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
            if n<v+w:assert g==1
            elif p==P:assert g==P
            else:assert g%p==0 and all(g%q for q in primerange(3,p))
        out.append((u,v,p,w));u+=p-1;v+=w
    assert (u,v)==(4*P,2*P)
    print('CRT',ps,'P',P,'modulus',M,'j',j,'path',out,flush=True)


def scan(cap):
    a=spf_table(cap+10);slots={};c=Counter();ex={};largest=(0,0);firstcross=Counter();crossstates=defaultdict(set);rank_preserve=Counter();rank_jumps=Counter()
    slopes=((2,3),(3,5),(4,7),(5,9),(6,11),(7,13),(8,15),(9,17),(10,19))
    for u in range(12,cap+1,2):
        ts=slots.pop(u,{})
        if u%12==0:ts.setdefault(u//2+3,0)
        for v,prev in ts.items():
            c['states']+=1
            g=gcd(u,v);k=u//g;b=v//g
            if k%2 and 3<=k<=19 and k<2*b<2*k and v%2==0:
                c['rank_states']+=1;c[(k,b)]+=1;ex.setdefault((k,b),(u,v,prev));largest=max(largest,(u,v))
                if prev:
                    assert g%prev==0
                    B=g//prev
                    assert B%2==0
                    # Exact prior line: x=(k B-1)prev+1, n=b B prev.
                    x=u-prev+1;assert x==(k*B-1)*prev+1
                    assert v==b*B*prev
                    rank_jumps['nonseed']+=1
            w,p,e=step(u,v,a);U=u+p-1;V=v+w
            if U<=cap:slots.setdefault(U,{})[V]=p
            if U>cap:continue
            for A,K in slopes:
                Z=A*u-K*v;ZZ=A*U-K*V;C=2*(A+K)
                if Z==0 and ZZ==0:
                    assert K*w==A*(p-1) and (p-1)%K==0
                    if V%2:assert C%p==0
                    rank_preserve[A,K]+=1
                if Z>0 and ZZ<=0:
                    firstcross[A,K]+=1;crossstates[A,K].add((U,V))
                    # General crossing arithmetic, no presumption this is
                    # a first crossing along the whole ancestry.
                    assert K*w>A*(p-1)
                    C0=0 if V%2==0 else C
                    assert (ZZ+C0)%p==0
                    assert -2*K <= (ZZ+C0)//p <= 2*(A+K)//p
                    if a[u-1] or a[u+1]:
                        assert all(2*K*q>A*(p-1) for q in factors(u-1,a)+factors(u+1,a))
                        assert (p-1)**2<16*(u+1)
                        c['nontwin_crossings']+=1
    print('cap',cap,'counts',dict(c),'rank examples',ex,'largest rank',largest)
    print('cross edges',dict(firstcross),'distinct destinations',{k:len(v) for k,v in crossstates.items()},'rank-preserving',dict(rank_preserve),'rank arrivals',dict(rank_jumps))


if __name__=='__main__':
    construct((7,));construct((31,37));scan(int(argv[1]) if len(argv)>1 else 1000000)
