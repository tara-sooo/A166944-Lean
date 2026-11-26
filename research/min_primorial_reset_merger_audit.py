"""Direct reset mergers and pre-record basin multiplicities.
Run: python min_primorial_reset_merger_audit.py 1000000 100000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
"""
from collections import Counter
from math import gcd
from sys import argv
from sympy import primerange, isprime
from min_primorial_record_supply_audit import spf_table, step, factors


def direct_scan(R):
    a=spf_table(2*R+10); counts=Counter(); maxima=[]; maxd=0; sumd=0; sumd2=0; tail=Counter(); candidates=0
    for r in range(7,R+1,6):
        labels=[]
        for p in factors(r,a):
            if p==r or p%12!=1:continue
            x=2*r-p-1;t=x//2+3;w=(p-1)//2
            assert x%12==0 and p<=x//2+1
            candidates+=1
            if step(x,t,a)==(w,p,-1):
                assert (x+p-1,t+w)==(2*r-2,r+2)
                assert p-1<=4*(2*r//p-1)
                labels.append(p)
        n=len(labels);counts[n]+=1;sumd+=n;sumd2+=n*n
        if n>maxd:maxd=n;maxima=[(r,labels)]
        elif n==maxd and len(maxima)<5:maxima.append((r,labels))
        for T in (13,31,61,127,257,1021):
            if labels and max(labels)>=T:tail[T]+=1
    print('direct cap',R,'counts',dict(sorted(counts.items())),'candidates',candidates,'edges',sumd,'second moment sum',sumd2,'max',maxima,'tail',dict(tail),flush=True)


def construct(ps):
    assert all(isprime(p) and p%12==1 for p in ps)
    r,M=1,6;B=max(ps)+6
    for q in map(int,primerange(5,B+1)):
        if q in ps:
            a=0;assert all((p+2)%q and p%q for p in ps if p!=q)
        else:
            a=next(a for a in range(q) if all((2*a-p-1)%q not in (1,q-1) for p in ps))
        r+=M*((a-r)*pow(M,-1,q)%q);M*=q
    r+=M
    for p in ps:
        x=2*r-p-1;t=x//2+3;w=(p-1)//2
        assert x%12==0 and p<=x//2+1
        for n in range(t+1,t+w+1):
            g=gcd(n if n%2==0 else n-2,x-1 if n%2==0 else x+1)
            assert g==(p if n==t+w else 1)
        assert (x+p-1,t+w)==(2*r-2,r+2)
    print('CRT labels',ps,'target r',r,'modulus',M,'ticks',sum((p-1)//2 for p in ps),flush=True)


def basin_scan(R):
    a=spf_table(4*R+10000); B=Counter(); terminal=Counter(); crossings=Counter(); total=0;false=0
    ks=(3,5,9,19,39,99)
    for r in range(7,R+1,6):
        u,v=2*r-2,r+2; found=set();m=0
        while True:
            B[u,v]+=1;total+=1
            w,p,e=step(u,v,a);m+=1
            assert m<100000
            if p>r:
                terminal[u,v]+=1
                false+=not (p==u+1 and isprime(u-1) and isprime(u+1))
                break
            U,V=u+p-1,v+w
            for k in ks:
                if k not in found and (k+1)*u>2*k*v and (k+1)*U<=2*k*V:
                    crossings[k,U,V]+=1;found.add(k)
            u,v=U,V
    print('basin cap',R,'states',len(B),'visits',total,'max',B.most_common(3),'terminals',len(terminal),'terminal max',terminal.most_common(3),'false records',false,'unordered state-origin collision incidences',sum(n*(n-1)//2 for n in B.values()),flush=True)
    for k in ks:
        values=[n for (a,u,v),n in crossings.items() if a==k]
        print('slope',k,'origins',sum(values),'destinations',len(values),'max basin',max(values,default=0))


if __name__=='__main__':
    construct((13,61));construct((13,61,73,109))
    direct_scan(int(argv[1]) if len(argv)>1 else 1000000)
    basin_scan(int(argv[2]) if len(argv)>2 else 100000)
