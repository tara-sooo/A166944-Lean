"""Stdlib-only audit: python min_simple_crossing_audit.py [max seed X]."""
from array import array
from math import gcd, isqrt
from collections import defaultdict
import sys

def spf(n):
    a=array('I',[0])*(n+1)
    for p in range(3,isqrt(n)+1,2):
        if not a[p]:
            for x in range(p*p,n+1,2*p):
                if not a[x]: a[x]=p
    return a

def factors(n,a):
    out=[]
    while n>1:
        p=a[n] or n
        out.append(p)
        while n%p==0:n//=p
    return out

def clock(u,v,ps):
    return min(((s-v)%(2*p) or 2*p,p) for p,s in ps)

def cert():
    Q=210
    F=[[0]*Q for _ in range(Q//2+1)]
    for u in range(Q-2,-1,-2):
        ps=[(p,s) for p in (3,5,7) for e,s in ((1,0),(-1,p+2)) if (u-e)%p==0]
        if ps:
            for v in range(Q):
                w,p=clock(u,v,ps)
                assert u+p-1<=Q
                F[u//2][v]=max(0,8*w-19*(p-1)+F[(u+p-1)//2][(v+w)%Q])
    # independent literal restricted tick scan, rather than modular wait formula
    for u in range(0,Q+1,2):
        for v in range(Q):
            candidates=[]
            for w in range(1,15):
                n=v+w
                g=gcd(n if n%2==0 else n-2, u-1 if n%2==0 else u+1)
                candidates=[p for p in (3,5,7) if g%p==0]
                if candidates:break
            expected=0
            if candidates:
                p=min(candidates)
                expected=max(0,8*w-19*(p-1)+F[(u+p-1)//2][(v+w)%Q])
            assert F[u//2][v]==expected
    B=max(map(max,F));I=max(F[(12*k%Q)//2][(6*k+3)%Q] for k in range(Q//6))
    print('certificate states',len(F)*Q,'B',B,'I',I)
    assert (B,I)==(14,6)

def run(limit):
    a=spf(2*limit+1); stats=defaultdict(list); edges=0; no_twin=0; bad_short=0; first_gap_max=(0,0)
    for X in range(6,limit+1,6):
        u=X;v=X//2+3;n=0;hit=False;first=None
        while u<2*X:
            fs,gs=factors(u-1,a),factors(u+1,a)
            twin=fs==[u-1] and gs==[u+1]
            if twin and first is None:first=n
            hit|=twin
            w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs])
            if not twin:
                assert w<=2*isqrt(u+1)
                # exact strict squared potential inequality
                B=2*v+1;A=B+2*w
                assert A<=B+4 or (A-B-4)**2<16*B
            u+=p-1;v+=w;n+=1;edges+=1
            d=2*v-u;G=u-X
            assert 0<=d and v<=u+1
            assert d<=8+4*G
            if X%12==0:assert 4*(d-6)-15*G<=6
        if not hit:
            no_twin+=1
            # sqrt(2X+1) < sqrt(X+7)+2N
            A=2*X+1;B=X+7;c=2*n
            assert A<=B+c*c or (A-B-c*c)**2<4*c*c*B
            if 25*n*n<=X and X>=10000:bad_short+=1
        else:
            if first>first_gap_max[0]:first_gap_max=(first,X)
        stats[1<<(X.bit_length()-1)].append((X,n,hit,first))
    print('seeds',limit//6,'events',edges,'no twin before crossing',no_twin,'bad short',bad_short,'max first-twin index',first_gap_max)
    for b,rows in sorted(stats.items()):
        print('slab',b,'seeds',len(rows),'mean N',round(sum(x[1] for x in rows)/len(rows),4),'max N',max(x[1] for x in rows),'no twin',sum(not x[2] for x in rows),'short',sum(25*x[1]**2<=x[0] for x in rows),'min N excluding initial twin',min((x[1] for x in rows if x[3]!=0),default=None))
    assert bad_short==0

if __name__=='__main__':
    cert();run(int(sys.argv[1]) if len(sys.argv)>1 else 100000)
