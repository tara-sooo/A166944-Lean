"""First high-repeat prefixes under total relay-gain budgets (stdlib).
Diagnostic h=4,A=T/4,U=8T; use B=8,16,32,64,128.
Not the asymptotic parameters of the theorem.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from math import gcd, isqrt, prod, comb
import sys


def sieve(n):
    a=list(range(n+1))
    for p in range(2,isqrt(n)+1):
        if a[p]==p:
            for j in range(p*p,n+1,p):
                if a[j]==j:a[j]=p
    return a


def factors(n,a):
    out=[]
    while n>1:
        p=a[n];out.append(p)
        while n%p==0:n//=p
    return out


def audit(R):
    a=sieve(2*R+1); h=4; budgets=(8,16,32,64,128)
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=min(((c-v-1)%(2*p)+1,p) for pp,k in ((fs,0),(gs,1)) for p in pp for c in (0 if k==0 else p+2,))
        U,V=u+p-1,v+w;e=1 if V%2==0 else -1
        q=min(fs[0],gs[0]);assert (u-e)%p==0 and w<=2*q
        if R<=10000:
            for n in range(v+1,V+1):
                g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                assert (g>1)==(n==V)
            assert factors(g,a)[0]==p
        return u,p,w,e,U,V,q
    total=Counter(); b=Counter(); hist=defaultdict(Counter); tuples=defaultdict(set); samples={}
    for X in range(6*((R+5)//6),3*R//2+1,6):
        u,v=X,X//2+3;path=[];total['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];total['visits']+=1;total['wait']+=s[2]
        for i,s in enumerate(path):
            x,p,w,e,_,_,_=s;T=1<<(p.bit_length()-1);A=T//4;U=8*T;W0=max(7,T//8)
            if A<=9:continue
            b['anchors']+=1;b['anchor_wait']+=w
            if w<W0:b['own_short']+=w;continue
            high=[]; positions=[]
            for j in range(i,len(path)):
                if path[j][1]>=A:
                    high.append(path[j]);positions.append(j)
                    if len(high)==h:break
            if len(high)<h:b['missing']+=w;continue
            if any(t[1]>U for t in high):b['upper']+=w;continue
            b['full']+=1;b['full_wait']+=w
            seen={};repeat=None;prefix=[]
            for j,t in enumerate(high):
                prefix.append(t)
                if t[1] in seen:repeat=(seen[t[1]],j);break
                seen[t[1]]=j
            n=len(seen);E=[];count_low=0;small_support=set()
            for j in range(len(prefix)-1):
                i0,i1=positions[j:j+2];lo=path[i0+1:i1]
                assert all(t[1]<A for t in lo)
                E.append(sum(t[1]-1 for t in lo));count_low+=len(lo);small_support.update(t[1] for t in lo)
                assert E[-1]==prefix[j+1][0]-prefix[j][4]
            G=sum(E);root=0;P=2
            for t in prefix:
                pp=t[1];r=(t[3]-(t[0]-x))%pp
                if P%pp==0:assert root%pp==r
                else:root+=P*((r-root)*pow(P,-1,pp)%pp);P*=pp
            assert P==2*prod(seen) and x%P==root
            key=(T,tuple(t[1] for t in prefix),tuple(t[3] for t in prefix),tuple(E),P,root)
            tuples[key].add(x)
            if repeat is not None:
                j,k=repeat; pp=prefix[j][1]
                c=k-j+prefix[k][3]-prefix[j][3]-sum(E[j:k])-sum(t[1] for t in prefix[j+1:k-1])
                if k-j>=2:
                    qq=prefix[k-1][1];aa,rem=divmod(qq-c,pp)
                    assert rem==0 and aa>=1 and c!=0 and qq!=pp
                else:
                    assert E[j]>=pp-3
            for B in budgets:
                z=hist[B]
                # The theorem has h*B+3<A. At finite scales use the
                # weaker observed gain condition, common to every budget.
                if G>n*B or G+3>=A:continue
                assert n>=2 and (repeat is None or repeat[1]-repeat[0]>=2)
                assert len(E)<=n and sum(E)<=n*B
                # Stars and bars: all possible E vectors fit in this count.
                assert comb(n*B+len(E),len(E))<=comb(n*B+n,n)
                z['windows']+=1;z['wait']+=w;z['repeat']+=repeat is not None
                z['low_repetition']+=count_low>len(small_support)
                z['many_lower']+=count_low>2+n//4
                z['individual_relay_over_B']+=max(E,default=0)>B
                z['two_rough']+=prefix[1][2]>=W0
                if prefix[1][2]>=W0:
                    z['two_rough_wait']+=w
                    d=prefix[1][0]-x; shifts=(-1,1,d-1,d+1)
                    assert len(set(shifts))==4
                    Delta=prod(abs(t-s0) for k,s0 in enumerate(shifts) for t in shifts[k+1:])
                    for ell in (5,7,11,13,17,19,23):
                        if (P*Delta)%ell:
                            assert len({(-(root+t)*pow(P,-1,ell))%ell for t in shifts})==4
                        if 2*ell<W0:assert all((x+t)%ell for t in shifts)
                if count_low>2+n//4 and B not in samples:
                    samples[B]=(X,tuple(t[1] for t in prefix),tuple(E),count_low,len(small_support),w)
    for key,xs in tuples.items():
        P,root=key[-2:];assert len(xs)<=(R-1)//P+1 and all(x%P==root for x in xs)
    assert b['anchor_wait']==sum(b[k] for k in ('own_short','missing','upper','full_wait'))
    print('R',R,'states',step.cache_info().currsize,'tuples',len(tuples),dict(total),flush=True)
    print('anchors',dict(b),flush=True)
    for B in budgets:print('B',B,dict(hist[B]),'sample',samples.get(B),flush=True)

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
