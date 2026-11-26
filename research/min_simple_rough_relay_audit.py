"""Rough endpoint relay compression. Fixed finite diagnostics, not asymptotic parameters."""
from collections import Counter, defaultdict
from functools import lru_cache
from math import gcd, prod
from min_simple_relay_budget_audit import sieve, factors
import sys


def audit(R):
    a=sieve(2*R+1);h=4;small=(3,5,7);Q=2*prod(small);B=32
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=min(((c-v-1)%(2*p)+1,p) for pp,k in ((fs,0),(gs,1)) for p in pp for c in (0 if k==0 else p+2,))
        U,V=u+p-1,v+w;e=1 if V%2==0 else -1
        assert (u-e)%p==0 and w<=2*min(fs[0],gs[0])
        if R<=10000:
            for t in range(v+1,V+1):
                g=gcd(t if t%2==0 else t-2,u-1 if t%2==0 else u+1)
                assert (g>1)==(t==V)
            assert factors(g,a)[0]==p
        return u,p,w,e,U,V
    allowed={r:tuple(E for E in range(B) if all((r+E-1)%q and (r+E+1)%q for q in small)) for r in range(Q)}
    assert sum(map(len,allowed.values()))==B*Q*prod(q-2 for q in small)//prod(small)
    total=Counter();b=Counter();tuples=defaultdict(set)
    for X in range(6*((R+5)//6),3*R//2+1,6):
        u,v=X,X//2+3;path=[];total['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];total['visits']+=1;total['wait']+=s[2]
        for i,s in enumerate(path):
            x,p,w,e,_,_=s;T=1<<(p.bit_length()-1);A=T//4;U=8*T;W0=max(15,T//8)
            if A<=10:continue
            b['anchors']+=1;b['anchor_wait']+=w
            if w<W0:continue
            prefix=[];seen={};repeat=None
            for t in path[i:]:
                if t[1]<A:continue
                if t[1]>U:break
                prefix.append(t)
                if t[1] in seen:repeat=(seen[t[1]],len(prefix)-1);break
                seen[t[1]]=len(prefix)-1
                if len(seen)==h:break
            if repeat is None and len(seen)<h:continue
            n=len(seen);E=[t[0]-s0[4] for s0,t in zip(prefix,prefix[1:])]
            assert all(g>=0 and g%2==0 for g in E)
            if sum(E)>n*B or sum(E)+3>=A:continue
            b['budget_windows']+=1;b['budget_wait']+=w
            if any(t[2]<W0 for t in prefix[1:]):b['short_interior']+=1;continue
            b['rough_windows']+=1;b['rough_wait']+=w;b['rough_repeat']+=repeat is not None
            b['over_individual_budget']+=max(E,default=0)>B
            root=x%Q;P=Q;rho=root
            for j,t in enumerate(prefix):
                xx,pp,ww,ee,UU,VV=t;r=(ee-(xx-x))%pp
                if P%pp==0:assert root%pp==r
                else:root+=P*((r-root)*pow(P,-1,pp)%pp);P*=pp
                assert all((xx-1)%q and (xx+1)%q for q in small)
                if j<len(E):
                    g=E[j];k,d=divmod(g,B);base=(UU+k*B)%Q
                    assert d in allowed[base]
                    b['checked_relays']+=1;b['nonzero_relays']+=g>0
            assert P==Q*prod(seen) and x%P==root
            if repeat is not None:
                j,k=repeat;pp=prefix[j][1];qq=prefix[k-1][1]
                assert k-j>=2
                c=k-j+prefix[k][3]-prefix[j][3]-sum(E[j:k])-sum(t[1] for t in prefix[j+1:k-1])
                aa,rem=divmod(qq-c,pp);assert rem==0 and aa>=1 and c!=0
                offset=rho
                for t,g in zip(prefix[:-2],E[:-1]):
                    offset=(offset+t[1]-1)%Q
                    kk,dd=divmod(g,B);assert dd in allowed[(offset+kk*B)%Q]
                    offset=(offset+g)%Q
                assert offset==prefix[-2][0]%Q
                shifts=[t[0]-x+sgn for t in prefix[:3] for sgn in (-1,1)]
                assert len(set(shifts))==6
                Delta=prod(abs(s1-s0) for j,s0 in enumerate(shifts) for s1 in shifts[j+1:])
                for ell in (11,13,17,19,23):
                    if P*Delta%ell:assert len({(-(root+t)*pow(P,-1,ell))%ell for t in shifts})==6
            tuples[(P,root,tuple(t[1] for t in prefix),tuple(E))].add(x)
    for (P,root,_,_),xs in tuples.items():
        assert len(xs)<=(R-1)//P+1 and all(x%P==root for x in xs)
    print('R',R,'states',step.cache_info().currsize,'tuples',len(tuples),dict(total),flush=True)
    print('diagnostic',dict(b),'residue interval min/max',min(map(len,allowed.values())),max(map(len,allowed.values())),flush=True)


if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
