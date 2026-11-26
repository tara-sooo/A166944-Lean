"""First-repeat prefix CRT and harmonic coefficient audit. Standard library.
Diagnostic z=3, h=4, A=T/4, U=8T, anchor wait>=max(7,T//8).
Interior waits are unrestricted. Not the asymptotic parameter regime.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from math import prod
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R, h=4, z=3):
    assert z == 3
    Q=6; a=spf(2*R+1)
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs])
        V=v+w; U=u+p-1; e=1 if V%2==0 else -1
        assert (u-e)%p==0 and w<=2*min(fs[0],gs[0])
        return (u,p,w,e,U,V)
    totals=Counter(); by=defaultdict(Counter); words=defaultdict(set)
    for X in range(6*((R+5)//6),3*R//2+1,6):
        u,v=X,X//2+3; path=[];totals['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];totals['visits']+=1;totals['wait']+=s[2]
        high=[s for s in path if s[1]>z]
        for i,s in enumerate(high):
            x,p,w,e,_,_=s;T=1<<(p.bit_length()-1); A=T//4;U=8*T;W0=max(7,T//8)
            if A<=Q+3:continue
            b=by[T]; b['anchors']+=1;b['anchor_wait']+=w
            if w<W0:b['own_short_wait']+=w;continue
            if i+h>len(high):b['missing_wait']+=w;continue
            word=high[i:i+h]
            if any(t[1]>U for t in word):b['upper_wait']+=w;continue
            if any(t[1]<A for t in word):b['lower_wait']+=w;continue
            b['good_wait']+=w;b['good_windows']+=1
            if any(t[2]<W0 for t in word[1:]):
                b['short_interior_windows']+=1;b['short_interior_wait']+=w
            E=[t[0]-s0[4] for s0,t in zip(word,word[1:])]
            assert all(0<=g<=Q and g%2==0 for g in E)
            for t in word[1:]:
                assert t[0]>x
            seen={};root=0;P=2;prefix=[];repeat=None
            for k,t in enumerate(word):
                xx,pp,ww,ee,_,_=t;r=(ee-(xx-x))%pp
                prefix.append(t)
                if pp in seen:
                    j=seen[pp];assert k-j>=2 and root%pp==r
                    q=word[k-1][1]; c=k-j+ee-word[j][3]-sum(E[j:k])-sum(t0[1] for t0 in word[j+1:k-1])
                    aa,rem=divmod(q-c,pp)
                    assert rem==0 and c!=0 and 1<=aa<= (k-j)*(U//A+2)
                    # Verify dyadic interval length bound for the pair p,q.
                    lo=1<<(pp.bit_length()-1);hi=1<<(q.bit_length()-1)
                    lower=max(lo,(hi-c+aa-1)//aa)
                    upper=min(2*lo-1,(2*hi-1-c)//aa)
                    assert lower<=pp<=upper
                    assert upper-lower+1<=lo and aa*(upper-lower)<=hi-1
                    b['repeat_windows']+=1;b['first_repeat_depth_'+str(k)]+=1
                    if j>0:b['noninitial_return']+=1
                    repeat=k;break
                seen[pp]=k;root+=P*((r-root)*pow(P,-1,pp)%pp);P*=pp
            if repeat is None:b['distinct_windows']+=1
            assert P==2*prod(seen) and x%P==root
            key=(T,tuple(t[1] for t in prefix),tuple(t[3] for t in prefix),tuple(E[:len(prefix)-1]),P,root)
            words[key].add(x)
    for key,xs in words.items():
        P,root=key[-2:];assert len(xs)<=(R-1)//P+1 and all(x%P==root for x in xs)
    b=sum(by.values(),Counter())
    assert b['anchor_wait']==sum(b[k] for k in ('own_short_wait','missing_wait','upper_wait','lower_wait','good_wait'))
    assert b['good_windows']==b['distinct_windows']+b['repeat_windows']
    print('R',R,'states',step.cache_info().currsize,'tuples',len(words),dict(totals),flush=True)
    print('diagnostic',dict(b),flush=True)

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
