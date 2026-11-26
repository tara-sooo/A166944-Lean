"""Sparse lower interruptions in actual high-label windows. Stdlib only.
Diagnostic h=4,z=3,A=T/4,U=8T, prefix cap 2+floor(n/4).
"""
from collections import Counter, defaultdict
from functools import lru_cache
from math import gcd, isqrt, prod
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
    a=sieve(2*R+1);h=4;z=3;Q=6;smax=2
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=min((((c-v-1)%(2*p)+1,p) for pp,c0 in ((fs,0),(gs,2)) for p in pp for c in (0 if c0==0 else p+2,)))
        U,V=u+p-1,v+w;e=1 if V%2==0 else -1
        assert (u-e)%p==0 and w<=2*min(fs[0],gs[0])
        if R<=10000:
            for n in range(v+1,V+1):
                g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                assert (g>1)==(n==V)
            assert factors(g,a)[0]==p
        return u,p,w,e,U,V
    total=Counter();b=Counter();tuples=defaultdict(set);samples={}
    for X in range(6*((R+5)//6),3*R//2+1,6):
        u,v=X,X//2+3;path=[];total['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];total['visits']+=1;total['wait']+=s[2]
        seq=[s for s in path if s[1]>z]
        for i,s in enumerate(seq):
            x,p,w,e,_,_=s;T=1<<(p.bit_length()-1);A=T//4;U=8*T;W0=max(7,T//8)
            if A<=Q+3:continue
            b['anchors']+=1;b['anchor_wait']+=w
            if w<W0:b['own_short']+=w;continue
            high=0;low=0;end=i
            for j in range(i,len(seq)):
                high+=seq[j][1]>=A;low+=seq[j][1]<A
                if high==h:end=j;break
            if high<h:b['missing']+=w;continue
            word=seq[i:end+1]
            if any(t[1]>U for t in word):b['upper']+=w;continue
            if low<=smax:b['fixed_full_windows']+=1;b['fixed_full_wait']+=w
            high_set=set();stop=len(word)-1
            for j,t in enumerate(word):
                if t[1]<A:continue
                if t[1] in high_set:stop=j;break
                high_set.add(t[1])
            word=word[:stop+1];n0=len(high_set);low=sum(t[1]<A for t in word)
            if low>smax+n0//4:b['many_lower']+=w;continue
            b['good']+=w;b['windows']+=1;b['lower_count_'+str(low)]+=1;b['wait_lower_count_'+str(low)]+=w
            if low>2:b['extra_prefix_windows']+=1
            E=[t[0]-s0[4] for s0,t in zip(word,word[1:])]
            assert all(0<=g<=Q and g%2==0 for g in E)
            low_labels=[t[1] for t in word if t[1]<A]
            b['repeated_lower_windows']+=len(set(low_labels))<len(low_labels)
            # Stop at first repeated HIGH label, not first repeated arbitrary label.
            seen={};high_seen={};root=0;P=2;prefix=[];repeat=False
            for k,t in enumerate(word):
                xx,pp,ww,ee,_,_=t;r=(ee-(xx-x))%pp;prefix.append(t)
                if pp in seen:assert root%pp==r
                else:seen[pp]=k;root+=P*((r-root)*pow(P,-1,pp)%pp);P*=pp
                if pp<A:continue
                if pp not in high_seen:high_seen[pp]=k;continue
                j=high_seen[pp];n=len(high_seen);repeat=True
                assert n>=2 # diagnostic parameters give smax*A+(smax+1)*Q<T
                interior=[t0[1] for t0 in word[j+1:k]]
                hc=[q for q in interior if q>=A]
                q=hc[0] if hc else max(interior);bb=interior.count(q)
                c=k-j+ee-word[j][3]-sum(E[j:k])-sum(r0 for r0 in interior if r0!=q)
                aa,rem=divmod(bb*q-c,pp)
                assert rem==0 and c!=0 and aa>=1 and aa<=len(word)*(U//A+2)
                assert bb*q==aa*pp+c and pp!=q
                if not hc:
                    assert q*len(interior)>=pp-(k-j)*Q-2
                    if A>=2*(smax+1)*Q+4:assert 2*smax*q>=A
                ss=1<<(pp.bit_length()-1);tt=1<<(q.bit_length()-1)
                lo=max(ss,(bb*tt-c+aa-1)//aa);hi=min(2*ss-1,(bb*(2*tt-1)-c)//aa)
                assert lo<=pp<=hi and hi-lo+1<=ss and aa*(hi-lo)<=bb*(tt-1)
                kind=('high_pair' if hc else 'lower_pair')+('_anchor' if j==0 else '_later')
                b[kind]+=1;b['repeat_windows']+=1
                b['multiple_pair_coefficient']+=bb>1
                samples.setdefault(kind,(X,tuple(t0[1] for t0 in prefix),tuple(E[:k]),pp,q,aa,bb,c))
                break
            if not repeat:b['distinct_high_windows']+=1
            assert P==2*prod(seen) and x%P==root
            key=(T,tuple(t[1] for t in prefix),tuple(t[3] for t in prefix),tuple(E[:len(prefix)-1]),P,root)
            tuples[key].add(x)
    for key,xs in tuples.items():
        P,root=key[-2:];assert len(xs)<=(R-1)//P+1 and all(x%P==root for x in xs)
    assert b['anchor_wait']==sum(b[k] for k in ('own_short','missing','upper','many_lower','good'))
    assert b['windows']==b['repeat_windows']+b['distinct_high_windows']
    assert b['windows']==sum(b['lower_count_'+str(i)] for i in range(smax+h//4+1))
    print('R',R,'states',step.cache_info().currsize,'tuples',len(tuples),dict(total),flush=True)
    print('diagnostic',dict(b),flush=True)
    print('samples',samples,flush=True)

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
