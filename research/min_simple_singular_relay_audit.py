"""Exact low-prime relay compression after singular arrivals, stdlib only."""
from collections import Counter, defaultdict
from functools import lru_cache
from math import prod, gcd
import sys
from min_simple_crossing_audit import spf, factors, clock


def make_relay(primes):
    Q=2*prod(primes); L=2*Q
    @lru_cache(None)
    def relay(a,d):
        assert a%2==0 and 0<=a<L and d in (0,6)
        u=a; v=(a+d)//2; events=0
        while True:
            ps=[(p,c) for p in primes for e,c in ((1,0),(-1,p+2)) if (u-e)%p==0]
            if not ps: break
            w,p=clock(u,v,ps);u+=p-1;v+=w;events+=1
            assert 0<=u-a<=Q and events<=Q//2
        return u-a,v-(a+d)//2,events
    return Q,L,relay


def controls():
    for primes in ((3,), (3,5), (3,5,7), (3,5,7,11)):
        Q,L,relay=make_relay(primes);count=0;maximum=0;positive=0
        for a in range(0,L,4):
            for d in (0,6):
                E,W,k=relay(a,d);maximum=max(maximum,E);positive+=E>0
                u0=a+17*L;v0=(u0+d)//2;u,v=u0,v0;j=0
                while any((u-1)%p==0 or (u+1)%p==0 for p in primes):
                    n=v+1
                    while True:
                        raw=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                        pp=[p for p in primes if raw%p==0]
                        if pp:break
                        n+=1
                    u+=min(pp)-1;v=n;j+=1
                assert (u-u0,v-v0,j)==(E,W,k)
                count+=1
        print('literal relay',primes,'Q',Q,'states',count,'positive',positive,'maxgain',maximum,flush=True)


def lifted_control():
    # Exact nonzero-relay return 29,3,31,29 from a reset seed.
    # A factorial multiple preserves all prime divisors of the small defects.
    shift=12*prod(range(1,102)); X=13020+shift; u=X;v=X//2+3
    path=[]
    for expected_p,expected_w in ((29,14),(3,1),(31,15),(29,11)):
        n=v
        while True:
            n+=1;even=n%2==0
            raw=gcd(n if even else n-2,u-1 if even else u+1)
            defect=2*n-u+(1 if even else -5)
            assert 0<abs(defect)<=101 and abs(defect)%raw==0
            if raw>1:break
        p=next(p for p in range(3,raw+1,2) if raw%p==0)
        assert (p,n-v)==(expected_p,expected_w)
        U=u+p-1;d=2*n-U;path.append((u,p,U,n,d));u,v=U,n
    Q,L,relay=make_relay((3,))
    assert relay(path[0][2]%L,6)==(2,1,1)
    assert relay(path[2][2]%L,6)==(0,0,0)
    assert (L*29*31)**2<X
    assert path[-1][-1]==0
    print('literal lifted reset return; seed digits',len(str(X)),
          'labels',[s[1] for s in path],'relays',[2,0],
          'actual distinct-prime modulus',L*29*31,'sieve room verified',flush=True)


def audit(R):
    a=spf(2*R+1); seeds=range(6*((R+5)//6),3*R//2+1,6)
    configs=[(primes,*make_relay(primes),Counter(),defaultdict(set)) for primes in ((3,), (3,5), (3,5,7))]
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs]);U,V=u+p-1,v+w
        d=2*V-U;e=1 if V%2==0 else -1
        singular=(e==1 and d==0) or (e==-1 and d==6)
        return (u,v,p,w,U,V,d,e,singular)
    total=Counter()
    for X in seeds:
        u,v=X,X//2+3;path=[];total['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];total['visits']+=1;total['wait']+=s[3]
        for primes,Q,L,relay,c,tuples in configs:
            z=primes[-1];marks=[i for i,s in enumerate(path) if s[2]>z]
            c['high_visits']+=len(marks)
            for j,k in zip(marks,marks[1:]):
                s,t=path[j],path[k];u,v,p,w,U,V,d,e,sing=s
                if not sing or t[3]<=2*z:continue
                E,W,n=relay(U%L,d)
                assert (E,W,n)==(t[0]-U,t[1]-V,k-j-1)
                c['compressed_pairs']+=1;c['positive_relays']+=E>0;c['max_relay']=max(c['max_relay'],E)
                T=1<<(p.bit_length()-1)
                if T<=t[2]<2*T and t[8] and w>2*z:
                    c['sameband_pairs']+=1;c['sameband_positive_relays']+=E>0
            for h in (2,3,4):
                for j in range(len(marks)-h+1):
                    word=[path[i] for i in marks[j:j+h]]
                    p0=word[0][2];T=1<<(p0.bit_length()-1)
                    if not all(T<=s[2]<2*T and s[8] and s[3]>2*z for s in word):continue
                    x0=word[0][0];rho=x0%L;x=rho;labels=[];ds=[];es=[];E=[];P=L;root=rho
                    for i,s in enumerate(word):
                        p=s[2];d=s[6];e=s[7];g=s[0]-x0
                        assert x==s[0]%L
                        r=(e-g)%p
                        if p not in labels:
                            root+=P*((r-root)*pow(P,-1,p)%p);P*=p
                        else:assert root%p==r
                        labels.append(p);ds.append(d);es.append(e)
                        if i<h-1:
                            rr=relay((x+p-1)%L,d)[0];E.append(rr);x=(x+p-1+rr)%L
                            assert rr==word[i+1][0]-s[4]
                    assert x0%P==root and P==L*prod(set(labels))
                    c[f'h{h}_windows']+=1;c[f'h{h}_wait']+=word[0][3]
                    c[f'h{h}_positive']+=any(E);c[f'h{h}_distinct']+=len(set(labels))==h
                    c[f'h{h}_room']+=P*P<=R
                    tuples[(rho,tuple(labels),tuple(ds),P,root)].add(x0)
                    if len(set(labels))<h:
                        dist,start=min((k-i,i) for i in range(h) for k in range(i+1,h) if labels[i]==labels[k])
                        pp=labels[start:start+dist+1];ee=es[start:start+dist+1];rr=E[start:start+dist]
                        c0=dist+ee[-1]-ee[0]-sum(rr)-sum(pp[1:-2])
                        val=pp[-2]-c0
                        assert val%pp[0]==0
                        if Q<T and T>5:
                            assert 1<=val//pp[0]<=4*dist and c0!=0
                        c[f'h{h}_repeat']+=1
    print('R',R,dict(total),'states',step.cache_info().currsize,flush=True)
    for primes,Q,L,relay,c,tuples in configs:
        for (rho,labels,ds,P,root),xs in tuples.items():
            assert len(xs)<=(R-1)//P+1 and all(x%P==root for x in xs)
        print('z',primes[-1],'Q',Q,'tuples',len(tuples),dict(c),flush=True)

if __name__=='__main__':
    controls();lifted_control()
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
