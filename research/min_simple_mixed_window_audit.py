"""Exact mixed-scale windows, arbitrary arrival residues, and interruption charges.
Stdlib; diagnostic widths/depths (not growing asymptotic regime).
"""
from collections import Counter, defaultdict
from functools import lru_cache
from math import prod, log, gcd
import sys
from min_simple_crossing_audit import spf, factors, clock


def make_relay(primes):
    Q=2*prod(primes); L=2*Q
    @lru_cache(None)
    def relay(a,d):
        u=a; v=(a+d)//2; count=0
        while True:
            ps=[(p,c) for p in primes for e,c in ((1,0),(-1,p+2)) if (u-e)%p==0]
            if not ps: break
            w,p=clock(u,v,ps);u+=p-1;v+=w;count+=1
            assert u-a<=Q
        return u-a,v-(a+d)//2,count
    return Q,L,relay


def controls():
    for primes in ((3,), (3,5)):
        Q,L,relay=make_relay(primes); maximum=0; count=0
        for a in range(0,L,2):
            for d in range(0,L,2):
                E,W,k=relay(a,d);maximum=max(maximum,E)
                u0=a+12*L;v0=(u0+d)//2+5*Q;u,v=u0,v0;j=0
                while any((u-1)%p==0 or (u+1)%p==0 for p in primes):
                    n=v+1
                    while True:
                        raw=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                        ps=[p for p in primes if raw%p==0]
                        if ps:break
                        n+=1
                    u+=min(ps)-1;v=n;j+=1
                assert (u-u0,v-v0,j)==(E,W,k);count+=1
        print('literal all-phase relay',primes,'residue pairs',count,'maximum gain',maximum,flush=True)


def audit(R,primes=(3,),h=4):
    a=spf(2*R+1);Q,L,relay=make_relay(primes);z=primes[-1]
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs]);U,V=u+p-1,v+w
        return (u,v,p,w,U,V,2*V-U,1 if V%2==0 else -1,min(fs[0],gs[0]))
    totals=Counter();bands=defaultdict(Counter)
    for X in range(6*((R+5)//6),3*R//2+1,6):
        u,v=X,X//2+3; path=[];gain=0;totals['origins']+=1
        while u<2*R:
            s=step(u,v)
            if s is None:break
            path.append(s);u,v=s[4:6];gain+=s[2]-1;totals['wait']+=s[3];totals['visits']+=1
        high=[s for s in path if s[2]>z];upper_charge=Counter();terminal_charge=Counter();per_band=defaultdict(Counter)
        for i,s in enumerate(high):
            x,_,p,w,*_=s;T=1<<(p.bit_length()-1); A=T//2;U=8*T
            if A<=Q+3:continue
            # Diagnostic lower/upper multiplicative widths and wait threshold.
            W=max(2*z+1,T//8); b=bands[T]; b['anchors']+=1;b['anchor_wait']+=w
            if w<W:
                b['short_anchor_wait']+=w;continue
            if i+h>len(high):
                b['terminal_wait']+=w;terminal_charge[T]+=w;continue
            word=high[i:i+h]
            # Prioritize upper interruptions even if another obstruction exists.
            big=next((j for j,t in enumerate(word) if t[2]>U),None)
            if big is not None:
                b['upper_wait']+=w;upper_charge[T,i+big]+=w;continue
            if any(t[2]<A for t in word):
                b['lower_wait']+=w;continue
            if any(t[3]<W for t in word):
                b['short_internal_wait']+=w;continue
            b['good_wait']+=w;b['good_windows']+=1
            labels=[t[2] for t in word];signs=[t[7] for t in word];rho=x%L
            root=rho;P=L;offset=rho;E=[]; seen=set()
            for j,t in enumerate(word):
                xx,_,pp,ww,UU,VV,d,e,q=t
                assert offset==xx%L and ww<=2*q and (xx-e)%pp==0
                r=(e-(xx-x))%pp
                if pp in seen:assert root%pp==r
                else:root+=P*((r-root)*pow(P,-1,pp)%pp);P*=pp;seen.add(pp)
                if j+1<h:
                    rr,tt,k=relay(UU%L,d%L); nxt=word[j+1]
                    assert (rr,tt)==(nxt[0]-UU,nxt[1]-VV)
                    E.append(rr);offset=(offset+pp-1+rr)%L
            assert P==L*prod(seen) and x%P==root
            b['positive_relays']+=any(E); b['mixed_words']+=len({pp.bit_length() for pp in labels})>1
            if len(seen)<h:
                dist,start=min((k-j,j) for j in range(h) for k in range(j+1,h) if labels[j]==labels[k]);assert dist>=2
                pp=labels[start:start+dist+1];ee=signs[start:start+dist+1];rr=E[start:start+dist]
                c=dist+ee[-1]-ee[0]-sum(rr)-sum(pp[1:-2]); aa=(pp[-2]-c)//pp[0]
                assert pp[-2]==aa*pp[0]+c and c!=0 and 1<=aa<=dist*(U//A+2)
                # All six source forms are distinct integers. Check the small-prime roots directly.
                base=word[start][0]; shifts=[word[start+j][0]-base+e for j in range(3) for e in (-1,1)]
                assert len(set(shifts))==6
                Delta=prod(abs(t-s) for i,s in enumerate(shifts) for t in shifts[i+1:])
                for ell in (3,5,7,11,13,17,19,23):
                    if Delta%ell and P%ell:
                        roots={(-(base+shift)*pow(P,-1,ell))%ell for shift in shifts}
                        assert len(roots)==6
                b['returns']+=1
            else:b['distinct_words']+=1
        # Each upper separator is charged by at most h anchors per band.
        by_separator=Counter()
        for (T,j),w in upper_charge.items():
            assert high[j][2]>8*T and w<=4*T*(h-1)
            by_separator[j]+=w
        for j,w in by_separator.items():
            # Geometric sum over dyadic T< p/8 gives <=p/4.
            assert w<=h*high[j][2]
        assert sum(by_separator.values())<=h*sum(t[2] for t in high)<=1.5*h*gain
        assert all(w<=4*T*(h-1) for T,w in terminal_charge.items())
        totals['upper_wait']+=sum(by_separator.values());totals['upper_separators']+=len(by_separator)
    print('R',R,'z',z,'h',h,'states',step.cache_info().currsize,dict(totals),flush=True)
    allb=sum(bands.values(),Counter())
    assert allb['anchor_wait']==sum(allb[k] for k in ('short_anchor_wait','terminal_wait','upper_wait','lower_wait','short_internal_wait','good_wait'))
    assert allb['upper_wait']==totals['upper_wait']
    assert allb['good_windows']==allb['distinct_words']+allb['returns']
    print('all bands',dict(allb),flush=True)
    for T,b in sorted(bands.items()):
        if b['good_windows']:print('T',T,dict(b),flush=True)


if __name__=='__main__':
    controls()
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
