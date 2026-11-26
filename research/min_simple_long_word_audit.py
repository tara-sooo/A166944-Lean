"""Growing-word CRT and minimal-return diagnostics (stdlib only).
Run: python min_simple_long_word_audit.py 1000 10000 100000 1000000
"""
from collections import Counter, defaultdict
from functools import lru_cache
from math import ceil, log, gcd, prod
import sys
from min_simple_crossing_audit import spf, factors, clock


def congruence(labels, signs, relays):
    E=0; x,P=0,2; first={}
    for i,(p,e) in enumerate(zip(labels,signs)):
        r=(e-E)%p
        if p in first:
            assert r==first[p]
        else:
            first[p]=r
            x+=P*((r-x)*pow(P,-1,p)%p);P*=p
        if i<len(relays):E+=p-1+relays[i]
    assert P==2*prod(first)
    return x,P


def synthetic_controls():
    labels=(11,13,17,19);signs=(1,-1,1,-1);relays=(0,2,4)
    x,P=congruence(labels,signs,relays)
    E=0; hits=[]
    for j in range(2*P):
        if j%2:continue
        E=0; ok=True
        for i,(p,e) in enumerate(zip(labels,signs)):
            if (j+E-e)%p:ok=False;break
            if i<len(relays):E+=p-1+relays[i]
        if ok:hits.append(j)
    assert hits==[x,x+P]
    print('independent enumerated CRT',labels,'modulus',P,'residue',x,'hits',hits)


def audit(R):
    a=spf(2*R+1); stats=Counter(); bands=defaultdict(Counter); tuple_sources=defaultdict(set)
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        q=min(fs[0],gs[0]);w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs]);n=v+w
        e=1 if n%2==0 else -1
        assert (u-e)%p==0 and w<=2*q
        return u,p,e,w,q,n
    for X in range(6*((R+5)//6),3*R//2+1,6):
        stats['origins']+=1; u,v=X,X//2+3; by=defaultdict(list)
        while u<2*R:
            s=step(u,v)
            if s is None:break
            x,p,e,w,q,n=s;T=1<<(p.bit_length()-1)
            stats['wait']+=w;stats['events']+=1
            if T>=8 and max(1,ceil(log(T)))*w>=T:by[T].append(s)
            u,v=x+p-1,n
        for T,ss in by.items():
            B=min(8,(T-4)//4); b=bands[T]; b['marks']+=len(ss)
            E=[y[0]-x[0]-x[1]+1 for x,y in zip(ss,ss[1:])]
            assert all(e>=0 and e%2==0 for e in E)
            G=sum(E); b['relay_gain']+=G
            for h in (3,4,8):
                windows=0; covered=0; long_relays=0; distinct=repeat=0; repetitions=set()
                # Each minimal return is recorded by its position and distance.
                for i in range(len(ss)-h+1):
                    if any(e>B for e in E[i:i+h-1]):long_relays+=1;continue
                    word=ss[i:i+h];labels=tuple(x[1] for x in word);signs=tuple(x[2] for x in word);relays=tuple(E[i:i+h-1]);windows+=1
                    x0=word[0][0];r,P=congruence(labels,signs,relays);assert (x0-r)%P==0
                    b[f'h{h}_wait']+=word[0][3]
                    if len(set(labels))==h:
                        distinct+=1;key=(T,labels,signs,relays);tuple_sources[key].add(x0)
                    else:
                        repeat+=1
                        j,l=min(((k-j,j) for j in range(h) for k in range(j+1,h) if labels[j]==labels[k]))
                        # j is return distance, l its start within this window.
                        assert 2<=j<h
                        sub=word[l:l+j+1];ps=tuple(x[1] for x in sub);es=tuple(x[2] for x in sub);rs=tuple(relays[l:l+j])
                        assert ps[-1]==ps[0] and len(set(ps[:-1]))==j
                        c=j+es[-1]-es[0]-sum(rs)
                        delta=sum(ps[1:-1])-c
                        assert delta%ps[0]==0 and abs(delta//ps[0])<=3*j
                        rr,PP=congruence(ps,es,rs);assert (sub[0][0]-rr)%PP==0
                        repetitions.add((i+l,j))
                        tuple_sources[T,ps,es,rs].add(sub[0][0])
                        b[f'h{h}_repeat_distance_{j}']+=1
                    if (2*T)**h<=R:b[f'h{h}_product_room']+=1
                    if (2*T)**h<=R**.5:b[f'h{h}_sieve_room']+=1
                assert windows==distinct+repeat and repeat<=h*len(repetitions)
                assert long_relays*(B+1)<=h*G
                # All marks not starting a short h-window are in the final h-1
                # positions of each short-relay run.
                uncovered=len(ss)-windows
                nruns=1+sum(e>B for e in E)
                assert uncovered<=max(0,h-1)*nruns
                b[f'h{h}_short_windows']+=windows;b[f'h{h}_distinct']+=distinct;b[f'h{h}_repeat']+=repeat
                b[f'h{h}_return_positions']+=len(repetitions);b[f'h{h}_long_relay_windows']+=long_relays
    for (_,labels,signs,relays),xs in tuple_sources.items():
        r,P=congruence(labels,signs,relays)
        assert len(xs)<=(R-1)//P+1
        assert all((x-r)%P==0 for x in xs)
    print('R',R,'stats',dict(stats),'states',step.cache_info().currsize,'distinct word tuples',len(tuple_sources))
    totals=sum(bands.values(),Counter())
    for h in (3,4,8):print('depth',h,{k:v for k,v in totals.items() if k.startswith(f'h{h}_')})
    print('marks',totals['marks'],'relay gain',totals['relay_gain'])
    for T,b in sorted(bands.items()):
        if b['h3_short_windows']:print('band',T,'h3',b['h3_short_windows'],'h4',b['h4_short_windows'],'h8',b['h8_short_windows'])


if __name__=='__main__':
    synthetic_controls()
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
