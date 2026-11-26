"""Heavy/light merger audit, stdlib only. Run with integer R arguments."""
from collections import defaultdict
from math import log, log2, log1p, ceil, isqrt, sqrt, gcd
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R):
    a=spf(2*R+1); seeds=list(range(6*((R+5)//6),3*R//2+1,6)); M=len(seeds)
    nodes={};rows=defaultdict(list)
    # mass, largest incoming group, heavy parent, next, p,w,q,twin, incoming entropy
    def add(s,m,parent):
        if s not in nodes:
            nodes[s]=[0,0,None,None,0,0,0,False,0.0];rows[s[0]].append(s)
        z=nodes[s];z[0]+=m;z[8]+=m*log2(m)
        if m>z[1]:z[1],z[2]=m,parent
    for X in seeds:add((X,X//2+3),1,None)
    exits=0
    for u in range(R+R%2,2*R,2):
        if u not in rows:continue
        fs,gs=factors(u-1,a),factors(u+1,a);q=min(fs[0],gs[0]);twin=fs==[u-1] and gs==[u+1]
        ps=[(p,0) for p in fs]+[(p,p+2) for p in gs]
        for s in rows[u]:
            z=nodes[s];w,p=clock(u,s[1],ps);U,V=u+p-1,s[1]+w
            z[4:8]=[p,w,q,twin]
            if U<2*R:
                assert not twin
                z[3]=(U,V);add((U,V),z[0],s)
            else:exits+=z[0]
    assert exits==M
    light=sum(z[0]-z[1] for z in nodes.values())
    entropy=sum(z[0]*log2(z[0]) for z in nodes.values() if z[3] is None)
    local=sum(z[0]*log2(z[0])-z[8] for z in nodes.values())
    assert abs(entropy-local)<1e-5
    assert light<=entropy+1e-5 and entropy<=M*log2(M)+1e-5
    L=max(1,int(R/log(R)**2));root={};span={}
    balancedq=balancedw=youngq=youngw=totalq=totalw=0
    count_light=maxlight=maxage=0;old=defaultdict(int)
    for u in sorted(rows):
        for s in rows[u]:
            z=nodes[s];parent=z[2];root[s]=s if parent is None else root[parent];span[root[s]]=u-root[s][0]
            if not z[7] and 2*z[1]<=z[0]:balancedq+=z[0]*z[6];balancedw+=z[0]*z[5]
    assert balancedq<=2*isqrt(2*R+1)*light and balancedw<=4*isqrt(2*R+1)*light
    D=max(1,int(R/log(R)**3));K=max(1,ceil(log(R)))
    chains=defaultdict(list)
    for u in sorted(rows):
        for s in rows[u]:chains[root[s]].append(s)
    predicted={}
    for chain in chains.values():
        j=-1
        for i,s in enumerate(chain):
            while j+1<i and chain[j+1][0]<=s[0]-D:j+=1
            if j>=0:
                m=nodes[chain[j]][0]
                if K*nodes[s][0]<=(K+1)*m:predicted[s]=m
    stable=defaultdict(int);stableq=stablew=recentq=growingq=0;log_charge=0.0
    for X in seeds:
        s=(X,X//2+3);parent=None;anchor=X;nlight=0;mass=1;history=[];j=-1
        while s is not None:
            z=nodes[s];u=s[0]
            if z[2]!=parent:
                nlight+=1;anchor=u;assert z[0]>=2*mass
            mass=z[0];history.append(s)
            while j+1<len(history)-1 and history[j+1][0]<=u-D:j+=1
            old_mass=nodes[history[j]][0] if j>=0 else 1
            if j>=0 and K*mass<=(K+1)*old_mass:stable[s]+=1
            if not z[7]:
                q,w=z[6],z[5];totalq+=q;totalw+=w;age=u-anchor;maxage=max(maxage,age)
                if age<L:youngq+=q;youngw+=w
                else:old[u]+=1
                log_charge+=q*log(mass/old_mass)
                if j<0:recentq+=q
                elif K*mass>(K+1)*old_mass:growingq+=q
                else:stableq+=q;stablew+=w
            parent,s=s,z[3]
        assert 2**nlight<=mass<=M
        count_light+=nlight;maxlight=max(maxlight,nlight)
    assert dict(stable)==predicted
    window=1.5*D+sqrt(2*R+1)
    assert log_charge<=M*log(M)*window+1e-4
    assert recentq<=M*window and growingq<=M*log(M)*window/log1p(1/K)
    assert stableq+recentq+growingq==totalq
    assert stableq==sum(m*nodes[s][6] for s,m in predicted.items() if not nodes[s][7])
    assert count_light==light
    assert youngq<=(M+light)*(1.5*L+sqrt(2*R+1))
    assert youngw<=(M+light)*(3*L+2*sqrt(2*R+1))
    assert totalq==sum(z[0]*z[6] for z in nodes.values() if not z[7])
    assert totalw==sum(z[0]*z[5] for z in nodes.values() if not z[7])
    assert totalq-youngq==sum(old[u]*nodes[rows[u][0]][6] for u in old)
    print(f'R={R} M={M} states={len(nodes)} light={light} entropy={entropy:.3f} maxlight={maxlight} L={L} maxage={maxage} chains={len(span)} longest_span={max(span.values())}')
    print(f'D={D} K={K} log_charge={log_charge:.3f} stable_states={len(stable)} stableq={stableq} stablew={stablew} recentq={recentq} growingq={growingq}')
    print(f'totalq={totalq} youngq={youngq} oldq={totalq-youngq} totalw={totalw} youngw={youngw} oldw={totalw-youngw} balancedq={balancedq} balancedw={balancedw} old_offsets={len(old)} old_Bmax={max(old.values(),default=0)}')


def controls():
    # Literal GCD ticks, independent of modular clocks.
    def tick_path(X,last):
        u=X;v=X//2+3;states={(u,v)};trace={v:u}
        for n in range(v+1,last+1):
            g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
            if g>1:
                p=next(k for k in range(3,g+1,2) if g%k==0)
                u+=p-1;states.add((u,n))
            trace[n]=u
        return states,trace
    a,ta=tick_path(1002,530);b,tb=tick_path(1008,530);c,tc=tick_path(1014,530)
    assert (1014,510) in a and (1014,510) in c and (1014,510) not in b
    assert (tb[529],tc[529],tb[530],tc[530])==(1008,1020,1060,1020)
    print('literal controls: noninterval basin (1014,510); strict crossing at tick 530')


if __name__=='__main__':
    controls()
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
