"""Common-boundary graph audit. Python standard library only.
Run: python research/min_simple_graph_audit.py 1000 10000 100000 1000000
"""
from collections import defaultdict, Counter
from math import isqrt
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R):
    a = spf(2*R+1)
    # s -> [mass, same-label collision pairs, distinct-label pairs, seed pairs,
    #       previous-label masses, next state, remaining length]
    nodes = {}
    rows = defaultdict(list)
    def node(u,v):
        s=(u,v)
        if s not in nodes:
            nodes[s]=[0,0,0,0,{},None,0]
            rows[u].append(s)
        return nodes[s]
    seeds=list(range(6*((R+5)//6),3*R//2+1,6))
    for X in seeds:
        z=node(X,X//2+3); z[0]=1
    S=Q=0; exits=0; maxphase=0; maxmass=0
    E=Bmax=H1=H2=W0=weighted_q=0
    qvals={};twins=set()
    for u in range(R+(R%2),2*R,2):
        fs,gs=factors(u-1,a),factors(u+1,a)
        twin=fs==[u-1] and gs==[u+1]
        q=min(fs[0],gs[0])
        if not twin:
            assert q*q<=u+1
            H1+=q;H2+=q*q
        if u not in rows: continue
        if twin: twins.add(u)
        qvals[u]=q
        B=sum(nodes[s][0] for s in rows[u]); E+=B*B;Bmax=max(Bmax,B)
        if not twin: weighted_q+=B*q
        maxphase=max(maxphase,len(rows[u]))
        ps=[(p,0) for p in fs]+[(p,p+2) for p in gs]
        for s in rows[u]:
            z=nodes[s]; b=z[0];v=s[1]; S+=b;Q+=b*b;maxmass=max(maxmass,b)
            w,p=clock(u,v,ps); U,V=u+p-1,v+w
            if not twin:
                assert w<=2*q
                W0+=b*w
            if U>=2*R:exits+=b;continue
            t=(U,V); y=node(U,V); same=y[4].get(p,0)
            other=sum(y[4].values())-same; seed=y[0]-same-other
            assert seed in (0,1)
            y[1]+=same*b;y[2]+=other*b;y[3]+=seed*b
            y[0]+=b;y[4][p]=same+b;z[5]=t
    assert exits==len(seeds)
    C=[0,0,0]; maxlen=0; lenhist=Counter(); first_pairs=[0,0,0]; hit={}
    for u in sorted(rows,reverse=True):
        for s in rows[u]:
            z=nodes[s];z[6]=1+(nodes[z[5]][6] if z[5] is not None else 0)
            hit[s]=u in twins or (z[5] is not None and hit[z[5]])
            for i in range(3):
                C[i]+=z[i+1]*z[6];first_pairs[i]+=z[i+1]
    for X in seeds:
        n=nodes[X,X//2+3][6];lenhist[n]+=1;maxlen=max(maxlen,n)
    assert S==sum(n*c for n,c in lenhist.items())
    assert Q==S+2*sum(C)
    K=sum(not hit[X,X//2+3] for X in seeds)
    assert K*(R-12)<=4*W0<=8*weighted_q
    assert weighted_q**2<=E*H2 and weighted_q<=Bmax*H1
    assert Q<=E<=maxphase*Q
    # Independent literal paths for small R (including collision energy).
    if R<=10000:
        counts=Counter()
        for X in seeds:
            u,v=X,X//2+3
            while u<2*R:
                counts[u,v]+=1
                from math import gcd
                n=v+1
                while True:
                    g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                    if g>1:break
                    n+=1
                p=factors(g,a)[0];u+=p-1;v=n
        assert counts==Counter({s:z[0] for s,z in nodes.items()})
    M=len(seeds);U=len(nodes)
    print(f'R={R} M={M} U={U} S={S} Q={Q} mean={S/M:.6f} CS={(U*Q)**.5/M:.6f} maxphase={maxphase} maxmass={maxmass} maxlen={maxlen}')
    print('first pairs',first_pairs,'suffix-weighted pairs',C,'shares',[round(x/sum(C),6) if sum(C) else 0 for x in C])
    print(f'offset E={E} Bmax={Bmax} H1={H1} H2={H2} W0={W0} weighted_q={weighted_q} twin_free={K} E/R^2={E/R**2:.8f}')
    return nodes,rows

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):
        audit(R)
