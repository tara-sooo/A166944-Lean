"""Local label-support audit for exact MIN heavy-chain segments (stdlib only).
Run: python research/min_simple_label_diversity_audit.py 1000 10000 100000 1000000
"""
from collections import defaultdict, Counter
from math import isqrt, log, log2, ceil
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R):
    a=spf(2*R+1)
    D=isqrt(isqrt(R**3))
    if D**4<R**3: D+=1
    seeds=list(range(6*((R+5)//6),3*R//2+1,6)); M=len(seeds)
    rows=defaultdict(list); nodes={}
    # mass, largest incoming, heavy parent, successor, label, wait, twin
    def add(s,m,parent):
        if s not in nodes:
            nodes[s]=[0,0,None,None,0,0,False]; rows[s[0]].append(s)
        z=nodes[s]; z[0]+=m
        if m>z[1]: z[1],z[2]=m,parent
    for X in seeds: add((X,X//2+3),1,None)
    exits=0; total=0; root={}; pieces=defaultdict(list)
    # Ambient capacity per p in each block: sum min(2p,2q).
    capacity=defaultdict(int)
    for u in range(R+R%2,2*R,2):
        fs,gs=factors(u-1,a),factors(u+1,a);q=min(fs[0],gs[0]);twin=fs==[u-1] and gs==[u+1]
        block=(u-R)//D
        if not twin:
            for p in fs+gs:capacity[block,p]+=2*min(p,q)
        if u not in rows:continue
        ps=[(p,0) for p in fs]+[(p,p+2) for p in gs]
        for s in rows[u]:
            z=nodes[s]; w,p=clock(u,s[1],ps); U,V=u+p-1,s[1]+w
            z[4:7]=[p,w,twin]
            parent=z[2];root[s]=s if parent is None else root[parent]
            if not twin:
                assert w<=2*min(p,q);total+=z[0]*w
                pieces[root[s],block].append(s)
            if U>=2*R: exits+=z[0]
            else:
                assert not twin; z[3]=(U,V);add((U,V),z[0],s)
    assert exits==M
    hist=defaultdict(lambda:[0,0,0]);support={};per_piece_ratio=0.;maxsupport=0
    T=max(3,ceil(log(R))); A=T; K=max(1,int(log2(log(R))/2))
    worst=0.; max_small_Q=0; gaps=0; no_gaps=0
    P0=isqrt(isqrt(R)); lowhist=defaultdict(lambda:[0,0,0]); max_high_support=0
    # Exact small-support gap decomposition for ALL pieces.
    for key,ss in pieces.items():
        block=key[1]; waits=Counter();weighted=0;prev=None
        for s in ss:
            z=nodes[s];waits[z[4]]+=z[5];weighted+=z[0]*z[5]
            if prev is not None:assert nodes[prev][3]==s
            prev=s
        for p,w in waits.items():assert w<=capacity[block,p]
        supp=sorted(waits);k=len(supp);support[key]=k;maxsupport=max(maxsupport,k)
        hist[k][0]+=1;hist[k][1]+=weighted;hist[k][2]+=sum(waits.values())
        Q=2; cut=None
        for p in supp:
            if p>=T and p>A*Q:cut=p;break
            Q*=p
        if cut is None:
            assert sum(waits.values())<=3*Q;no_gaps+=1
        else:
            small=sum(w for p,w in waits.items() if p<cut)
            count=sum(nodes[s][4]>=cut for s in ss)
            assert (count-1)*(cut-1)<=D
            assert small<=3*Q*(count+1)
            gaps+=1
        if k<=K:
            max_small_Q=max(max_small_Q,Q)
            per_piece_ratio=max(per_piece_ratio,sum(waits.values())/D)
        # Low support below floor(R^(1/4)), with arbitrary larger-label separators.
        low=[p for p in supp if p<P0]; high=[p for p in supp if p>=P0]
        max_high_support=max(max_high_support,len(high))
        Qlo=2; cutlo=P0
        for p in low:
            if p>=T and p>A*Qlo:cutlo=p;break
            Qlo*=p
        smalllo=sum(w for p,w in waits.items() if p<cutlo)
        seps=sum(nodes[s][4]>=cutlo for s in ss)
        assert (seps-1)*(cutlo-1)<=D
        assert smalllo<=3*Qlo*(seps+1)
        loW=sum(nodes[s][0]*nodes[s][5] for s in ss if nodes[s][4]<P0)
        lowhist[len(low)][0]+=1;lowhist[len(low)][1]+=loW;lowhist[len(low)][2]+=weighted-loW
        worst=max(worst,max((w*log(p)**2/D for p,w in waits.items()),default=0.))
    # Independent origin replay: path changes heavy chain only on light arrivals.
    per_origin=Counter();pieces_max=0;light_max=0
    for X in seeds:
        s=(X,X//2+3);prev=None;last=None;seen=0;light=0
        while s is not None:
            z=nodes[s]
            if z[2]!=prev:light+=1
            if not z[6]:
                key=root[s],(s[0]-R)//D
                if key!=last:seen+=1;last=key
                per_origin[support[key]]+=z[5]
            prev,s=s,z[3]
        assert 2**light<=M
        assert seen<=ceil(R/D)+1+light
        pieces_max=max(pieces_max,seen);light_max=max(light_max,light)
    assert sum(per_origin.values())==total==sum(row[1] for row in hist.values())
    assert all(per_origin[k]==row[1] for k,row in hist.items())
    ambient=max((w*log(p)**2/D for (block,p),w in capacity.items()),default=0.)
    print(f'R={R} M={M} D={D} states={len(nodes)} pieces={len(pieces)} total_wait={total} max_support={maxsupport} K={K} max_pieces_per_origin={pieces_max} max_light={light_max}')
    print(f'gap_pieces={gaps} no_gap_pieces={no_gaps} max_Q_at_K={max_small_Q} max_piece_wait_over_D_at_K={per_piece_ratio:.6f} max_actual_label_ratio={worst:.6f} max_ambient_label_ratio={ambient:.6f}')
    for k in sorted({1,2,4,8,16,32,K}):
        n=sum(row[0] for j,row in hist.items() if j<=k);w=sum(row[1] for j,row in hist.items() if j<=k)
        print(f'support<={k} pieces={n} weighted_wait={w} share={w/total:.6f}')
    assert sum(z[1]+z[2] for z in lowhist.values())==total
    print(f'low_threshold={P0} max_high_support={max_high_support} low_wait={sum(z[1] for z in lowhist.values())} high_wait={sum(z[2] for z in lowhist.values())}')
    for k in sorted({1,2,4,8,K}):
        n=sum(z[0] for j,z in lowhist.items() if j<=k); w=sum(z[1] for j,z in lowhist.items() if j<=k)
        print(f'low_support<={k} pieces={n} low_wait={w}')

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
