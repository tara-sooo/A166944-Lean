"""Audit arrival-phase capacity, rank spectra and singular excursion budgets.
Run: python min_simple_rank_spectrum_audit.py 1000 10000 100000 1000000
Standard library; requires min_simple_crossing_audit.py.
"""
from collections import defaultdict, Counter
from math import isqrt, log, ceil, gcd
import sys
from min_simple_crossing_audit import spf, factors, clock


def rank_defect(U,V,A,K):
    return A*U-K*V+2*(A+K)*(V%2)


def audit(R):
    a=spf(2*R+1); M=0; rows=defaultdict(list); nodes={}; terminal=defaultdict(int)
    seeds=list(range(6*((R+5)//6),3*R//2+1,6)); M=len(seeds)
    # mass, heavy incoming mass, parent, successor, p, w, q, twin, destination, root
    def add(s,m,parent):
        if s not in nodes:
            nodes[s]=[0,0,None,None,0,0,0,False,None,None];rows[s[0]].append(s)
        z=nodes[s];z[0]+=m
        if m>z[1]:z[1],z[2]=m,parent
    for X in seeds:add((X,X//2+3),1,None)
    total=0; ambient=0; H1=0; exits=0
    D=isqrt(isqrt(R**3)); D+=D**4<R**3
    pieces=defaultdict(list); capacities=defaultdict(int)
    slopes=((1,2),(2,3),(3,5),(5,9))
    for u in range(R+R%2,2*R,2):
        fs,gs=factors(u-1,a),factors(u+1,a);q=min(fs[0],gs[0]);twin=fs==[u-1] and gs==[u+1]
        if not twin:
            ambient+=2*q*(len(fs)+len(gs)); H1+=q
            for p in fs+gs:capacities[(u-R)//D,p]+=2*min(p,q)
        if u not in rows:continue
        ps=[(p,0) for p in fs]+[(p,p+2) for p in gs]
        for s in rows[u]:
            z=nodes[s];v=s[1];w,p=clock(u,v,ps);U,V=u+p-1,v+w;y=U,V
            z[4:9]=[p,w,q,twin,y]
            parent=z[2];z[9]=s if parent is None else nodes[parent][9]
            for A,K in slopes:assert rank_defect(U,V,A,K)%p==0
            d=2*V-U;ad=d-6*(V%2)
            assert ad% (2*p)==0 and 0<=d<=U+2
            if not twin:
                assert w<=2*q and w<=2*p
                total+=z[0]*w;pieces[z[9],(u-R)//D].append(s)
                if ad==0:assert U%4==0 and d in (0,6)
            if U>=2*R:terminal[y]+=z[0];exits+=z[0]
            else:
                assert not twin
                z[3]=y;add(y,z[0],s)
    assert exits==M
    def mass(y):return nodes[y][0] if y in nodes else terminal[y]
    # Destination capacity: fixed rank singularity, and a graph-dependent
    # per-offset selection of up to two arbitrary arrival phases.
    dest_wait=defaultdict(Counter); dest_max=defaultdict(int)
    for s,z in nodes.items():
        if z[7]:continue
        y=z[8];dest_wait[y[0]][y[1]]+=z[0]*z[5];dest_max[y]=max(dest_max[y],z[5])
    top={u:set(v for v,_ in counter.most_common(2)) for u,counter in dest_wait.items()}
    H=(isqrt(R)+1)*max(1,ceil(log(R)))**2
    for mode,H in [('reset',H),('rank_2_3',H),('two_largest_wait',H),('reset',8),('two_largest_wait',8)]:
        def chosen(y):
            if mode=='reset':return rank_defect(*y,1,2)==0
            if mode=='rank_2_3':return rank_defect(*y,2,3)==0
            return y[1] in top.get(y[0],())
        targets={y for y in dest_max if chosen(y)}
        by_u=Counter(y[0] for y in targets);assert max(by_u.values(),default=0)<=2
        cap=sum(dest_max[y] for y in targets);assert cap<=2*ambient
        wait=small=threshold_wait=threshold_mass=0; direct=defaultdict(int);incoming=Counter()
        for s,z in nodes.items():
            if z[7] or z[8] not in targets:continue
            b,w=z[0],z[5]; y=z[8];wait+=b*w;incoming[y]+=b
            if b>H:continue
            small+=b*w
            if mass(y)>H:threshold_wait+=b*w;threshold_mass+=b
            else:direct[y]+=b*w
        assert all(m<=mass(y) for y,m in incoming.items())
        assert all(w<=H*dest_max[y] for y,w in direct.items())
        assert threshold_mass<=M and threshold_wait<=2*isqrt(2*R+1)*threshold_mass
        assert small==sum(direct.values())+threshold_wait and small<=H*cap+threshold_wait
        print(f'R={R} target={mode} H={H} targets={len(targets)} capacity={cap} wait={wait} small_wait={small} threshold_mass={threshold_mass} threshold_wait={threshold_wait}')
    # Divisor-spectrum: high labels arriving at nonzero adjusted rank values.
    # Bound per piece using the exact ambient per-label capacity, and check
    # each distinct prime divides at least one nonzero value. Use integer
    # prime-product inequality as well as log-product.
    T=max(5,isqrt(isqrt(R)));Kmax=max(1,ceil(log(R)))
    spectral=defaultdict(Counter)
    for (root,block),ss in pieces.items():
        for A,K in slopes:
            labels=Counter();values=set();weighted=0;singular=0
            for s in ss:
                z=nodes[s];p,w=z[4],z[5];Z=rank_defect(*z[8],A,K)
                if p<T:continue
                if not Z:singular+=z[0]*w;continue
                values.add(abs(Z));labels[p]+=w;weighted+=z[0]*w
            # Distinct high-prime product divides product of distinct defects.
            # Divide out each prime once, without constructing a giant integer.
            remaining=list(values)
            for p,w in labels.items():
                assert w<=capacities[block,p]
                i=next(i for i,n in enumerate(remaining) if n%p==0)
                remaining[i]//=p
            budget=sum(log(n) for n in values)
            assert sum(log(p) for p in labels)<=budget+1e-9
            assert sum(1/log(p)**2 for p in labels)<=budget/log(T)**3+1e-9
            row=spectral[A,K];row['high_nonzero_wait']+=weighted;row['high_singular_wait']+=singular
            row['max_values']=max(row['max_values'],len(values));row['max_high_labels']=max(row['max_high_labels'],len(labels))
            if len(values)<=Kmax:
                row['sparse_nonzero_wait']+=weighted;row['sparse_pieces']+=1
    # Independent replay: all non-twin singular/nonsingular excursion budgets.
    counts=Counter(); max_ratio=0; max_relay=0
    for X in seeds:
        s=(X,X//2+3);relayG=relayW=0;start_d=6
        Wn=Gn=Ws=excess=long_wait=high_pre_wait=0
        while s is not None:
            z=nodes[s]
            if z[7]:break
            p,w=z[4],z[5];U,V=z[8];d=2*V-U;pre_d=2*s[1]-s[0]
            if rank_defect(U,V,1,2)==0:
                assert pre_d>=start_d
                assert relayG==2*relayW+start_d-pre_d
                assert relayG<=2*relayW
                assert max(0,pre_d-6)<=2*relayW
                assert abs(2*w-(p-1))<=6+5*relayG
                if 4*relayG>=p:long_wait+=w
                if 4*max(0,pre_d-6)>=p:high_pre_wait+=w
                excess+=max(0,pre_d-6);Ws+=w
                counts['singular_visits']+=1
                counts['relay_nonempty']+=bool(relayG);max_relay=max(max_relay,relayG)
                relayG=relayW=0;start_d=d
            else:
                assert d>=start_d
                if d<6:assert d==0 and V%2 and p==3 and pre_d==0 and w==1
                relayG+=p-1;relayW+=w;Wn+=w;Gn+=p-1
                counts['nonsingular_visits']+=1
            s=z[3]
        assert relayG<=2*relayW
        assert Gn<=2*Wn and excess<=2*Wn
        assert long_wait<=8*Gn and high_pre_wait<=8*excess
        counts['nonsingular_wait']+=Wn;counts['singular_wait']+=Ws;counts['nonsingular_gain']+=Gn
        counts['excess']+=excess;counts['long_relay_wait']+=long_wait;counts['high_pre_wait']+=high_pre_wait
        if Wn:max_ratio=max(max_ratio,Gn/Wn)
    assert counts['nonsingular_wait']+counts['singular_wait']==total
    # Independent literal tick selection on the small slab.
    if R<=10000:
        for s,z in nodes.items():
            u,v=s;n=v+1
            while True:
                g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
                if g>1:break
                n+=1
            assert (n-v,factors(g,a)[0])==(z[5],z[4])
    print(f'R={R} M={M} states={len(nodes)} D={D} pieces={len(pieces)} total_wait={total} H1={H1} arrival_ambient={ambient} T={T} Kmax={Kmax}')
    for slope,row in spectral.items():print('rank',slope,dict(row))
    print('excursions',dict(counts),'max_Gn_Wn',round(max_ratio,6),'max_relay',max_relay)

def direct_reset_control(labels):
    B=max(labels)+6; a=spf(B); E=[0]
    for p in labels:
        assert p%12==1 and factors(p,a)==[p];E.append(E[-1]+p-1)
    X,Q=0,12
    def impose(r,q):
        nonlocal X,Q
        if Q%q==0:assert X%q==r%q;return
        X+=Q*((r-X)*pow(Q,-1,q)%q);Q*=q
    for i,p in enumerate(labels):
        r=(-1-E[i])%p
        assert all((r+E[j])%p not in (1,p-1) for j in range(len(labels)) if j!=i)
        impose(r,p)
    for q in range(3,B+1,2):
        if factors(q,a)!=[q] or q in labels:continue
        ok=[r for r in range(q) if all((r+e)%q not in (1,q-1) for e in E[:-1])]
        impose(0 if Q%q==0 else ok[0],q)
    X+=Q;u,v=X,X//2+3;events=[]
    for p in labels:
        n=v+1
        while True:
            g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
            if g>1:break
            n+=1
        assert g==p and n-v==(p-1)//2
        u+=p-1;v=n;assert u%12==0 and 2*v-u==6 and v%2
        events.append((p,(p-1)//2))
    print('literal direct reset chain',labels,'seed',X,'modulus',Q,'events',events)

if __name__=='__main__':
    direct_reset_control((13,61,73,109))
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
