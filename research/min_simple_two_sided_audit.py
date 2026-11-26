"""Two-sided significant-clock transport and slot capacity. Standard library.
Run: python research/min_simple_two_sided_audit.py 1000 10000 100000 1000000
"""
from collections import defaultdict
from math import isqrt, ceil, log
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R):
    a=spf(2*R+1); L=max(1,ceil(log(R)))
    seeds=list(range(6*((R+5)//6),3*R//2+1,6)); M=len(seeds)
    nodes={}; rows=defaultdict(list)
    # mass, heavy mass, parent, successor, p,w,q,twin,marked
    def add(s,m,parent):
        if s not in nodes:
            nodes[s]=[0,0,None,None,0,0,0,False,False]; rows[s[0]].append(s)
        z=nodes[s]; z[0]+=m
        if m>z[1]: z[1],z[2]=m,parent
    for X in seeds: add((X,X//2+3),1,None)
    exits=0; total=0; unmarked=0; exitmass=defaultdict(int); dest={}
    for u in range(R+R%2,2*R,2):
        if u not in rows: continue
        fs,gs=factors(u-1,a),factors(u+1,a); q=min(fs[0],gs[0])
        twin=fs==[u-1] and gs==[u+1]
        ps=[(p,0) for p in fs]+[(p,p+2) for p in gs]
        for s in rows[u]:
            z=nodes[s]; w,p=clock(u,s[1],ps); U,V=u+p-1,s[1]+w
            mark=not twin and L*w>=p-1
            z[4:9]=[p,w,q,twin,mark]
            if not twin:
                assert w<=2*q
                total+=z[0]*w
                if not mark: unmarked+=z[0]*w
            dest[s]=(U,V)
            if U>=2*R:
                exits+=z[0]; exitmass[U,V]+=z[0]
            else:
                assert not twin
                z[3]=(U,V); add((U,V),z[0],s)
    assert exits==M and L*unmarked<=3*R*M
    # Full-history small-cohort bound, including terminal merger groups.
    # q-thresholds are integer approximations of sqrt(R)/4 and R^(1/4).
    q_thresholds=[(max(7,isqrt(R)//4),max(1,ceil(log(R)**2))),
                  (max(7,isqrt(isqrt(R))),L)]
    for T,H in q_thresholds:
        rough_count=0
        for u in range(R+R%2,2*R,2):
            fs,gs=factors(u-1,a),factors(u+1,a)
            rough_count+=min(fs[0],gs[0])>=T and not (fs==[u-1] and gs==[u+1])
        by_slot=defaultdict(lambda:[0,0]); growth_mass=growth_wait=0; allsmall=0
        for s,z in nodes.items():
            if z[7] or z[6]<T or z[0]>H:continue
            u,v=s; y=dest[s]; m=nodes[y][0] if y in nodes else exitmass[y]
            allsmall+=z[0]*z[5]
            if m>H:
                assert m>z[0]
                growth_mass+=z[0];growth_wait+=z[0]*z[5]
            else:
                slot=by_slot[u,y[1]];slot[0]+=z[0];slot[1]=max(slot[1],z[5])
        intervals=defaultdict(list)
        for (u,n),(m,w) in by_slot.items():
            assert m<=H; intervals[u].append((n-w,n))
        for u,ints in intervals.items():
            ints.sort()
            assert all(x[1]<=y[0] for x,y in zip(ints,ints[1:]))
            assert sum(n-v for v,n in ints)<=u//2+3
        assert growth_mass<=M
        assert allsmall-growth_wait<=H*(R+3)*rough_count
        print(f'all_history T={T} H={H} rough_count={rough_count} small_wait={allsmall} growth_mass={growth_mass} growth_wait={growth_wait}')
    # Mass/phase-width tradeoff; the center may be chosen after the graph is known.
    Hmax=(isqrt(R)+1)*L*L; groups=defaultdict(list)
    for s,z in nodes.items():
        if not z[7] and z[0]<=Hmax:
            b=z[0]; H=1<<(b-1).bit_length(); groups[H].append(s)
    centers={u:(min(2*s[1]-u for s in ss)+max(2*s[1]-u for s in ss))//2
             for u,ss in rows.items()}
    for mode in ('zero','midpoint'):
        result=0; exceptional=0; capacity=0; selected=0
        for H,ss in groups.items():
            D=2*R//(H*L*L); byslot=defaultdict(lambda:[0,0]); cross=0; cw=0; wait=0
            for s in ss:
                u,v=s; z=nodes[s]; b=z[0]; d=2*v-u
                c=0 if mode=='zero' else centers[u]
                if b*abs(d-c)*L*L>R:continue
                assert abs(d-c)<=D
                selected+=1; wait+=b*z[5]; y=dest[s]
                m=nodes[y][0] if y in nodes else exitmass[y]
                if m>H:cross+=b;cw+=b*z[5]
                else:
                    slot=byslot[u,y[1]];slot[0]+=b;slot[1]=max(slot[1],z[5])
            ints=defaultdict(list)
            for (u,n),(m,w) in byslot.items():
                assert m<=H;ints[u].append((n-w,n))
            cap=0
            for u,iv in ints.items():
                iv.sort();assert all(x[1]<=y[0] for x,y in zip(iv,iv[1:]))
                q=nodes[rows[u][0]][6]
                length=D+2*q # |d-c|<=D gives v-band width D.
                assert sum(n-v for v,n in iv)<=length
                cap+=H*length
            assert cross<=M and cw<=2*isqrt(2*R+1)*cross
            assert wait-cw<=cap
            result+=wait;exceptional+=cw;capacity+=cap
        print(f'product {mode} Hmax={Hmax} mass_defect_limit={R/L**2:.3f} states={selected} wait={result} threshold_wait={exceptional} slot_cap={capacity}')
    # Previous marked state along a heavy chain, and next marked state along successor.
    prev={}; nxt={}
    for u in sorted(rows):
        for s in rows[u]:
            p=nodes[s][2]
            prev[s]=None if p is None else (p if nodes[p][8] else prev[p])
    for u in sorted(rows,reverse=True):
        for s in rows[u]:
            t=nodes[s][3]
            nxt[s]=None if t is None else (t if nodes[t][8] else nxt[t])
    marked=[s for s,z in nodes.items() if z[8]]
    print(f'R={R} M={M} states={len(nodes)} L={L} total_non_twin_wait={total} unmarked_wait={unmarked}')
    for h in sorted({1,4,16,isqrt(isqrt(R))}):
        stable={}; logcharge=0.; missing=growth=0
        J=max(3,ceil(R**(7/8))); big_windows=big_stable_wait=0; total_big=0
        # Exact cohort reconstruction from the h-th preceding marked heavy state.
        for s in marked:
            t=r=s
            for _ in range(h):
                t=prev[t] if t is not None else None
                r=nxt[r] if r is not None else None
                if t is None or r is None: break
            if t is not None and r is not None and 2*nodes[r][0]<=3*nodes[t][0]:
                stable[s]=nodes[t][0]
                assert 2*nodes[s][0]<=3*nodes[t][0]
        # Independent per-origin replay of all marked windows.
        counted=defaultdict(int)
        for X in seeds:
            s=(X,X//2+3); seq=[]; before=[]; big=0; origin_big_windows=0
            while s is not None:
                z=nodes[s]
                if z[8]: seq.append(s); before.append(big)
                if not z[7] and z[4]>=J: big+=1
                s=z[3]
            for j,s in enumerate(seq):
                w=nodes[s][5]
                if j<h or j+h>=len(seq): missing+=w;continue
                m0=nodes[seq[j-h]][0];m1=nodes[seq[j+h]][0]
                logcharge+=w*log(m1/m0)
                has_big=before[j+h]>before[j-h]
                if has_big: origin_big_windows+=1; big_windows+=w
                if 2*m1<=3*m0:
                    counted[s]+=1
                    if has_big: big_stable_wait+=w
                else: growth+=w
            assert origin_big_windows<=2*h*big and big*(J-1)<3*R
            total_big+=big
        assert dict(counted)==stable
        assert big_windows<=4*h*(2*R+1)**.5*total_big+1e-5
        assert missing<=4*h*(2*R+1)**.5*M+1e-6
        assert logcharge<=4*h*(2*R+1)**.5*M*log(M)+1e-5
        assert growth*log(1.5)<=logcharge+1e-5
        sw=sum(m*nodes[s][5] for s,m in stable.items())
        assert sw+missing+growth+unmarked==total
        # At most one stable carrier per active tick at each offset.
        # Their waiting intervals are disjoint; capacity <=u/2+3.
        slots=defaultdict(list)
        for s,m in stable.items():
            u,v=s; w=nodes[s][5]; slots[u].append((v,v+w,m,nodes[s][0],nodes[s][6]))
        for u,intervals in slots.items():
            intervals.sort()
            assert all(x[1]<=y[0] for x,y in zip(intervals,intervals[1:]))
            assert sum(n-v for v,n,*_ in intervals)<=u//2+3
        # Measured traffic at high-q offsets carried by small stable state groups.
        T=max(7,isqrt(R)//4); H=max(1,ceil(log(R)**2)); rough_count=0
        for u in range(R+R%2,2*R,2):
            fs,gs=factors(u-1,a),factors(u+1,a)
            rough_count+=min(fs[0],gs[0])>=T and not (fs==[u-1] and gs==[u+1])
        small=high=0; maxmass=0
        for s,m in stable.items():
            z=nodes[s]
            if z[6]>=T:
                high+=m*z[5];maxmass=max(maxmass,z[0])
                if z[0]<=H: small+=m*z[5]
        assert small<=H*(R+3)*rough_count
        print(f'h={h} stable_states={len(stable)} stable_wait={sw} missing_wait={missing} growth_wait={growth} logcharge={logcharge:.3f} T={T} H={H} rough_count={rough_count} highq_wait={high} small_carrier_wait={small} max_highq_mass={maxmass} J={J} big_events={total_big} big_window_wait={big_windows} stable_big_wait={big_stable_wait}')

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']): audit(R)
