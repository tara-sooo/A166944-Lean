"""Common-boundary rough flux, small-label compression, and greedy comparator.
Stdlib only. Run: python min_simple_rough_flux_audit.py 1000 10000 100000 1000000
"""
from collections import defaultdict, Counter
from math import isqrt
import sys
from min_simple_crossing_audit import spf, factors, clock


def audit(R, z=7):
    P=2*3*5*7 if z==7 else 2*3*5
    assert z in (5,7)
    a=spf(2*R+1)
    seeds=list(range(6*((R+5)//6),3*R//2+1,6));M=len(seeds)
    rows=defaultdict(dict)
    for X in seeds: rows[X][X//2+3]=(1,0)  # origin mass, weighted pending low wait
    W=G=0; Wlow=Whigh=Jhigh=0; exits=0; pending_end=0
    H=[0,0]; weighted=0; E1=0; bins=defaultdict(lambda:[0]*6)
    qvals={};rough=set(); Bmax=0; S=0; E=0; hit=0
    cutdiff=defaultdict(int)
    for u in range(R+R%2,2*R,2):
        fs,gs=factors(u-1,a),factors(u+1,a);q=min(fs[0],gs[0]);twin=fs==[u-1] and gs==[u+1]
        qvals[u]=(q,twin)
        if not twin:
            H[0]+=q;H[1]+=q*q
            binrow=bins[q.bit_length()-1];binrow[0]+=1;binrow[1]+=q*q
        if u not in rows:continue
        B=sum(b for b,_ in rows[u].values());S+=B;E+=B*B;Bmax=max(Bmax,B)
        if twin:hit+=B
        else:
            weighted+=B*q;E1+=q*B*B
            binrow=bins[q.bit_length()-1];binrow[2]+=B;binrow[3]+=B*q;binrow[4]+=B*B;binrow[5]=max(binrow[5],B)
        for v,(b,pending) in rows[u].items():
            w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs]);U,V=u+p-1,v+w
            W+=b*w;G+=b*(p-1)
            cutdiff[u]+=b;cutdiff[min(U,2*R)]-=b
            if p<=z:
                assert u//P==(U-1)//P or U%P==0
                Wlow+=b*w;pending+=b*w
            else:
                Jhigh+=b;Whigh+=b*w
                assert pending<=3*P*b
                pending=0
            if U>=2*R:
                exits+=b;pending_end+=pending;assert pending<=3*P*b
            else:
                m,l=rows[U].get(V,(0,0));rows[U][V]=(m+b,l+pending)
    assert exits==M and W==Wlow+Whigh
    assert Wlow<=3*P*(Jhigh+M)
    assert weighted**2<=E1*H[0]
    f=0
    for y in range(R,2*R+1):
        f+=cutdiff[y]
        if 3*R//2<=y<2*R:assert f==M
    assert f==0
    # deterministic offset-only comparator; always choose the smallest neighbor factor.
    mass=Counter(seeds);gS=gE=gB=ghit=gex=0;gcut=defaultdict(int);small=large=0
    for u in range(R+R%2,2*R,2):
        b=mass[u]
        if not b:continue
        q,twin=qvals[u];gS+=b;gE+=b*b;gB=max(gB,b);ghit+=b*twin
        U=u+q-1
        if q<=z:small+=b
        else:large+=b
        if U<2*R:mass[U]+=b
        else:gex+=b
    assert gex==M and small+large==gS
    print(f'R={R} M={M} S={S} E={E} Bmax={Bmax} twin_hits={hit} E1={E1} W={W} G={G} weighted_q={weighted} low_wait={Wlow} high_events={Jhigh} high_wait={Whigh} terminal_pending={pending_end}')
    print('greedy',gS,gE,gB,ghit,small,large)
    print('q_bin_lower ambient_count H2 traffic weighted_q E Bmax')
    for j,row in sorted(bins.items()): print(1<<j,*row)

if __name__=='__main__':
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
