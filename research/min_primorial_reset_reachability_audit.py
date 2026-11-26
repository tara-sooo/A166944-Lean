"""Exact all-reset reachability and convex-hull relaxation.
Run: python min_primorial_reset_reachability_audit.py [offset cap] [seed bound]
Requires sympy and sibling min_primorial_record_supply_audit.py.
"""
from min_primorial_record_supply_audit import spf_table,factors,block
from collections import Counter
from sys import argv
from math import prod
from sympy import primerange


def audit(cap,seed_bound):
    a=spf_table(max(cap+10,4*seed_bound+10000))
    starts=Counter(); maxrow=None; maxratio={k:(-1,None) for k in (7,1000,10000)}
    for r in range(7,seed_bound+1,6):
        z=block(r,a)
        if z is None: starts['incomplete']+=1;continue
        starts['complete']+=1;starts['false']+=not z[5]
        if maxrow is None or z[1]>maxrow[1]:maxrow=z
        for k in maxratio:
            if r>=k and z[2]/(2*r-2)>maxratio[k][0]:maxratio[k]=(z[2]/(2*r-2),z)
    print('arbitrary seeds',seed_bound,dict(starts),'max events',maxrow,'max ratios',maxratio,flush=True)
    # Sparse slots: exact event-time sets, plus the exact one-step image of
    # their interval-hull relaxation, whose lower/upper endpoints are stored.
    slots={}; hull={}; stats=Counter(); false_exact=[];false_hull=[]
    maxd=(0,0,0);maxwidth=0;maxhullwidth=0;first_hole=None
    ratios={k:(0,0,0) for k in (100,1000,10000,100000)}
    def push(U,V):
        if U<=cap:slots.setdefault(U,set()).add(V)
    def push_hull(U,lo,hi):
        if U>cap:return
        x=hull.get(U)
        hull[U]=(lo,hi) if x is None else (min(lo,x[0]),max(hi,x[1]))
    for u in range(4,cap+1,2):
        times=slots.pop(u,set());bounds=hull.pop(u,None)
        if u%12==0:
            v=u//2+3;times.add(v)
            bounds=(v,v) if bounds is None else (min(v,bounds[0]),max(v,bounds[1]))
        if not times and bounds is None:continue
        ff=[(p,0 if e==1 else p+2) for e in (1,-1) for p in factors(u-e,a)]
        twin=a[u-1]==0 and a[u+1]==0
        def next_event(v):
            return min((v+((s-v)%(2*p) or 2*p),p) for p,s in ff)
        def at(n):return min(p for p,s in ff if (n-s)%(2*p)==0)
        if times:
            stats['horizons']+=1;stats['states']+=len(times)
            maxwidth=max(maxwidth,len(times));d=2*max(times)-u
            maxd=max(maxd,(d,u,len(times)))
            for k in ratios:
                if u>=k and (ratios[k][1]==0 or d*ratios[k][1]>ratios[k][0]*u):
                    ratios[k]=(d,u,len(times))
            if max(times)-min(times)+1>len(times):
                stats['noninterval_horizons']+=1
                if first_hole is None:first_hole=(u,sorted(times))
            if bounds is None or min(times)<bounds[0] or max(times)>bounds[1]:raise AssertionError('hull lost exact state')
            dest=set()
            for v in times:
                n,p=next_event(v);U=u+p-1
                assert u<=2*v<=2*u+2
                if p==u+1 and not twin:false_exact.append((u,v))
                dest.add((U,n));push(U,n)
            stats['same_horizon_merges']+=len(times)-len(dest)
        if bounds is not None:
            lo,hi=bounds;maxhullwidth=max(maxhullwidth,hi-lo+1)
            nlo,_=next_event(lo);nhi,_=next_event(hi)
            # Exactly the range of event ticks attainable from some integer
            # time in [lo,hi] is the set of active ticks in [nlo,nhi].
            for p,s in ff:
                left=nlo+(s-nlo)%(2*p);right=nhi-(nhi-s)%(2*p)
                while left<=right and at(left)!=p:left+=2*p
                while right>=left and at(right)!=p:right-=2*p
                if left>right:continue
                if p==u+1 and not twin:false_hull.append((u,lo,hi,left))
                push_hull(u+p-1,left,right)
    print('offset cap',cap,'exact stats',dict(stats),'max width',maxwidth,'max deficit',maxd,'ratios',ratios)
    print('first hole',first_hole,'exact false doubles',len(false_exact),false_exact[:10])
    print('convex hull max width',maxhullwidth,'false doubles',len(false_hull),false_hull[:10])


def prefix_lift(m):
    # An exact finite diagonal lift of the first m events from seed r0=7.
    # Prime factors of all relative defects through the final tick are <= B.
    from min_primorial_record_supply_audit import step
    r0=7;u,v=12,9;path=[];B=7;a=spf_table(10000)
    for _ in range(m):
        w,p,e=step(u,v,a);B=max(B,2*(v+w)-u+1)
        path.append((w,p,e));u+=p-1;v+=w
    Q=2*prod(primerange(3,B+1));r=r0+Q
    # Verify by the raw defect factors, never factor the huge shifted neighbors.
    from math import gcd
    from sympy import factorint
    U,V=2*r-2,r+2
    for w,p,e in path:
        for n in range(V+1,V+w+1):
            g=gcd(n if n%2==0 else n-2,U-1 if n%2==0 else U+1)
            assert g==1 if n<V+w else min(factorint(g))==p
        U+=p-1;V+=w
        assert p<r
    print('lift m',m,'defect bound',B,'seed bits',r.bit_length(),'max label',max(x[1] for x in path))

def first_wait_stats(limit):
    a=spf_table(2*limit+10)
    thresholds=(10,30,100,300,1000)
    counts=Counter();total=0;size=0
    for r in range(7,limit+1,6):
        from min_primorial_record_supply_audit import step
        w,p,e=step(2*r-2,r+2,a)
        assert w<=2*p and p<=2*w+7
        size+=1;total+=w
        for W in thresholds:counts[W]+=w>W
    print('first waits',limit,'size',size,'mean',total/size,'tail',[(W,counts[W],counts[W]/size) for W in thresholds])

if __name__=='__main__':
    audit(int(argv[1]) if len(argv)>1 else 1000000,int(argv[2]) if len(argv)>2 else 100000)
    for m in (5,10,15):prefix_lift(m)
    first_wait_stats(1000000)
