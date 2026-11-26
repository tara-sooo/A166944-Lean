"""Direct reset forest: exact fixed-depth ancestor counts and CRT chain.
Run: python min_primorial_direct_forest_audit.py 1000000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
"""
from collections import Counter
from math import gcd
from sys import argv
from sympy import primerange, isprime
from min_primorial_record_supply_audit import spf_table, step, factors


def chain_construct(ps):
    assert all(isprime(p) and p%12==1 for p in ps)
    E=[0]
    for p in ps:E.append(E[-1]+(p-1)//2)
    B=max(ps)+6;r,M=1,6
    for q in map(int,primerange(5,B+1)):
        if q in ps:
            i=ps.index(q);a=-E[i+1]%q
            assert all((2*(a+E[j]))%q not in (1,3) for j in range(len(ps)) if j!=i)
        else:
            a=next(a for a in range(q) if all((2*(a+g))%q not in (1,3) for g in E[:-1]))
        r+=M*((a-r)*pow(M,-1,q)%q);M*=q
    r+=M
    path=[r]
    for p in ps:
        u,v=2*r-2,r+2;w=(p-1)//2
        assert p<=r and (r+w)%p==0
        for n in range(v+1,v+w+1):
            g=gcd(n if n%2==0 else n-2,u-1 if n%2==0 else u+1)
            assert g==(p if n==v+w else 1)
        r+=w;path.append(r)
    print('CRT chain',ps,'ticks',sum((p-1)//2 for p in ps),'seed digits',len(str(path[0])),'relative offsets',[x-path[0] for x in path],flush=True)


def scan(R):
    a=spf_table(2*R+10);N=(R-7)//6+1
    pred=[[] for _ in range(N)];succ=[-1]*N;D=[0]*N
    for j,r in enumerate(range(7,R+1,6)):
        for p in factors(r,a):
            if p==r or p%12!=1:continue
            s=r-(p-1)//2
            if s<7:continue
            if step(2*s-2,s+2,a)!=((p-1)//2,p,-1):continue
            i=(s-7)//6
            assert succ[i]==-1 and i<j
            succ[i]=j;pred[j].append((i,p));D[j]+=1
    B=[1]*N;depth=[0]*N
    for j in range(N):
        B[j]+=sum(B[i] for i,p in pred[j]);depth[j]=max((depth[i]+1 for i,p in pred[j]),default=0)
    outdepth=[0]*N
    for i in range(N-1,-1,-1):
        if succ[i]>=0:outdepth[i]=1+outdepth[succ[i]]
    print('cap',R,'nodes',N,'edges',sum(D),'max D',max(D),'max full direct basin',max(B),'max depth',max(depth),'max basin r',7+6*B.index(max(B)),flush=True)
    i=outdepth.index(max(outdepth)); path=[7+6*i]
    while succ[i]>=0:i=succ[i];path.append(7+6*i)
    print('longest chain',path,'labels',[2*(y-x)+1 for x,y in zip(path,path[1:])],flush=True)
    print('forward chain length tail',[(h,sum(d>=h for d in outdepth)) for h in range(1,max(depth)+1)],flush=True)
    exact=[1]*N;cum=[1]*N;maximum=[0]*N
    for h in range(1, max(depth)+2):
        old=exact;exact=[sum(old[i] for i,p in edges) for edges in pred]
        for k in (1,2,3):
            assert sum(x**k for x in exact)**2<=sum(d**(2*k-1) for d in D)*sum(x**(2*k) for x in old)
        cum=[x+y for x,y in zip(cum,exact)]
        maximum=[max([D[j]]+[maximum[i] for i,p in edges]) for j,edges in enumerate(pred)]
        # The propagated maximum includes depth h-1; using h instead is also safe.
        assert sum(exact)==sum(d>=h for d in outdepth)
        assert all(c<=(h+1)*max(1,m)**h for c,m in zip(cum,maximum))
        for T in (13,61,257):
            high=[False]*N
            for _ in range(h):high=[any(p>=T or high[i] for i,p in edges) for edges in pred]
            assert sum(high)<=h*sum(p>=T for edges in pred for i,p in edges)
        print('depth',h,'exact paths',sum(exact),'max cumulative',max(cum),'sum cumulative',sum(cum),'sum squares',sum(x*x for x in cum),flush=True)
    assert cum==B
    print('full basin histogram',sorted(Counter(B).items()),flush=True)

def one_step_scan(R):
    from collections import defaultdict
    a=spf_table(4*R+10);dest=defaultdict(list);c=Counter();example={}
    for r in range(7,R+1,6):
        u,v=2*r-2,r+2;w,p,e=step(u,v,a)
        if p>r:continue
        U,V=u+p-1,v+w
        if U>2*R-2:continue
        d=2*V-U;assert d>=0
        if V%2==0:
            assert d%p==0 and d in (0,2*p,4*p)
            if d==4*p:assert p<=7
        else:
            assert (d-6)%p==0 and d in (6,6+2*p)
        if d not in (0,6):
            h=(d if V%2==0 else d-6)//2
            while h%2==0:h//=2
            assert h==p
        else:
            assert V%2==(d==6)
            n=U if d==0 else U+2
            assert n%p==0 and n//p>=4
            k=n//p-1;assert (p-7 if d==0 else p-1)<=4*k
        dest[U,V].append((r,p));c['edges']+=1
    for (U,V),orig in dest.items():
        d=2*V-U;c['states']+=1
        if d not in (0,6):assert len(orig)==1;c['nonsingular']+=1
        else:
            c[f'd{d}_states']+=1;c[f'd{d}_edges']+=len(orig)
            if len(orig)>1:c[f'd{d}_mergers']+=1
            if len(orig)>c[f'd{d}_max']:
                c[f'd{d}_max']=len(orig);example[d]=(U,V,orig)
    print('one step all arrivals',dict(c),'max examples',example,flush=True)

if __name__=='__main__':
    R=int(argv[1]) if len(argv)>1 else 1000000
    chain_construct((13,157,4093))
    scan(R)
    one_step_scan(R)


def strip_scan(cap,D):
    # Complete graph on envelope-valid states in a fixed deficit strip.
    # Cut the source label at u/2+1, so every pre-first-record edge is included
    # whenever both endpoints lie in the strip.
    a=spf_table(cap+10);L=D//2+1;N=(cap//2-5)*L
    pred=[[] for _ in range(N)];succ=[-1]*N;degree=[0]*N;valid=[False]*N
    def idx(u,d):return (u//2-6)*L+d//2
    def state(i):return (2*(i//L+6),2*(i%L))
    for u in range(12,cap+1,2):
        for d in range(0,min(D,u+2)+1,2):
            i=idx(u,d);valid[i]=True;v=(u+d)//2
            w,p,e=step(u,v,a);U=u+p-1;V=v+w;dd=2*V-U
            if p>u//2+1 or U>cap or not 0<=dd<=D:continue
            j=idx(U,dd);assert i<j
            c=0 if V%2==0 else 6
            assert (dd-c)%p==0
            if p>=max(17,2*D+2):
                assert dd==c and w>=p/4
                n=U if c==0 else U+2
                assert n%p==0 and n//p>=4
                assert (p-1)**2<=64*(u+1)
            succ[i]=j;pred[j].append((i,p));degree[j]+=1
    B=[int(b) for b in valid];exact=B[:]
    count=sum(valid);total=sum(degree)
    maxima=[]
    for h in range(1,4):
        old=exact;exact=[sum(old[i] for i,p in z) for z in pred]
        for k in (1,2,3):
            assert sum(x**k for x in exact)**2<=sum(d**(2*k-1) for d in degree)*sum(x**(2*k) for x in old)
        B=[x+y for x,y in zip(B,exact)]
        maxima.append((h,max(B),sum(B),sum(x*x for x in B)))
    high=sum(p>=max(17,2*D+2) for z in pred for i,p in z)
    print('strip',D,'cap',cap,'nodes',count,'edges',total,'high',high,'max incoming',max(degree),'max state',state(degree.index(max(degree))),'depth stats',maxima,flush=True)

if __name__=='__main__':
    for D in (6,24):strip_scan(100000,D)
