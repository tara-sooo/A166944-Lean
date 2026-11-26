"""Growing-depth transport and singular-free excursions in a strip.
Run: python min_primorial_growing_depth_audit.py 20000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
"""
from math import prod
from sys import argv
from sympy import primerange
from min_primorial_record_supply_audit import spf_table, factors, step


def audit(cap,D):
    L=D//2+1; B=max(3,D//2); Q=2*prod(primerange(3,B+1))
    a=spf_table(cap+10); N=(cap//2-5)*L
    valid=[False]*N; singular=[False]*N; pred=[[] for _ in range(N)]; succ=[-1]*N
    def idx(u,d):return (u//2-6)*L+d//2
    def state(i):return 2*(i//L+6),2*(i%L)
    for u in range(12,cap+1,2):
        for d in range(0,min(D,u+2)+1,2):
            i=idx(u,d);valid[i]=True;v=(u+d)//2
            c=0 if v%2==0 else 6
            singular[i]=d==c
            w,p,e=step(u,v,a);U=u+p-1;V=v+w;dd=2*V-U
            if p>u//2+1 or U>cap or not 0<=dd<=D:continue
            j=idx(U,dd);assert j>i
            pred[j].append(i);succ[i]=j
            c=0 if V%2==0 else 6
            assert (dd-c)%(2*p)==0
            if dd!=c:assert p<=B
    degree=list(map(len,pred));run=[0]*N;span=[0]*N
    for j in range(N):
        if not valid[j]:continue
        u,d=state(j);v=(u+d)//2;c=0 if v%2==0 else 6
        n=u+c//3 if d==c else abs(d-c)//2
        while n%2==0:n//=2
        assert degree[j]<=L*len(factors(n,a))
        if singular[j]:continue
        for i in pred[j]:
            x,_=state(i);run[j]=max(run[j],run[i]+1);span[j]=max(span[j],span[i]+u-x)
        assert run[j]<=Q//2 and span[j]<=Q
    # Exact forward reachability within h steps versus first-bad charging.
    cases=0; largest=0
    for M in (2,4,8,16):
        bad=[d>M for d in degree]; badmass=sum(1+d for d,b in zip(degree,bad) if b)
        sets=[bad,[v and i%97==0 for i,v in enumerate(valid)],singular]
        for S in sets:
            cur=S[:]; good=[s and not b for s,b in zip(S,bad)]; firstbad=bad[:]
            for h in range(1,9):
                cur=[b or (j>=0 and cur[j]) for b,j in zip(cur,succ)]
                good=[(not bad[i]) and (S[i] or (j>=0 and good[j])) for i,j in enumerate(succ)]
                firstbad=[b or (j>=0 and firstbad[j]) for b,j in zip(firstbad,succ)]
                assert sum(good)<=sum(S)*(h+1)*M**h
                assert sum(firstbad)<=(h+1)*M**(h-1)*badmass
                assert all(not x or g or b for x,g,b in zip(cur,good,firstbad))
                assert sum(cur)<=(h+1)*M**h*sum(S)+(h+1)*M**(h-1)*badmass
                cases+=1;largest=max(largest,sum(cur))
    print('strip',D,'cap',cap,'vertices',sum(valid),'edges',sum(degree),'max indegree',max(degree),'Q',Q,'max nonsingular run',max(run),'max nonsingular span',max(span),'transport cases',cases,'max origins',largest,flush=True)

if __name__=='__main__':
    cap=int(argv[1]) if len(argv)>1 else 20000
    for D in (6,12,24):audit(cap,D)
