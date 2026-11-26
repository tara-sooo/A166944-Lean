"""Bounded-cofactor record rank-tail and all-scale CRT kernel checks.
Run: python min_primorial_rank_tail_audit.py 100000
Requires sibling min_primorial_record_supply_audit.py and SymPy.
"""
from collections import Counter
from math import gcd
from sys import argv
from min_primorial_record_supply_audit import spf_table, step, factors

def check_rank(rows, i, stats):
    u,v,p,w,e=rows[i]; k=(u-e)//p
    if not (3<=k<=19 and p>max(k,5)):return
    n=v+w; c=0 if e==1 else 2; a=(n-c)//p
    assert n==a*p+c and a%2==(e==-1)
    assert (k+1)//2<=a<=k-1
    if e==-1:assert a<=k-2
    assert w<=2*k
    Z=a*u-k*v
    assert Z==a*e+k*(w-c) and Z!=0
    C=2*(a+k); H=1+a+2*k; M=abs(Z)+C
    stats['bounded_cofactor']+=1;stats[f'cofactor_{k}']+=1
    if k==3:
        assert e==1 and a==2 and 2*(v+w)-(u+p-1)==0
        if i:assert rows[i-1][2]<=30
    for j in range(i-1,-1,-1):
        U,V,q,W,sgn=rows[j]
        assert (U+q-1,V+W)==(u,v)
        if v%2==0:
            assert Z%q==0
            if Z==0:stats['rank_hit']+=1;break
        else:
            assert (Z+C)%q==0 and (Z+C)%2==1
        assert q<=M
        Z0=a*U-k*V
        assert Z0==Z-a*(q-1)+k*W
        assert abs(Z0)+C<=H*M
        stats['rank_reverse_edges']+=1
        if j==0:stats['seed_reached']+=1
        u,v,Z,M=U,V,Z0,abs(Z0)+C

def check_kernel(labels, X, stats):
    # Exact finite accounting behind the bare CRT inequality; no numerical
    # attempt to check unknown asymptotic constants.
    ps=sorted(set(labels)); counts=Counter(p.bit_length()-1 for p in ps)
    if not ps:return
    tmin=1<<min(counts); tmax=1<<max(counts)
    raw=sum(min(p,q)/max(p,q) for p in ps for q in ps if p!=q)
    residual=sum(1/max(p,q) for p in ps for q in ps if p!=q)
    kernel=0.; error=0.
    for i,s in counts.items():
        for j,t in counts.items():
            kernel+=2*s*t*2.**(-abs(i-j))
            error+=s*t/(1<<max(i,j))
    assert raw<=kernel+1e-9 and residual<=error+1e-9
    stats['kernel_checks']+=1

def main(R):
    A=spf_table(4*R+10000);stats=Counter(); maxk=0; sample=None
    for seed in range(7,R+1,6):
        X=2*seed-2;u,v=X,seed+2;rows=[]; labels=[]
        while True:
            w,p,e=step(u,v,A);rows.append((u,v,p,w,e))
            assert len(rows)<100000
            check_rank(rows,len(rows)-1,stats)
            stats['events']+=1
            if p>seed:
                stats['first_records']+=1
                if p!=u+1:stats['non_doubling_records']+=1
                break
            if 2*w>p-1:
                fs=factors(u-1,A)+factors(u+1,A)
                assert all(2*q>=w for q in fs)
                assert (p-1)**2<16*(u+1)
                stats['upward_checks']+=1
                if p>=7:labels.append(p)
            u+=p-1;v+=w
        check_kernel(labels,X,stats)
        idx=[i for i,(u,v,p,w,e) in enumerate(rows[:-1]) if p>=7 and 2*w>p-1]
        G=[0]
        for _,_,p,_,_ in rows:G.append(G[-1]+p-1)
        types=set(); count=Counter()
        for i,j in zip(idx,idx[1:]):
            u,v,p,w,e=rows[i];U,V,q,W,f=rows[j]
            E=U-u-(p-1);assert E==G[j]-G[i+1]
            if 2*E<=min(p,q):
                assert p!=q
                D=U-u;x0=e+p*((f-D-e)*pow(p,-1,q)%q)
                if x0%2:x0+=p*q
                assert (u-x0)%(2*p*q)==0
                types.add((p,q));count[p,q,E,e,f]+=1
                stats['upward_short_pairs']+=1
        stats['ordered_types']+=len(types)
        for (p,q,E,e,f),n in count.items():
            assert n<=1+(rows[-1][0]-X)//(2*p*q)
            stats['fixed_tuple_checks']+=1
    # Independent envelope-valid local controls (not asserted reset-reachable).
    for p in (17,31,101,1009):
        u=3*p+1
        for w in range(1,7):
            v=2*p-w
            a=spf_table(u+10)
            if step(u,v,a)==(w,p,1):
                stats['local_cofactor3']+=1
                check_rank([(u,v,p,w,1)],0,stats)
                if sample is None:sample=(u,v,p,w)
    print(dict(stats)); print('local cofactor-3 example',sample)
if __name__=='__main__':main(int(argv[1]) if len(argv)>1 else 100000)
