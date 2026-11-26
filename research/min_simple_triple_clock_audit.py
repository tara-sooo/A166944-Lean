"""Three-point roughness and return-word audit. Standard library only.
Run: python min_simple_triple_clock_audit.py 1000 10000 100000 1000000
"""
from collections import defaultdict, Counter
from math import log, gcd
from functools import lru_cache
import sys
from min_simple_crossing_audit import spf, factors, clock


def density_controls():
    checks=0
    for ell in (11,13,17,19,23):
        for p in (17,19,29,31,43,47):
            for E in (0,2,6):
                for F in (0,2,8):
                    for f in (-1,1):
                        D=p-1+E
                        C={(D-f-1)%ell,(D-f+1)%ell,(-f-1)%ell,(-f+1)%ell}
                        H={(-F-f)%ell,(2-F-f)%ell}
                        nu=2*(D%ell==0)+((D-2)%ell==0)+((D+2)%ell==0)
                        assert len(C)==4-nu and len(H)==2
                        overlap=len(C&H)
                        predicted=ell+(len(C)+2)*(ell-1)-2*len(C)+overlap
                        literal=sum(r==0 or r*s%ell in C or r*(s+1)%ell in H
                                    for r in range(ell) for s in range(ell))
                        assert predicted==literal
                        checks+=1
    print('exact local seven-condition densities:',checks)


def audit(R):
    a=spf(2*R+1)
    @lru_cache(None)
    def step(u,v):
        fs,gs=factors(u-1,a),factors(u+1,a)
        if fs==[u-1] and gs==[u+1]:return None
        q=min(fs[0],gs[0]);w,p=clock(u,v,[(p,0) for p in fs]+[(p,p+2) for p in gs])
        n=v+w;e=1 if n%2==0 else -1
        assert (u-e)%p==0 and n%(2*p)==(0 if e==1 else p+2)
        assert w<=2*q
        return u,p,e,w,n,q
    stats=Counter(); bands=defaultdict(Counter); unique=set(); returns=set(); controls=set()
    for X in range(6*((R+5)//6),3*R//2+1,6):
        stats['origins']+=1;u,v=X,X//2+3; by=defaultdict(list)
        while u<2*R:
            s=step(u,v)
            if s is None:break
            x,p,e,w,n,q=s;assert x==u
            stats['wait']+=w;stats['events']+=1
            T=1<<(p.bit_length()-1)
            if T>=8:by[T].append(s)
            u,v=u+p-1,n
        for T,ss in by.items():
            # Asymptotic cutoff and larger finite diagnostic cutoff.
            B=min((T-4)//4,max(1,int(log(T)**.25)))
            Bcontrol=min(8,(T-4)//4)
            for i in range(len(ss)-2):
                x,p,e,w,n,q=ss[i];y,r,f,W,N,Q=ss[i+1];z,t,g,V,L,S=ss[i+2]
                E=y-x-p+1;F=z-y-r+1
                assert E>=0 and F>=0 and E%2==F%2==0
                if E>Bcontrol or F>Bcontrol:continue
                assert p!=r and r!=t
                D=p-1+E; aa=E+e-1-f; s=(y-f)//r
                assert aa%p and (r*s-aa)%p==0
                assert y==r*s+f and z==y+r-1+F
                # Clock congruences for prescribed elapsed time.
                tau=N-n;c0=0 if e==1 else p+2;c1=0 if f==1 else r+2
                assert 1<=tau<=3*E+2*r
                assert (c1-tau-c0)%2==0
                k=((c1-tau-c0)//2*pow(p,-1,r))%r
                residue=(c0+2*p*k)%(2*p*r)
                assert n%(2*p*r)==residue
                if len(controls)<10000:controls.add((p,r,e,f,E,F,tau,residue))
                bands[T]['short_triples_control']+=1
                if min(w,W,V)*2>=T:
                    bands[T]['long_wait_triples_control']+=1
                    unique.add((T,x,p,r,e,f,E,F))
                    # Check actual roughness exclusions at small sieve primes.
                    for ell in (11,13,17,19,23):
                        if 2*ell>=min(w,W,V) or ell>=T:continue
                        C={(D-f-1)%ell,(D-f+1)%ell,(-f-1)%ell,(-f+1)%ell}
                        H={(-F-f)%ell,(2-F-f)%ell}
                        assert r%ell and r*s%ell not in C and r*(s+1)%ell not in H
                if p==t:
                    c=2+g-e-E-F
                    assert c!=0 and c%2==0 and r==p+c
                    assert -2*Bcontrol<=c<=4
                    if E==F==0:assert r>p
                    if i+3<len(ss) and E==F==0:
                        z2,t2,*_=ss[i+3]
                        if z2-z-(t-1)==0:assert t2!=r
                    bands[T]['returns_control']+=1
                    bands[T]['return_wait_control']+=w+W+V
                    returns.add((T,x,p,r,e,f,g,E,F))
                    if E or F:bands[T]['returns_positive_relay']+=1
                    if E<=B and F<=B:
                        bands[T]['returns_theorem']+=1
                        bands[T]['return_wait_theorem']+=w+W+V
    print('R',R,'stats',dict(stats),'cached states',step.cache_info().currsize,'unique long-wait triple tuples',len(unique),'unique return tuples',len(returns),'clock controls',len(controls))
    for T,b in sorted(bands.items()):
        if b['short_triples_control']:print('band',T,dict(b))
    print('totals',dict(sum(bands.values(),Counter())))

if __name__=='__main__':
    density_controls()
    for R in map(int,sys.argv[1:] or ['1000','10000','100000','1000000']):audit(R)
