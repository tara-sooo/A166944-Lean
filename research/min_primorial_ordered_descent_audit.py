"""Exact local exclusions and ordered descent pairs on integer reset rays.
Run: python min_primorial_ordered_descent_audit.py [seed bound]
Requires sibling min_primorial_record_supply_audit.py and sympy.
Finite diagnostics only; the hyperbola and Selberg estimates are paper results.
"""
from collections import Counter
from itertools import product
from sys import argv
from sympy import primerange
from min_primorial_record_supply_audit import spf_table, step


def residues(p, e, f, E, ell):
    a = E + e - 1 - f
    b, c, d = p + a, p + a - 2*e, -2*f
    h = len({x % ell for x in (b,c,d)} - {0})
    rho = 2*ell-1+h*(ell-1)
    assert 1 <= h <= 3
    assert 3*ell-2 <= rho <= 5*ell-4
    deficiency=2*((p+E-1)%ell==0)+((p+E-3)%ell==0)+((p+E+1)%ell==0)
    assert h==3-deficiency
    D=p+E-1
    # With both labels fixed, pre-offset is on a CRT progression.
    # The four forbidden residues are +/-1 and -D +/-1.
    assert len({1%ell,-1%ell,(1-D)%ell,(-1-D)%ell})==4-deficiency
    return rho, (b,c,d)


def local_audit():
    cnt=Counter()
    for p in primerange(7, 80):
        p=int(p)
        for E,e,f,ell in product(range(0,p-3,2),(-1,1),(-1,1),(7,11,13,17,19)):
            if ell==p: continue
            rho,(b,c,d)=residues(p,e,f,E,ell)
            actual=sum(1 for x in range(ell) for y in range(ell)
                       if x==0 or y==0 or x*y%ell in (b%ell,c%ell,d%ell))
            assert actual==rho
            cnt['local_density']+=1
            cnt[f'h={(rho-(2*ell-1))//(ell-1)}']+=1
    for p in primerange(5,100):
        for e,f in product((-1,1),repeat=2):
            E=next(E for E in range(2*p+1) if E%2==0 and (E-(f-e+1))%p==0)
            assert E==p+(f-e+1) and E>=p-1
            cnt['repeat_minimum']+=1
    print('local',dict(cnt),flush=True)


def ray_audit(R):
    a=spf_table(4*R+10000)
    bands=(7,13,31,61,127,257)
    primes=tuple(map(int,primerange(7,max(bands)*3)))
    cnt=Counter(); byT={T:Counter() for T in bands}
    witnesses={}
    for r0 in range(7,R+1,6):
        cnt['seeds']+=1; u=2*r0-2; v=r0+2; last={}; m=0
        while True:
            w,p,e=step(u,v,a)
            if p>r0:break
            cnt['events']+=1
            if w>=p:
                cnt['descents']+=1
                for T in bands:
                    if not T<=p<=6*T:continue
                    byT[T]['band_events']+=1
                    prev=last.get(T)
                    if prev is not None:
                        x,P,eps,W=prev
                        E=u-x-(P-1)
                        assert E>=0 and E%2==0
                        byT[T]['pairs']+=1
                        if P==p:
                            assert E>=p-1
                            byT[T]['repeats']+=1
                        if E<T-3:
                            byT[T]['short']+=1
                            if E==0:byT[T]['zero']+=1
                            assert P!=p
                            sh=E+eps-1-e
                            assert sh%2 and abs(sh)<P
                            q=(x-eps)//P; s=(u-e)//p
                            assert p*s==P*(q+1)+sh
                            for ell in primes:
                                if 2*ell>=T:break
                                rho,(b,c,d)=residues(P,eps,e,E,ell)
                                assert p%ell and s%ell
                                assert (p*s)%ell not in (b%ell,c%ell,d%ell)
                                byT[T]['exclusion_checks']+=1
                            witnesses.setdefault(T,(r0,x,P,W,u,p,w,E))
                    last[T]=(u,p,e,w)
            u+=p-1;v+=w;m+=1
            assert m<100000
    print('rays',dict(cnt))
    for T in bands:print('band',T,dict(byT[T]),'first short pair',witnesses.get(T))

if __name__=='__main__':
    local_audit();ray_audit(int(argv[1]) if len(argv)>1 else 100000)
