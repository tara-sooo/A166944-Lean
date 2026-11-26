"""Periodic low-label terminal maps and two large departures.
Run: python min_primorial_periodic_relay_audit.py 100000
Requires SymPy and sibling min_primorial_record_supply_audit.py.
Finite checks of deterministic terminal maps, not asymptotic sieve bounds.
"""
from collections import Counter
from functools import lru_cache
from math import prod
from sys import argv
from sympy import primerange
from min_primorial_record_supply_audit import spf_table, factors, step


def terminal_map(B):
    ps=tuple(map(int,primerange(3,B+1))); Q=2*prod(ps)
    @lru_cache(None)
    def terminal(a,b):
        assert 0<=a<Q and 0<=b<Q
        u,v=a,b; m=0
        while True:
            clocks=[(((0 if e==1 else p+2)-v)%(2*p) or 2*p,p,e)
                    for p in ps for e in (1,-1) if (u-e)%p==0]
            if not clocks:break
            w,p,e=min(clocks);u+=p-1;v+=w;m+=1
            assert u<=Q and m<=Q//2
        return u-a,v-b,m
    return Q,terminal


def audit(cap):
    a=spf_table(4*cap+10000)
    for B in (3,5,7,11,19):
        Q,terminal=terminal_map(B); R=2*Q; T=max(17,8*B+8)
        c=Counter(); maxrelay=(0,None); maxprefix=(0,None)
        for seed in range(7,cap+1,6):
            X=2*seed-2; u,v=X,seed+2; start=(u,v); first=None; previous=None; small=0
            c['seeds']+=1
            while True:
                w,p,e=step(u,v,a)
                if p>seed:break
                if p<=B:
                    small+=1;u+=p-1;v+=w;continue
                c['large_events']+=1
                x,t=start; E=u-x
                assert E<=Q and E%2==0
                if w>2*B:
                    du,dv,m=terminal(x%Q,t%Q)
                    assert (du,dv,m)==(u-x,v-t,small)
                    assert terminal((x+3*R)%Q,(t+3*Q)%Q)==(du,dv,m)
                    c['terminal_matches']+=1
                strong=p>=T and 4*w>=p and w>2*B
                if strong:
                    c['strong_departures']+=1
                    assert all(8*q>=p for q in factors(u-1,a)+factors(u+1,a))
                    assert p*p<=64*(u+1)
                    if first is None:
                        c['first_strong']+=1
                        assert start==(X,seed+2)
                        assert terminal((X%R)%Q,((X%R)//2+3)%Q)[0]==u-X
                        if E>maxprefix[0]:maxprefix=(E,(seed,u,p,small))
                    if previous is not None:
                        z,P,sign,origin,arrival,ok=previous
                        if ok:
                            U,V=arrival;cc=0 if sign==1 else 6
                            assert 2*V-U==cc
                            D=u-z;relay=D-P+1
                            assert relay==E and relay<=Q
                            # Once source residue and first label/sign are fixed,
                            # the entire relay is determined, including its duration.
                            A=(z+P-1)%R
                            assert terminal(A%Q,(A//2+cc//2)%Q)==(relay,v-V,small)
                            k=(z-sign)//P
                            assert z==P*k+sign
                            for ell in map(int,primerange(7,(min(P,p)-1)//8+1)):
                                assert k*(P*k+2*sign)*(P*k+sign+D-1)*(P*k+sign+D+1)%ell
                                c['four_form_checks']+=1
                            c['strong_pairs']+=1
                            if relay>maxrelay[0]:maxrelay=(relay,(seed,z,P,u,p,small))
                if first is None:first=(u,p)
                U,V=u+p-1,v+w;cc=0 if e==1 else 6
                previous=(u,p,e,start,(U,V),strong and 2*V-U==cc)
                start=(U,V);small=0;u,v=U,V
        print('B',B,'Q',Q,'T',T,dict(c),'max prefix',maxprefix,'max relay',maxrelay,flush=True)

if __name__=='__main__':audit(int(argv[1]) if len(argv)>1 else 100000)
