"""Mixed-scale consecutive descent accounting (finite audit).
Run: python min_primorial_multiscale_relay_audit.py 100000
Requires the sibling record-supply audit and SymPy.
"""
from collections import Counter
from sys import argv
from sympy import primerange
from min_primorial_record_supply_audit import spf_table, step

def audit(R):
    a=spf_table(4*R+10000)
    ell_list=tuple(map(int,primerange(7,400)))
    c=Counter(); worst=(0,1,None)
    for seed in range(7,R+1,6):
        u,v=2*seed-2,seed+2; rows=[]; pref=[0]
        while True:
            w,p,e=step(u,v,a)
            if p>seed:break
            rows.append((u,p,e,w));pref.append(pref[-1]+p-1)
            u+=p-1;v+=w
            assert len(rows)<100000
        c['seeds']+=1;c['events']+=len(rows)
        # Full set and every other band: both are unions of disjoint bands.
        for parity in (None,0,1):
            idx=[i for i,(_,p,_,w) in enumerate(rows)
                 if p>=8 and w>=p and (parity is None or (p.bit_length()-1)%2==parity)]
            bands=sorted({rows[i][1].bit_length()-1 for i in idx})
            mass={j:sum(rows[i][1]-1 for i in idx if rows[i][1].bit_length()-1==j) for j in bands}
            R0=pref[-1]-sum(mass.values());lower=0
            for j in bands:
                T=1<<j; I=[i for i in idx if rows[i][1]>=T]
                g=[rows[i][1]-1 for i in I]
                W=sum(min(x,y) for x,y in zip(g,g[1:]));V=sum(abs(x-y) for x,y in zip(g,g[1:]))
                assert 2*W==2*sum(g)-g[0]-g[-1]-V
                Rj=sum(pref[b]-pref[a0+1] for a0,b in zip(I,I[1:]))
                assert Rj==pref[I[-1]]-pref[I[0]]-sum(g[:-1])
                assert Rj<=R0+lower
                assert mass[j]<=3*W+2*T
                c['suffixes']+=1;c['pairs']+=len(I)-1
                Ws={d:0 for d in (2,8,32)};Ls={d:0 for d in Ws}
                for i,k in zip(I,I[1:]):
                    x,p,e,w=rows[i];y,q,f,z=rows[k];E=y-x-(p-1);m=min(p,q)
                    assert E==pref[k]-pref[i+1] and E>=0 and E%2==0
                    if p.bit_length()!=q.bit_length():c['mixed_pairs']+=1
                    if max(p,q)>=4*m:c['ratio_ge_4']+=1
                    if p==q:assert E>=p-1;c['repeat']+=1
                    for den in Ws:
                        if den*E<=m:
                            assert p!=q
                            Ws[den]+=m-1;c['short_checks']+=1
                        else:
                            Ls[den]+=m-1;assert m-1<=den*E
                    if 2*E<=m:
                        D=y-x;assert x%p==e%p and y%q==f%q
                        # Exact unique even CRT class for any scales.
                        x0=e+p*((f-D-e)*pow(p,-1,q)%q)
                        if x0%2:x0+=p*q
                        assert (x-x0)%(2*p*q)==0
                        for ell in ell_list:
                            if 2*ell>=m:break
                            assert all(n%ell for n in (x-1,x+1,y-1,y+1))
                            nu=2*(D%ell==0)+((D-2)%ell==0)+((D+2)%ell==0)
                            assert len({1%ell,-1%ell,(1-D)%ell,(-1-D)%ell})==4-nu
                            c['rough_checks']+=1
                for den in Ws:
                    assert Ws[den]+Ls[den]==W and Ls[den]<=den*Rj
                    c['budget_checks']+=1
                if sum(g)>0 and W*worst[1]>worst[0]*sum(g):worst=(W,sum(g),(seed,parity,j))
                lower+=mass[j]
    print('seed cap',R,dict(c));print('largest W/marked gain',worst)
if __name__=='__main__':audit(int(argv[1]) if len(argv)>1 else 100000)
