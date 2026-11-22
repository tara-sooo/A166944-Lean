#!/usr/bin/env python3
"""A166944 cross-key rainbow CRT audit; Python 3 stdlib only.

Calculates original parity-gcd events, validates all 2..5-key rainbow
patterns and checks a finite CRT prefix of an artificial five-hit word.
Does not prove Cap B or twin-prime infinitude.
"""
from math import gcd, isqrt, prod

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

def original_events(limit=2_500_000):
    C=1
    out=[]
    for n in range(2,limit+1):
        e=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
        if e>1:
            out.append((n,e,C,C+e-1))
            C+=e-1
    assert (len(out),C)==(250,2_860_770)
    return out

def audit_rainbows(events):
    pref=[0]
    for n,e,pre,post in events:
        pref.append(pref[-1]+e-1)
    stats={k:0 for k in range(2,6)}
    same_parity=0
    found_example=False
    for k in range(2,6):
        for i in range(len(events)-2*k+1):
            ps=[events[h][1] for h in range(i,i+k)]
            if min(ps)<5 or len(set(ps))!=k or not all(is_prime(p) for p in ps):
                continue
            for j in range(i+k,len(events)-k+1):
                if ps!=[events[h][1] for h in range(j,j+k)]:
                    continue
                T=pref[j+1]-pref[i+1]
                assert T==events[j][3]-events[i][3]
                residues=[]
                for a,p in enumerate(ps):
                    f,l=events[i+a],events[j+a]
                    assert l[3]-f[3]==T
                    c=(2 if f[0]%2 and not l[0]%2
                       else -2 if not f[0]%2 and l[0]%2 else 0)
                    assert (T-c)%p==0
                    residues.append(c)
                assert T>2 and (T*(T-2)*(T+2))%prod(ps)==0
                if not any(residues):
                    assert T%prod(ps)==0
                    same_parity+=1
                if all(events[h][1]%12==1 for h in range(i+1,j+1)):
                    assert T%12==0
                    P0=prod(p for p,c in zip(ps,residues) if c==0)
                    Ppos=prod(p for p,c in zip(ps,residues) if c==2)
                    Pneg=prod(p for p,c in zip(ps,residues) if c==-2)
                    assert T>=max(12*P0,10*Ppos+2,2*Pneg-2)
                stats[k]+=1
                if k==2 and ps==[7,11] and T==5544:
                    assert [events[h][0] for h in (i,i+1,j,j+1)]==[2674,2675,5474,5491]
                    assert [events[h][3] for h in (i,i+1,j,j+1)]==[5334,5344,10878,10888]
                    assert T==72*7*11
                    found_example=True
    assert stats=={2:41,3:0,4:0,5:0}
    assert same_parity==17 and found_example
    print("Original sequence: 250 events; rainbow counts",stats,
          "same-parity pairs",same_parity)
    print("Witness: (7,11,...,7,11), T=5544=72*(7*11)")

def crt_step(x, modulus, residue, prime):
    assert gcd(modulus,prime)==1
    j=((residue-x)*pow(modulus,-1,prime))%prime
    return x+modulus*j,modulus*prime

def audit_synthetic_crt():
    p,q,r=421,2521,2_228_813_161
    assert all(is_prime(v) and v%420==1 for v in (p,q,r))
    word=[p,q,r,p,q]
    shifts=[0]
    for e in word[:-1]:
        shifts.append(shifts[-1]+e-1)
    T=(p-1)+(q-1)+(r-1)
    assert T==2_228_816_100 and T%(12*p*q)==0
    c0_mod={p:-1,q:-p,r:1-p-q}
    selected={p:[0,3],q:[1,4],r:[2]}
    for f,desired in selected.items():
        times=[i for i,d in enumerate(shifts)
               if (c0_mod[f]+d)%f in (1,f-1)]
        assert times==desired
        assert all((c0_mod[f]+shifts[i])%f==f-1 for i in times)
    assert all((e-1)%420==0 for e in word)
    # For every unselected ell>=11, exactly 5 horizons forbid at most
    # 10 out of ell residues. The full finite CRT therefore exists.
    # Instantiate and verify a small-prime prefix of that construction.
    x,m=0,420
    for f in (p,q,r):
        x,m=crt_step(x,m,c0_mod[f]%f,f)
    for f in range(11,1001,2):
        if f in (p,q,r) or not is_prime(f):
            continue
        choice=next((v for v in range(f)
                     if all((v+d)%f not in (1,f-1) for d in shifts)),None)
        assert choice is not None
        x,m=crt_step(x,m,choice,f)
    assert x%420==0
    for f,desired in selected.items():
        assert all((x+shifts[i])%f==f-1 for i in desired)
    s=(x+6)//2
    assert s%2==1 and 2*s-6==x
    print("Artificial p,q,r,p,q CRT prime clocks:",(p,q,r),
          "T/(12pq)=",T//(12*p*q),
          "partial modulus bits=",m.bit_length())
    print("Unselected ell up to r+6 follow by the <=10 forbidden-residue argument")

if __name__=="__main__":
    audit_rainbows(original_events())
    audit_synthetic_crt()
    print("PASS: finite CRT/rainbow audits; global theorem still open")
