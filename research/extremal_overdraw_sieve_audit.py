#!/usr/bin/env python3
"""A166944 overdraw roughness and 210-potential classification certificate.

Python 3 standard library only. Not a Lean proof or twin-prime proof.
"""
from fractions import Fraction
from math import gcd, isqrt

W = 210
STATES = [(s, c) for s in range(W) for c in range(0, W, 2)]
INDEX = {x: i for i, x in enumerate(STATES)}
INERT = {c for c in range(0, W, 2) if gcd(c-1,W)==gcd(c+1,W)==1}
EXPECTED = {
    11: {10,22,24,26,28,34,36,40,64,100,104,106},
    13: {20,22,36,64,100},
    17: set(),
    19: set(),
}


def clipped(s,c):
    for g in range(1,15):
        r=s+g
        e=gcd(gcd(r if r%2==0 else r-2,c-1 if r%2==0 else c+1),W)
        if e>1:
            return g,e
    return None


def potential():
    edges=[]
    for s,c in STATES:
        h=clipped(s,c)
        if h is None:
            continue
        gap,e0=h
        for e in (e0,)+tuple(z for z in (9,25,27,33) if gcd(z,W)==e0):
            edges.append((INDEX[(s,c)],INDEX[((s+gap)%W,(c+e-1)%W)],gap-(e-1)))
    V=[0]*len(STATES)
    for iteration in range(1,100):
        nxt=V.copy()
        for src,dst,w in edges:
            nxt[src]=max(nxt[src],w+V[dst])
        if nxt==V:
            break
        V=nxt
    assert (len(STATES),len(edges),iteration,max(V))==(22050,58232,19,29)
    assert all(w+V[dst]<=V[src] for src,dst,w in edges)
    return V


def classify_small_primes(V):
    for p,expected in EXPECTED.items():
        residues=set()
        total=0
        max_signed=-100
        for i,(s,c) in enumerate(STATES):
            if c in INERT:
                continue
            h=clipped(s,c)
            assert h is not None
            for g in range(1,min(2*p,h[0]-1)+1):
                va=V[INDEX[((s+g)%W,(c+p-1)%W)]]
                eta_signed=g+va-V[i]-2*(p-1)
                max_signed=max(max_signed,eta_signed)
                if eta_signed>0:
                    residues.add(c)
                    total+=1
        assert residues==expected, (p,residues)
        assert (p<17 or max_signed<=0)
        print("p",p,"noninert C residues",len(residues),
              "candidate triples",total,"largest signed overdraw",max_signed)
    assert 13+29<2*(23-1)
    print("All prime increments p>=17 with positive overdraw have inert C mod 210.")


def primes(B):
    return [q for q in range(3,B+1,2)
            if all(q%j for j in range(2,isqrt(q)+1))]


def check_rough_crt():
    for B in (3,5,7,11,13):
        P=R=1
        for q in primes(B):
            P*=q
            R*=q-2
        rho=Fraction(R,P)
        assert sum(gcd((2*t-1)*(2*t+1),P)==1 for t in range(P))==R
        for start in (0,1,37,P//3):
            for length in (1,7,P//2,P+1,2*P+3):
                actual=sum(gcd((2*t-1)*(2*t+1),P)==1
                           for t in range(start,start+length))
                assert actual<=rho*length+R
        print("q <=",B,"period",P,"allowed",R,"density",rho)
    assert len(INERT)==15
    coefficient=Fraction(1,14)+Fraction(12,105*11)+Fraction(5,105*13)
    assert coefficient==Fraction(2567,30030)
    print("Universal H <= 2567/30030 G + 49; coefficient",float(coefficient))


def isprime(n):
    return n>1 and all(n%q for q in range(2,isqrt(n)+1))


def hit(n,C):
    return gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)


def overdraw(s,C,r,Cpre,p,V):
    vb=V[INDEX[(s%210,C%210)]]
    va=V[INDEX[(r%210,(Cpre+p-1)%210)]]
    g=r-s
    return g,max(0,g+va-vb-2*(p-1))


def original_prefix(V,limit=2_500_000):
    D=1
    prev_s=prev_C=2
    events=0
    excess=[]
    for n in range(2,limit+1):
        e=hit(n,D)
        if e>1:
            events+=1
            if n>=3 and e>=11 and isprime(e):
                g,eta=overdraw(prev_s,prev_C,n,D,e,V)
                if eta:
                    assert 2*e-30<=g<=2*e
                    if e>=17:
                        assert D%W in INERT
                    for q in primes(e-16):
                        assert (D*D-1)%q!=0
                    excess.append((n,e,g,eta))
            prev_s,prev_C=n,D+e-1
        D+=e-1
    assert (events,D)==(250,2_860_770)
    assert excess==[(22321,11,13,2),(22357,17,31,2),
                    (88849,11,19,2),(88868,13,14,6),
                    (1429573,11,19,2),(1431003,11,20,1)]
    assert len(excess)<=Fraction(2567,30030)*(D-2)+49
    print("Original recurrence",limit,"events",events,"overdraw",len(excess),
          "D",D, "excess",excess)


def canonical_45895573(V):
    M=45_895_573
    s,C=M+2,2*M-2
    excess=[]
    for _ in range(37):
        for r in range(s+1,C+1):
            e=hit(r,C)
            if e>1:
                break
        else:
            raise AssertionError("unexpected quiet exit")
        if e>=11 and isprime(e):
            g,eta=overdraw(s,C,r,C,e,V)
            if eta:
                excess.append((r,e,g,eta))
        s,C=r,C+e-1
    assert (s,C)==(45_896_532,91_793_058)
    assert isprime(C-1) and isprime(C+1)
    assert excess==[(45_895_920,17,30,8),(45_896_064,47,90,2)]
    G=C-(2*M-2)
    assert len(excess)<=Fraction(2567,30030)*G+49
    print("Official M",M,"G",G,"H",len(excess),"exception events",excess)


if __name__=="__main__":
    V=potential()
    classify_small_primes(V)
    check_rough_crt()
    original_prefix(V)
    canonical_45895573(V)
    print("PASS: finite certificates only, no global twin-prime proof")
