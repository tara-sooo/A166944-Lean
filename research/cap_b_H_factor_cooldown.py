#!/usr/bin/env python3
"""Exact first-hit factor sieve, H split, and shared-divisor cooldown.

Python 3 stdlib only. Concrete finite audits, NOT a proof of general Cap B.
"""
from math import gcd

M_MAX=2_860_771
THRESHOLD=45_895_573
THRESHOLD_EVENTS=((2,5),(1,3),(106,73),(15,19),(147,151),(34,53),
(4,3),(3,5),(3,3),(30,17),(6,3),(3,77),(3,3),(8,5),(4,3),
(4,23),(2,3),(10,5),(2,3),(7,13),(2,7),(2,11),(1,3),
(90,47),(6,3),(3,13),(338,229),(19,31),(3,7),(7,5),
(2,3),(68,83),(4,3),(2,53),(4,3),(11,977),(1,3))

def factors(n):
    assert n>=1
    out=[]
    if n%2==0:
        out.append(2)
        while n%2==0:n//=2
    p=3
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=2
    if n>1:out.append(n)
    return out

def d_at(n,C):
    return gcd(n,C-1) if n%2==0 else gcd(n-2,C+1)

def next_first_hit(s,C):
    # Even hits: r == 0 mod 2p for p|C-1.
    # Odd hits: r == p+2 mod 2p for p|C+1.
    candidates=[]
    for p in factors(C-1):
        r=2*p*(s//(2*p)+1)
        if r<=C:candidates.append(r)
    for p in factors(C+1):
        a=p+2
        r=a+2*p*((s-a)//(2*p)+1)
        if r<=C:candidates.append(r)
    if not candidates:return None
    r=min(candidates)
    e=d_at(r,C)
    assert e>1
    return r,e

def replay(M,expected=None):
    s=M+2;C=2*M-2;K=(7*M-1)//4
    events=[];Hs=Hl=0;up=down=0
    while s<K:
        hit=next_first_hit(s,C)
        if hit is None or hit[0]>K:break
        r,e=hit;g=r-s
        if expected is not None:assert (g,e)==expected[len(events)]
        assert r<=C and d_at(r,C)==e
        assert all(d_at(j,C)==1 for j in range(s+1,r))
        if e-1<3*(g+1):
            if g<=10:
                assert e<=33
                Hs+=e-1
            else:
                assert factors(e)==[e]
                assert (e-4)*e<6*(C+1)
                assert C%30 in (0,12,18)
                Hl+=e-1
                if 2*g<e-1:down+=e-1
                else:up+=e-1
        events.append((s,C,r,e,g))
        s=r;C+=e-1
        assert len(events)<5000
    if expected is not None:assert len(events)==len(expected)
    assert all(3<=e<=M for _,_,_,e,_ in events)
    G=C-(2*M-2);T=s-(M+2)
    assert G==2*T+6-(2*s-C)
    return dict(M=M,K=K,events=events,Hshort=Hs,Hlong=Hl,
                H=Hs+Hl,G=G,T=T,s=s,C=C,up=up,down=down)

def verify_cooldown(x):
    E=x['events'];checks=0
    for i,(_,C1,r1,e1,g1) in enumerate(E):
        for j in range(i+1,len(E)):
            _,C2,r2,e2,g2=E[j]
            q=gcd(e1,e2)
            if q<5:continue
            sig1=1 if r1%2==0 else -1
            sig2=1 if r2%2==0 else -1
            middle=C2-C1-(e1-1)
            assert middle>=q+1+sig2-sig1,(x['M'],i,j,q,middle)
            assert (middle-1-sig2+sig1)%q==0
            checks+=1
    ds={q for _,_,_,e,_ in E for q in range(5,e+1,2) if e%q==0}
    for q in ds:
        k=sum(e%q==0 for _,_,_,e,_ in E)
        if k>=2:assert x['G'] >= (2*k-1)*q-3
    return checks

def authentic_records(limit):
    D=2;record=1;out=[]
    for n in range(3,limit+3):
        e=d_at(n,D);D+=e-1
        if e>record:
            record=e
            assert n==record+2 and D==2*record-2
            if 7<=record<=limit:out.append(record)
    return out

CYCLE=((10,19),(10,13),(10,13),(10,5),(5,3),
       (10,13),(10,19),(10,11),(6,3),(9,13),
       (10,5),(5,3),(9,7),(9,5),(6,3),
       (6,11),(6,3),(9,5),(3,3),(7,13),
       (10,7),(10,13),(10,13),(10,19),(10,13))
def check_spurious_cycle():
    s,C=147,192
    for g,e in CYCLE:
        r=s+g
        assert r<=C and g<=10 and e-1<3*(g+1)
        assert all(gcd(d_at(j,C),210)==1 for j in range(s+1,r))
        assert gcd(d_at(r,C),210)==gcd(e,210)
        s=r;C+=e-1
    assert (s,C)==(357,402) and 2*s-C==312
    assert CYCLE[1][1]==CYCLE[2][1]==13
    # Two successive e=13 would require 0 >= 13-1: impossible.
    print("PASS: 25-event mod-210 fake cycle; T=G=210, offset +210; exact e=13 cooldown rejects it")

def main():
    records=authentic_records(M_MAX)
    assert records==[7,13,43,139,313,661,1321,2659,5419,
                    10891,22039,44383,88801,177841,355723,
                    713833,1427749,2860771]
    checks=0
    for M in records:
        x=replay(M);checks+=verify_cooldown(x)
        print(f"M={M:>9} events={len(x['events']):>3} "
              f"Hshort={x['Hshort']:>5} Hlong={x['Hlong']:>5} "
              f"H={x['H']:>5} G={x['G']:>5}")
    threshold=replay(THRESHOLD,THRESHOLD_EVENTS)
    checks+=verify_cooldown(threshold)
    assert (threshold['Hshort'],threshold['Hlong'],
            threshold['H'],threshold['G'],threshold['C'])==(72,694,766,1914,91_793_058)
    assert (threshold['up'],threshold['down'])==(694,0)
    big=replay(5_875_882_249)
    checks+=verify_cooldown(big)
    assert (len(big['events']),big['Hshort'],big['Hlong'],big['H'],big['G'])==(
            26,72,30298,30370,30564)
    assert (big['up'],big['down'])==(30196,102)
    print("PASS: 18 authentic low records, 37-event threshold replay, 26-event big record-form replay")
    print("PASS: every shared-gcd cooldown, pair phase, and q-frequency bound checked; pairs=",checks)
    check_spurious_cycle()
    print("Global H bound and Cap B remain OPEN.")

if __name__=="__main__":main()
