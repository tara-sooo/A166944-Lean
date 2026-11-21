#!/usr/bin/env python3
"""Mod-210 fake cycle passes immediate shared-gcd tests but fails nonlocal phase.
Finite arithmetic only. NOT an actual first-gcd path or a Cap B proof.
"""
from math import gcd
STEPS=((10,7),(7,13),(10,19),(10,13),(10,11),
       (5,3),(9,13),(10,5),(5,3),(10,13),
       (10,19),(10,11),(6,3),(9,13),(10,5),
       (5,3),(9,7),(9,5),(6,9),(8,13),
       (10,7),(6,5),(6,3),(10,19),(10,13))

def d(n,C):
    return gcd(n,C-1) if n%2==0 else gcd(n-2,C+1)

def main():
    s,C=116,162
    events=[]
    previous=None
    for g,e in STEPS:
        r=s+g
        assert r<=C and g<=10 and e-1<3*(g+1) and g<=2*e
        assert all(gcd(d(n,C),210)==1 for n in range(s+1,r))
        assert gcd(d(r,C),210)==gcd(e,210)
        if previous is not None:
            q=gcd(previous,e)
            assert q in (1,3)
            if q==3:assert g==1
        events.append((s,C,r,g,e))
        previous=e
        s=r
        C+=e-1
    assert (s,C)==(326,372) and (s-116,C-162)==(210,210)
    assert 2*116-162==70 and 2*s-C==280
    first,later=events[1],events[3]
    assert (first[4],later[4])==(13,13)
    assert first[2]%2==later[2]%2==1
    H=later[1]-first[1]-(first[4]-1)
    assert H==18 and H%13!=1
    print("PASS: 25 clipped first hits and all adjacent-gcd tests")
    print("PASS: T=G=210, offset 70 -> 280")
    print("NONLOCAL FAIL: q=13 at events 2 and 4 requires H == 1 mod 13; H=18")
    print("NOT a true gcd trajectory. Cap B remains OPEN.")

if __name__=="__main__":main()
