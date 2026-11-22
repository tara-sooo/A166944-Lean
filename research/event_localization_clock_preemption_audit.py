#!/usr/bin/env python3
"""A166944 clock preemption/localization finite exact verifier. Python stdlib.
No claim of universal event localization, Cap B or twin-prime infinitude.
"""
from math import gcd, isqrt, sqrt

def factors(n):
    assert n >= 1
    out=[]
    d=3
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=2
    if n>1:out.append(n)
    return out

def prime(n):
    if n<2:return False
    if n%2==0:return n==2
    return all(n%d for d in range(3,isqrt(n)+1,2))

def test_q_recharge():
    tested=0
    for q in range(7,501,2):
        if not prime(q):continue
        for e in range(5,q,2):
            for sign in (-1,+1):
                C=(1 if sign==-1 else -1)%(2*q)
                if C%2:C+=q
                assert C%2==0 and (C+sign)%q==0
                post=C+e-1
                assert (post-1)%q and (post+1)%q
                y=next(y for y in range(0,4*q+2,2)
                       if (post-1+y)%q==0 or (post+1+y)%q==0)
                target=2*q-e-1 if sign==-1 else 2*q-e+1
                assert y==target and y>=q+1
                tested+=1
    assert tested==21066
    for q in (7,11,13):
        # e=3 exception: + side switches to - without further growth.
        C=2*q-2
        assert (C+1)%q==0
        assert (C+2-1)%q==0
        # - side requires 2q-4 extra even horizon growth.
        C=2*q+2
        assert (C-1)%q==0
        post=C+2
        y=next(y for y in range(0,4*q+2,2)
               if (post-1+y)%q==0 or (post+1+y)%q==0)
        assert y==2*q-4
    assert gcd(40,36-1)==5  # q=7 clock at C=36 before e=5
    assert (40-1)%7 and (40+1)%7
    print("PASS exact directional preemption:",tested,"triples plus e=3 exceptions")

def exact_path(M):
    start=M+2
    K=(7*M-1)//4
    pos=start
    C=2*M-2
    event_count=0
    last=start
    while pos<K:
        next_index=K+1
        for p in factors(C-1):
            r=2*p*((pos//(2*p))+1)
            next_index=min(next_index,r)
        for p in factors(C+1):
            r=pos+(p+2-pos)%(2*p)
            if r<=pos:r+=2*p
            next_index=min(next_index,r)
        if next_index>K:break
        e=gcd(next_index if next_index%2==0 else next_index-2,
              C-1 if next_index%2==0 else C+1)
        assert e>1
        C+=e-1
        pos=next_index
        last=pos
        event_count+=1
    return K,event_count,last-start,K-last,C

def test_localization():
    cases=[
        (305,26,220,6,False),
        (365,29,203,68,True),
        (5419,9,75,3987,True),
        (28549,177,1887,19522,True),
        (113623,107,2181,83034,True),
        (355723,57,1317,265473,True),
        (475381,186,4173,352360,True),
        (22933441,209,14343,17185735,True),
        (91793059,53,15195,68829597,True)]
    for M,N,L,tail,expected_good in cases:
        K,n,l,t,C=exact_path(M)
        good=prime(C-1) and prime(C+1)
        assert (n,l,t,good)==(N,L,tail,expected_good), (M,n,l,t,good)
        print("M",M,"N",n,"last_offset",l,"over_sqrtM",
              round(l/sqrt(M),5),"quiet_tail",t,"GOOD",good)
    print("PASS exact original parity-gcd first-hit paths; no global theorem")

def test_X_identity():
    C=1
    X=2*1-C
    for n in range(2,20000):
        orig=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
        transformed=gcd(n,X+3) if n%2==0 else gcd(n-2,X-3)
        assert orig==transformed
        C+=orig-1
        X+=3-orig
        assert X==2*n-C
    print("PASS deficit X=2n-D exact parity-gcd identity")

if __name__=="__main__":
    test_X_identity()
    test_q_recharge()
    test_localization()
