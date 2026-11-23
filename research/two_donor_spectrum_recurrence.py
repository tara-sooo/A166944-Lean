#!/usr/bin/env python3
"""Complete two-prime growth-spectrum gate and q-post CRT cone first-return audit.
Exact for any odd-prime p<r<q with p>=5 (run listed small examples).
A q event resets C mod q, so only 2*(p*r)**2 post-q residue states remain.
"""
from math import gcd

def isprime(n):
    return n>=2 and all(n%d for d in range(2,int(n**0.5)+1))

def pf(n):
    n=abs(n)
    out=set()
    for d in range(2,int(n**0.5)+1):
        if n%d==0:
            if isprime(d):out.add(d)
            while n%d==0:n//=d
    if n>1:out.add(n)
    return out

def spectrum(p,r):
    assert p>=5 and p<r and isprime(p) and isprime(r)
    return sorted({0,p-1,r-1,p+r-2,2*p+r-3,p*r-1})

def candidates(p,r):
    return sorted({q for e in spectrum(p,r) for a in (-1,1,3)
                    for q in pf(e-a) if q>r})

def gap(t,c,primes):
    best=None;d=1
    for p in primes:
        if (c-1)%p==0:residue=0
        elif (c+1)%p==0:residue=p+2
        else:continue
        wait=(residue-t)%(2*p) or 2*p
        if best is None or wait<best:best=wait;d=p
        elif wait==best:d*=p
    return best,d

def test_first_return(p,r,q):
    P=p*r;inv=pow(2*P,-1,q)
    winners=0;example=None;actual=0;actual_example=None
    for tr in range(2*P):
        parity=tr%2
        qt=0 if not parity else 2
        t=tr+2*P*((qt-tr)*inv%q)
        qpost=0 if not parity else q-2
        for h in range(P):
            C=2*h+2*P*((qpost-2*h)*inv%q)
            tt,cc=t,C
            for i in range(4):
                gs,d=gap(tt,cc,(p,r))
                gq,_=gap(tt,cc,(q,))
                if gq is not None and (gs is None or gq<=gs):
                    winners+=1
                    if example is None:example=(t,C,tt+gq,i)
                    constructed=construct_witness(p,r,q,(t,C,tt+gq,i))
                    if constructed is not None:
                        actual+=1
                        if actual_example is None:actual_example=constructed
                    break
                if gs is None:break
                assert i<3,(p,r,q,'three-event theorem broken')
                tt+=gs;cc+=d-1
    return winners,example,actual,actual_example

def construct_witness(p,r,q,post):
    if post is None:return None
    t,C,n,i=post
    T=2*p*r*q
    if t<1:t+=T;n+=T
    for a in (1,p,r,p*r):
        C0=C-(q*a-1)
        if C0<=0:continue
        d=1
        raw=gcd(t,C0-1) if t%2==0 else gcd(t-2,C0+1)
        for pp in (p,r,q):
            if raw%pp==0:d*=pp
        if d==q*a:return (t-1,C0,t,n)
    # All modulo-state witnesses can be shifted in C by a multiple of 2Pq.
    for shift in (T,2*T):
        for a in (1,p,r,p*r):
            C0=C+shift-(q*a-1)
            if C0<=0:continue
            d=1
            raw=gcd(t,C0-1) if t%2==0 else gcd(t-2,C0+1)
            for pp in (p,r,q):
                if raw%pp==0:d*=pp
            if d==q*a:return (t-1,C0,t,n)
    return None

if __name__=='__main__':
    for p,r in [(5,7),(7,11),(11,13),(13,17),(17,19),(19,23)]:
        qs=candidates(p,r)
        print('DONOR_SPECTRUM p=',p,'r=',r,'gains=',spectrum(p,r),'candidate_q=',qs,flush=True)
        for q in qs:
            winners,post,actual,witness=test_first_return(p,r,q)
            print(' Q_POST_CHECK q=',q,'states=',2*(p*r)**2,'ghostWinnerPostStates=',winners,'reachableWitnesses=',actual,
                  'witness=',witness,flush=True)
            assert actual>0, (p,r,q)
