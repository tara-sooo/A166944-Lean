#!/usr/bin/env python3
"""Exact A166944 reverse-gcd certificates for BAD cutoff endpoints.

Python 3 standard library. Original parity-gcd forward checks, all
predecessor branches, and infinite affine CRT periods. Does not prove
Cap B or twin-prime infinitude; large lifted starts are only finite-wheel
prime-admissible, not asserted to be twin primes.
"""
from functools import lru_cache
from math import gcd, isqrt, lcm

@lru_cache(None)
def odd_divisors(n):
    assert n >= 1
    while n % 2 == 0:
        n //= 2
    divs = [1]
    p = 3
    while p*p <= n:
        if n % p == 0:
            powers = [1]
            v = 1
            while n % p == 0:
                n //= p
                v *= p
                powers.append(v)
            divs = [a*b for a in divs for b in powers]
        p += 2
    if n > 1:
        divs += [x*n for x in divs]
    return tuple(sorted(divs))

def increment(n, pre):
    return gcd(n if n % 2 == 0 else n-2,
               pre-1 if n % 2 == 0 else pre+1)

def predecessors(n, post):
    """ALL exact even-horizon >=2 predecessors; returns (pre,e)."""
    u = n % 2
    A, B = n-2*u, post+2*u
    out = []
    for e in odd_divisors(gcd(A,B)):
        pre = post-e+1
        if pre >= 2 and gcd(A//e,B//e-1) == 1:
            assert increment(n,pre) == e and pre+e-1 == post
            out.append((pre,e))
    return tuple(out)

def layers(K,C,depth):
    sets=[{C}]
    for j in range(1,depth+1):
        n=K-j+1
        sets.append({pre for post in sets[-1]
                     for pre,e in predecessors(n,post)})
    return sets

def prime(n):
    return n > 1 and all(n % p for p in range(2,isqrt(n)+1))

def canonical(M):
    s,K,C=M+2,(7*M-1)//4,2*M-2
    d={s:C}
    for n in range(s+1,K+1):
        C+=increment(n,C)-1
        d[n]=C
    return K,C,d

CASES=(
    (101119,176958,236004,3,11,8,(1,2,2,3,2,2,2,1,0),(176951,236000)),
    (100549,175960,241340,5,3,6,(1,2,2,3,2,1,0),(175955,241340)),
)

def proof_checks():
    checked=0
    for n in range(3,180):
        for pre in range(2,min(2*(n-1),400)+1,2):
            e=increment(n,pre)
            assert (pre,e) in predecessors(n,pre+e-1)
            checked+=1
    assert checked==15930
    print('PASS inverse exactness',checked,'forward gcd steps')
    for M in (13,43,305,307,101119,100549):
        K,C,d=canonical(M)
        depth=min(230,K-M-2)
        ss=layers(K,C,depth)
        assert all(d[K-j] in ss[j] for j in range(depth+1))
        if depth==K-M-2:
            assert 2*M-2 in ss[-1]
        print('TRUE M',M,'positive-control layers',depth,
              'max width',max(map(len,ss)))

def affine_certificate(case):
    M,K,C,eK,eNext,L,counts,trap=case
    assert prime(M) and prime(M-2)
    assert K==(7*M-1)//4 and K%2==0
    assert 2*M-2 <= C <= 2*K
    assert increment(K,C-eK+1)==eK
    assert increment(K+1,C)==eNext
    assert not (prime(C-1) and prime(C+1))
    original=layers(K,C,L)
    assert tuple(map(len,original))==counts
    assert not original[-1]
    n,h=trap
    assert n==K-L+1 and h in original[-2]
    A,B=n-2,h+2
    assert gcd(A,B)==1 and gcd(A,B-1)==3
    assert not predecessors(n,h)
    print('BAD-candidate M=',M,'eK,eK+1=',(eK,eNext),
          'inverse widths=',counts,'TRAP=',trap)

    # M(t)=M+840t, K(t)=K+1470t, C(t)=C+2100t.
    beta,delta=1470,2100
    small=(3,5,7,11,13,17,19,23,29,31)
    assert all(M%p not in (0,2) for p in small)
    # Preserve both specified local gcd values.
    D1=delta*K-beta*(C-eK)
    D2=delta*(K-1)-beta*(C+1)
    assert D1!=0 and D2!=0
    Q=lcm(abs(D1),abs(D2),*small)
    checked_dets=2
    for j in range(1,L+1):
        n=K-j+1
        u=n%2;A=n-2*u
        for post in original[j-1]:
            B=post+2*u
            D=delta*A-beta*B
            assert D!=0
            Q=lcm(Q,abs(D))
            checked_dets+=1
            for e in odd_divisors(gcd(A,B)):
                De=D+beta*e
                assert De!=0
                Q=lcm(Q,abs(De))
                checked_dets+=1
    # gcd(A(t),B(t)) divides delta*A0-beta*B0;
    # gcd(A(t),B(t)-e) divides that determinant+beta*e.
    # Thus the whole predecessor tree repeats modulo Q.
    for k in (1,2,5):
        m=M+840*k*Q
        r=K+1470*k*Q
        c=C+2100*k*Q
        assert r==(7*m-1)//4 and r%2==0
        assert 2*m-2<=c<=2*r
        assert gcd(r,c-eK)==eK
        assert gcd(r-1,c+1)==eNext
        assert all(m%p not in (0,2) for p in small)
        shifted=layers(r,c,L)
        assert all({z-2100*k*Q for z in shifted[j]}==original[j]
                   for j in range(L+1))
    print('INFINITE LIFT: digits(Q)=',len(str(Q)),
          'bits(Q)=',Q.bit_length(),'determinants=',checked_dets,
          'k=1,2,5 PASS; proof via affine determinant periodicity')
    return Q

if __name__=='__main__':
    proof_checks()
    for case in CASES:
        affine_certificate(case)
    print('PASS BAD-terminal inverse certificates; global Cap B OPEN')
