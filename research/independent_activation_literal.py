#!/usr/bin/env python3
"""Independent literal n-by-n GCD oracle, no prime-clock event jumping.
Tests q>=19 dormant->active transitions and return trichotomy.
"""
from math import gcd, isqrt
import sys


def primes(B):
    return [p for p in range(3,B+1,2) if all(p % a for a in range(3,isqrt(p)+1,2))]


def prime_factors(x,ps):
    return [p for p in ps if x % p == 0]


def run(X):
    B = isqrt(7*X) + (isqrt(7*X)**2 < 7*X)
    ps = primes(B)
    qs = [p for p in ps if p>=19]
    h = first = repeats = activations = lost = cutoff = 0
    immediate = flip = large = 0
    small_persist = large_persist = 0
    for M in range(X+1,2*X,2):
        C=2*M-2
        seen=set()
        active={}  # q -> [flips, hasLarge]
        for n in range(M+3, (7*M-1)//4 + 1):
            raw = gcd(n if n % 2 == 0 else n-2, C-1 if n % 2 == 0 else C+1)
            factors=prime_factors(raw,ps)
            if not factors:
                continue
            d=1
            for p in factors:d*=p
            prev={q for q in qs if q in seen and ((C-1)%q==0 or (C+1)%q==0)}
            hit={q for q in factors if q>=19}
            for q in hit:
                h += 1
                if q in seen:
                    repeats+=1
                    assert q in active
                    f,L=active[q]
                    if L:large+=1
                    elif f==0:immediate+=1
                    elif f==1:flip+=1
                    else:raise AssertionError((M,n,q,f,L))
                else:
                    first+=1
                    seen.add(q)
                active.pop(q,None)
            Y=C+d-1
            post={q for q in qs if q in seen and ((Y-1)%q==0 or (Y+1)%q==0)}
            for q in prev-hit:
                if q not in post:
                    assert q in active
                    lost+=1
                    active.pop(q)
                else:
                    assert q in active
                    f,L=active[q]
                    if d==3:
                        assert (C+1)%q==0
                        assert L or f==0
                        small_persist += 1
                        active[q]=[f+1,L]
                    else:
                        assert d>=2*q-1 and (d-3)*(d-1)*(d+1)%q==0
                        large_persist+=1
                        active[q]=[f,True]
            for q in post-prev:
                assert q not in active
                activations+=1
                active[q]=[0,False]
            assert set(active)==post
            C=Y
        cutoff+=len(active)
    assert h==first+repeats
    assert activations==repeats+lost+cutoff
    assert repeats==immediate+flip+large
    print(f'LITERAL_ACTIVATION_PASS X={X} B={B} H={h} first={first} repeats={repeats} activations={activations} lost={lost} cutoff={cutoff} direct={immediate} flip={flip} large={large} persisted3={small_persist} persistedLarge={large_persist}')

for val in map(int,sys.argv[1:] or [256,512,1024]):
    run(val)
