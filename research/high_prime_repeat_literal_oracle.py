#!/usr/bin/env python3
"""Independent literal-step original parity GCD check of first/repeated prime hits.
Only small X for independent algorithmic validation, not a twin-prime proof.
"""
from math import gcd, isqrt

EXPECTED={256:(163,128),512:(265,265),1024:(640,577),4096:(5391,4823)}

def sieve_primes(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]

def run(X):
    B=isqrt(7*X)+(isqrt(7*X)**2 < 7*X)
    primes=sieve_primes(B)
    H={p:0 for p in primes if p>=19}
    F={p:0 for p in primes if p>=19}
    count_high19=0
    for M in range(X+1,2*X,2):
        C=2*M-2
        seen=set()
        for n in range(M+3,(7*M-1)//4+1):
            g=gcd(n if n%2==0 else n-2, C-1 if n%2==0 else C+1)
            d=1
            high=False
            for p in primes:
                if g%p==0:
                    d*=p
                    if p>=19:
                        H[p]+=1
                        high=True
                        if p not in seen:
                            F[p]+=1
                            seen.add(p)
            count_high19+=high
            C+=d-1
    h,f=sum(H.values()),sum(F.values())
    assert (h,f)==EXPECTED[X],(X,h,f,EXPECTED[X])
    print(f'REPEATED_Q_LITERAL_PASS X={X} B={B} H={h} F={f} R={h-f} '
          f'T19={count_high19} ratio={(h-f)/h:.9f}')
if __name__=='__main__':
    for x in EXPECTED:run(x)
