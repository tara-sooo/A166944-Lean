#!/usr/bin/env python3
"""Independent exact parity-gcd wheel-insertion signed-cost verifier.
Reproduce X=256,512 dyadic blocks. No Lean or twin-prime proof.
Run: python research/wheel_signed_growth_dyadic_audit.py
"""
from math import gcd, isqrt

def prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    return all(n % p != 0 for p in range(3, isqrt(n)+1, 2))

def growth(m, L):
    c = 2*m - 2
    for n in range(m+3, (7*m-1)//4 + 1):
        e = gcd(n, c-1) if n%2==0 else gcd(n-2, c+1)
        e = gcd(e, L) if L else e
        c += e-1
    return c - (2*m-2)

def prime_powers(limit):
    steps=[]
    for p in range(3,limit+1,2):
        if not prime(p):continue
        q=p
        while q<=limit:
            steps.append((q,p))
            q*=p
    return sorted(steps)

def audit(X):
    starts=list(range(X+1,2*X,2))
    before={m:0 for m in starts}
    L=1
    positives=negatives=0
    signed_steps={}
    steps=prime_powers(4*X)
    for q,p in steps:
        L*=p
        stage=0
        for m in starts:
            K=(7*m-1)//4
            # No index-gcd operand can be divisible by q if no multiple
            # of q is in the generous enclosing interval [m+1,K].
            if (m+q)//q > K//q:
                continue
            after=growth(m,L)
            diff=after-before[m]
            before[m]=after
            positives+=max(0,diff)
            negatives+=max(0,-diff)
            stage+=diff
        signed_steps[q]=stage
    actual=sum(growth(m,0) for m in starts)
    assert sum(before.values())==actual
    return (len(starts),len(steps),positives,negatives,actual,
            sum(starts)//4,signed_steps)

def main():
    expected={
       256:(128,188,12658,372,12286,12288),
       512:(256,329,25622,6342,19280,49152),
    }
    for X in (256,512):
        counts= audit(X)
        assert counts[:6]==expected[X],(X,counts[:6],expected[X])
        print(f"X={X} inputs={counts[0]} prime-powers={counts[1]} "
              f"positive={counts[2]} negative={counts[3]} "
              f"net={counts[4]} target={counts[5]}")
        if X==256:
            assert counts[-1][47]==2798
        else:
            assert counts[-1][43]==4002
            assert counts[-1][31]==-1770
    print("PASS exact parity-gcd signed ladder; global average OPEN")

if __name__=="__main__":
    main()
