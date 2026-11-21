"""Reproducible diagnostic for the 2026-11-22 adaptive slow-block bound.

All computations use Python standard library and integer arithmetic.
The synthetic recurrence from (M+2, 2*M-2) is NOT an attained-record test.
"""
from math import gcd, isqrt


def local_block_length(u):
    """Elementary sufficient block length for u >= 24."""
    assert u >= 24
    t = isqrt(2*u + 1)
    ell = 14 + 2*t
    assert isqrt(2*(u+ell)+1) <= t+3
    return ell


def exact_block_length(u):
    """Least integer length guaranteed slow if all increments in block are 1."""
    lower = 8 + 2*isqrt(2*u+1)
    for ell in range(lower, local_block_length(u)+1):
        if 4*ell >= 32 + 8*isqrt(2*(u+ell)+1):
            return ell
    raise AssertionError("no length found")


def count_blocks(M, length=local_block_length):
    u=M+2
    K=(7*M-1)//4
    q=0
    while u <= K:
        ell=length(u)
        if u+ell > K: break
        u+=ell
        q+=1
    return q, K-u


def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    for p in range(3,isqrt(n)+1,2):
        if n%p==0: return False
    return True


def synthetic_replay(M):
    """Exact direct-gcd replay, starting at an arbitrary record-shaped state."""
    s=M+2
    C=2*M-2
    K=(7*M-1)//4
    n=0
    minF=4*s-9*C
    has_slow=False
    for r in range(s+1,K+1):
        d=gcd(r if r%2==0 else r-2, C-1 if r%2==0 else C+1)
        if d>1:
            n+=1
            C+=d-1
        F=4*r-9*C
        if F-minF >= 32+8*isqrt(C+1):
            has_slow=True
        minF=min(minF,F)
    return n,has_slow


def main():
    M=45_895_573
    q,rem=count_blocks(M)
    qe,re=count_blocks(M,exact_block_length)
    assert (q,qe)==(1545,1546), (q,qe)
    print(f"M={M}, K={(7*M-1)//4}, sufficient N <= {q-1} via simple blocks")
    print(f"M={M}, sufficient N <= {qe-1} via exact variable blocks")
    M=28_549
    assert isprime(M) and isprime(M-2)
    N,slow=synthetic_replay(M)
    assert (N,slow)==(177,True), (N,slow)
    print(f"Synthetic M={M}: pair (M-2,M) prime, N={N}, slow={slow}; not an attained A166944 record")

if __name__ == '__main__':
    main()
