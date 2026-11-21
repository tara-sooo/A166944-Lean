#!/usr/bin/env python3
"""Joint event phase/cooldown and prime-word CRT checks; NOT a Cap B proof."""
from functools import cache
from itertools import combinations
from math import gcd, prod

GAPS=((2,5),(1,3),(106,73),(15,19),(147,151),(34,53),
(4,3),(3,5),(3,3),(30,17),(6,3),(3,77),(3,3),(8,5),
(4,3),(4,23),(2,3),(10,5),(2,3),(7,13),(2,7),(2,11),
(1,3),(90,47),(6,3),(3,13),(338,229),(19,31),(3,7),
(7,5),(2,3),(68,83),(4,3),(2,53),(4,3),(11,977),(1,3))
PRIMES=(11,13,17,19,23,29,31)

def d(r,C):return gcd(r,C-1) if r%2==0 else gcd(r-2,C+1)

def check_actual_cooldowns():
    M=45_895_573;s,C=M+2,2*M-2;E=[]
    for g,e in GAPS:
        r=s+g
        assert r<=C and all(d(j,C)==1 for j in range(s+1,r))
        assert d(r,C)==e
        E.append((r,C,e));s,C=r,C+e-1
    assert (s,C)==(45_896_532,91_793_058)
    count=0
    for i,(r,C,e) in enumerate(E):
        for R,D,f in E[i+1:]:
            q=gcd(e,f)
            if q<5:continue
            sigma=1 if r%2==0 else -1
            tau=1 if R%2==0 else -1
            index_min=2*q if sigma==tau else q+sigma-tau
            growth_min=2*q+tau-sigma
            assert R-r>=index_min and (R-r-index_min)%(2*q)==0
            assert D-C>=growth_min and (D-C-growth_min)%(2*q)==0
            count+=1
    assert count==16
    return count

def longest_horizon_word(primes):
    primes=tuple(primes)
    # For each p: current accumulated growth B mod p and the remaining
    # possible initial horizon C0 mod p (empty tuple means unconstrained).
    @cache
    def go(offsets,allowed):
        best=()
        for k,p in enumerate(primes):
            wanted={(1-offsets[k])%p,(-1-offsets[k])%p}
            valid=wanted if not allowed[k] else wanted.intersection(allowed[k])
            if not valid:continue
            nxt=tuple((offsets[j]+p-1)%q for j,q in enumerate(primes))
            opts=allowed[:k]+(tuple(sorted(valid)),)+allowed[k+1:]
            candidate=(p,)+go(nxt,opts)
            if len(candidate)>len(best):best=candidate
        return best
    word=go((0,)*len(primes),((),)*len(primes))
    return word,go.cache_info().currsize

def period_max(primes):
    # An independent exhaustive test over all even C modulo 2*product(primes).
    period=2*prod(primes)
    assert period<3_000_000
    dp=bytearray(period//2+1)
    for C in range(0,period+1,2):
        k=C//2
        for p in primes:
            if C%p in (1,p-1):
                assert C+p-1<=period
                dp[(C+p-1)//2]=max(dp[(C+p-1)//2],dp[k]+1)
    return max(dp)

def main():
    print('PASS: actual first-gcd threshold trajectory; common-q phase pairs:',check_actual_cooldowns())
    m=(0,())
    for triple in combinations(PRIMES,3):
        word,_=longest_horizon_word(triple)
        if len(word)>m[0]:m=(len(word),triple)
    assert m==(7,(11,13,31))
    print('PASS: all 35 small-prime triples have <=7 horizon-only hits')
    for p,expected in (((11,13,17),4),
                       ((11,13,17,19,23),11),
                       ((11,13,17,19,23,29),19)):
        word,count=longest_horizon_word(p)
        assert len(word)==expected
        if len(p)<=5:assert period_max(p)==expected
        print('PASS: prime alphabet',p,'max',expected,'CRT states',count)
    print('Only horizon-divisibility words tested; arbitrary distinct primes remain unrestricted.')

if __name__=='__main__':main()
