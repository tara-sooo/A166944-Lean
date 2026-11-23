#!/usr/bin/env python3
"""Original-source MIN replay: positions 1,3,5 versus 3,6,9 sampling.

Uses the pre-existing exact prime-clock oracle. The small-X first-event
choices are checked independently against literal integer-by-integer GCD.
All counts stop at each original M's own K(M). No asymptotic assumption.
"""
import math
import sys
from collections import Counter
from min_return_frequency_audit import spf_table, next_clock, literal, primes_to, factors

def one(X):
    assert X >= 256 and X % 4 == 0
    B = math.isqrt(7*X)
    if B*B < 7*X:
        B += 1
    primes = primes_to(B)
    y, L = 2, 2
    for p in primes:
        if L*p > math.isqrt(B):
            break
        y, L = p, L*p
    P = sum(p > y for p in primes)
    P7 = sum(p > 7 for p in primes)
    a = math.ceil(math.sqrt(math.log(B)))
    W = 4*P
    spf = spf_table(7*X+64)
    D2=D3=small_excess=large_pairs=second_moment=0
    pqp7=pqp_growth=first_pair_7=first_pair_growth=0
    twin_terminals=long_bad=literal_checked=0
    histlength_max=0
    pqp7_labels=Counter()
    for M in range(X+1,2*X,2):
        t,C,K = M+2,2*M-2,(7*M-1)//4
        history = []
        i = 0
        while True:
            hit = next_clock(t,C,K,B,spf)
            if X<=1024 and M<X+72 and i<25:
                oracle = literal(t,C,K,B,spf)
                assert hit == oracle, (X,M,i,hit,oracle)
                literal_checked+=1
            if hit is None: break
            t,p=hit
            history.append(p)
            C+=p-1
            i+=1
        twin = all(not factors(n,spf,math.isqrt(n)) for n in (C-1,C+1))
        twin_terminals+=int(twin)
        high = [p for p in history if p>y]
        high7 = [p for p in history if p>7]
        histlength_max = max(histlength_max,len(high))
        sampled2 = high[::2][:2*P]
        sampled3 = high[2::3][:2*P]
        c = Counter(sampled2)
        D2+=len(sampled2)-len(c)
        D3+=len(sampled3)-len(set(sampled3))
        for p,n in c.items():
            j=n-1
            if p<=W:
                small_excess+=max(0,j-a)
                second_moment+=j*j
            else:
                large_pairs+=n*(n-1)//2
        is_pqp7 = len(high7)>=3 and high7[0]==high7[2]
        is_pqpy = len(high)>=3 and high[0]==high[2]
        pqp7+=int(is_pqp7)
        pqp_growth+=int(is_pqpy)
        sample7=high7[::2][:2*P7]
        if is_pqp7:
            assert P7>=1 and len(sample7)>=2 and sample7[0]==sample7[1]==high7[0]
            assert len(sample7)-len(set(sample7))>=1
            pqp7_labels[high7[0]]+=1
        if is_pqpy:
            assert P>=1 and len(sampled2)>=2 and sampled2[0]==sampled2[1]==high[0]
            assert len(sampled2)-len(set(sampled2))>=1
        first_pair_7 += int(len(sample7)>=2 and sample7[0]==sample7[1])
        first_pair_growth += int(len(sampled2)>=2 and sampled2[0]==sampled2[1])
        if not twin and 4*P*(2*B+3*L)<K-(M+2):
            assert len(high)>=4*P and len(sampled2)==2*P
            assert len(sampled2)-len(set(sampled2))>=P
            long_bad+=1
    assert pqp7==first_pair_7
    assert pqp_growth==first_pair_growth
    assert D2 <= (X//2)*sum(y<p<=W for p in primes)*a+small_excess+large_pairs
    print(f'X={X} B={B} y={y} L={L} P={P} W={W} '
          f'D_every_other={D2} D_every_third={D3} '
          f'D2_over_XP={D2/max(1,X*P):.9f} '
          f'pqp_FIXED_LOW7={pqp7} first_pair_FIXED_LOW7={first_pair_7} '
          f'pqp_growing={pqp_growth} first_pair_growing={first_pair_growth} '
          f'small_excess={small_excess} small_J2={second_moment} '
          f'large_pairs={large_pairs} terminal_twins={twin_terminals}/{X//2} '
          f'max_high_events={histlength_max} non_twin_long_checked={long_bad} '
          f'literal_crosschecks={literal_checked} '
          f'pqp7_primes={pqp7_labels.most_common(8)}',flush=True)

if __name__ == '__main__':
    for s in (sys.argv[1:] or ['256','1024','4096','16384']):
        one(int(s))
