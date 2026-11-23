#!/usr/bin/env python3
"""Exact source-counted MIN p-return audit, with independent literal-GCD checks."""
import math
import sys
from collections import Counter

def spf_table(n):
    a = list(range(n + 1))
    for p in range(2, math.isqrt(n) + 1):
        if a[p] == p:
            for k in range(p*p, n+1, p):
                if a[k] == k: a[k] = p
    return a

def factors(n, spf, limit):
    out = []
    while n > 1:
        p = spf[n]
        if 2 < p <= limit: out.append(p)
        while n % p == 0: n //= p
    return out

def next_clock(t, C, K, B, spf):
    ans = None
    for p in factors(C-1, spf, B):
        u = (t // (2*p) + 1) * (2*p)
        if u <= K and (ans is None or (u,p)<ans): ans=(u,p)
    for p in factors(C+1, spf, B):
        u = t+1 + (p+2-t-1)%(2*p)
        if u <= K and (ans is None or (u,p)<ans): ans=(u,p)
    return ans

def literal(t,C,K,B,spf):
    for u in range(t+1,K+1):
        g = math.gcd(u,C-1) if u%2==0 else math.gcd(u-2,C+1)
        primes = factors(g,spf,B)
        if primes: return (u,primes[0])
    return None

def primes_to(B):
    return [p for p in range(3,B+1,2) if all(p%d for d in range(3,math.isqrt(p)+1,2))]

def audit(X):
    assert X >= 256 and X%4 == 0
    B=math.isqrt(7*X)
    if B*B<7*X: B+=1
    ps=primes_to(B)
    L,y=2,2
    for p in ps:
        if L*p>math.isqrt(B):break
        L*=p; y=p
    P=sum(p>y for p in ps); W=6*P
    a=math.ceil(math.sqrt(math.log(B)))
    spf=spf_table(7*X+64)
    second=third=returns=short=good=literal_checks=0
    first_pqp=first_pqp_top=first_pqp_Q=0
    offsets=Counter(); repeat_p=Counter(); pqp_p=Counter()
    small_sq=small_excess=large_pairs=D=0
    for M in range(X+1,2*X,2):
        t,C,K=M+2,2*M-2,(7*M-1)//4
        prev={}; selected=Counter(); high=[]; high7=[]
        low_gain=0; i=0
        while True:
            hit=next_clock(t,C,K,B,spf)
            if X<=1024 and M<X+70 and i<20:
                assert hit==literal(t,C,K,B,spf),(X,M,i,hit)
                literal_checks+=1
            if hit is None:break
            t,p=hit
            i+=1
            if p<=7:
                low_gain+=p-1
                assert low_gain<210,(X,M,t,low_gain)
            else:
                high7.append(p);low_gain=0
            if p>y:high.append(p)
            selected[p]+=1
            if p>=5 and p in prev:
                E=C-prev[p]
                assert E>=p-1,(X,M,p,E)
                if E<=2*p:
                    assert E in (p-1,p+1,p+3),(X,M,p,E)
                    short+=1;offsets[E-p]+=1
                returns+=1;repeat_p[p]+=1
                if selected[p]==2:second+=1
                if selected[p]==3:third+=1
            prev[p]=C+(p-1)
            C+=p-1
        good+=int(all(not factors(z,spf,math.isqrt(z)) for z in (C-1,C+1)))
        if len(high7)>=3 and high7[0]==high7[2]:
            p=high7[0];first_pqp+=1;pqp_p[p]+=1
            first_pqp_top+=int(2*p>=B)
            first_pqp_Q+=int(p>=max(840,math.ceil(B/math.log(B))))
        sample=high[:W][2::3]
        c=Counter(sample)
        D+=len(sample)-len(c)
        for p,n in c.items():
            J=n-1
            if p<=W:
                small_sq+=J*J
                small_excess+=max(0,J-a)
            else:
                large_pairs+=n*(n-1)//2
    assert D <= (X//2)*sum(y<p<=W for p in ps)*a+small_excess+large_pairs
    print(
        f'X={X} B={B} y={y} L={L} P={P} W={W} '
        f'sources={X//2} twin_terminals={good} second_p_hits={second} '
        f'third_p_hits={third} all_returns_p_ge5={returns} '
        f'short_recharge_gaps={short} offsets={dict(sorted(offsets.items()))} '
        f'first3_high7_pqp={first_pqp} pqp_upper_half={first_pqp_top} '
        f'pqp_p_ge_max840_BlogB={first_pqp_Q} pqp_top_labels={pqp_p.most_common(8)} '
        f'sampled_repeats={D} small_second_moment={small_sq} '
        f'small_excess={small_excess} large_pairs={large_pairs} '
        f'moment_normalized={small_sq/(X*max(1,sum(y<p<=W for p in ps))*math.log(B)):.6f} '
        f'literal_crosschecks={literal_checks}', flush=True
    )

if __name__ == '__main__':
    for arg in (sys.argv[1:] or ['256','1024','4096']):
        audit(int(arg))
