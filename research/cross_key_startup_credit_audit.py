#!/usr/bin/env python3
"""Audits a cross-key startup-credit lemma for 210-potential prime debts.

Run from the research/ folder alongside cap_b_prime_debt_210.py.
Requires only Python 3 standard library. No Lean proof, Cap B or twin prime proof.
"""
import random
from collections import defaultdict
from math import gcd
import cap_b_prime_debt_210 as base


def ledger(pairs):
    """pairs: chronologically ordered (pre-horizon, prime, debt).

    Exactly 2m+1 selected occurrences for each prime, m>=1.
    The earliest is free starter; all remaining occurrences are demanded.
    """
    by_prime = defaultdict(list)
    for C, p, b in pairs:
        assert p >= 61 and base.is_prime(p) and 0 <= b <= p + 30
        by_prime[p].append((C, b))
    assert all(len(v) >= 3 and len(v) % 2 == 1 for v in by_prime.values())
    A, B = pairs[0][0], pairs[-1][0]
    assert all(pairs[i][0] < pairs[i+1][0] for i in range(len(pairs)-1))
    p_end = pairs[-1][1]
    demanded = [(p, C, b) for p, hits in by_prime.items() for C, b in hits[1:]]
    R = len(demanded)
    D = sum(b for _, _, b in demanded)
    excess = sum(max(0, b-(p-1)) for p, _, b in demanded)
    startup_credit = sum(p-1 for p in by_prime if p != p_end)
    lower = startup_credit - excess
    assert B - A - D >= lower, (A, B, D, lower)
    if (len(by_prime)-1)*(min(by_prime)-1) >= 31*R:
        assert D <= B-A
    return len(by_prime), R, B-A, D, excess, lower


def random_abstract_words(trials=1200):
    rng=random.Random(166944)
    primes=[p for p in range(61,3000,2) if base.is_prime(p)]
    certified = 0
    for _ in range(trials):
        k=rng.randint(1,12)
        ps=rng.sample(primes,k)
        vals=[]
        for p in ps:
            m=rng.randint(1,5)
            vals.extend([p]*(2*m+1))
        rng.shuffle(vals)
        C=rng.randint(100,10000)*2
        data=[]
        for p in vals:
            b=rng.randint(0,p+30)
            data.append((C,p,b))
            C+=p-1+rng.randint(0,200)
        k,R,L,D,extra,_=ledger(data)
        if (k-1)*(min(ps)-1) >=31*R:
            certified+=1
    print('Abstract accounting stress tests:', trials,
          'startup-certificate cases', certified)


def scan_original(V,limit=2_500_000):
    D=2    # d(2)=2, D(2)=2 (the potential requires even horizon)
    prev_s=2
    prev_C=2
    events=1
    positives=[]
    for r in range(3,limit+1):
        e=gcd(r if r%2==0 else r-2, D-1 if r%2==0 else D+1)
        if e>1:
            events+=1
            g=r-prev_s
            Cnext=D+e-1
            before=V[base.INDEX[(prev_s%210, prev_C%210)]]
            after=V[base.INDEX[(r%210, Cnext%210)]]
            if e>=61 and base.is_prime(e):
                b=max(0,g-(e-1)+after-before)
                eta=max(0,b-(e-1))
                assert b<=e+30 and g<=2*e
                if eta:
                    assert 2*e-30<=g<=2*e
                    assert e*(e-15)<=D+1
                if b:
                    positives.append((r,e,D,g,b,eta))
            prev_s,prev_C=r,Cnext
        D+=e-1
    assert (events,D)==(250,2_860_770), (events,D)
    assert len(positives)==5
    assert not any(x[5]>0 for x in positives)
    assert len(set(x[1] for x in positives))==5
    print('Actual A166944 to', limit, ': nonunit events', events,
          'p>=61 positive debts',len(positives),'near-maximal excess',0)
    print('  [index, p, preceding C, gap, debt, excess]:',positives)


def synthetic_61(V):
    s,C=8_289_324,16_578_642  # artificial moving-horizon start
    selected=[]
    for _ in range(30):
        hit=base.actual_first_hit(s,C)
        assert hit is not None
        r,e=hit
        g=r-s
        Cp=C+e-1
        before=V[base.INDEX[(s%210,C%210)]]
        after=V[base.INDEX[(r%210,Cp%210)]]
        b=max(0,g-(e-1)+after-before) if e==61 else 0
        if e==61:
            selected.append((C,e,b))
        s,C=r,Cp
        if len(selected)==3:
            break
    assert [x[2] for x in selected]==[28,40,12], selected
    result=ledger(selected)
    assert (result[0],result[1],result[2],result[3],result[4])==(1,2,366,52,0),result
    print('Artificial exact first-hit 61 triple:',selected,
          'startup lemma (k,R,L,D,excess,lower)=',result)


def check_canonical_slow_certificate(V):
    """Official M: direct 37 first hits, followed by a prime-neighbor quiet tail.

    Record attainment is supplied by existing external A166944 Lean results,
    and not independently established by this local replay.
    """
    from math import isqrt
    M = 45_895_573
    K = (7*M-1)//4
    s, C = M+2, 2*M-2
    H = 0
    exceptions=[]
    for _ in range(37):
        hit=base.actual_first_hit(s,C)
        assert hit is not None
        r,e=hit
        g=r-s
        Cf=C+e-1
        vb=V[base.INDEX[(s%210,C%210)]]
        va=V[base.INDEX[(r%210,Cf%210)]]
        if e>=11 and base.is_prime(e):
            b=max(0,g-(e-1)+va-vb)
            if b>e-1:
                H+=1
                exceptions.append((r,e,g,b,b-(e-1)))
        s,C=r,Cf
    assert (s,C,H)==(45_896_532,91_793_058,2), (s,C,H)
    assert exceptions == [(45_895_920,17,30,24,8),
                          (45_896_064,47,90,48,2)]
    # Both adjacent horizon numbers are prime, hence no new hit for s<r<=K<C.
    assert base.is_prime(C-1) and base.is_prime(C+1)
    assert s<K<C-1
    G=C-(2*M-2)
    T=K-(M+2)
    bound=2*G+31*H+41+2*isqrt(2*K+1)
    assert (G,T,bound)==(1914,34_421_677,29_279)
    assert bound<T
    print('Official M=',M, 'K=',K,'G=',G,'H=',H,'T=',T,
          'finite sufficient bound=',bound, 'PASS')


if __name__=='__main__':
    V=base.potential(base.make_edges())
    random_abstract_words()
    synthetic_61(V)
    check_canonical_slow_certificate(V)
    scan_original(V)
    print('PASS; paper inequality audited, not Lean-proved or asymptotically closed')
