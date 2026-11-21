#!/usr/bin/env python3
"""Exact A166944 terminal-envelope audit and high-growth synthetic examples.
Standard-library only. Neither Cap B nor twin prime infinitude is proved.
"""
from math import gcd, isqrt


def hit(r, C):
    return gcd(r if r % 2 == 0 else r - 2,
               C - 1 if r % 2 == 0 else C + 1)


def check(M, D, events, start, K):
    selected = [(r, e, C) for r, e, C in events if start < r <= K]
    last = selected[-1][0] if selected else start
    C = D[K]
    threshold = 32 + 8 * isqrt(C + 1)
    weights = []
    prior = start
    for r, e, before in selected:
        assert e >= 3 and r > prior
        w = 4 * (r - prior) - 9 * (e - 1)
        if e >= 9:
            assert w <= 0
        weights.append(w)
        prior = r
    run = E = 0
    for w in reversed(weights):
        run += w
        E = max(E, run)
    assert 0 <= E <= 32
    n3 = sum(e == 3 for r, e, C in selected)
    n5 = sum(e == 5 for r, e, C in selected)
    n7 = sum(e == 7 for r, e, C in selected)
    assert E <= 6*n3 + 4*n5 + 2*n7

    F = lambda i: 4*i - 9*D[i]
    starts = [start] + [r for r, e, C in selected]
    envelope = 4 * (K-last) + E
    assert envelope == F(K)-min(F(i) for i in starts)

    # Independently test all possible earlier endpoints via a running minimum.
    min_F = F(start)
    slow_ends = []
    for j in range(start+1,K+1):
        if F(j)-min_F >= 32+8*isqrt(D[j]+1):
            slow_ends.append(j)
        min_F = min(min_F,F(j))
    slow = envelope >= threshold
    assert slow == bool(slow_ends)
    if slow:
        assert slow_ends[-1] == K
        assert all(D[j] == D[K] and j >= last for j in slow_ends)

    t = isqrt(C+1)
    if K-last < 2*t:
        assert not slow
    if K-last >= 2*t+8:
        assert slow
    if n3+n5+n7 == 0:
        assert E == 0 and (slow == (K-last >= 2*t+8))

    return (M, K, D[K]-(2*M-2), len(selected), last, K-last,
            E, threshold, envelope, F(K)-F(start),
            slow, slow_ends[0] if slow_ends else None)


def original(limit=2_500_000):
    D = [0]*(limit+1)
    D[1] = 1
    C = 1
    max_increment = 2
    events = []
    records = []
    for n in range(2,limit+1):
        e = hit(n,C)
        if e > max_increment:
            max_increment = e
            if e > 5:
                records.append((e,n))
        if e > 1:
            events.append((n,e,C))
        C += e-1
        D[n] = C
    assert len(records)==17 and len(events)==250 and C==2_860_770
    results = []
    for M,index in records:
        K = (7*M-1)//4
        if K>limit:
            continue
        assert index==M+2 and D[index]==2*M-2
        results.append(check(M,D,events,M+2,K))
    assert len(results)==17
    assert [x[0] for x in results if not x[10]] == [7,13,43]
    assert [(x[0],x[2],x[5],x[8],x[7]) for x in results if x[0] in (13,43)] == [
        (13,16,2,8,80),(43,48,9,36,120)]
    print('Original A166944: 17 genuine records, 250 events,')
    print('  14 slow and 3 no-slow records; exact terminal equivalence PASS')
    return results


def synthetic(M):
    start = M+2
    K = (7*M-1)//4
    assert K<=2*M-2
    D=[0]*(K+1)
    C=2*M-2
    D[start]=C
    events=[]
    for n in range(start+1,K+1):
        e=hit(n,C)
        assert e<=M, (M,n,e)
        if e>1:
            events.append((n,e,C))
        C+=e-1
        D[n]=C
    output=check(M,D,events,start,K)
    print('Synthetic (NOT an attained record):',output)
    return output


if __name__=='__main__':
    original()
    r=synthetic(367)
    assert (r[1],r[2],r[3],r[4],r[5],r[6],r[7],r[8],r[9],r[11]) == (
        642,288,27,570,72,0,280,288,-1500,640)
    r=synthetic(81)
    assert (r[2],r[8],r[7],r[9]) == (32,156,136,-56)
    print('PASS: exact terminal envelope and bounded F recovery')
