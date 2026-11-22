#!/usr/bin/env python3
"""Exact A166944 return-span CRT and reordered-block audit (stdlib only).

Finite recurrence checks through index 2,500,000, not a Cap B proof.
Companion: 2026-11-22-return-span-entropy-permutation-lattice.md.
"""
from math import gcd, isqrt, prod
from collections import defaultdict


def prime(n):
    return n >= 2 and all(n % q for q in range(2, isqrt(n) + 1))


def factors(n):
    out = []
    f = 3
    while f*f <= n:
        if n % f == 0:
            if f >= 5:
                out.append(f)
            while n % f == 0:
                n //= f
        f += 2
    if n >= 5:
        out.append(n)
    return out


def original_events(limit=2_500_000):
    horizon = 1
    events = []
    for n in range(2, limit+1):
        d = gcd(n if n%2 == 0 else n-2,
                horizon-1 if n%2 == 0 else horizon+1)
        if d > 1:
            post = horizon+d-1
            # A genuine increment must divide the next a-value.
            assert (n+post) % d == 0
            events.append((n,d,horizon,post))
            horizon = post
    assert (len(events), horizon) == (250,2_860_770)
    return events


def audit_all_return_spans(events):
    uses = defaultdict(list)
    for event in events:
        for p in factors(event[1]):
            assert prime(p)
            uses[p].append(event)
    H, U, L = defaultdict(dict),defaultdict(dict),defaultdict(dict)
    count = 0
    for p, occurrences in uses.items():
        for i, first in enumerate(occurrences):
            for second in occurrences[i+1:]:
                n1,e1,cp1,h1=first
                n2,e2,cp2,h2=second
                time=n2-n1
                horizon=h2-h1
                a_span=(n2+h2)-(n1+h1)
                orient=(2 if n1%2 and not n2%2
                        else -2 if not n1%2 and n2%2 else 0)
                assert time>0 and horizon>2 and a_span==time+horizon
                assert (horizon-orient)%p==0
                assert (time+orient)%p==0
                assert a_span%p==0
                H[horizon][p]=(first,second,orient)
                U[a_span][p]=(first,second)
                L[time][p]=(first,second,orient)
                count+=1
    assert (len(uses),count)==(45,1769)
    for horizon, keys in H.items():
        pp=prod(keys)
        assert horizon*(horizon*horizon-4)%pp==0
        same=prod(p for p, (_,_,orientation) in keys.items()
                  if orientation==0)
        assert horizon%same==0
    for a_span, keys in U.items():
        assert a_span%prod(keys)==0
    for time, keys in L.items():
        pp=prod(keys)
        assert time*(time*time-4)%pp==0
        same=prod(p for p, (_,_,orientation) in keys.items()
                  if orientation==0)
        assert time%same==0
        if len(keys)==len([x for x in keys.values() if x[2]==0]):
            assert time%(2*pp)==0
    assert (len(H), sum(len(v)>=2 for v in H.values()),
            max(len(v) for v in H.values()))==(1552,110,3)
    assert (len(U), sum(len(v)>=2 for v in U.values()),
            max(len(v) for v in U.values()))==(1701,22,3)
    assert {5,7,11}.issubset(U[4_275_810])
    print('Real 2.5M: 45 prime keys, 1769 return pairs')
    print('Horizon spans:',len(H),'distinct,',
          sum(len(v)>=2 for v in H.values()),'shared, max 3 keys')
    print('a-spans:',len(U),'distinct,',
          sum(len(v)>=2 for v in U.values()),'shared, max 3 keys')
    return uses,H,U,L


def audit_permutations(events):
    counts={2:0,3:0,4:0}
    found=False
    for k in (2,3,4):
        for i in range(len(events)-2*k+1):
            first=[ev[1] for ev in events[i:i+k]]
            if len(set(first))!=k or not all(p>=5 and prime(p) for p in first):
                continue
            for j in range(i+k,len(events)-k+1):
                second=[ev[1] for ev in events[j:j+k]]
                if set(first)!=set(second) or first==second:
                    continue
                counts[k]+=1
                middle=sum(ev[1]-1 for ev in events[i+k:j])
                baseline=sum(p-1 for p in first)+middle
                delta={}
                for p in first:
                    fi=first.index(p)
                    sj=second.index(p)
                    delta[p]=(sum(q-1 for q in second[:sj])
                              -sum(q-1 for q in first[:fi]))
                    earliest=events[i+fi]
                    later=events[j+sj]
                    span=later[3]-earliest[3]
                    assert span==baseline+delta[p]
                    assert (span-(2 if earliest[0]%2 and not later[0]%2
                                  else -2 if not earliest[0]%2 and later[0]%2
                                  else 0))%p==0
                assert sum((p-1)*d for p,d in delta.items())==0
                inversions=0
                for a,p in enumerate(first):
                    for q in first[a+1:]:
                        if second.index(q)<second.index(p):
                            inversions+=1
                            assert delta[p]-delta[q]>=p+q-2
                assert sum(d==0 for d in delta.values())>=k-2*inversions
                if k==2 and i==3 and j==28:
                    assert first==[7,13] and second==[13,7]
                    assert baseline==2634 and delta=={7:12,13:-6}
                    assert [events[h][0] for h in (i,i+1,j,j+1)]==[
                        9,15,1326,1339]
                    found=True
    assert counts=={2:23,3:0,4:0} and found
    print('Permuted event blocks:',counts,
          '; real inverted example 7,13,...,13,7 has ±12/−6 defects')


def audit_exact_shift(events):
    by_index={ev[0]:ev for ev in events}
    first=[2674,2675,2676,2680,2682]
    shift=1_425_270
    second=[n+shift for n in first]
    e=[7,11,3,5,3]
    assert [by_index[n][1] for n in first]==e
    assert [by_index[n][1] for n in second]==e
    for n,m in zip(first,second):
        a,b=by_index[n],by_index[m]
        assert b[3]-a[3]==2*shift
        assert (m+b[3])-(n+a[3])==3*shift
    keys=prod((5,7,11))
    assert shift%(2*keys)==0
    assert (2*shift)%keys==0 and (3*shift)%keys==0
    assert (shift//(2*keys),(2*shift)//keys,(3*shift)//keys)==(
        1851,7404,11106)
    print('Real copied event motif [7,11,3,5,3], shift',shift,
          ', horizon shift',2*shift,', a-shift',3*shift)


if __name__=='__main__':
    events=original_events()
    audit_all_return_spans(events)
    audit_permutations(events)
    audit_exact_shift(events)
    print('PASS finite all-pair span CRT, inversion conservation, time-shift copy')
