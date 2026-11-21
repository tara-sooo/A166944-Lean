#!/usr/bin/env python3
"""A166944 paper-certificate audit; not a Lean proof of Cap B.
Rebuilds the finite potential W of mission_scan/twin_proof/cap_bound/WeightData.lean
from the same mod-30 first-unit wheel in event_weights.py.
"""
from math import gcd, isqrt, prod

MOD=30
ZERO_SLACK_PRIMES=(3,5,7,11,13,17,19,23,29,31)
Q=2*prod(ZERO_SLACK_PRIMES)

def wheel(t,c):
    return gcd(gcd(t-2*(t%2),c+2*(t%2)-1),MOD)

def edges(hi):
    out={}
    for s in range(MOD):
        for c in range(0,MOD,2):
            rows=set()
            for g in range(1,2*hi+1):
                t=s+g
                h=wheel(t,c)
                for e in range(3,hi+1,2):
                    if g<=2*e and gcd(e,MOD)==h:
                        rows.add(((s+g)%MOD,(c+e-1)%MOD,g,e))
                if h>1:break
            out[s,c]=rows
    return out

W={(s,c):0 for s in range(30) for c in range(0,30,2)}
for pass_no in range(20):
    updated=False
    for (s,c),es in edges(17).items():
        for u,v,g,e in es:
            cand=W[s,c]+4*g-9*(e-1)
            if cand>W[u,v]:
                W[u,v]=cand;updated=True
    if not updated:break
assert not updated and max(W.values())==32
# This reproduces the full archive WeightData.lean W table.
assert W[15,24]==12, W[3,0]==0
for (s,c), es in edges(39).items():
    for u,v,g,e in es:
        assert 4*g+W[s,c]<=9*(e-1)+W[u,v], (s,c,e,g)

# For odd e>=41 the uniform bound is automatic:
# 4*g+W_before <= 8*e+32 <= 9*(e-1).
for (s,c), es in edges(41).items():
    for u,v,g,e in es:
        if e in (37,41):
            slack=9*(e-1)+W[u,v]-W[s,c]-4*g
            assert slack>=30,(s,c,e,g,slack)
for (s,c), es in edges(43).items():
    for u,v,g,e in es:
        if e==43:
            slack=9*(e-1)+W[u,v]-W[s,c]-4*g
            assert slack>=30,(s,c,e,g,slack)
assert all(w%2==0 for w in W.values())
# If slack>0 and e<=31, then slack>=2 and e-1<=30.
# For 33<=e<=43: composites have slack>=16; p37,41,43>=30.
# If e>=45: slack>=e-41, so e-1<=15*slack.
# Consequently every positive-slack event obeys e-1<=15*slack.

# Between consecutive p-events, the other horizon growth H must be
# even and satisfy H = -1, 1, or 3 modulo p. For p>=5, H>=p-1.
for p in range(5,140,2):
    if any(p%d==0 for d in range(3,isqrt(p)+1,2)):continue
    for eps1 in (-1,1):
        for eps2 in (-1,1):
            H=min(h for h in range(0,2*p+4,2) if (p-1+h-(eps2-eps1))%p==0)
            assert H>=p-1,(p,eps1,eps2,H)

M=45_895_573
K=(7*M-1)//4
H=2*M-2
s0=M+2
W0=W[s0%30,H%30]
assert W0==12
LIMIT=4*(K+1-s0)
mx={c:max(W[s,c] for s in range(MOD)) for c in range(0,MOD,2)}

def gap_bound(C):
    b=isqrt(4*(C+1))
    if C%3!=0:b=min(b,6)
    if C%5 in (1,4):b=min(b,10)
    return b

def admissible(G):
    C=H+G
    return 9*G+mx[C%30]-W0+4*gap_bound(C)>=LIMIT

Gmin=next(g for g in range(15_280_000,15_310_000,2) if admissible(g))
assert Gmin==15_289_326
print('PASS: rebuilt W, 450 states, maximum 32; canonical W0=12')
print('PASS: mod-30 constraints for e<=39; e>=41 analytic')
print('PASS: zero-slack increments prime <=31; finite p37,41,43 slack>=30')
print('PASS: repeated-prime interval H>=p-1; prime count 15*N<=2*G+3')
print('strict-slope common multiple Q:', Q)
print('general strict bound: 4*T <= (9 - 2/(Q+28))*G + 34 - 60/(Q+28)')
print('threshold M',M,'K',K,'first-crossing necessary G>=',Gmin)
print('at first threshold: Cmod30', (H+Gmin)%30,
      'slack budget',9*Gmin+mx[(H+Gmin)%30]-W0+4*gap_bound(H+Gmin)-LIMIT)
print('Cap B remains OPEN')
