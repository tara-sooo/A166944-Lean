#!/usr/bin/env python3
"""Reproducible finite certificate for the A166944 dual mod-210 potential.

Not a Lean proof. Rebuilds the exact 450-cell WeightData.lean W table (SHA256
checked), checks all zero-slack edges in 22,050 mod-210 states, and then checks
the dual inequality on every necessary first-hit residue edge e<=55.
For e>=57 the inequality follows analytically from g<=2e, W<=32, U<=214.
Uses only the Python standard library.
"""
from collections import deque, Counter
from hashlib import sha256
from math import gcd, isqrt

MOD = 210
N = MOD * (MOD // 2)
EXPECTED_W_HASH = "bcbf78aa63d6835881fe3514c2813af743b690b76278cc0a5fe3b6e8e3ff75b2"

def wheel(j, c):
    if j % 2 == 0:
        return gcd(gcd(j, c + 29), 30)
    return gcd(gcd(j + 28, c + 1), 30)

def edge_allowed(s, c, e, g):
    return wheel(s + g, c) == gcd(e, 30) and all(
        wheel(s + k, c) == 1 for k in range(1, g))

def key(s, c):
    return ((c % MOD) // 2) * MOD + (s % MOD)

def weight_table():
    W = {(s, c): 0 for s in range(30) for c in range(0, 30, 2)}
    for _ in range(25):
        changed = False
        for s, c in W:
            for e in range(3, 18, 2):
                for g in range(1, 2 * e + 1):
                    if not edge_allowed(s, c, e, g):
                        continue
                    dst = ((s + g) % 30, (c + e - 1) % 30)
                    n = W[s, c] + 4*g - 9*(e-1)
                    if n > W[dst]:
                        W[dst] = n
                        changed = True
        if not changed:
            break
    assert not changed
    digest = sha256(bytes(W[s,c] for s in range(30)
                          for c in range(0,30,2))).hexdigest()
    assert digest == EXPECTED_W_HASH
    assert max(W.values()) == 32
    return W

def all_base_edges(W):
    base = {}
    for s in range(30):
        for c in range(0, 30, 2):
            a = []
            for e in range(3, 56, 2):
                for g in range(1, 2*e + 1):
                    if not edge_allowed(s,c,e,g):
                        continue
                    dest = ((s+g)%30, (c+e-1)%30)
                    lam = 9*(e-1) + W[dest] - W[s,c] - 4*g
                    assert lam >= 0
                    a.append((e,g,lam))
            base[s,c] = a
    return base

def permitted(s,c,e,g):
    # Extra necessary divisibility, beyond the mod-30 first-hit wheel.
    if e % 7 != 0:
        return True
    r = s + g
    return (c % 7 in (1,6)) and ((r if r%2==0 else r-2) % 7 == 0)

def construct_U(base):
    succ = [[] for _ in range(N)]
    indeg = [0]*N
    zeros = Counter()
    for c in range(0,MOD,2):
        for s in range(MOD):
            i=key(s,c)
            for e,g,lam in base[s%30,c%30]:
                if lam != 0 or not permitted(s,c,e,g):
                    continue
                j=key(s+g,c+e-1)
                succ[i].append((j,e,g))
                indeg[j]+=1
                zeros[e]+=1
    todo=deque(i for i,x in enumerate(indeg) if x==0)
    order=[]
    while todo:
        i=todo.popleft()
        order.append(i)
        for j,e,g in succ[i]:
            indeg[j]-=1
            if indeg[j]==0:
                todo.append(j)
    assert len(order)==N, "zero-slack directed cycle"
    U=[0]*N
    steps=[0]*N
    travel=[0]*N
    for i in reversed(order):
        for j,e,g in succ[i]:
            U[i]=max(U[i],e-1+U[j])
            steps[i]=max(steps[i],1+steps[j])
            travel[i]=max(travel[i],g+travel[j])
    assert sum(zeros.values())==33049
    assert set(zeros)=={3,5,7,11,13,17,19,23,29,31}
    assert max(U)==214 and max(steps)==27 and max(travel)==476
    return U, zeros

def verify_all_edges(base,W,U):
    total=0
    max_ratio=(0,None)
    for c in range(0,MOD,2):
        for s in range(MOD):
            i=key(s,c)
            for e,g,lam in base[s%30,c%30]:
                if not permitted(s,c,e,g):
                    continue
                j=key(s+g,c+e-1)
                gain=(e-1)+U[j]-U[i]
                assert gain<=17*lam, (s,c,e,g,lam,gain)
                total+=1
                if lam and gain/lam>max_ratio[0]:
                    max_ratio=(gain/lam,(s,c,e,g,lam,gain))
    assert total==3883994
    assert max_ratio[0]==17
    # e>=57: lambda>=e-41 and gain<=e-1+214.
    # 17(e-41)-(e-1+214)=16e-910>=2 for e>=57.
    assert 16*57-910==2
    return total,max_ratio

def canonical_constant(W,U):
    # A genuine canonical record M>=5 satisfies M%6==1.
    costs=[]
    for M in range(1,MOD,6):
        s=M+2
        C=2*M-2
        costs.append(17*(32-W[s%30,C%30])+U[key(s,C)])
    assert len(costs)==35 and max(costs)==544
    return max(costs)

def first_crossing_test(W,U,M=45_895_573):
    K=(7*M-1)//4
    s0=M+2
    H=2*M-2
    W0=W[s0%30,H%30]
    U0=U[key(s0,H)]
    assert (W0,U0)==(12,0)
    target=68*(K+1-s0)

    def right(G):
        C=H+G
        gap=isqrt(4*(C+1))
        if C%3!=0:gap=min(gap,6)
        if C%5 in (1,4):gap=min(gap,10)
        term=max(17*(W[s%30,C%30]-W0)+U0-U[key(s,C)]
                 for s in range(MOD))
        return 152*G+term+68*gap

    # Coarse monotone bound rules out every G<=15,380,000,
    # then exact mod-210 bound checks the rest of the initial window.
    Gbase=15_380_000
    R=isqrt(4*(H+Gbase+1))+1
    assert 152*Gbase + 17*(32-W0) + U0 + 68*R < target
    first=next(g for g in range(Gbase+2,15_420_000,2)
               if right(g)>=target)
    assert first==15_389_916
    return K,first,right(first)-target

def main():
    W=weight_table()
    base=all_base_edges(W)
    U,zeros=construct_U(base)
    tested,sharp=verify_all_edges(base,W,U)
    const=canonical_constant(W,U)
    K,first,margin=first_crossing_test(W,U)
    print("PASS: WeightData.lean W identical by SHA256; Wmax=32")
    print("PASS: mod-210 states",N,"zero-slack edges",sum(zeros.values()),
          "acyclic; max steps=27, max G=214, max travel=476")
    print("PASS: finite dual inequality on",tested,"edges for e<=55")
    print("PASS: maximum ratio gain/lambda =",sharp)
    print("PASS: e>=57 analytic margin >=2")
    print("PASS: canonical residue bound",const,"for all M%6=1")
    print("PAPER theorem: 68*T <= 152*G + 544 for every canonical path")
    print("PAPER consequence: 1000*D(K)<=2335*M suffices for Cap B")
    print("M=45895573: K=",K,"first-crossing requires G>=",first,
          "cut margin",margin)
    print("Cap B remains open; finite checks are not Lean kernel proofs.")

if __name__=="__main__":
    main()
