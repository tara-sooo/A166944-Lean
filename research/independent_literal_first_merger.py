#!/usr/bin/env python3
"""Independent brute-force first-merger genealogy via each original one-step GCD.
No event jumping, no shared-cohort sweep, no input from C++ implementation.
"""
from math import gcd, isqrt
import sys


def primes_through(B):
    return [q for q in range(3, B+1, 2) if all(q % j for j in range(3, isqrt(q)+1, 2))]


def run(X):
    B=isqrt(7*X)+(isqrt(7*X)**2 < 7*X)
    primes=primes_through(B)
    traces=[]
    for M in range(X+1,2*X,2):
        s=M+2;K=(7*M-1)//4;c=2*M-2
        states={s:c}; qweights={}
        for n in range(s+1,K+1):
            raw=gcd(n if n%2==0 else n-2,c-1 if n%2==0 else c+1)
            d=1;weight=0
            for q in primes:
                if raw%q==0:
                    d*=q
                    if q>=13:weight+=q
            c+=d-1;states[n]=c
            if weight:qweights[n]=weight
        traces.append((M,s,K,states,qweights))
    firstpairs=0;credit=0;birthpairs=0
    for i in range(len(traces)):
        M,s,K,S,W=traces[i]
        for j in range(i+1,len(traces)):
            M2,s2,K2,S2,W2=traces[j]
            tau=next((t for t in range(s2,K+1) if S[t]==S2[t]),None)
            if tau is None:continue
            assert all(S[t]==S2[t] for t in range(tau,K+1))
            firstpairs+=1
            birthpairs+=tau==s2
            credit+=sum(w for n,w in W.items() if n>tau)
    # Independent whole-family joined energy at pre-event high hit (source pairs)
    joined=0
    for n in range(X+3,(7*(2*X-1)-1)//4+1):
        buckets={}
        for M,s,K,S,W in traces:
            if s>=n or K<n:continue
            w=W.get(n,0)
            if w:
                c=S[n-1]
                if c not in buckets:buckets[c]=[0,w]
                else:assert buckets[c][1]==w
                buckets[c][0]+=1
        joined+=sum(m*(m-1)*w for m,w in buckets.values())
    assert 2*credit==joined,(X,credit,joined)
    known={256:(1001,124,30426,60852),512:(2520,565,97174,194348),1024:(6326,838,221565,443130)}
    if X in known:assert (firstpairs,birthpairs,credit,joined)==known[X]
    print('INDEPENDENT_LITERAL_GENEALOGY_PASS',f'X={X}',f'B={B}',f'firstpairs={firstpairs}',f'birthpairs={birthpairs}',f'credit={credit}',f'joined={joined}')

if __name__=='__main__':
    for x in map(int,sys.argv[1:] or ['256','512','1024']):run(x)
