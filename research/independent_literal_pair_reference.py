#!/usr/bin/env python3
"""Independent literal one-step parity GCD reference for the (q,n,C) pair split.
Does NOT use prime clocks or event jumping. Runs X=256,512,1024 by default.
"""
from collections import defaultdict
from math import gcd, isqrt
import sys

def odd_primes(B):
    return [q for q in range(3,B+1,2) if all(q%d for d in range(3,isqrt(q)+1,2))]

def run(X):
    B=isqrt(7*X)+(isqrt(7*X)**2<7*X)
    P=odd_primes(B)
    pairs=defaultdict(lambda: defaultdict(int))
    events=hits=0
    for M in range(X+1,2*X,2):
        C=2*M-2
        for n in range(M+3,(7*M-1)//4+1):
            raw=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
            d=1
            for q in P:
                if raw%q==0:
                    d*=q
                    if q>=13:
                        pairs[(q,n)][C]+=1
                        hits+=1
            events+=any(raw%q==0 for q in P if q>=13)
            C+=d-1
    J=joined=0;maxr=0;maxmass=0;maxclock=0;maxState=0
    for (q,n),hist in pairs.items():
        mu=sum(hist.values())
        J+=q*mu*mu
        joined+=q*sum(v*v for v in hist.values())
        maxr=max(maxr,len(hist))
        maxmass=max(maxmass,mu)
        maxclock=max(maxclock,mu)
        maxState=max(maxState,max(hist.values()))
    print(f"LITERAL_PASS X={X} high={events} qHits={hits} J={J} joined={joined} off={J-joined} maxR={maxr} maxMu={maxclock} maxState={maxState}")
    known={256:(306,306,69690,66920,2770),512:(548,548,211392,207270,4122),1024:(992,992,477950,469820,8130)}
    if X in known:
        assert (events,hits,J,joined,J-joined)==known[X], (X,(events,hits,J,joined,J-joined),known[X])

if __name__=="__main__":
    for X in map(int,sys.argv[1:] or ['256','512','1024']):
        run(X)
