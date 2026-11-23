#!/usr/bin/env python3
"""Independent per-integer parity-GCD check of top-band donor-diversity and event-fibre counts."""
from collections import Counter
from math import gcd, isqrt
import sys

def primes_upto(B):
    return [n for n in range(3, B + 1, 2)
            if all(n % p for p in range(3, isqrt(n) + 1, 2))]

def audit(X):
    B = isqrt(7*X)
    if B*B < 7*X: B += 1
    pp = primes_upto(B)
    incidents=firsts=0
    hist=Counter()
    episode=Counter()
    for M in range(X+1, 2*X, 2):
        K = (7*M-1)//4
        C = 2*M-2
        events=[]
        for n in range(M+3,K+1):
            raw = gcd(n,C-1) if n%2==0 else gcd(n-2,C+1)
            d=1
            f=[]
            for p in pp:
                if raw%p==0:
                    d*=p
                    f.append(p)
            if d>1:
                C+=d-1
                events.append((n,C,tuple(f)))
        last={}
        for k,(n,C,fs) in enumerate(events):
            for q in fs:
                if q>=11 and 2*q>=B:
                    incidents+=1
                    if q not in last: firsts+=1
                    else:
                        i=last[q]
                        high=[]
                        for _,_,between in events[i+1:k]:
                            rr=[r for r in between if r>=11]
                            if rr:high.extend(rr)
                        hist[min(len(set(high)),4)]+=1
                        episode[q,events[i][0],events[i][1],n]+=1
                    last[q]=k
    out={"X":X,"B":B,"incidence":incidents,"first":firsts,
         "returns":incidents-firsts,"diversity":tuple(hist[i] for i in range(5)),
         "episode_classes":len(episode),"max_fibre":max(episode.values(), default=0)}
    print("LITERAL_DONOR_DIVERSITY_PASS",out)
    return out

if __name__=="__main__":
    for X in map(int,sys.argv[1:] or [256,512,1024]):audit(X)
