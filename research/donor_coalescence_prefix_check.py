#!/usr/bin/env python3
"""Source coalescence is compatible with distinct signed full-prefix words."""
from collections import defaultdict
from donor_word_crt_cylinder import trace
from math import isqrt

def run(X):
    B=isqrt(7*X)+(isqrt(7*X)**2<7*X)
    episodes=defaultdict(list)
    for M in range(X+1,2*X,2):
        events=trace(M,B)
        last={}
        C=2*M-2
        for k,(d,odd,t) in enumerate(events):
            C+=d-1
            for q in range(11,B+1,2):
                if 2*q<B or d%q:continue
                if any(q%r==0 for r in range(3,isqrt(q)+1,2)):continue
                if q in last:
                    prev,prev_t,prev_C=last[q]
                    key=(q,prev_t,prev_C,t)
                    prefix=tuple((ed,eo) for ed,eo,_ in events[:k+1])
                    episodes[key].append((M,prefix))
                last[q]=(k,t,C)
    maxkey,maxvals=max(episodes.items(),key=lambda kv:len(kv[1]))
    unique=len({w for m,w in maxvals})
    print('COALESCENCE_FULL_PREFIX_PASS',f'X={X}',f'B={B}',f'key={maxkey}',f'weight={len(maxvals)}',f'unique_signed_full_prefixes={unique}',f'M_example={[v[0] for v in maxvals[:8]]}')
    assert unique==len(maxvals)

if __name__=='__main__':
    for x in (256,2048,4096):run(x)
