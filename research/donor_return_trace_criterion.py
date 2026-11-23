#!/usr/bin/env python3
"""Exact source-weighted q-return trace via SIGNED FULL PREFIX words.
Run: python3 research/donor_return_trace_criterion.py 256 1024 4096
"""
from collections import defaultdict
from math import isqrt
from donor_word_crt_cylinder import trace,primes
import sys

def audit(X):
 B=isqrt(7*X)+(isqrt(7*X)**2<7*X)
 ps=primes(B);N=X//2
 words=defaultdict(list)
 owner=defaultdict(list)
 for M in range(X+1,2*X,2):
  path=trace(M,B);seen=set();oldowner=set()
  for i,(d,parity,t) in enumerate(path):
   qs=[q for q in ps if q>=11 and d%q==0]
   key=tuple((dd,par) for dd,par,_ in path[:i+1])
   for q in qs:
    if q in seen:words[(q,key)].append(M)
    seen.add(q)
   if qs:
    qowner=min(qs)
    if qowner in oldowner:owner[(qowner,key)].append(M)
    oldowner.add(qowner)
 real=sum(map(len,words.values()));owner_real=sum(map(len,owner.values()));bound=0;unique_single=0;max_weight=0;max_bound=0
 for (q,key),starts in words.items():
  D=1;marked=set()
  for d,_ in key:
   for p in ps:
    if d%p==0 and p not in marked:marked.add(p);D*=p
  assert all(m%D==starts[0]%D for m in starts),(X,key,q,D,starts)
  b=(N-1)//D+1
  assert len(starts)<=b
  bound+=b
  max_weight=max(max_weight,len(starts));max_bound=max(max_bound,b)
  unique_single+=(len(starts)==1)
 print('RETURN_WORD_TRACE_PASS',f'X={X}',f'B={B}',f'all_q_returns={real}',f'owner_returns={owner_real}',f'distinct_signed_prefix_words={len(words)}',f'CRT_upper_sum_on_realized_words={bound}',f'max_word_source_weight={max_weight}',f'max_single_word_CRT_bound={max_bound}',f'single_source_words={unique_single}')
if __name__=='__main__':
 for x in map(int,sys.argv[1:] or ['256','1024']):audit(x)
