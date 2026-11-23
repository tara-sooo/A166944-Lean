#!/usr/bin/env python3
"""Exact LOW7 prefix-growth spectrum and CRT-compressed post-q refiring screen.
Runs both frozen event jumps and an independent integer-by-integer LOW7 oracle.
The q-positive set is finite, independently of q's size, once the spectrum is known.
"""
from math import gcd
from itertools import combinations
S=(3,5,7)
P=105

def gap(t,c,ps):
    g=None;d=1
    for p in ps:
        if (c-1)%p==0:r=0
        elif (c+1)%p==0:r=p+2
        else:continue
        step=(r-t)%(2*p) or 2*p
        if g is None or step<g:g=step;d=p
        elif step==g:d*=p
    return g,d

def jumps(t,c):
    out=[0];E=0
    for _ in range(10):
        g,d=gap(t,c,S)
        if g is None:return out
        t+=g;c+=d-1;E+=d-1;out.append(E)
    raise AssertionError('LOW7 depth>9')

def literal(t,c):
    out=[0];E=0
    for n in range(t+1,t+60):
        if all((c-1)%p and (c+1)%p for p in S):return out
        raw=gcd(n,c-1) if n%2==0 else gcd(n-2,c+1)
        d=1
        for p in S:
            if raw%p==0:d*=p
        if d>1:c+=d-1;E+=d-1;out.append(E)
    raise AssertionError('LOW7 time>56')

def primes_up_to(B):
    return [p for p in range(11,B+1,2) if all(p%d for d in range(3,int(p**.5)+1,2))]

def reconstructed(t,C,q,return_t):
    T=2*P*q
    if t<1:t+=T;return_t+=T
    for a in (1,3,5,7,15,21,35,105):
        pre=C-(a*q-1)
        if pre<=0:pre+=T
        raw=gcd(t,pre-1) if t%2==0 else gcd(t-2,pre+1)
        d=1
        for p in (*S,q):
            if raw%p==0:d*=p
        if d==a*q:
            return (t-1,pre,t,return_t,a)
    return None

def q_cone(q):
    inv=pow(2*P,-1,q)
    winners=0;reachable=0;witness=None
    for local_t in range(2*P):
        even=(local_t%2==0)
        q_clock_t=0 if even else 2
        t=local_t+2*P*((q_clock_t-local_t)*inv%q)
        q_c=0 if even else q-2
        for h in range(P):
            C=2*h+2*P*((q_c-2*h)*inv%q)
            now_t,now_c=t,C
            for _ in range(10):
                gs,ds=gap(now_t,now_c,S)
                gq,_=gap(now_t,now_c,(q,))
                if gq is not None and (gs is None or gq<=gs):
                    winners+=1
                    res=reconstructed(t,C,q,now_t+gq)
                    if res is not None:
                        reachable+=1
                        if witness is None:witness=res
                    break
                if gs is None:break
                now_t+=gs;now_c+=ds-1
            else:raise AssertionError('LOW7 event bound')
    return winners,reachable,witness

def main():
    union=set();sample=0
    for t in range(2*P):
        for h in range(P):
            E=jumps(t,2*h);E2=literal(t,2*h)
            assert E==E2,(t,h,E,E2)
            union.update(E);sample+=1
    spec=sorted(union)
    print('LOW7_FULL_PREFIX_SPECTRUM_PASS states=',sample,'size=',len(spec),'values=',spec,flush=True)
    qs=[q for q in primes_up_to(151) if any((x-a)%q==0 for x in spec for a in (-1,1,3))]
    print('POSSIBLE_Q_FROM_SPECTRUM=',qs,flush=True)
    assert qs==[11,13,17,19,23,29,31,37,41,43,101,103,107]
    for q in sorted(set(qs)|{47,53,59,97,109,149}):
        winners,reachable,witness=q_cone(q)
        print('LOW7_Q_CONE_PASS q=',q,'states=',2*P*P,'ghostPositive=',winners,
             'reachable=',reachable,'witness=',witness,flush=True)
        assert (q in qs)==(winners>0), (q,winners)
        assert (q in qs)==(reachable>0), (q,reachable)

if __name__=='__main__':main()
