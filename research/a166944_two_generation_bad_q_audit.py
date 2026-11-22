#!/usr/bin/env python3
"""GOOD-parent -> BAD-child q-clock and prime-quartet arithmetic audit.
Original A166944 parity-sensitive gcd; Python 3 stdlib only.
Finite integer checks are not a proof of Cap B or twin-prime infinitude.
"""
from math import gcd, isqrt
from collections import Counter

def factors(n):
    out=[];d=3
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=2
    if n>1:out.append(n)
    return out

def prime(n):
    return n>1 and all(n%d for d in range(2,isqrt(n)+1))

def replay(M):
    s=M+2;K=(7*M-1)//4;C=2*M-2;events=[]
    for n in range(s+1,K+1):
        before=C
        e=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
        if e>1:
            C+=e-1
            events.append((n,e,before,C))
    return dict(M=M,s=s,K=K,C=C,F=C+1,G=C-2*M+2,
                events=events,good=prime(C-1) and prime(C+1))

def terminal_q_catalysts(z):
    M,s,K,C=z['M'],z['s'],z['K'],z['C']
    qparts=[(q,sign) for sign in (-1,+1) for q in factors(C+sign)
            if q<=isqrt(C+1)]
    witnesses=[]
    for q,sign in qparts:
        changing=[(n,e,pre,post) for n,e,pre,post in z['events']
                  if (e-1)%q]
        if K-s>=2*q:
            assert changing,(M,K,C,q,sign)
        if not changing:continue
        r,e,pre,post=changing[-1]
        assert K-r<2*q,('last q change too early',M,K,C,q,r)
        assert (C-post)%q==0 and (post+sign)%q==0
        if q>=5:assert e%q not in (0,1),(M,q,r,e)
        elif q==3 and e%3==0:
            assert r==K and r%6==5 and C%3==1
        witnesses.append((q,sign,r,e,K-r))
    return witnesses

def good_parent_to_child(m):
    parent=replay(m)
    assert parent['good']
    M=parent['F']
    assert prime(M-2) and prime(M)
    s=M+2
    assert gcd(s-2,parent['C']+1)==M
    assert parent['C']+(M-1)==2*M-2
    child=replay(M)
    assert child['s']==s
    for q,sign,r,e,lag in terminal_q_catalysts(child):
        if q>=5:
            assert q<M-2
            assert (parent['C']-1)%q and (parent['C']+1)%q
    return parent,child

def quiet_parent_five_free(m):
    assert m>7 and all(prime(x) for x in (m-2,m,2*m-3,2*m-1))
    p=replay(m)
    assert (p['G'],p['F'])==(0,2*m-1)
    C0=4*m-4
    assert gcd((C0-1)*(C0+1),15)==1
    assert m%3==1 and m%5 not in (0,2)
    return p['F']

def inherited_prime_quartet(parent):
    m,G,M=parent['M'],parent['G'],parent['F']
    assert parent['good'] and all(prime(x) for x in (m-2,m,M-2,M))
    oddpart=G
    if oddpart:
        while oddpart%2==0:oddpart//=2
    for q in factors(oddpart) if oddpart else []:
        if q>=m-2:continue
        inv2=pow(2,-1,q)
        forbidden={0,2,inv2%q,(3*inv2)%q}
        assert m%q not in forbidden,(m,M,G,q,forbidden)
    if m>7 and G%5==0:
        assert m%30==1 and M%30==1
        assert (2*M-2)%60==0
        assert (2*M-3)%5 and (2*M-1)%5
    # Exact child q=5 initial-clock test, even without 5|G:
    c0=2*M-2
    assert ((c0-1)%5==0)==((G-3*m)%5==0)
    assert ((c0+1)%5==0)==((G-3*m-4)%5==0)
    return True

def check():
    a,b=good_parent_to_child(7)
    assert (a['F'],a['G'],b['good'],b['G'])==(13,0,False,16)
    w=terminal_q_catalysts(b)
    assert (3,-1,20,5,2) in w
    print('ORIGINAL record 7 GOOD -> 13 BAD:',w)

    a,b=good_parent_to_child(19)
    assert (a['F'],a['G'],b['good'],b['G'])==(43,6,False,48)
    w=terminal_q_catalysts(b)
    assert (7,1,66,33,9) in w
    print('ARTIFICIAL GOOD 19 -> BAD 43:',w)

    for m in (31,237691,9931771):
        M=quiet_parent_five_free(m)
        assert m%30==1 and M%60==1 and (2*M-2)%120==0
        if m<1000000:
            p,c=good_parent_to_child(m)
            assert c['good']
            inherited_prime_quartet(p)
            print('QUIET parent',m,'->',M,
                  'child nonunit count',len(c['events']))
        else:
            print('QUIET parent',m,'->',M,'3/5-inert child seed')

    quartets=g5=quiet=0
    for m in range(31,10001,2):
        if not (prime(m) and prime(m-2)):continue
        p=replay(m)
        if not p['good']:continue
        inherited_prime_quartet(p)
        quartets+=1;g5+=p['G']%5==0;quiet+=p['G']==0
    assert (quartets,g5,quiet)==(200,24,9)
    print('GOOD twin-prime parents <=10000:',quartets,
          '5|G:',g5,'G=0:',quiet)

    bad=[];stats=Counter()
    for M in range(7,3001,2):
        z=replay(M)
        if not z['good']:
            bad.append(M)
            w=terminal_q_catalysts(z)
            stats['bad_starts']+=1
            stats['proper_factor_witnesses']+=len(w)
            for q,sign,r,e,lag in w:
                stats['foreign_q5plus']+=q>=5
                stats['q3_special_selfhit']+=(q==3 and e%3==0)
    assert bad==[11,13,23,25,39,41,43,45,305]
    assert stats==Counter({'bad_starts':9,'proper_factor_witnesses':9,
                          'foreign_q5plus':8,'q3_special_selfhit':0})
    print('BAD synthetic M<=3000:',bad)

    arcs=[]
    for m in range(7,801,2):
        p=replay(m)
        if not p['good']:continue
        c=replay(p['F'])
        if not c['good']:arcs.append((m,p['F'],prime(m-2) and prime(m)))
    assert arcs==[(7,13,True),(15,43,False),(17,43,False),
                  (19,43,True),(21,43,False)]
    print('GOOD-parent to BAD-child synthetic arcs m<=800:',arcs)

    e=gcd(11-2,8+1)
    assert e==9 and (8+e-1)%3==1 and gcd(12,8+e-2)==3
    print('PASS exact 2-generation q catalyst and 4-form prime gate; Cap B OPEN')

if __name__=='__main__':
    check()
