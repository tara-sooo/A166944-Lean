#!/usr/bin/env python3
"""Complete CRT test for short selective-H strings followed by one fast low return.

This is a finite necessary-condition certificate, NOT a Lean proof of Cap B.
Requires only the Python 3 standard library.
"""
from math import gcd


def join(a, L, b, e):
    d = gcd(L, e)
    if (b-a) % d:
        return None
    q = e // d
    if q == 1:
        return a, L
    t = ((b-a)//d * pow(L//d, -1, q)) % q
    return (a+L*t) % (L*q), L*q


def projected(r, C, L):
    d = gcd(r if r%2 == 0 else r-2, C-1 if r%2 == 0 else C+1)
    return gcd(d, L)


def valid(word, a, L, x0):
    t, x = 0, x0
    for g, e in word:
        C = (2*(a+t)-x) % L
        for h in range(1, g):
            if projected(a+t+h, C, L) != 1:
                return False
        if projected(a+t+g, C, L) != e:
            return False
        t += g
        x += 2*g-(e-1)
    return True


def short_roots():
    total = 0
    global_max_x = 0
    canonical_max_x = 0
    high = []
    canonical = []
    for x0 in range(0, 11, 2):
        for root in range(6):
            def dfs(t, x, a, L, word):
                nonlocal total, global_max_x, canonical_max_x
                total += 1
                global_max_x = max(global_max_x, x)
                if x0 == 6 and root == 3:
                    canonical_max_x = max(canonical_max_x, x)
                    canonical.append((x0,root,t,x,a,L,word))
                if x >= 96:
                    high.append((x0,root,t,x,a,L,word))
                for g in range(1, 11):
                    even = (root+t+g)%2 == 0
                    for e in range(3,34,2):
                        if g > 2*e or e-1 >= 3*(g+1):
                            continue
                        xn = x+2*g-(e-1)
                        if xn < 0:
                            continue
                        if (x+2*g+(1 if even else -5))%e:
                            continue
                        joined = join(a,L,((0 if even else 2)-t-g)%e,e)
                        if joined is None:
                            continue
                        b,m = joined
                        w = word+((g,e),)
                        if valid(w,b,m,x0):
                            dfs(t+g,xn,b,m,w)
            dfs(0,x0,root,6,())
    assert (total,global_max_x,canonical_max_x,len(high),len(canonical)) == (214780,138,90,108,5123)
    return high,canonical


def bridge_max(nodes, limit):
    crt_count = passed = 0
    best = (0,None)
    for x0,root,t,x,a,L,word in nodes:
        for xend in (0,6):
            delta = x-xend
            # Fast iff e-1 = delta+2g >= 3(g+1), hence g<=delta-3.
            for g in range(1,delta-2):
                e = delta+2*g+1
                if e>limit:
                    continue
                if (root+t+g)%2 != (0 if xend==0 else 1):
                    continue
                joined = join(a,L,((0 if xend==0 else 2)-t-g)%e,e)
                if joined is None:
                    continue
                crt_count += 1
                b,m = joined
                if valid(word+((g,e),),b,m,x0):
                    passed += 1
                    if e>best[0]:
                        best = e,(x0,root,t,x,g,xend,b,m,word)
    return best,crt_count,passed


def actual(r,C):
    return gcd(r if r%2==0 else r-2,C-1 if r%2==0 else C+1)


def check_witness(s0,x0,word,last_e,expected):
    s,C = s0,2*s0-x0
    for i,(g,e) in enumerate(word,1):
        assert 1<=g and s+g<=C
        for j in range(s+1,s+g):
            assert actual(j,C)==1,(i,j)
        assert actual(s+g,C)==e,(i,s+g,C,e)
        s,C=s+g,C+e-1
        assert 2*s>=C
        if i<len(word):
            assert g<=10 and e<=33 and e-1<3*(g+1)
        else:
            assert e==last_e and e-1>=3*(g+1)
    assert (s,C)==expected and 2*s-C in (0,6)
    return (s0,2*s0-x0,s,C)


GENERAL=((4,3),(9,5),(3,3),(10,17),(2,3),(9,7),(6,5),(3,9),
         (10,5),(2,3),(5,11),(1,3),(9,5),(3,3),(3,7),(7,5),(2,3),
         (90,283))
CANONICAL=((7,7),(10,5),(4,3),(9,7),(3,11),(2,7),(4,3),(7,19),
           (8,5),(3,9),(10,5),(2,3),(6,17),(6,3),(9,13),(77,239))


def main():
    high,canonical = short_roots()
    # At x<96, a fast bridge has e<=3*x-5<=277<283.
    overall,all_crt,all_valid = bridge_max(high,409)
    canon,can_crt,can_valid = bridge_max(canonical,265)
    assert (overall[0],all_crt,all_valid) == (283,5272,768)
    assert (canon[0],can_crt,can_valid) == (239,45647,14947)
    assert check_witness(124860554,6,GENERAL,283,(124860732,249721464))
    assert check_witness(1703085153,6,CANONICAL,239,(1703085320,3406170640))
    print('PASS 214780 low-offset short-H prefixes: max end X=138; canonical root max=90')
    print('PASS 108 high-X roots (X>=96), 5272 CRT bridges, 768 projected valid: max fast e=283')
    print('PASS 5123 canonical roots, 45647 CRT bridges, 14947 projected valid: max fast e=239')
    print('PASS exact full-gcd witnesses: e=283 (18 events) and canonical-shaped e=239 (16 events)')
    print('Consequently each low-start short-only + one fast-low-return macro has Hshort<=234 and G<=516.')
    print('These are synthetic local witnesses and conditional macros. Unrestricted Cap B remains OPEN.')

if __name__=='__main__':
    main()
