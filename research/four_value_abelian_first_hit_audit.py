"""Exact integer certificates for four-value Abelian squares in A166944.

Python standard library only. The four-letter congruence classification and the
projected first-hit sieve are finite computations, not a twin-prime proof.
"""
from itertools import permutations, product
from math import gcd, isqrt


def det3(a):
    x, y, z = a[0]
    u, v, w = a[1]
    p, q, r = a[2]
    return x*(v*r-w*q)-y*(u*r-w*p)+z*(u*q-v*p)


def cof4(a):
    return [[(-1 if (i+j)%2 else 1)*det3(
        [[a[u][v] for v in range(4) if v != j]
         for u in range(4) if u != i])
             for j in range(4)] for i in range(4)]


def coefficients(perm):
    w = (0, 1, 2, 3) + perm
    return [[w[w.index(i):w.index(i,4)].count(j) for j in range(4)]
            for i in range(4)]


def forbidden_short(perm):
    w = (0, 1, 2, 3) + perm
    return (any(w[i] == w[i+1] for i in range(7)) or
            any(w[i] == w[i+2] and w[i+1] == w[i+3]
                for i in range(5)))


def prime(n):
    return n > 1 and all(n % j for j in range(2, isqrt(n)+1))


def certify_four():
    epsilons = tuple(product((-2, 0, 2), repeat=4))
    found = set()
    nonsingular = singular = 0
    for perm in permutations(range(4)):
        if forbidden_short(perm):
            continue  # immediate identical or alternating >=5 event increments
        A = coefficients(perm)
        counts = [sum(row) for row in A]
        for q in product((2, 4, 6, 8, 10, 12, 14), repeat=4):
            M = [[A[i][j] - (q[i] if i == j else 0)
                  for j in range(4)] for i in range(4)]
            co = cof4(M)
            det = sum(M[0][j]*co[0][j] for j in range(4))
            adj = [list(row) for row in zip(*co)]
            if det == 0:
                singular += 1
                nullrow = next((row for row in adj if any(row)), None)
                assert nullrow is not None  # all 157 have rank 3
                for eps in epsilons:
                    rhs = [counts[i]+eps[i] for i in range(4)]
                    assert sum(x*y for x,y in zip(nullrow,rhs)) != 0
                continue
            nonsingular += 1
            for eps in epsilons:
                rhs = [counts[i]+eps[i] for i in range(4)]
                first = sum(a*b for a,b in zip(adj[0],rhs))
                if first%det or first//det<5 or (first//det)%2==0:
                    continue
                nums = [sum(a*b for a,b in zip(row,rhs)) for row in adj]
                if any(n%det for n in nums):
                    continue
                es = tuple(n//det for n in nums)
                if (min(es)<5 or len(set(es))!=4 or
                    any(e%2==0 for e in es) or max(es)>2*min(es)):
                    continue
                other = tuple(es[j] for j in perm)
                word = es+other
                pref=[0]
                for e in word: pref.append(pref[-1]+e-1)
                assert all(
                    (pref[word.index(e,4)]-pref[word.index(e)])%e
                    in (0,2,e-2) for e in es)
                found.add((es,other))
    assert (nonsingular,singular,len(found)) == (38259,157,98)
    assert max(max(w1) for w1,w2 in found)==175
    allprime = sorted((a,b) for a,b in found if all(prime(e) for e in a))
    assert len(allprime)==4
    assert {tuple(sorted(a)) for a,b in allprime}=={(109,127,131,163)}
    print('Four-value exact integer certificate:',
          'nonsingular',nonsingular,'singular',singular,
          'compatible',len(found),'maximum',175)
    for a,b in allprime: print('  prime-only modular candidate:',a,b)


def crt(aa,pp):
    M=1
    for p in pp: M*=p
    return sum(a*(M//p)*pow(M//p,-1,p)
               for a,p in zip(aa,pp))%M


def projected_hit(r,C,P):
    # Restrict to factors dividing P. Reducing C mod P alone inside gcd
    # would introduce unrelated factors, which would be an invalid sieve.
    term = r if r%2==0 else r-2
    side = (C-1 if r%2==0 else C+1)%P
    return gcd(gcd(term,P),gcd(side,P))


def certify_odd_four_witness():
    word = (7,13,9,11,9,7,11,13)
    pref=[0]
    for e in word: pref.append(pref[-1]+e-1)
    P=9*7*11*13
    profiles=[]
    for nine in (1,8):
        c0=crt((6,6,6,nine),(7,13,11,9))
        positions={r for r in range(2*P)
                   if r%14==9 and projected_hit(r,c0,P)==7}
        counts=[len(positions)]
        for i,e in enumerate(word[1:],1):
            C=(c0+pref[i])%P
            nxt=set()
            for r in positions:
                for gap in range(1,27):
                    h=projected_hit(r+gap,C,P)
                    if h>1:
                        if h==e: nxt.add((r+gap)%(2*P))
                        break
            positions=nxt
            counts.append(len(positions))
        profiles.append(counts)
    assert profiles==[[1287,87,29,29,9,9,9,0],
                     [858,30,10,0,0,0,0,0]]
    print('Projected first-hit 7,13,9,11 word:',profiles)
    print('PASS')


if __name__=='__main__':
    certify_four()
    certify_odd_four_witness()
