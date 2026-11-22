#!/usr/bin/env python3
"""Exact A166944 artificial canonical GOOD-ancestry witnesses (stdlib only).
Every index step is independently checked by original parity-sensitive gcd.
Artificial starts are NOT asserted reached from a(1)=2. Cap B remains open.
"""
from math import gcd, isqrt

def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))

def factors(n):
    out = set()
    d = 3
    while d*d <= n:
        if n % d == 0:
            out.add(d)
            while n % d == 0: n //= d
        d += 2
    if n > 1: out.add(n)
    return out

def replay(m):
    s, K, C = m+2, (7*m-1)//4, 2*m-2
    N = R = 0
    used = set()
    peak = 1
    for n in range(s+1,K+1):
        e = gcd(n if n%2==0 else n-2, C-1 if n%2==0 else C+1)
        if e>1:
            N+=1
            fs=factors(e)
            R+=bool(fs & used)
            used |= fs
            peak=max(peak,e)
            C+=e-1
    return dict(M=m,K=K,N=N,R=R,G=C-(2*m-2),C=C,F=C+1,
                peak=peak,initial_twin=prime(m-2) and prime(m),
                final_twin=prime(C-1) and prime(C+1))

def check_relays(chain):
    rows = [replay(m) for m in chain]
    for row,child in zip(rows,chain[1:]):
        assert row['initial_twin'] and row['final_twin']
        assert row['F']==child and row['peak']<row['M']
        assert row['K'] < row['C']+3 == child+2
        assert gcd(row['C']+1,row['C']+1)==child
        assert row['C']+child-1 == 2*child-2
    return rows


def phase_collision_audit():
    """One actual record and two synthetic starts share the same 3465-wheel phase."""
    L=3465
    sources=(713833,124783,291103)
    expected=((2,5),(3,3),(6,7),(15,5),(21,33),(34,7))
    assert all(((m+2)%(2*L),(2*m-2)%L)==(45,84) for m in sources)
    for m in sources:
        s=m+2
        C=2*m-2
        hits=[]
        for n in range(s+1,s+100):
            e=gcd(gcd(n if n%2==0 else n-2,
                      C-1 if n%2==0 else C+1),L)
            if e>1:
                hits.append((n-s,e))
                C+=e-1
        assert tuple(hits)==expected
        assert C%L==138 and gcd((C-1)*(C+1),L)==1

    expected_stats={713833:(11,6,84),
                    124783:(93,72,2226),
                    291103:(142,117,7248)}
    for m,stats in expected_stats.items():
        z=replay(m)
        assert (z['N'],z['R'],z['G'])==stats
        assert z['initial_twin'] and z['final_twin']

    # Independent attainment test from the ORIGINAL initial recurrence D(1)=1.
    C=1
    record=1
    last=None
    for n in range(2,713833+3):
        e=gcd(n if n%2==0 else n-2,
              C-1 if n%2==0 else C+1)
        C+=e-1
        if e>record:
            record=e
            last=(n,e)
    assert last==(713835,713833) and C==2*713833-2
    print('PASS shared exact L=3465 phase (45,84), R values (6,72,117)')
    print('PASS independently attained original record M=713833 at n=713835')

def main():
    chain=[859,1723,3463,6961,13999,28183,56713,113623,230563]
    rows=check_relays(chain)
    assert [(x['M'],x['N'],x['R'],x['G']) for x in rows[:-1]]==[
        (859,1,0,6),(1723,4,2,18),(3463,6,1,36),
        (6961,9,4,78),(13999,11,4,186),(28183,21,12,348),
        (56713,19,13,198),(113623,107,84,3318)]
    c=3/(8*(3.5**.5))
    assert rows[-2]['R']/113623**.5>c
    print('PASS seven preceding GOOD relays, terminal M=113623: N=107 R=84, c=',c)

    parent,child =check_relays([237691,475381,957601])[:2]
    assert all(prime(x) for x in (237689,237691,475379,475381))
    assert (parent['N'],parent['R'],parent['G'],parent['F'])==(0,0,0,475381)
    assert (child['N'],child['R'],child['G'],child['F'])==(186,157,6840,957601)
    assert child['R']/475381**.5 >c
    print('PASS quiet parent 237691 -> busy child 475381, N=186, R=157')

    parent=replay(9931771)
    assert parent['initial_twin'] and parent['final_twin']
    assert (parent['N'],parent['G'],parent['F'])==(0,0,19863541)
    child=replay(19863541)
    assert child['initial_twin'] and child['final_twin']
    assert (child['N'],child['R'],child['G'],child['F'])==(401,357,41262,39768343)
    print('PASS quiet parent 9931771 -> busy child 19863541, N=401 R=357')
    print('PASS exact original parity gcd and prime tests; global bound OPEN')
    phase_collision_audit()

if __name__=='__main__':
    main()
