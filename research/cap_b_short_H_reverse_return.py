#!/usr/bin/env python3
"""Finite arithmetic certificate for low-offset returns via short-H events.

The CRT enumeration deliberately overapproximates genuine first-gcd paths.
Not a Lean proof and not a proof of unrestricted Cap B.
"""
from math import gcd

OFFSETS = tuple(range(0, 11, 2))
EXPECTED = (110466, 22, 180, 86, 16)


def join(a, L, b, m):
    d = gcd(L, m)
    if (b - a) % d:
        return None
    q = m // d
    if q == 1:
        return a, L
    step = ((b - a) // d * pow(L // d, -1, q)) % q
    return (a + L * step) % (L * q), L * q


def clipped(r, C, L):
    v = gcd(r, C - 1) if r % 2 == 0 else gcd(r - 2, C + 1)
    return gcd(v, L)


def validates(word, terminal_s, L, terminal_X):
    travel = sum(g for g, _ in word)
    growth = sum(e - 1 for _, e in word)
    s = (terminal_s - travel) % L
    C = (2 * terminal_s - terminal_X - growth) % L
    for g, e in word:
        for k in range(1, g):
            if clipped(s + k, C, L) != 1:
                return False
        if clipped(s + g, C, L) != e:
            return False
        s += g
        C += e - 1
    return True


def enumerate_reverse():
    nodes = 0
    maxima = {'count': 0, 'growth': 0, 'travel': 0, 'start_X': 0}

    def dfs(Xf, sf_parity, a, L, travel, growth, word):
        nonlocal nodes
        nodes += 1
        start_X = Xf + growth - 2 * travel
        maxima['count'] = max(maxima['count'], len(word))
        maxima['growth'] = max(maxima['growth'], growth)
        maxima['travel'] = max(maxima['travel'], travel)
        maxima['start_X'] = max(maxima['start_X'], start_X)
        after_X = Xf + growth - 2 * travel
        even_hit = (sf_parity - travel) % 2 == 0
        for gap in range(1, 11):
            for e in range(3, 34, 2):
                if gap > 2 * e or e - 1 >= 3 * (gap + 1):
                    continue
                before_X = after_X + (e - 1) - 2 * gap
                if before_X < 0:
                    continue
                # An actual hit has post-offset 0 mod 2e (even),
                # or 6 mod 2e (odd).
                if (after_X - (0 if even_hit else 6)) % e:
                    continue
                # Event index r=sf-travel is divisible by e when even,
                # or r-2 is divisible by e when odd.
                required = ((0 if even_hit else 2) + travel) % e
                crt = join(a, L, required, e)
                if crt is None:
                    continue
                new_a, new_L = crt
                new_word = ((gap, e),) + word
                if not validates(new_word, new_a, new_L, Xf):
                    continue
                dfs(Xf, sf_parity, new_a, new_L,
                    travel + gap, growth + e - 1, new_word)

    for Xf in OFFSETS:
        for sf_mod6 in range(6):
            dfs(Xf, sf_mod6, sf_mod6, 6, 0, 0, ())
    result = (nodes, maxima['count'], maxima['growth'], maxima['travel'], maxima['start_X'])
    assert result == EXPECTED, (result, EXPECTED)
    return result


def full_gcd(r, C):
    return gcd(r, C - 1) if r % 2 == 0 else gcd(r - 2, C + 1)


def full_witness(s0, C0, word, expected_travel, expected_growth, expected_end_X, short_only=True):
    s, C = s0, C0
    for i, (g, e) in enumerate(word):
        assert e % 2 == 1 and e >= 3
        if short_only:
            assert g <= 10 and e <= 33 and e - 1 < 3 * (g + 1)
        r = s + g
        assert r <= C
        for j in range(s + 1, r):
            assert full_gcd(j, C) == 1, (i, j)
        assert full_gcd(r, C) == e, (i, r, e, full_gcd(r, C))
        s = r
        C += e - 1
        assert 2*s-C >= 0
    assert (s-s0, C-C0, 2*s-C) == (expected_travel, expected_growth, expected_end_X)
    return s,C

# True local first-gcd witness reaching offset 0 with growth=180.
LOW_GROWTH = ((9,29),(4,9),(2,5),(4,3),(5,11),(1,3),(6,19),(9,13),
              (2,5),(1,3),(3,7),(9,25),(8,17),(2,5),(1,3),(1,3),
              (5,5),(1,3),(8,23),(4,9))
# Same target state; alternate first gap gives travel=86.
LOW_TRAVEL = ((10,29),) + LOW_GROWTH[1:]
# Sharp starting offset 16, returning to 0 after 12 short-H events.
LOW_START16 = ((9,29),(1,3),(6,19),(2,5),(4,3),(5,11),
               (1,3),(3,7),(5,17),(2,5),(1,3),(1,3))
# A true 42-event short-H run from a VERY HIGH offset, not a real record state.
HIGH_42 = ((1,3),(1,3),(1,5),(2,7),(3,3),(3,11),(3,3),
           (7,17),(2,5),(2,3),(1,3),(7,23),(5,3),(8,5),
           (4,3),(5,11),(1,3),(7,5),(5,3),(9,29),(3,3),
           (9,17),(3,3),(7,11),(4,13),(1,3),(4,11),(2,3),
           (3,5),(3,9),(10,25),(10,7),(10,5),(6,3),
           (5,17),(1,3),(6,19),(8,17),(1,5),(2,3),
           (1,3),(10,31))


def main():
    n = enumerate_reverse()
    print('PASS reverse CRT: nodes=%d, count<=%d, Hshort<=%d, travel<=%d, startX<=%d' % n)
    assert len(LOW_GROWTH)==20 and len(LOW_START16)==12 and len(HIGH_42)==42
    full_witness(117649232195,235298464380,LOW_GROWTH,85,180,0)
    full_witness(117649232194,235298464380,LOW_TRAVEL,86,180,0)
    full_witness(51171392,102342768,LOW_START16,40,96,0)
    full_witness(4066542049924,5776231270430,HIGH_42,186,322,2356852829468)
    # The two remaining ways to return from high offset are both real
    # locally: fast non-H or long-prime H, neither is a short-H event.
    full_witness(200,304,((2,101),),2,100,0,short_only=False)
    full_witness(1482,2928,((35,101),),35,100,6,short_only=False)
    print('PASS full-gcd witnesses: H=180, T=86, Xstart=16, and high-offset 42-event run')
    print('PASS exact high-to-low resets: fast p=101/g=2 and long-H p=101/g=35')
    print('All witnesses are synthetic local states; universal Cap B remains OPEN.')

if __name__ == '__main__':
    main()
