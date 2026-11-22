#!/usr/bin/env python3
"""OEIS A166944/A167493/A174214 and Shevelev f comparison audit.

Python 3 stdlib only. Exhaustive finite checks up to N=1,000,000.
The paper lemmas are argued separately in the companion research note.
Neither these checks nor OEIS's conditional theorems prove twin-prime
infinitude or Cap B.
"""
from math import gcd, isqrt
from bisect import bisect_right

N = 1_000_000

def prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    return all(n % p for p in range(3, isqrt(n) + 1, 2))

def verify():
    dual = [0] * (N + 1)
    alternate = [0] * (N + 1)
    reset = [0] * (N + 1)
    dual[1] = alternate[1] = 2
    reset[9] = 14

    records_dual = []
    records_alt = []
    last_dual = last_alt = 0
    reset_indices = [9]
    reset_fundamental = []
    dual_fundamental = []

    for n in range(2, N + 1):
        x = dual[n - 1]
        y = alternate[n - 1]
        ed = gcd(n if n & 1 else n - 2, x)
        ef = gcd(n, y if n & 1 else y + 2)
        dual[n] = x + ed
        alternate[n] = y + ef
        if ed > last_dual:
            last_dual = ed
            records_dual.append((n, ed))
        if ef > last_alt:
            last_alt = ef
            records_alt.append((n, ef))
        if n >= 7 and 2 * dual[n] == 3 * (n - 1):
            dual_fundamental.append(n)

        if n >= 10:
            old = reset[n - 1]
            g = gcd(n - 2 if n % 2 == 0 else n, old)
            reset[n] = old + 1 if g == 1 else 2 * n - 4
            if g > 1: reset_indices.append(n)
            if 2 * reset[n] == 3 * (n - 1):
                reset_fundamental.append(n)

    first_dual = [n for n in dual_fundamental if n <= 50000]
    first_reset = [n for n in reset_fundamental if n <= 50000]
    assert first_dual == [7,27,63,123,279,567,1143,2307,4623,9303,18687,38283]
    assert first_reset == [27,63,123,279,567,1143,2307,4623,9447,18927,38283]
    assert reset[15] == 26 and 2 * reset[15] != 3 * 14

    for k in reset_fundamental:
        r = (k + 5) // 2
        assert k == 2 * r - 5 and r % 2 == 0 and r >= 12
        assert reset[r] == 2 * r - 4
        assert prime(r - 5) and prime(r - 3)
        idx = bisect_right(reset_indices, r)
        assert idx == len(reset_indices) or reset_indices[idx] > k

    # For each actual even reset, test BOTH directions of the prime-pair
    # equivalence, if the candidate fundamental position is in the scan.
    tested_resets = 0
    for r in reset_indices:
        if r < 12 or r % 2 != 0: continue
        k = 2 * r - 5
        if k > N: continue
        idx = bisect_right(reset_indices, r)
        quiet = idx == len(reset_indices) or reset_indices[idx] > k
        assert quiet == (prime(r - 5) and prime(r - 3))
        tested_resets += 1

    assert (dual[4680], reset[4680]) == (9300,9300)
    assert (dual[4681], reset[4681]) == (9331,9358)
    assert dual[19035] != reset[19035] and dual[19036] == reset[19036] == 38068
    equal_dual_reset_50k = sum(dual[n] == reset[n] for n in range(9,50001))
    assert equal_dual_reset_50k == 35541

    # Section 4 alternative f(n) in Shevelev's 0912.4006.
    equal_dual_f = sum(dual[n] == alternate[n] for n in range(2,N+1))
    assert equal_dual_f == 999600

    dual_main = [(n,v) for n,v in records_dual if v >= 13]
    alt_main = [(n,v) for n,v in records_alt if v >= 13]
    assert len(dual_main) == len(alt_main) == 15
    assert [(n-2,v) for n,v in dual_main] == alt_main
    assert (28,13) in dual_main and (26,13) in alt_main
    assert (620464,310231) in dual_main and (620462,310231) in alt_main

    # Three-step commuting diamond: if synchronized at even n-1,
    # f takes q>1 at n while dual takes 1, and three other increments
    # are 1, then dual takes q at n+2 and states resynchronize.
    eligible = successful = 0
    defect_examples = []
    for n in range(4,N-2,2):
        x = dual[n-1]
        if x != alternate[n-1]: continue
        q = gcd(n,x+2)
        if q <= 1 or gcd(n-2,x) != 1: continue
        eligible += 1
        good = (gcd(n+1,x+1) == 1 and
                gcd(n+1,x+q) == 1 and
                gcd(n+2,x+q+3) == 1)
        if good:
            successful += 1
            assert dual[n+2] == alternate[n+2] == x+q+2
            assert dual[n] == x+1 and alternate[n] == x+q
        else:
            defect_examples.append((n,q))
    assert (eligible,successful) == (59,53)
    assert len(defect_examples) == 6
    assert (26,13) not in defect_examples

    # OEIS A167493 reports a composite increment 27.
    assert dual[620757] - dual[620756] == 27
    assert alternate[620757] - alternate[620756] == 27

    print("PASS reset twin-pair equivalence, tested even reset starts:",tested_resets)
    print("A174214 fundamental indices <=50000:",first_reset)
    print("A167493 fundamental indices <=50000:",first_dual)
    print("A167493=A174214 indices among 9..50000:",equal_dual_reset_50k)
    print("A167493=f same-value indices among 2..1e6:",equal_dual_f)
    print("A167493/f identical record values >=13:",len(dual_main),"offset: -2")
    print("Three-step commuting diamond eligible/success/defects:",
          eligible,successful,len(defect_examples))
    print("PASS finite exact recurrence audit; Cap B and infinitude OPEN")

if __name__ == "__main__":
    verify()
