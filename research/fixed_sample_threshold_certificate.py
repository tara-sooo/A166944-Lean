#!/usr/bin/env python3
"""Finite first-hit certificate for FixedSample2333 at M=45,895,573.

Does NOT establish the universal fixed sample theorem or twin prime infinitude.
Canonical start (M+2,2M-2) is provided by the existing verified record
prefix; this standalone script verifies its local continuation.
"""
from math import gcd, isqrt

M = 45_895_573
K = (7 * M - 1) // 4
GAPS_INCREMENTS = (
    (2,5), (1,3), (106,73), (15,19), (147,151), (34,53),
    (4,3), (3,5), (3,3), (30,17), (6,3), (3,77),
    (3,3), (8,5), (4,3), (4,23), (2,3), (10,5),
    (2,3), (7,13), (2,7), (2,11), (1,3), (90,47),
    (6,3), (3,13), (338,229), (19,31), (3,7), (7,5),
    (2,3), (68,83), (4,3), (2,53), (4,3), (11,977),
    (1,3),
)


def prime_by_complete_trial_division(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    for p in range(3, isqrt(n) + 1, 2):
        if n % p == 0:
            return False
    return True


def first_hit_gcd(index: int, horizon: int) -> int:
    if index % 2 == 0:
        return gcd(index, horizon - 1)
    return gcd(index - 2, horizon + 1)


def main() -> None:
    assert prime_by_complete_trial_division(M)
    assert prime_by_complete_trial_division(M - 2)
    assert len(GAPS_INCREMENTS) == 37
    s, C = M + 2, 2 * M - 2
    for i, (gap, e) in enumerate(GAPS_INCREMENTS, 1):
        r = s + gap
        assert r <= C, (i, s, C, r)
        for j in range(s + 1, r):
            assert first_hit_gcd(j, C) == 1, (i, j, C)
        assert first_hit_gcd(r, C) == e, (i, r, C, e)
        assert e >= 3 and e % 2 == 1 and e <= M
        s, C = r, C + e - 1
    assert (s, C) == (45_896_532, 91_793_058), (s, C)
    assert s < K <= C
    assert prime_by_complete_trial_division(C - 1)
    assert prime_by_complete_trial_division(C + 1)
    # For any j in (s,C], the even branch has j even with
    # 0 < j <= C and odd prime C-1: j cannot be a positive multiple of
    # C-1, because C-1 itself is odd and 2*(C-1)>C.
    # The odd branch has 0 < j-2 < C+1, a prime.
    # Thus all intervening gcd increments equal 1, and D(K)=C.
    D_at_K = C
    assert 1000 * D_at_K <= 2333 * M
    print(f"PASS: M={M}, K={K}, events={len(GAPS_INCREMENTS)}")
    print(f"PASS: terminal first-hit state s={s}, C={C}")
    print(f"PASS: complete trial division proves {C-1}, {C+1} prime")
    print(f"PASS: D(K)={C}; 1000*D(K)={1000*C} <= 2333*M={2333*M}")
    print("The universal FixedSample2333 statement remains OPEN.")


if __name__ == "__main__":
    main()
