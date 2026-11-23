#!/usr/bin/env python3
"""Strict finite MIN wheel source-weighted first-top and repeat diagnostic.

Prime calendars are reconstructed from prime factors of C-1 and C+1.
For tiny inputs, literal integer-by-integer parity-GCD transitions are crosschecked.
Finite checks only; no analytic or twin-prime infinitude claim.
"""
from __future__ import annotations

import math
import sys
from collections import Counter, defaultdict


def smallest_factors(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for i in range(2, math.isqrt(limit) + 1):
        if spf[i] == i:
            for k in range(i * i, limit + 1, i):
                if spf[k] == k:
                    spf[k] = i
    return spf


def distinct_factors(n: int, spf: list[int], B: int) -> list[int]:
    ans = []
    while n > 1:
        p = spf[n]
        if p <= B and p != 2:
            ans.append(p)
        while n % p == 0:
            n //= p
    return ans


def next_event(t: int, C: int, bound: int, B: int,
               spf: list[int]) -> tuple[int, int] | None:
    if C < 2:
        raise AssertionError((t, C))
    best = None
    for p in distinct_factors(C - 1, spf, B):
        v = (t // (2 * p) + 1) * (2 * p)
        if v <= bound and (best is None or (v, p) < best):
            best = (v, p)
    for p in distinct_factors(C + 1, spf, B):
        base = t + 1
        v = base + ((p + 2 - base) % (2 * p))
        if v <= bound and (best is None or (v, p) < best):
            best = (v, p)
    return best


def literal_next_event(t: int, C: int, bound: int, B: int,
                       spf: list[int]):
    for j in range(t + 1, bound + 1):
        g = math.gcd(j, C - 1) if j % 2 == 0 else math.gcd(j - 2, C + 1)
        p = distinct_factors(g, spf, B)
        if p:
            return j, p[0]
    return None


def wheel_path(t: int, C: int, bound: int, B: int, spf: list[int]):
    while True:
        event = next_event(t, C, bound, B, spf)
        if event is None:
            return
        t, p = event
        C += p - 1
        assert C % 2 == 0
        yield t, p, C


def audit(X: int) -> None:
    assert X >= 256 and X % 4 == 0
    B = math.isqrt(7 * X)
    if B * B < 7 * X:
        B += 1
    L = 2
    y = 2
    # Maximal primorial <= floor(sqrt(B)), odd primes only.
    for q in range(3, B + 1, 2):
        if all(q % d for d in range(3, math.isqrt(q) + 1, 2)):
            if L * q > math.isqrt(B):
                break
            L *= q
            y = q
    Kmax = (7 * (2 * X - 1) - 1) // 4
    spf = smallest_factors(max(7 * X + 64, 2 * Kmax + 64))

    # Compare the prime-clock accelerated transition with a literal oracle.
    if X <= 1024:
        for M in range(X + 1, min(2 * X, X + 49), 2):
            t, C, bound = M + 2, 2 * M - 2, (7 * M - 1) // 4
            for i in range(10):
                a = next_event(t, C, bound, B, spf)
                b = literal_next_event(t, C, bound, B, spf)
                assert a == b, (M, i, t, C, a, b)
                if a is None:
                    break
                t, p = a
                C += p - 1

    masses = Counter()
    E = 0
    raw_high = 0
    first = 0
    repeats = 0
    repeat_gap = Counter()
    terminal_pairs = set()
    travel_sum = 0
    source_count = 0
    for M in range(X + 1, 2 * X, 2):
        source_count += 1
        t0, C0, K = M + 2, 2 * M - 2, (7 * M - 1) // 4
        travel_sum += K - t0
        hist = []
        last = {}
        reset = None
        Cend = C0
        for t, p, Cend in wheel_path(t0, C0, K, B, spf):
            if p > y:
                raw_high += 1
                if p in last:
                    repeats += 1
                    repeat_gap[len(hist) - last[p] - 1] += 1
                else:
                    first += 1
                last[p] = len(hist)
                hist.append(p)
            if reset is None and p >= 11 and (2 * t - Cend == (0 if t % 2 == 0 else 6)):
                reset = t
                E += Cend - C0
        if reset is not None:
            masses[reset] += 1
        # A terminal pair must be prime if both frozen neighbors are prime.
        if Cend > 3 and all(distinct_factors(z, spf, math.isqrt(z)) == [] for z in (Cend - 1, Cend + 1)):
            terminal_pairs.add((Cend - 1, Cend + 1))

    assert travel_sum * 16 == 9 * X * X - 20 * X
    assert first + repeats == raw_high
    square_mass = sum(w * w for w in masses.values())
    S = sum(masses.values())
    assert 2 * (square_mass - S) <= E, (X, square_mass, S, E)

    def first_top(n):
        C0 = 2 * n if n % 2 == 0 else 2 * n - 6
        for t, p, C in wheel_path(n, C0, Kmax, B, spf):
            if p >= 11:
                return p >= max(37, (B + 1) // 2)
        return False

    top_set = {n for n in range(X + 3, Kmax + 1) if first_top(n)}
    reached_top = top_set.intersection(masses)
    weighted_top = sum(masses[n] for n in reached_top)
    assert weighted_top**2 <= len(reached_top) * square_mass
    assert len(reached_top) <= len(top_set)
    print(
        f'X={X} B={B} y={y} L={L} '
        f'reset_atoms={len(masses)} S={S} E={E} '
        f'sum_w2={square_mass} all_reset_first_top={len(top_set)} '
        f'reached_first_top={len(reached_top)} '
        f'weighted_first_top={weighted_top} '
        f'weighted_top/(XB)={weighted_top / (X * B):.8f} '
        f'high={raw_high} first={first} repeat={repeats} '
        f'repeat_m0={repeat_gap[0]} repeat_m1={repeat_gap[1]} '
        f'repeat_m2plus={sum(v for k, v in repeat_gap.items() if k >= 2)} '
        f'distinct_terminal_twins={len(terminal_pairs)}', flush=True,
    )


if __name__ == '__main__':
    args = [int(x) for x in sys.argv[1:]] or [256, 1024, 4096]
    for X in args:
        audit(X)
