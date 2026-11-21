"""Direct-gcd audit of small-wheel inertia and the phase-growth budget.

All arithmetic uses the Python standard library. Synthetic seeds are NOT
attained A166944 canonical records. The first synthetic M and M-2 are prime.
"""
from math import gcd, isqrt

WITNESSES = [
    (1_369_875_375_961, [(421, 210), (2521, 1260)], True),
    (735_167_457_611_161, [(421, 210), (2521, 1260),
                            (3361, 1680)], False),
    (9_801_898_053_991, [(421, 210), (176401, 88200),
                          (421, 210)], False),
]


def is_prime_64(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def step_gcd(r, C):
    return gcd(r if r % 2 == 0 else r - 2,
               C - 1 if r % 2 == 0 else C + 1)


def check_synthetic(M, events, twin):
    if twin:
        assert is_prime_64(M) and is_prime_64(M - 2)
    s, C = M + 2, 2*M - 2
    initial_C = C
    min_F = 4*s - 9*C
    max_drawup = 0
    for i, (e, g) in enumerate(events, 1):
        assert is_prime_64(e) and e % 420 == 1
        assert s % 2 == 1 and C % 210 == 0 and 2*s-C == 6
        for r in range(s + 1, s + g + 1):
            d = step_gcd(r, C)
            assert d == (e if r == s + g else 1), (i, r, d)
            next_C = C + d - 1
            F = 4*r - 9*next_C
            max_drawup = max(max_drawup, F-min_F)
            min_F = min(min_F, F)
            assert F-min_F < 32 + 8*isqrt(next_C+1)
        C += e - 1
        s += g
        assert 2*s-C == 6 and C % 210 == 0
        print("event", i, "r", s, "gap", g, "increment", e,
              "C", C, "offset", 2*s-C)
    assert max_drawup <= 4*(max(g for e, g in events)-1)
    print("synthetic M", M, "twin-shaped", twin,
          "maximum F drawup", max_drawup,
          "initial slow threshold", 32 + 8*isqrt(initial_C+1))


def check_actual_coverage(limit=1_000_000):
    D = [0]*(limit+1)
    d = [0]*(limit+1)
    D[1] = 1
    d[1] = 2
    for r in range(2, limit+1):
        d[r] = step_gcd(r, D[r-1])
        D[r] = D[r-1] + d[r] - 1
    for u, v in ((2, 15000), (2500, 250000),
                 (45895, 80000), (500000, limit)):
        growth = D[v]-D[u]
        data = []
        for q in (3, 5, 7, 11):
            active = sum(D[s] % q in (1, q-1)
                         for s in range(u, v-2*q+1))
            changes = sum(d[r] % q != 1 for r in range(u+1, v+1))
            assert active <= 2*q*changes
            data.append((q, active, changes))
        assert sum(active/q for q, active, _ in data)/len(data) <= growth
        print("actual window", u, v, "growth", growth,
              "q/active/phase changes:", data)


if __name__ == "__main__":
    for witness in WITNESSES:
        check_synthetic(*witness)
    check_actual_coverage()
    print("PASS")
