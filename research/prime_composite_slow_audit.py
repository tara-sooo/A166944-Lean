"""Integer-only audit for the prime/composite gap-sum reduction.

Runs A166944 from a(1)=2. It checks finite cases, not any asymptotic conjecture.
"""
from math import gcd, isqrt

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def main(limit=2_500_000):
    d = [0] * (limit + 1)
    D = [0] * (limit + 1)
    D[1] = 1
    d[1] = 2
    max_increment = 2
    records = []
    for n in range(2, limit + 1):
        e = gcd(n if n % 2 == 0 else n-2,
                D[n-1]-1 if n % 2 == 0 else D[n-1]+1)
        d[n] = e
        D[n] = D[n-1] + e - 1
        if e > max_increment:
            max_increment = e
            if e > 5:
                records.append(e)
    print("M prime_hits composite_hits first_slow comp_gap_total comp_growth")
    for M in records:
        s = M + 2
        K = (7*M-1)//4
        if K > limit:
            break
        assert d[s] == M and D[s] == 2*M-2
        P = Q = gap_sum = growth = 0
        last = s
        minimum_F = 4*s - 9*D[s]
        slow_at = -1
        for r in range(s+1, K+1):
            e = d[r]
            if e > 1:
                g = r-last
                C = D[last]
                assert e <= M
                assert g*e <= 2*(C+1)
                if is_prime(e):
                    P += 1
                else:
                    Q += 1
                    gap_sum += g
                    growth += e-1
                    assert g*g <= 4*e
                last = r
            F = 4*r - 9*D[r]
            if slow_at < 0 and F-minimum_F >= 32+8*isqrt(D[r]+1):
                slow_at = r
            minimum_F = min(minimum_F, F)
        assert gap_sum*gap_sum <= 4*Q*(growth+Q)
        print(M, P, Q, slow_at, gap_sum, growth)

if __name__ == "__main__":
    main()
