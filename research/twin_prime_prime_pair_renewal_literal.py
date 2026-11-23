#!/usr/bin/env python3
"""Independent literal n-by-n oracle for individual/prime-pair renewal packing.
Run python3 research/twin_prime_prime_pair_renewal_literal.py 256 512 1024
"""
from itertools import combinations
from math import gcd, isqrt, prod
from sys import argv


def primes_to(b):
    return [q for q in range(3, b + 1, 2)
            if all(q % v for v in range(3, isqrt(q) + 1, 2))]


def audit(x):
    b = isqrt(7 * x) + (isqrt(7 * x) ** 2 < 7 * x)
    ps = primes_to(b)
    sums = dict(growth=0, events=0, prime_hits=0, prime_returns=0,
                pair_hits=0, pair_first=0, pair_returns=0, pair_weight=0,
                pair_return_weight=0, max_pair=0, max_repeated_pair=0,
                max_pair_multiplicity=0, pair_return_over_x4=0,
                pair_return_over_x2=0, big_pair_first_over_x2=0,
                triple_events=0, triple_pair_weight=0, odd_pair_return=0,
                large_reset=0, large_comp_reset=0, large_pair_k6=0, large_pair_k4=0)
    for m in range(x + 1, 2 * x, 2):
        c = 2 * m - 2
        k = (7 * m - 1) // 4
        first_c = c
        prime_occ = {}
        pair_occ = {}
        for n in range(m + 3, k + 1):
            raw = gcd(n - 2 if n % 2 else n, c + 1 if n % 2 else c - 1)
            factors = [p for p in ps if raw % p == 0]
            if not factors:
                continue
            d = prod(factors)
            assert d <= n and d >= 3
            qval = (n - 2 if n % 2 else n) // d
            assert (qval >= 3 and qval % 2 == 1) if n % 2 else (qval >= 2 and qval % 2 == 0)
            if 4 * d > k:
                assert qval == (3 if n % 2 else 2)
                assert 2 * n - (c + d - 1) == (6 if n % 2 else 0)
                sums['large_reset'] += 1
                sums['large_comp_reset'] += len(factors) >= 2
            sums['events'] += 1
            sums['triple_events'] += len(factors) >= 3
            sums['growth'] += d - 1
            for p in factors:
                sums['prime_hits'] += 1
                if p in prime_occ:
                    last_c, last_n, count = prime_occ[p]
                    recharge = c - last_c
                    if p >= 5:
                        assert recharge >= p - 1 and recharge % 2 == 0
                        if last_n % 2:
                            assert recharge >= p + 1
                        assert n - last_n >= p - 2
                    sums['prime_returns'] += 1
                else:
                    count = 0
                prime_occ[p] = (c + d - 1, n, count + 1)
            for p, q in combinations(factors, 2):
                target = p * q
                if 6 * target > k:
                    assert d == target
                    sums['large_pair_k6'] += 1
                if 4 * target > k:
                    assert d == target
                    sums['large_pair_k4'] += 1
                charge = (p - 1) * (q - 1) * (d // target)
                sums['pair_hits'] += 1
                sums['pair_weight'] += charge
                sums['max_pair'] = max(sums['max_pair'], target)
                if len(factors) >= 3:
                    sums['triple_pair_weight'] += charge
                if target in pair_occ:
                    last_c, last_n, count = pair_occ[target]
                    recharge = c - last_c
                    assert recharge >= target - 1 and recharge % 2 == 0
                    if last_n % 2:
                        assert recharge >= target + 1
                        sums['odd_pair_return'] += 1
                    assert n - last_n >= target - 2
                    sums['pair_returns'] += 1
                    sums['pair_return_weight'] += charge
                    sums['max_repeated_pair'] = max(sums['max_repeated_pair'], target)
                    sums['pair_return_over_x4'] += target > x // 4
                    sums['pair_return_over_x2'] += target > x // 2
                else:
                    count = 0
                    sums['pair_first'] += 1
                    sums['big_pair_first_over_x2'] += target > x // 2
                count += 1
                pair_occ[target] = (c + d - 1, n, count)
                sums['max_pair_multiplicity'] = max(sums['max_pair_multiplicity'], count)
            c += d - 1
            assert c <= 2 * n
        growth = c - first_c
        assert growth <= 2 * k - first_c
        for p, (_, _, count) in prime_occ.items():
            if p >= 5:
                assert (2 * count - 1) * (p - 1) <= growth
        for target, (_, _, count) in pair_occ.items():
            assert (2 * count - 1) * (target - 1) <= growth
            if count >= 2:
                assert target <= 1 + (2 * k - first_c) // 3
    assert sums['pair_hits'] == sums['pair_first'] + sums['pair_returns']
    assert not sums['pair_return_over_x2']
    fixed = {
        256: (10222, 23, 0, 500, 0, 55, 0),
        512: (20048, 27, 0, 948, 0, 145, 0),
        1024: (39940, 48, 0, 1164, 0, 133, 0),
        4096: (399142, 535, 0, 36604, 0, 481, 0),
        16384: (2915326, 4396, 249, 342248, 12484, 1357, 143),
    }
    if x in fixed:
        assert (sums['growth'], sums['pair_hits'], sums['pair_returns'],
                sums['pair_weight'], sums['pair_return_weight'],
                sums['max_pair'], sums['max_repeated_pair']) == fixed[x]
    print(f"PAIR_LITERAL_PASS X={x} B={b} {sums}")


def check_witness(m, b, pair, expected):
    ps = primes_to(b)
    c = 2 * m - 2
    k = (7 * m - 1) // 4
    matched = []
    for n in range(m + 3, k + 1):
        raw = gcd(n - 2 if n % 2 else n, c + 1 if n % 2 else c - 1)
        f = [p for p in ps if raw % p == 0]
        d = prod(f)
        if d > 1:
            if d % pair == 0:
                matched.append((n, c, d, c + d - 1, 2 * n - c - (d - 1)))
            c += d - 1
    assert matched == expected, (m, matched, expected)


if __name__ == '__main__':
    check_witness(49, 31, 33, [(66, 100, 33, 132, 0)])
    check_witness(17373, 339, 21, [(17556, 35050, 21, 35070, 42),
                                   (17808, 35512, 21, 35532, 84)])
    print('PAIR_LITERAL_WITNESSES_PASS M=49 M=17373')
    for arg in argv[1:] or ('256', '512'):
        x = int(arg)
        assert x >= 256 and x % 4 == 0
        audit(x)