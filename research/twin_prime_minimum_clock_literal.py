#!/usr/bin/env python3
"""Independent n-by-n squarefree wheel for minimal-triggered-prime gap/repeat ledger.
Run python3 research/twin_prime_minimum_clock_literal.py 256 512 1024 4096
"""
from math import gcd, isqrt, prod, log
from sys import argv


def primes_to(b):
    return [q for q in range(3, b + 1, 2)
            if all(q % j for j in range(3, isqrt(q) + 1, 2))]


def is_prime(n):
    return n >= 2 and all(n % q for q in range(2, isqrt(n) + 1))


def audit(x):
    b = isqrt(7 * x)
    b += b * b < 7 * x
    ps = primes_to(b)
    stat = dict(W=0, events=0, travel=0, first_min_p=0, repeat_min_p=0,
                first_time=0, repeat_time=0, all_first_p=0, all_repeat_p=0,
                good=0, bad=0, certified=0, min_f=0, min_z=0, min_z3=0,
                max_min_hits=0, comp_events=0, min3_repeat=0)
    for m in range(x + 1, 2 * x, 2):
        c = 2 * m - 2
        start = c
        t = m + 2
        k = (7 * m - 1) // 4
        minhits = {}
        allhits = {}
        for n in range(m + 3, k + 1):
            raw = gcd(n - 2 if n & 1 else n, c + 1 if n & 1 else c - 1)
            fac = [p for p in ps if raw % p == 0]
            if not fac:
                continue
            d = prod(fac)
            gap = n - t
            least = fac[0]
            assert gap <= 2 * least, (m, n, least, gap)
            stat['events'] += 1
            stat['comp_events'] += len(fac) >= 2
            stat['travel'] += gap
            if least in minhits:
                stat['repeat_min_p'] += least
                stat['repeat_time'] += gap
                stat['min3_repeat'] += least == 3
            else:
                stat['first_min_p'] += least
                stat['first_time'] += gap
            minhits[least] = minhits.get(least, 0) + 1
            for p in fac:
                allhits[p] = allhits.get(p, 0) + 1
            c += d - 1
            stat['W'] += d - 1
            t = n
            assert c <= 2 * n
        stat['min_f'] += len(minhits)
        stat['min_z'] += sum(v * v for v in minhits.values())
        stat['min_z3'] += minhits.get(3, 0) ** 2
        stat['max_min_hits'] = max(stat['max_min_hits'], *(minhits.values() or [0]))
        stat['all_first_p'] += sum(allhits)
        stat['all_repeat_p'] += sum(p * (v - 1) for p, v in allhits.items())
        prime_pair = is_prime(c - 1) and is_prime(c + 1)
        stat['good'] += prime_pair
        stat['bad'] += not prime_pair
        if k - t >= 2 * b:
            assert prime_pair
            stat['certified'] += 1
        assert c - start <= 2 * k - start
        assert t - (m + 2) <= 2 * sum(p * v for p, v in minhits.items())
    stat['min_zreturn'] = stat['min_z'] - 2 * stat['events'] + stat['min_f']
    assert stat['min_zreturn'] >= 0
    assert stat['events'] >= stat['min_f']
    assert stat['travel'] == stat['first_time'] + stat['repeat_time']
    assert stat['travel'] <= 2 * (stat['first_min_p'] + stat['repeat_min_p'])
    assert stat['repeat_min_p'] <= stat['all_repeat_p']
    assert stat['good'] + stat['bad'] == x // 2
    values = {
        256: (10222, 1321, 8925, 6626, 4207, 4965, 3960, 127, 1, 5577),
        512: (20048, 2401, 12404, 14987, 6176, 8040, 4364, 256, 0, 10649),
        1024: (39940, 4497, 30289, 32225, 10640, 20964, 9325, 512, 0, 17423),
        4096: (399142, 29349, 272966, 290960, 92301, 189369, 83597, 2048, 0, 170051),
    }
    actual = tuple(stat[v] for v in ('W', 'events', 'travel', 'first_min_p',
                                       'repeat_min_p', 'first_time', 'repeat_time',
                                       'good', 'bad', 'min_z'))
    if x in values:
        assert actual == values[x], (x, actual, values[x])
    print('MIN_CLOCK_LITERAL_PASS', x, 'B=', b, stat,
          'minZOverXBLogB=', stat['min_z'] / (x * b * log(b)))


if __name__ == '__main__':
    for arg in argv[1:] or ('256', '512'):
        x = int(arg)
        assert x >= 256 and x % 4 == 0
        audit(x)