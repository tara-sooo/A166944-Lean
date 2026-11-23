#!/usr/bin/env python3
"""Independent literal n-by-n parity-clipped gcd oracle for signed stages and nonlinear prime charges."""
from math import gcd, isqrt
from sys import argv


def primes_to(n):
    return [p for p in range(3, n + 1, 2)
            if all(p % d for d in range(3, isqrt(p) + 1, 2))]


def path(M, prime_list):
    c = 2 * M - 2
    k = (7 * M - 1) // 4
    hit = {p: 0 for p in prime_list}
    excess = linear = growth = events = compounds = compound_growth = 0
    for n in range(M + 3, k + 1):
        raw = gcd(n - 2 if n & 1 else n, c + 1 if n & 1 else c - 1)
        ps = [p for p in prime_list if raw % p == 0]
        d = 1
        for p in ps:
            hit[p] += 1
            d *= p
        if d > 1:
            events += 1
            compounds += len(ps) >= 2
            compound_growth += (d - 1) if len(ps) >= 2 else 0
            lin = sum(p - 1 for p in ps)
            linear += lin
            excess += d - 1 - lin
            growth += d - 1
            c += d - 1
    assert linear + excess == growth
    return dict(growth=growth, linear=linear, excess=excess, hit=hit,
                events=events, compounds=compounds, compound_growth=compound_growth)


def audit(X):
    b = isqrt(7 * X)
    b += b * b < 7 * X
    prime_list = primes_to(b)
    starts = range(X + 1, 2 * X, 2)
    old = {m: dict(growth=0, linear=0, excess=0, hit={}) for m in starts}
    stage = dict(delta=0, positive=0, negative=0, first=0, repeat=0, interaction_pos=0)
    for p in prime_list:
        for m in starts:
            a = path(m, [q for q in prime_list if q <= p])
            z = old[m]
            delta = a['growth'] - z['growth']
            new_charge = (p - 1) * a['hit'][p]
            displaced = a['linear'] - new_charge - z['linear']
            nonlinear = a['excess'] - z['excess']
            assert delta == new_charge + displaced + nonlinear
            stage['delta'] += delta
            stage['positive'] += max(delta, 0)
            stage['negative'] += max(-delta, 0)
            stage['first'] += (p - 1) * (a['hit'][p] > 0)
            stage['repeat'] += (p - 1) * max(a['hit'][p] - 1, 0)
            stage['interaction_pos'] += max(displaced + nonlinear, 0)
            old[m] = a
    final = dict(growth=0, linear=0, excess=0, first=0, repeat=0,
                 events=0, composites=0, composite_growth=0, h=0, f=0, zz=0)
    for m in starts:
        a = old[m]
        for k, key in [('growth', 'growth'), ('linear', 'linear'),
                       ('excess', 'excess'), ('events', 'events'),
                       ('composites', 'compounds'), ('composite_growth', 'compound_growth')]:
            final[k] += a[key]
        for p, n in a['hit'].items():
            final['first'] += (p - 1) * (n > 0)
            final['repeat'] += (p - 1) * max(n - 1, 0)
            if p >= 19:
                final['h'] += n
                final['f'] += n > 0
                final['zz'] += n * n
    assert final['growth'] == final['linear'] + final['excess']
    assert final['linear'] == final['first'] + final['repeat']
    assert stage['delta'] == final['growth']
    assert stage['positive'] - stage['negative'] == stage['delta']
    assert stage['positive'] <= stage['first'] + stage['repeat'] + stage['interaction_pos']
    regressions = {
        256: (10222, 500, 163, 128, 233, 10270, 48),
        512: (20048, 948, 265, 265, 265, 26042, 5994),
        1024: (39940, 1164, 640, 577, 778, 40426, 486),
    }
    if X in regressions:
        assert (final['growth'], final['excess'], final['h'], final['f'], final['zz'],
                stage['positive'], stage['negative']) == regressions[X]
    print(f"LITERAL_ORACLE_PASS X={X} B={b} final={final} stage={stage}")


if __name__ == '__main__':
    for x in map(int, argv[1:] or ('256', '512')):
        assert x >= 256 and x % 4 == 0
        audit(x)
