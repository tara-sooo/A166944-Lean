#!/usr/bin/env python3
"""Independent n-by-n original clipped GCD oracle for the elementary LOW3=7 and high>=5 owned shadow one-step split."""
from math import gcd, isqrt, prod
from sys import argv


def prime_list(b):
    return [p for p in range(3, b + 1, 2) if all(p % j for j in range(3, isqrt(p) + 1, 2))]


def raw(n, c):
    return gcd(n - 2 if n & 1 else n, c + 1 if n & 1 else c - 1)


def one_step_shadow(q, t, c, end, primes, cutoff):
    last_other = t
    for n in range(t + 1, end + 1):
        factors = [p for p in primes if raw(n, c) % p == 0]
        if q in factors:
            d = prod(factors)
            high_min = min(p for p in factors if p > cutoff)
            return n, c + d - 1, n - last_other, d, high_min == q
        d = prod(factors)
        if d > 1:
            c += d - 1
            last_other = n
    return None


def verify_low3():
    maximum = 0
    for t in range(6):
        for c in (0, 2, 4):
            now, horizon, spent = t, c, 0
            for _ in range(4):
                next_event = None
                for n in range(now + 1, now + 8):
                    if raw(n, horizon) % 3 == 0:
                        next_event = n
                        break
                if next_event is None:
                    break
                spent += next_event - now
                now = next_event
                horizon += 2
            else:
                raise AssertionError('LOW3 cannot terminate in 3-hit bound')
            maximum = max(maximum, spent)
            assert spent <= 7
    assert maximum == 7
    return maximum


def audit(x):
    b = isqrt(7 * x)
    b += b * b != 7 * x
    primes = prime_list(b)
    z = dict(total_travel=0, low_time=0, high_first_time=0, high_repeat_time=0,
             high_first_count=0, high_repeat_count=0, high_first_weight=0,
             high_repeat_weight=0, high_clean_time=0, high_mask_time=0,
             high_clean_count=0, high_mask_count=0, masked_high_weight=0,
             masked_high_hits=0, masks_cost=0, max_low_block=0, shadow_checks=0, Z5=0, Z5_q5=0, extra=0)
    for m in range(x + 1, 2 * x, 2):
        t = m + 2
        c = 2 * m - 2
        end = (7 * m - 1) // 4
        seen_high = {}
        masked_since = {}
        post_high = {}
        low_block = 0
        for n in range(t + 1, end + 1):
            factors = [p for p in primes if raw(n, c) % p == 0]
            if not factors:
                continue
            d = prod(factors)
            delta = n - t
            z['total_travel'] += delta
            z['extra'] += d - 1 - sum(p - 1 for p in factors)
            hi = [p for p in factors if p > 3]
            if not hi:
                low_block += delta
                z['low_time'] += delta
                z['max_low_block'] = max(z['max_low_block'], low_block)
                assert low_block <= 7, (m, n, low_block)
            else:
                low_block = 0
                q = hi[0]
                if seen_high.get(q, 0):
                    z['high_repeat_time'] += delta
                    z['high_repeat_count'] += 1
                    z['high_repeat_weight'] += q
                    if masked_since.get(q, 0):
                        z['high_mask_time'] += delta
                        z['high_mask_count'] += 1
                    else:
                        z['high_clean_time'] += delta
                        z['high_clean_count'] += 1
                        assert q in post_high
                        s = one_step_shadow(q, *post_high[q], end, primes, 3)
                        assert s is not None and s[:5] == (n, c + d - 1, delta, d, True), (m, q, n, s)
                        z['shadow_checks'] += 1
                else:
                    z['high_first_time'] += delta
                    z['high_first_count'] += 1
                    z['high_first_weight'] += q
                for p in hi[1:]:
                    z['masked_high_weight'] += p
                    z['masked_high_hits'] += 1
                    z['masks_cost'] += 2 * p + 7
                    if seen_high.get(p, 0):
                        masked_since[p] = masked_since.get(p, 0) + 1
                seen_high[q] = seen_high.get(q, 0) + 1
                masked_since[q] = 0
            for p in hi:
                post_high[p] = (n, c + d - 1)
            c += d - 1
            t = n
        z['Z5'] += sum(max(0, count - 1)**2 for count in seen_high.values())
        z['Z5_q5'] += max(0, seen_high.get(5,0) - 1)**2
    assert 8*z['masks_cost'] <= 7*z['extra']
    assert z['total_travel'] == z['low_time'] + z['high_first_time'] + z['high_repeat_time']
    assert z['high_repeat_time'] == z['high_clean_time'] + z['high_mask_time']
    assert z['high_repeat_count'] == z['high_clean_count'] + z['high_mask_count']
    assert z['high_mask_time'] + 7 * z['high_mask_count'] <= z['masks_cost']
    assert z['total_travel'] <= (7 * (x // 2 + z['high_first_count'] + z['high_repeat_count'])
                                 + 2 * z['high_first_weight'] + z['high_repeat_time'])
    regression = {
      256: (8925,1543,4693,2689,462,316,6356,2980,2689,0),
      512: (12404,2193,7550,2661,876,510,14444,3834,2661,0),
      1024:(30289,4731,19755,5803,1756,866,30912,6538,5803,0),
      4096:(272966,30217,184029,58720,10299,7774,286095,66268,58696,24)
    }
    keys = ('total_travel','low_time','high_first_time','high_repeat_time',
            'high_first_count','high_repeat_count','high_first_weight',
            'high_repeat_weight','high_clean_time','high_mask_time')
    if x in regression:
        assert tuple(z[k] for k in keys) == regression[x], (x, z, regression[x])
    z_regression={256:(644,329,500),512:(1546,1054,948),1024:(2404,1756,1164),4096:(31060,19622,36604)}
    if x in z_regression:
        assert (z['Z5'],z['Z5_q5'],z['extra']) == z_regression[x], (x,z,z_regression[x])
    print('LOW3_SHADOW_LITERAL_PASS',x,'B=',b,z)

if __name__ == '__main__':
    print('LOW3_PROOF_STATE_AUDIT', verify_low3())
    for x in argv[1:] or ('256','512'):
        audit(int(x))