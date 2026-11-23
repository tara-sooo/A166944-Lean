#!/usr/bin/env python3
"""Independent literal integer-by-integer oracle for tagged q-deleted first returns.
python3 twin_prime_shadow_minowner_literal.py 256 512 1024
"""
from math import gcd, isqrt, prod
from sys import argv


def prime_list(bound):
    return [p for p in range(3, bound + 1, 2)
            if all(p % j for j in range(3, isqrt(p) + 1, 2))]


def raw(n, c):
    return gcd(n - 2 if n & 1 else n, c + 1 if n & 1 else c - 1)


def shadow_next(q, t, c, end, ps):
    """Advance q-deleted state each n; stop just BEFORE the next q-bearing event."""
    prior_event = t
    skipped_events = 0
    for n in range(t + 1, end + 1):
        r = raw(n, c)
        div = [p for p in ps if r % p == 0]
        if q in div:
            d = prod(div)
            return (n, c + d - 1, n - prior_event, d, min(div) == q, skipped_events)
        other = prod(div)
        if other != 1:
            c += other - 1
            prior_event = n
            skipped_events += 1
    return None


def audit(x):
    B = isqrt(7 * x)
    B += B * B < 7 * x
    ps = prime_list(B)
    z = dict(events=0, W=0, extra=0, first_time=0, repeat_time=0,
             first_weight=0, repeat_weight=0, clean_time=0, mask_time=0,
             clean_count=0, mask_return_count=0, masked_weight=0,
             masked_hits=0, shadow_match=0, shadow_end=0, shadow_skipped=0)
    witness = None
    for m in range(x + 1, 2 * x, 2):
        c = 2 * m - 2
        t = m + 2
        end = (7 * m - 1) // 4
        q_prev = {}
        q_owned = {}
        q_masked_since = {}
        for n in range(t + 1, end + 1):
            div = [p for p in ps if raw(n, c) % p == 0]
            if not div:
                continue
            d = prod(div)
            owner = div[0]
            dt = n - t
            z['events'] += 1
            z['W'] += d - 1
            z['extra'] += d - 1 - sum(p - 1 for p in div)
            if q_owned.get(owner, 0):
                z['repeat_time'] += dt
                z['repeat_weight'] += owner
            else:
                z['first_time'] += dt
                z['first_weight'] += owner
            for q in div:
                if q in q_prev:
                    pred = shadow_next(q, *q_prev[q], end, ps)
                    assert pred is not None, (m, q, n, 'shadow missed a q hit')
                    assert pred[:5] == (n, c + d - 1, dt, d, q == owner), (
                        m, q, n, pred, c, d, dt)
                    z['shadow_match'] += 1
                    z['shadow_skipped'] += pred[5]
                if q != owner:
                    z['masked_hits'] += 1
                    z['masked_weight'] += q
                    if q_owned.get(q, 0):
                        q_masked_since[q] = q_masked_since.get(q, 0) + 1
                else:
                    if q_owned.get(q, 0):
                        if not q_masked_since.get(q, 0):
                            z['clean_time'] += dt
                            z['clean_count'] += 1
                        else:
                            z['mask_time'] += dt
                            z['mask_return_count'] += 1
                            if witness is None and q >= 19:
                                witness = (m, q, q_prev[q][0], n,
                                           q_masked_since[q])
                    q_owned[q] = q_owned.get(q, 0) + 1
                    q_masked_since[q] = 0
                q_prev[q] = (n, c + d - 1)
            c += d - 1
            t = n
        for q, (old_t, old_c) in q_prev.items():
            assert shadow_next(q, old_t, old_c, end, ps) is None, (m, q)
            z['shadow_end'] += 1
    assert z['repeat_time'] == z['clean_time'] + z['mask_time']
    assert 8 * z['masked_weight'] <= 5 * z['extra']
    assert z['repeat_time'] <= z['clean_time'] + 2 * z['masked_weight']
    regression = {256: (1321, 10222, 500, 4965, 3960, 6626, 4207, 3861, 99, 23, 233),
                  512: (2401, 20048, 948, 8040, 4364, 14987, 6176, 4344, 20, 27, 365),
                  1024: (4497, 39940, 1164, 20964, 9325, 32225, 10640, 9260, 65, 48, 456),
                  4096: (29349, 399142, 36604, 189369, 83597, 290960, 92301, 82905, 692, 535, 9161)}
    keys = ('events', 'W', 'extra', 'first_time', 'repeat_time', 'first_weight',
            'repeat_weight', 'clean_time', 'mask_time', 'masked_hits', 'masked_weight')
    if x in regression:
        assert tuple(z[k] for k in keys) == regression[x], (x, z, regression[x])
    print('SHADOW_LITERAL_PASS', x, 'B=', B, z, 'high_mask_witness=', witness)


if __name__ == '__main__':
    for value in argv[1:] or ('256', '512'):
        audit(int(value))