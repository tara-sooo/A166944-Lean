#!/usr/bin/env python3
"""Read LOW_HIGH_PASS output, compute the exact integer-valued high-owner second-moment twin certificate.

Example:
  /tmp/low_high 4096 16384 65536 262144 | python3 twin_prime_high_owner_moment_certificate.py
"""
from math import isqrt
import sys


def primes_under(bound):
    small = bytearray(b'\x01') * (bound + 1)
    small[0] = small[1] = 0
    for p in range(2, isqrt(bound) + 1):
        if small[p]:
            for z in range(p * p, bound + 1, p):
                small[z] = 0
    return [p for p in range(5, bound + 1) if small[p]]


def inspect(text):
    if not text.startswith('LOW_HIGH_PASS'):
        return None
    kv = {}
    for field in text.split()[1:]:
        if '=' in field:
            k, v = field.split('=', 1)
            kv[k] = v
    if int(kv['cutoff']) != 3:
        return None
    X = int(kv['X'])
    B = int(kv['B'])
    F = int(kv['highFirstCount'])
    FW = int(kv['highFirstWeight'])
    Z = int(kv['ZhiReturn'])
    c = isqrt(7 * X)
    assert B == c + (c * c < 7 * X)
    assert 9 * X * X % 16 == 0 and 5 * X % 4 == 0
    horizon = 9 * X * X // 16 - 5 * X // 4
    P2 = sum((2 * p + 7)**2 for p in primes_under(B))
    D = horizon - X * B - 7 * (X // 2 + F) - 2 * FW
    lhs = (X // 2) * P2 * Z
    rhs = D * D
    cert = D > 0 and lhs <= rhs
    expected = {65536: (69348969, 1678123, 2338846133,
                        3813412041693167616, 5470201233849053689),
                262144: (470734799, 11447377, 38065260743,
                         706304896030765613056, 1448964075432576912049)}
    if X in expected:
        assert (P2, Z, D, lhs, rhs) == expected[X]
        assert cert
    return f'EXACT_MOMENT_CERTIFICATE X={X} B={B} P2={P2} Z={Z} D={D} lhs={lhs} rhs={rhs} certifies_twin={cert}'


if __name__ == '__main__':
    n = 0
    for line in sys.stdin:
        outcome = inspect(line)
        if outcome is not None:
            print(outcome)
            n += 1
    if not n:
        raise SystemExit('No cutoff=3 LOW_HIGH_PASS lines supplied')