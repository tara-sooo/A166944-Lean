"""Richert-weight certificates on the prescribed D*_.313 incidence population.

Run beside negative_min_bilateral_rough_bounds.py with Python 3.9+.
"""
from fractions import Fraction as F
from functools import lru_cache

from negative_min_bilateral_rough_bounds import floor_decimal, log_bounds


@lru_cache(None)
def log_interval(x):
    assert x >= 1
    k = 0
    while x > 2:
        x /= 2
        k += 1
    low, high = log_bounds(x)
    l2, u2 = log_bounds(F(2))
    return low + k * l2, high + k * u2


@lru_cache(None)
def three_factor_lower(d, h, z):
    y = F(".236")
    assert 2 < d / z < 4 and z < y < d and 4 * y > h
    # For v up to y, the upper-sieve cutoff can be reduced to (d-v)/2.
    # The corresponding upper coefficient is always 1/(d-v).
    positive = log_interval(d / z - 1)[0] / d
    upper_integral = (log_interval(y / z)[1] / d
                      + (1 / d - 1 / y) * log_interval((d - z) / (d - y))[0])
    return positive - upper_integral / (4 - h / y)


def certify(z):
    total = F(0)
    cells = 0
    for t_milli in range(160, 219):
        for u_milli in range(156, 189):
            if u_milli + 1 > t_milli - 1 or t_milli + u_milli + 2 > 374:
                continue
            t, u, delta = F(t_milli, 1000), F(u_milli, 1000), F(1, 1000)
            t1, u1 = t + delta, u + delta
            assert t1 <= F(".3128") and u >= (F(".6246") - t) / 3 + F(".0002")
            assert u1 <= t - F(".0002") and u1 <= 1 - 2 * t1 - F(".0002")
            assert t1 + u1 < F(".3748") < F(".49")
            d, h = F(".6245") - t1 - u1, F("1.0001") - t - u
            weight = three_factor_lower(d, h, z)
            if weight > 0:
                mass = log_interval(t1 / t)[0] * log_interval(u1 / u)[0]
                total += mass * weight
                cells += 1
    # The tail product over all integers n>=12 is 11/12.
    c2_lower = F(11, 12)
    for n in (2, 4, 6, 10):
        c2_lower *= 1 - F(1, n * n)
    assert c2_lower == F(2541, 4096)
    # Published in the preceding project audit: J* <= .2907047167... < .291.
    j_upper = F(".291")
    return total, 4 * c2_lower * total / j_upper, cells


def main():
    for z, required in [(F(".08"), F(".175")), (F(".09"), F(".101"))]:
        total, ratio, cells = certify(z)
        assert ratio > required
        print(f"z={float(z):.2f} cells={cells} integral >= {floor_decimal(total)}"
              f"   L * P(rough quotient with Omega<=3) >= {floor_decimal(ratio)}")


if __name__ == "__main__":
    main()
