"""Rational certificates for the bilateral rough-pair argument, Issue 10.

Run with Python 3.9+. The decimal display truncates proven rational bounds.
The certificates evaluate analytic coefficients, not prime counts.
"""
from fractions import Fraction as F

SCALE = 10**14
D0 = F(4, 7) - F(1, 10000)
DUP = F("0.5999")
OMEGA_UP = F("0.561522")


def log_bounds(x):
    """Enclose log(x) by the positive atanh series and a geometric tail."""
    assert 1 <= x <= 4
    y = (x - 1) / (x + 1)
    square = y * y
    power = y
    partial = F(0)
    for k in range(36):
        partial += 2 * power / (2 * k + 1)
        power *= square
    tail = 2 * power / (73 * (1 - square))
    low = (partial * SCALE) // 1
    high = -((-(partial + tail) * SCALE) // 1)
    return F(low, SCALE), F(high, SCALE)


def floor_decimal(value, places=9):
    n = value * 10**places // 1
    sign = "-" if n < 0 else ""
    whole, frac = divmod(abs(n), 10**places)
    return f"{sign}{whole}.{frac:0{places}d}"


def lower_sieve(d, a):
    assert 2 < d / a < 4
    return 2 * log_bounds(d / a - 1)[0] / d


def classical(c, a):
    mass = 1 + log_bounds((1 - c) / c)[0]
    return lower_sieve(D0, a) * mass - (2 / D0) * (OMEGA_UP / a - mass)


def short_level(left, right):
    # Worst-case level throughout the closed exponent cell.
    cap = min((2 + 3 * left) / 5, 1 - right)
    return max(D0, cap - F(1, 10000))


def bilateral(c, a, cells):
    assert F(1, 3) <= c < F(1, 2)
    mass = 1 + log_bounds((1 - c) / c)[0]
    positive = lower_sieve(D0, a)
    width = (F(1, 2) - c) / cells
    for i in range(cells):
        left = c + i * width
        right = left + width
        odds_ratio = (right * (1 - left)) / (left * (1 - right))
        cell_mass = log_bounds(odds_ratio)[0]
        positive += cell_mass * lower_sieve(short_level(left, right), a)
    upper = 2 / DUP * (OMEGA_UP / a - mass)
    sliver = log_bounds(2 * c / (1 - c))[1]
    upper += (2 / D0 - 2 / DUP) * sliver
    return positive - upper


def main():
    k0 = classical(F(".324"), F(".207"))
    k1 = bilateral(F(".334"), F(".2062"), 160)
    assert k0 > F(".0136")
    assert k1 > F(".005")
    print("classical c=.324 lower  >=", floor_decimal(k0))
    print("bilateral c=.334 lower  >=", floor_decimal(k1))
    ideal_d, amax = F(5, 8), F(".568")
    assert log_bounds(1 / amax)[1] < amax
    ceiling = 2 * ideal_d * (1 + log_bounds(F(3, 2))[1]) * amax
    assert ceiling < F(".999")
    print("ideal single-exchange obstruction at c=.4: factor < .999")


if __name__ == "__main__":
    main()
