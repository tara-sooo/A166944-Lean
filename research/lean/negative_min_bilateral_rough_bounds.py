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


def phase_mass(ell, b, cells=200):
    """Half the sum of the two bare masses, discarding nonnegative 4-prime rows."""
    third = F(1, 3)
    width = (third - ell) / cells
    triple_lower = F(0)
    for i in range(1, cells + 1):
        t = ell + i * width
        # Each factor of this nonnegative integrand decreases up to 1/3.
        triple_lower += width * log_bounds((1 - 2 * t) / t)[0] / (t * (1 - t))
    mass_ell = 1 + log_bounds((1 - ell) / ell)[0] + triple_lower
    mass_b = 1 + log_bounds((1 - b) / b)[0]
    return (mass_ell + mass_b) / 2


def phase_exchange(ell, b, a):
    # For b=1/2 the high cutoff means 'prime'; large balanced semiprime
    # rows restricted by the cofactor class use the smaller level.
    assert F(3, 14) < ell < F(1, 3) <= b <= F(1, 2)
    mass = phase_mass(ell, b)
    low = lower_sieve(D0, a) * mass
    upper = 2 / DUP * (OMEGA_UP / a - mass)
    if b > F(2, 5):
        balanced_mass = log_bounds((F(3, 2) * b) / (1 - b))[1] / 2
        d_balanced = F(".4999")
        # Use an upper enclosure for the cost in the lower coefficient.
        cost = 2 / D0 * log_bounds(D0 / a - 1)[1] - lower_sieve(d_balanced, a)
        low -= balanced_mass * cost
        upper += balanced_mass * (2 / d_balanced - 2 / DUP)
    return low - upper


def prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors.append(n)
    return factors


def first_event_check():
    # Integer proxies exercise the clock and both signs, not the asymptotic estimates.
    R, H = 100000, 100
    counts = dict(stationary=0, plus=0, minus=0)
    for center in range(R + (-R) % 6, 2 * R + 1, 6):
        fs = {s: prime_factors(center + s) for s in (-1, 1)}
        if any(ps[0] < 7 or (len(ps) > 1 and ps[1] <= 4 * ps[0])
               for ps in fs.values()):
            continue
        if any(ps[0] < 4 * H and (center + s) // ps[0] % 4 != (3 if s == 1 else 1)
               for s, ps in fs.items()):
            continue
        for age in range(1, H - 2):
            clock = 3 - center // 2 + age
            sign = 1 if clock % 2 == 0 else -1
            candidates = [p for p in fs[sign]
                          if clock % (2 * p) == (0 if sign == 1 else p + 2)]
            if candidates:
                p = min(candidates)
                assert p == fs[sign][0]
                assert 3 + age - (p - 1) // 2 == p + (0 if sign == 1 else 3)
                counts["plus" if sign == 1 else "minus"] += 1
                break
        else:
            counts["stationary"] += 1
    assert min(counts.values()) > 0
    return counts


def main():
    k0 = classical(F(".324"), F(".207"))
    k1 = bilateral(F(".334"), F(".2062"), 160)
    assert k0 > F(".0136")
    assert k1 > F(".005")
    print("classical c=.324 lower  >=", floor_decimal(k0))
    print("bilateral c=.334 lower  >=", floor_decimal(k1))
    for ell, b, minimum in [(".28", ".4", ".01"), (".312", ".35", ".03"),
                            (".223", ".5", ".035")]:
        result = phase_exchange(F(ell), F(b), F(".206"))
        assert result > F(minimum), (ell, b, float(result))
        print(f"phase ell={ell} b={b} lower >=", floor_decimal(result))
    print("finite first-event check:", first_event_check())
    for theta, bound in [(F(".49"), F(".32")), (F(".4999"), F(".0032"))]:
        k_upper = 4 * (2 - 1 / (1 - theta) + log_bounds((1 - theta) / theta)[1])
        assert k_upper < bound
        print(f"non-twin upper constant at theta={float(theta)} < {float(bound)}")
    ideal_d, amax = F(5, 8), F(".568")
    assert log_bounds(1 / amax)[1] < amax
    ceiling = 2 * ideal_d * (1 + log_bounds(F(3, 2))[1]) * amax
    assert ceiling < F(".999")
    print("ideal single-exchange obstruction at c=.4: factor < .999")


if __name__ == "__main__":
    main()
