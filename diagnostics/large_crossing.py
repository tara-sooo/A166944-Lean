"""Integer diagnostics for the large-old crossing branch.

This inverts the gcd recurrence from a hypothetical crossing. The prefix
constraints are necessary for real canonical-origin paths. The numerical
search is separate from the Lean proofs.
"""
from math import gcd, isqrt


def odd_divisors(n):
    while n % 2 == 0:
        n //= 2
    for factor in range(1, isqrt(n) + 1, 2):
        if n % factor == 0:
            yield factor
            if factor * factor != n:
                yield n // factor


def predecessors(index, horizon, cap, lower):
    if index % 2 == 0:
        left, right = index, horizon
    else:
        left, right = index - 2, horizon + 2
    for increment in odd_divisors(gcd(left, right)):
        previous = horizon + 1 - increment
        if increment <= cap and max(index, lower) <= previous <= 2 * (index - 1):
            if gcd(left, right - increment) == increment:
                yield previous


def backward(e):
    largest_m = (4 * e - 4) // 3
    smallest_m = max(968, e)
    frontier = {3 * e + 1}
    matches = []
    for index in range(2 * e - 1, smallest_m + 1, -1):
        if index <= largest_m + 2 and index % 6 == 3 and 2 * index - 6 in frontier:
            matches.append(index - 2)
        frontier = {
            previous
            for horizon in frontier
            for previous in predecessors(index, horizon, largest_m, 2 * smallest_m - 2)
        }
        if not frontier:
            return matches, index - 1
    return matches, smallest_m + 1


def check_synthetic_suffix():
    horizon = 3510
    for index in range(2318, 2519):
        left, right = (index, horizon - 1) if index % 2 == 0 else (index - 2, horizon + 1)
        increment = gcd(left, right)
        assert index <= horizon and increment <= 1321
        if index == 2517:
            assert horizon == 3774 and increment == 5
        if index == 2518:
            assert horizon == 3778 and increment == 1259
        horizon += increment - 1
    assert horizon == 5036
    value = 2
    for index in range(2, 2318):
        increment = gcd(index if index % 2 == 0 else index - 2, value)
        value += increment
        if index == 1323:
            assert increment == 1321
    assert value - 2317 == 2658


if __name__ == "__main__":
    for e in range(729, 20_002, 2):
        matches, exhausted_at = backward(e)
        assert not matches, (e, matches)
        assert exhausted_at > (4 * e - 4) // 3 + 2, (e, exhausted_at)
    print("9637 odd e from 729 to 20001: all frontiers exhausted before an origin index")
    check_synthetic_suffix()
    print("M=1321 synthetic suffix reproduced. Actual D(2317)=2658.")
