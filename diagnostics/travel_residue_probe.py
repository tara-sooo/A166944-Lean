"""Compare two travel budgets on one actual and two synthetic starts."""

from math import gcd, isqrt


def odd_prime_divisors(value):
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            yield divisor
            while value % divisor == 0:
                value //= divisor
        divisor += 2
    if value > 1:
        yield value


def next_hit(index, horizon):
    earliest = horizon + 1
    for term, odd in ((horizon - 1, False), (horizon + 1, True)):
        for prime in odd_prime_divisors(term):
            residue = prime + 2 if odd else 0
            candidate = index + 1 + (residue - index - 1) % (2 * prime)
            earliest = min(earliest, candidate)
    return earliest


def increment_at(index, horizon):
    if index % 2 == 0:
        return gcd(index, horizon - 1)
    return gcd(index - 2, horizon + 1)


def travel_probe(record):
    index, horizon = record + 2, 2 * record - 2
    hits, six_starts = [], 0
    while True:
        hit = next_hit(index, horizon)
        if hit > horizon:
            return horizon, hits, six_starts
        assert all(increment_at(j, horizon) == 1 for j in range(index + 1, hit))
        increment = increment_at(hit, horizon)
        assert 1 < increment <= record
        if horizon % 6 == 0:
            six_starts += 1
        horizon += increment - 1
        index = hit
        hits.append(hit)


if __name__ == "__main__":
    for record in (22_933_441, 23_613_589, 23_619_049):
        assert list(odd_prime_divisors(record)) == [record]
        assert list(odd_prime_divisors(record - 2)) == [record - 2]
        horizon, hits, six_starts = travel_probe(record)
        travel = hits[-1] - (record + 2)
        count_budget = 48 * len(hits)**2 + 1
        weighted_budget = 6 * len(hits) + six_starts * (isqrt(4 * (3 * record + 4)) - 6)
        assert 2 * travel <= record
        assert (count_budget < record) == (record == 22_933_441)
        assert 2 * weighted_budget <= record
        print(f"{record=}, {horizon=}, events={len(hits)}, {six_starts=}, {travel=}, "
              f"{count_budget=}, twice_weighted_budget={2 * weighted_budget}")
