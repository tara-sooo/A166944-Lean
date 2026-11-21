"""Finite diagnostics for the event-word congruence obstruction in A166944.

Requires only Python 3 standard library. Tests the original recurrence and finite
arithmetic cases; this does not prove the liminf hypothesis or twin primes.
"""
from itertools import combinations
from math import gcd


def twice_compatible(word):
    L = sum(e - 1 for e in word)
    return all(L % e in (0, 2, e - 2) for e in word)


def thrice_compatible(word):
    L = sum(e - 1 for e in word)
    return all(L % e == 0 for e in word)


def original_events(limit=2_500_000):
    D = 1
    max_d = 2
    records = []
    events = {}
    for n in range(2, limit + 1):
        e = gcd(n if n % 2 == 0 else n - 2,
                D - 1 if n % 2 == 0 else D + 1)
        D += e - 1
        if e > max_d:
            max_d = e
            if e > 5:
                records.append((e, n))
        if e > 1:
            events[n] = e
    count = 0
    doubled = []
    tripled = []
    for M, index in records:
        K = (7 * M - 1) // 4
        if K > limit:
            continue
        assert index == M + 2, (M, index)
        seq = [e for r, e in events.items() if index < r <= K]
        count += len(seq)
        for k in range(1, min(15, len(seq) // 2) + 1):
            for i in range(len(seq) - 2 * k + 1):
                W = seq[i:i + k]
                if W == seq[i + k:i + 2 * k]:
                    doubled.append((M, i, k, W))
                    assert twice_compatible(W)
                    if i + 3 * k <= len(seq) and W == seq[i + 2 * k:i + 3 * k]:
                        tripled.append((M, i, k, W))
                        assert thrice_compatible(W)
    return count, doubled, tripled


def main():
    for k in (2, 3):
        count = 0
        for values in combinations(range(5, 102, 2), k):
            count += 1
            assert not twice_compatible(values), (k, values)
        print(f"k={k}: {count} odd tuples checked; no twice-compatible values")
    W = (11, 15, 23, 45)
    assert twice_compatible(W) and not thrice_compatible(W)
    print("Four-value modular example (necessary condition only):", W)
    event_count, doubles, triples = original_events()
    assert not triples
    assert all(
        not (k in (2, 3) and len(set(W)) == k and min(W) >= 5)
        for _, _, k, W in doubles
    )
    print("Original recurrence through 2.5M: event count", event_count)
    print("Doubled words of length <=15:", doubles)
    print("Triple words of length <=15:", triples)
    print("PASS")


if __name__ == "__main__":
    main()
