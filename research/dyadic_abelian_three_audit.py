"""Arithmetic audit of the dyadic three-increment multiset repetition theorem.

Python 3 standard library only. Finite computations corroborate (but do not
prove) the universal arithmetic claim. This is not a twin-prime proof.
"""
from bisect import bisect_right
from itertools import combinations, permutations
from math import gcd


def horizon_differences(w1, w2):
    assert len(w1) == len(w2) == 3 and len(set(w1)) == 3
    assert sorted(w1) == sorted(w2)
    L = sum(e - 1 for e in w1)
    first, second = {}, {}
    t = 0
    for e in w1:
        first[e] = t
        t += e - 1
    t = 0
    for e in w2:
        second[e] = t
        t += e - 1
    return {e: L + second[e] - first[e] for e in w1}


def compatible(w1, w2):
    return all(x % e in (0, 2, e - 2)
               for e, x in horizon_differences(w1, w2).items())


def short_case_checks():
    acb = [(9, 5, 7), (11, 7, 9), (13, 7, 11), (9, 7, 5),
           (13, 7, 9), (11, 9, 7), (15, 9, 11), (17, 9, 13)]
    bac = [(5, 7, 9), (7, 9, 11), (7, 11, 13), (7, 5, 9),
           (7, 9, 13), (9, 7, 11), (9, 11, 15), (9, 13, 17)]
    for a, b, c in acb:
        assert max(a, b, c) <= 2 * min(a, b, c)
        assert not compatible((a, b, c), (a, c, b))
        assert (a + b + 2 * c - 4) % b not in (0, 2, b - 2)
    for a, b, c in bac:
        assert max(a, b, c) <= 2 * min(a, b, c)
        assert not compatible((a, b, c), (b, a, c))
        assert (a + 2 * b + c - 4) % a not in (0, 2, a - 2)
    print("Sixteen reduced cases excluded: eight per transposition.")


def audit_odd_triples(upper=101):
    total = compatible_count = dyadic_count = 0
    for values in combinations(range(5, upper + 1, 2), 3):
        for w1 in permutations(values):
            for w2 in permutations(values):
                total += 1
                if compatible(w1, w2):
                    compatible_count += 1
                    if max(values) <= 2 * min(values):
                        dyadic_count += 1
    assert dyadic_count == 0
    assert compatible((5, 19, 23), (19, 5, 23))
    print(f"Odd triples <= {upper}: {total} ordered word pairs; "
          f"{compatible_count} congruence-compatible, "
          f"{dyadic_count} in a dyadic band.")


def four_letter_witness():
    w1, w2 = (7, 13, 9, 11), (9, 7, 11, 13)
    L = sum(e - 1 for e in w1)
    first, second = {}, {}
    t = 0
    for e in w1:
        first[e] = t
        t += e - 1
    t = 0
    for e in w2:
        second[e] = t
        t += e - 1
    diffs = {e: L + second[e] - first[e] for e in w1}
    assert diffs == {7: 44, 13: 54, 9: 18, 11: 24}
    assert all(delta % e in (0, 2, e - 2)
               for e, delta in diffs.items())
    print("Four-letter necessary-congruence witness:", w1, w2, diffs)


def audit_original_recurrence(limit=2_500_000):
    D = 1
    record = 2
    records, events = [], []
    for n in range(2, limit + 1):
        e = gcd(n if n % 2 == 0 else n - 2,
                D - 1 if n % 2 == 0 else D + 1)
        D += e - 1
        if e > record:
            record = e
            if e > 5:
                records.append((e, n))
        if e > 1:
            events.append((n, e))

    indices = [n for n, e in events]
    n_records = n_events = n_candidates = 0
    for M, s0 in records:
        K = (7 * M - 1) // 4
        if K > limit:
            continue
        n_records += 1
        first = bisect_right(indices, s0)
        last = bisect_right(indices, K)
        values = [e for n, e in events[first:last]]
        n_events += len(values)
        for i in range(len(values) - 5):
            w1 = tuple(values[i:i + 3])
            w2 = tuple(values[i + 3:i + 6])
            if len(set(w1)) == 3 and min(w1) >= 5 and sorted(w1) == sorted(w2):
                n_candidates += 1
                assert compatible(w1, w2)
                assert max(w1) > 2 * min(w1)

    assert n_records == 17 and n_events == 228
    print(f"Original recurrence through {limit}: "
          f"{n_records} canonical records, {n_events} nonunit events, "
          f"{n_candidates} three-distinct-value multiset doubles.")


if __name__ == "__main__":
    short_case_checks()
    audit_odd_triples()
    four_letter_witness()
    audit_original_recurrence()
    print("PASS")
