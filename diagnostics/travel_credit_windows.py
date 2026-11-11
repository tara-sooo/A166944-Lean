"""Extract exact interval Hall obstructions from phase-credit replay ledgers.

This is integer arithmetic on finite replay traces, not a Lean certificate.
Synthetic canonical-shaped starts are explicitly distinguished from actual
sequence records. Only left/right request endpoints need to be tested: any
nonempty obstruction tightens to the hull of the requests it contains.
"""

from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from itertools import product

from travel_funded_probe import funded_summary
from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


@dataclass(frozen=True)
class Request:
    event: int
    anchor: int
    amount: int
    increment: int

    @property
    def left(self):
        return 2 * self.anchor + 1

    @property
    def right(self):
        return 2 * self.event + 1


@dataclass(frozen=True)
class Source:
    time: int
    negative: int
    first: int


def replay_ledger(record, table, growth_charge=2, *, residual=False, hits=None):
    assert growth_charge in (2, 4)
    if hits is None:
        _, hits, _ = travel_probe(record)
    index, horizon = record + 2, 2 * record - 2
    last_long, last_positive, startup_keys = {}, {}, set()
    requests, sources = [], []
    startup = signed = 0
    for ordinal, hit in enumerate(hits):
        increment = increment_at(hit, horizon)
        gap, growth = hit - index, increment - 1
        updated = horizon + growth
        long_prime = gap > 10 and list(odd_prime_divisors(increment)) == [increment]
        key = (increment, hit % 2, horizon % P)
        previous = last_long.get(key) if long_prime else None
        anchor = previous if previous is not None else last_positive.get(key)
        excess = max(0, 24 * gap - growth) if gap <= 10 or previous is not None else 0
        balance = excess + table[hit % P, updated % P][1] - table[index % P, horizon % P][1] - growth_charge * growth
        if residual:
            remaining = 0 if long_prime and previous is None else gap
            balance = 24 * remaining + table[hit % P, updated % P][1] - table[index % P, horizon % P][1] - 11 * growth
        if long_prime and previous is None:
            sources.append(Source(2 * ordinal + 1, 0, gap))
        if P % increment:
            signed += balance
            if balance < 0:
                sources.append(Source(2 * ordinal, -balance, 0))
            elif balance > 0 and anchor is not None:
                assert anchor < ordinal
                requests.append(Request(ordinal, anchor, balance, increment))
            elif balance > 0:
                assert increment <= 630 and balance <= 29613 and key not in startup_keys
                if growth_charge == 4:
                    assert increment <= 315 and balance <= 14810
                if residual:
                    assert increment <= 169 and balance <= 1478
                startup_keys.add(key)
                startup += balance
            if balance > 0:
                last_positive[key] = ordinal
        if long_prime:
            last_long[key] = ordinal
        index, horizon = hit, updated
    assert len(startup_keys) <= 631 * 420
    assert startup <= 631 * 420 * 29613
    assert sum(request.amount for request in requests) + startup == signed + sum(s.negative for s in sources)
    return hits, requests, sources, startup


def endpoint_window_totals(requests, sources):
    """Yield (left, right, confined demand, negative supply, first gaps)."""
    ordered = sorted(sources, key=lambda source: source.time)
    times = [source.time for source in ordered]
    negative_prefix, first_prefix = [0], [0]
    for source in ordered:
        negative_prefix.append(negative_prefix[-1] + source.negative)
        first_prefix.append(first_prefix[-1] + source.first)
    for left in sorted({request.left for request in requests}):
        confined = sorted((request for request in requests if left <= request.left),
                          key=lambda request: request.right)
        demand = 0
        start = bisect_left(times, left)
        for k, request in enumerate(confined):
            demand += request.amount
            right = request.right
            if k + 1 < len(confined) and confined[k + 1].right == right:
                continue
            stop = bisect_right(times, right)
            negative = negative_prefix[stop] - negative_prefix[start]
            first = first_prefix[stop] - first_prefix[start]
            yield left, right, demand, negative, first


def minimum_multiplier(requests, sources):
    """Return the least integer multiplier and a maximizing window witness.

    None means a positive deficiency in a window with no first-gap funding.
    The witness tuple is (left, right, demand, negative supply, first gaps).
    """
    required, witness = 0, None
    for row in endpoint_window_totals(requests, sources):
        left, right, demand, negative, first = row
        deficiency = max(0, demand - negative)
        if deficiency and not first:
            return None, row
        coefficient = (deficiency + first - 1) // first if first else 0
        if coefficient > required:
            required, witness = coefficient, row
    return required, witness


def minimum_deficient_window(requests, sources, multiplier=0):
    """Choose a deficient endpoint window of least timestamp length."""
    bad = (row for row in endpoint_window_totals(requests, sources)
           if row[2] > row[3] + multiplier * row[4])
    return min(bad, key=lambda row: (row[1] - row[0], row[0], row[1]), default=None)


def hall_by_subsets(requests, sources, multiplier):
    """Independent direct Hall test for the small self-test instances."""
    for mask in range(1 << len(requests)):
        chosen = [request for i, request in enumerate(requests) if mask >> i & 1]
        demand = sum(request.amount for request in chosen)
        capacity = sum(source.negative + multiplier * source.first for source in sources
                       if any(request.left <= source.time <= request.right for request in chosen))
        if demand > capacity:
            return False
    return True


def self_test():
    checked = 0
    # Three possible time intervals, duplicate timestamps, zero capacities,
    # and both ordinary and first-gap funding. Check every selected family.
    intervals = [(1, 1), (1, 3), (3, 3)]
    for demands in product(range(3), repeat=3):
        requests = [Request((right - 1) // 2, (left - 1) // 2, demand, 9)
                    for (left, right), demand in zip(intervals, demands)]
        for capacities in product(range(3), repeat=3):
            sources = [Source(1, capacities[0], 0), Source(3, 0, capacities[1]), Source(3, capacities[2], 0)]
            minimum, _ = minimum_multiplier(requests, sources)
            for multiplier in (0, 1, 2):
                hall = hall_by_subsets(requests, sources, multiplier)
                assert hall == (minimum is not None and minimum <= multiplier)
                assert hall == (minimum_deficient_window(requests, sources, multiplier) is None)
                checked += 1
    return checked


def main():
    print("Direct-subset Hall comparisons:", self_test())
    table = residue_tables()
    for label, record in (("actual", 355_723), ("actual", 22_933_441),
                          ("replayed", 367_232_911), ("synthetic", 4_394_191),
                          ("synthetic", 7_874_413), ("synthetic", 23_619_049),
                          ("synthetic", 56_837_371)):
        for growth_charge, residual in ((2, False), (4, False), (4, True)):
            hits, requests, sources, startup = replay_ledger(record, table, growth_charge, residual=residual)
            required, witness = minimum_multiplier(requests, sources)
            for multiplier in (0, 1, 2, 24):
                failure = funded_summary(record, table, multiplier, growth_charge, residual=residual)[-1]
                assert (failure is None) == (required is not None and required <= multiplier)
            print(f"{label:10} {record=:10} {growth_charge=} {residual=} events={len(hits):4} "
                  f"requests={len(requests):3} {startup=:5} minimum_multiplier={required}")
            if required:
                print("  minimum-length zero-funded deficit:", minimum_deficient_window(requests, sources))
            if witness is not None:
                left, right, demand, negative, first = witness
                confined = [request for request in requests if left <= request.left and request.right <= right]
                print(f"  window timestamps=[{left},{right}] demand={demand} negative={negative} "
                      f"first={first} increments={[request.increment for request in confined]}")
                print(f"  event hits=[{hits[(left - 1) // 2]},{hits[(right - 1) // 2]}] "
                      f"coefficient-2 deficit={max(0, demand - negative - 2 * first)}")


if __name__ == "__main__":
    main()
