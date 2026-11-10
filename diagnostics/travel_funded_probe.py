"""Check startup costs, first-phase funding and every credit allocation."""

from collections import defaultdict

from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


def funded_summary(record, table, multiplier):
    _, hits, _ = travel_probe(record)
    index, horizon = record + 2, 2 * record - 2
    last_long, last_positive, startup_keys = {}, {}, set()
    sources, allocations, demands = [], [], []
    signed = startup = first = positive_count = negative_total = 0
    maximum_signed = 0
    failure = None

    for ordinal, hit in enumerate(hits):
        increment = increment_at(hit, horizon)
        gap, growth = hit - index, increment - 1
        updated = horizon + growth
        long_prime = gap > 10 and list(odd_prime_divisors(increment)) == [increment]
        key = (increment, hit % 2, horizon % P)
        previous = last_long.get(key) if long_prime else None
        anchor = previous if previous is not None else last_positive.get(key)
        excess = max(0, 24 * gap - growth) if gap <= 10 or previous is not None else 0
        balance = excess + table[hit % P, updated % P][1] - table[index % P, horizon % P][1] - 2 * growth

        if long_prime and previous is None:
            first += gap
            sources.append([2 * ordinal + 1, multiplier * gap, multiplier * gap])
        if P % increment:
            signed += balance
            maximum_signed = max(maximum_signed, signed)
            if balance < 0:
                negative_total -= balance
                sources.append([2 * ordinal, -balance, -balance])
            elif balance > 0 and anchor is not None:
                positive_count += 1
                owed = balance
                raw_capacity = sum(source[1] for source in sources if source[0] > 2 * anchor)
                for source_index, source in enumerate(sources):
                    if source[0] <= 2 * anchor:
                        continue
                    amount = min(owed, source[2])
                    if amount:
                        allocations.append((ordinal, source_index, amount))
                    source[2] -= amount
                    owed -= amount
                    if owed == 0:
                        break
                demands.append((ordinal, anchor, balance - owed))
                if owed:
                    failure = (increment, hits[anchor], hit, balance, raw_capacity, owed)
                    break
            elif balance > 0:
                assert increment <= 630 and balance <= 29613
                assert key not in startup_keys
                startup_keys.add(key)
                startup += balance
            if balance > 0:
                last_positive[key] = ordinal
        assert signed <= startup + multiplier * first
        if long_prime:
            last_long[key] = ordinal
        index, horizon = hit, updated

    row_use, column_use = defaultdict(int), defaultdict(int)
    anchors = {event: anchor for event, anchor, _ in demands}
    for event, source_index, amount in allocations:
        source = sources[source_index]
        assert 2 * anchors[event] < source[0] <= 2 * event + 1
        row_use[event] += amount
        column_use[source_index] += amount
    for event, _, paid in demands:
        assert row_use[event] == paid
    for source_index, source in enumerate(sources):
        assert column_use[source_index] <= source[1]
        assert column_use[source_index] + source[2] == source[1]
    assert sum(source[1] for source in sources) == negative_total + multiplier * first
    assert len(startup_keys) <= 631 * 420
    assert startup <= (631 * 420) * 29613
    return first, startup, maximum_signed, signed, positive_count, failure


if __name__ == "__main__":
    table = residue_tables()
    for label, record in (("actual", 355_723), ("actual", 22_933_441),
                          ("replayed", 367_232_911), ("synthetic", 4_394_191),
                          ("synthetic", 7_874_413), ("synthetic", 23_619_049)):
        for multiplier in (0, 1, 24):
            first, startup, peak, signed, demands, failure = funded_summary(record, table, multiplier)
            print(f"{label:10} {record=:9} {multiplier=:2} {first=:5} {startup=:5} "
                  f"{peak=:5} {signed=:7} {demands=:3}")
            if failure is not None:
                print("  (increment, earlier hit, hit, demand, eligible capacity, unpaid):", failure)
