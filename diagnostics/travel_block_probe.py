"""Check reuse-block inequalities and disjoint credit covers."""

from math import lcm

from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


def cover_budget(balances, blocks):
    """Minimize uncredited positive balances using disjoint supplied blocks."""
    ending = [[] for _ in range(len(balances) + 1)]
    for start, stop in blocks:
        assert sum(balances[start:stop]) <= 0
        ending[stop].append(start)
    budget = [0]
    signed = 0
    for stop, balance in enumerate(balances, 1):
        budget.append(min([budget[-1] + max(0, balance)] +
                          [budget[start] for start in ending[stop]]))
        signed += balance
        assert signed <= budget[-1]
    return budget[-1]


def block_summary(record, table, phase_modulus=P):
    _, hits, _ = travel_probe(record)
    start, base = record + 2, 2 * record - 2
    index, horizon = start, base
    previous_phase, history, separators = {}, [], []
    analytic_blocks, exact_blocks, credits = [], [], []
    first = signed = peak = separator_excess = demand = paid = small_positive = 0
    witness = None

    for hit in hits:
        increment = increment_at(hit, horizon)
        gap, growth = hit - index, increment - 1
        updated = horizon + growth
        long_prime = gap > 10 and list(odd_prime_divisors(increment)) == [increment]
        key = (increment, hit % 2, horizon % phase_modulus)
        previous = previous_phase.get(key) if long_prime else None
        excess = max(0, 24 * gap - growth) if gap <= 10 or previous else 0
        balance = excess + table[hit % P, updated % P][1] - table[index % P, horizon % P][1] - 2 * growth

        if long_prime and previous is None:
            first += gap
        if P % increment:
            ordinal = len(separators)
            signed += balance
            peak = max(peak, signed)
            separator_excess += excess
            if previous is not None:
                prior, left = previous
                earlier = history[prior]
                period = lcm(phase_modulus, 2 * increment)
                assert horizon - earlier[1] >= period
                assert (horizon - earlier[1]) % period == 0
                middle = separators[left:]
                middle_excess = sum(event[3] for event in middle)
                block_balance = sum(event[4] for event in middle) + balance
                bound = middle_excess + 1678 * len(middle) + 1679 + 47 * increment - 2 * period
                assert block_balance <= bound
                if bound <= 0:
                    analytic_blocks.append((left, ordinal + 1))
                if block_balance <= 0:
                    exact_blocks.append((left, ordinal + 1))
                if record == 15_609_199 and hit == 15_611_827:
                    witness = (increment, earlier[0], hit, len(middle), middle_excess,
                               block_balance, bound)

            if balance < 0:
                credits.append([ordinal, -balance])
            elif balance > 0 and previous is not None:
                demand += balance
                owed = balance
                for credit in credits:
                    if credit[0] < previous[1]:
                        continue
                    amount = min(owed, credit[1])
                    credit[1] -= amount
                    owed -= amount
                    if owed == 0:
                        break
                paid += balance - owed
            elif balance > 0:
                assert increment <= 630
                small_positive += balance
            separators.append((hit, horizon, increment, excess, balance))

        remainder_before, remainder_after = (base - 1) % P, (updated - 1) % P
        assert signed + 2 * (updated - base) + 2 * remainder_before <= (
            separator_excess + 2 * remainder_after + 1678 * len(separators))
        assert signed <= small_positive + demand - paid
        assert 24 * (hit - start) + table[hit % P, updated % P][1] <= (
            24 * first + 11 * (updated - base) + table[start % P, base % P][1] + signed)
        if long_prime:
            previous_phase[key] = len(history), len(separators)
        history.append((hit, horizon, increment, excess, balance))
        index, horizon = hit, updated

    balances = [event[4] for event in separators]
    return (peak, signed, first, demand, paid, small_positive,
            cover_budget(balances, analytic_blocks), cover_budget(balances, exact_blocks), witness)


if __name__ == "__main__":
    table = residue_tables()
    for label, record in (("actual", 355_723), ("actual", 22_933_441),
                          ("replayed", 367_232_911), ("synthetic", 15_609_199),
                          ("synthetic", 23_613_589), ("synthetic", 23_619_049)):
        for modulus in (210, 840):
            peak, signed, first, demand, paid, small, analytic, exact, witness = block_summary(record, table, modulus)
            print(f"{label:10} {record=:9} {modulus=:3} {peak=:5} {signed=:7} {first=:5} "
                  f"{demand=:4} {paid=:4} {small=:5} cover={analytic, exact}")
            if witness is not None:
                print("  (prime, earlier hit, hit, separators, middle excess, block balance, bound):", witness)
