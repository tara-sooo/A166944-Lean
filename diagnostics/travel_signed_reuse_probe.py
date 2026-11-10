"""Measure signed balances and assign earlier negative charges to reuses."""

from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


def check_reuse(p, first_hit, first_horizon, hit, horizon):
    period = 2 * p
    first_odd, odd = first_hit % 2, hit % 2
    if first_odd == odd:
        expected = (0, 0)
    elif first_odd:
        expected = (p - 2, 2)
    else:
        expected = (p + 2, period - 2)
    assert ((hit - first_hit) % period, (horizon - first_horizon) % period) == expected


def signed_reuse_summary(record, table):
    finish, hits, _ = travel_probe(record)
    index, horizon = record + 2, 2 * record - 2
    start_potential = table[index % P, horizon % P][1]
    history, last_use = [], {}
    negative_credits, available = [], []
    all_negative_prefix = [0]
    supported = separators = peak = excess_total = 0
    reuse_charge = independent_paid = assigned = single_middle = 0
    unpaid_example = None

    for hit in hits:
        ordinal = len(history)
        gap = hit - index
        increment = increment_at(hit, horizon)
        growth = increment - 1
        factors = list(odd_prime_divisors(increment))
        earlier = last_use.get(increment) if factors == [increment] else None
        reused = earlier is not None
        updated = horizon + growth
        excess = max(0, 24 * gap - growth) if gap <= 10 or reused else 0
        potential = table[index % P, horizon % P][1]
        after = table[hit % P, updated % P][1]
        balance = excess + after - potential - 2 * growth

        if P % increment == 0:
            assert balance <= 0
            supported += balance
        else:
            separators += balance
            if balance < 0:
                negative_credits.append((ordinal, -balance))
                available.append(-balance)
            elif balance > 0 and gap > 10 and reused:
                reuse_charge += balance
                # Credit lies strictly after the preceding use and
                # strictly before the event asking for payment.
                local_credit = sum(amount for when, amount in negative_credits if earlier < when)
                independent_paid += min(balance, local_credit)
                owed = balance
                for i, (when, _) in enumerate(negative_credits):
                    if earlier < when:
                        paid = min(owed, available[i])
                        available[i] -= paid
                        owed -= paid
                        if owed == 0:
                            break
                assigned += balance - owed
                if owed and unpaid_example is None:
                    all_credit = all_negative_prefix[-1] - all_negative_prefix[earlier + 1]
                    unpaid_example = (increment, history[earlier][0], hit, balance, local_credit, all_credit, owed)
        peak = max(peak, separators)

        for p in factors:
            previous = last_use.get(p)
            if previous is not None:
                first_hit, first_horizon, first_increment = history[previous]
                check_reuse(p, first_hit, first_horizon, hit, horizon)
                if p >= 5 and previous + 2 == ordinal and first_increment == p:
                    middle = history[-1][2]
                    if middle < 3 * p:
                        if first_hit % 2 == hit % 2:
                            assert middle == p + 2
                        else:
                            assert first_hit % 2 == 1 and hit % 2 == 0 and middle == p + 4
                        single_middle += 1
            last_use[p] = ordinal
        history.append((hit, horizon, increment))
        all_negative_prefix.append(all_negative_prefix[-1] + max(0, -balance))
        excess_total += excess
        index, horizon = hit, updated

    assert horizon == finish
    end_potential = table[index % P, horizon % P][1]
    assert excess_total + end_potential == (
        2 * (horizon - (2 * record - 2)) + start_potential + supported + separators
    )
    return separators, peak, reuse_charge, independent_paid, assigned, single_middle, unpaid_example


if __name__ == "__main__":
    table = residue_tables()
    for label, record in (("certified", 22_933_441), ("actual start", 45_895_573),
                          ("synthetic", 23_613_589), ("synthetic", 23_619_049)):
        signed, peak, reuse, local, assigned, middle, example = signed_reuse_summary(record, table)
        print(f"{label:12} {record=:9} {signed=:7} {peak=:5} {reuse=:6} "
              f"{local=:6} {assigned=:6} {middle=}")
        if example:
            print(f"  unpaid example (prime, prior hit, hit, charge, separator credit, all credit, unpaid): {example}")
