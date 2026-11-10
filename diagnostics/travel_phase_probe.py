"""Compare signed prefixes when the first long gap in each phase is free."""

from math import gcd, lcm
from typing import NamedTuple

from generate_record_replays import record_segments
from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


class Event(NamedTuple):
    hit: int
    horizon: int
    increment: int
    excess: int
    balance: int


def phase_summary(record, table, hits):
    start, base = record + 2, 2 * record - 2
    index, horizon = start, base
    start_potential = table[start % P, base % P][1]
    history, previous_phase, seen_factors = [], {}, set()
    available_credit, positive_reuses, paid_pairs = [], [], []
    old_signed = signed = old_peak = peak = first = demand = paid = 0
    reuse_19 = None

    for hit in hits:
        gap = hit - index
        increment = increment_at(hit, horizon)
        growth = increment - 1
        updated = horizon + growth
        factors = list(odd_prime_divisors(increment))
        long_prime = gap > 10 and factors == [increment]
        phase = (increment, hit % 2, horizon % P)
        previous = previous_phase.get(phase) if long_prime else None
        full_excess = max(0, 24 * gap - growth)
        old_excess = full_excess if gap <= 10 or (long_prime and increment in seen_factors) else 0
        excess = full_excess if gap <= 10 or previous is not None else 0
        potential = table[index % P, horizon % P][1]
        after = table[hit % P, updated % P][1]
        net_growth = after - potential - 2 * growth
        balance = excess + net_growth
        ordinal = len(history)

        if P % increment:
            old_signed += old_excess + net_growth
            signed += balance
            if balance < 0:
                available_credit.append([ordinal, -balance])
        else:
            assert balance <= 0

        if long_prime:
            if previous is None:
                first += gap
            else:
                earlier = history[previous]
                period = lcm(P, 2 * increment)
                drift = horizon - earlier.horizon
                assert drift >= period and drift % period == 0
                intervening = [event for event in history[previous + 1:] if P % event.increment]
                breaker = next(event for event in intervening if period % event.increment)
                if gcd(P, increment) == 1 and increment >= 11 and len(intervening) == 1:
                    middle = intervening[0]
                    assert 209 * increment <= middle.increment + 416
                    if middle.excess == 0:
                        assert middle.balance + balance <= 3357 - 373 * increment
                        paid_pairs.append((increment, earlier.hit, middle.hit, middle.increment, hit,
                                           middle.balance, balance))
                if P % increment and balance > 0:
                    positive_reuses.append((increment, earlier.hit, hit, drift, len(intervening),
                                            balance, breaker.hit, breaker.increment, breaker.balance))
                    demand += balance
                    owed = balance
                    for credit in available_credit:
                        if previous < credit[0]:
                            amount = min(owed, credit[1])
                            credit[1] -= amount
                            owed -= amount
                            if owed == 0:
                                break
                    paid += balance - owed
            previous_phase[phase] = ordinal

        if record == 22_933_441 and hit == 22_940_203:
            reuse_19 = (old_excess + net_growth, balance)
        old_peak, peak = max(old_peak, old_signed), max(peak, signed)
        assert signed <= old_signed
        assert 24 * (hit - start) + after <= 24 * first + 11 * (updated - base) + start_potential + signed
        seen_factors.update(factors)
        history.append(Event(hit, horizon, increment, excess, balance))
        index, horizon = hit, updated

    return (old_peak, peak, old_signed, signed, first, demand, paid, positive_reuses, paid_pairs, reuse_19)


def print_summary(label, record, table):
    finish, hits, _ = travel_probe(record)
    assert [increment_at(finish + gap, finish) for gap in (1, 2, 3)] == [1, 1, finish + 1]
    old_peak, peak, old_signed, signed, first, demand, paid, reuses, pairs, reuse_19 = phase_summary(record, table, hits)
    print(f"{label:10} {record=:10} peaks={old_peak, peak} signed={old_signed, signed} "
          f"{first=:5} {demand=:4} {paid=:4}")
    if reuses and label == "replayed":
        for reuse in reuses:
            print("  (prime, earlier hit, hit, growth, intervening separators, balance, breaker hit, "
                  "breaker increment, breaker balance):", reuse)
    for pair in pairs:
        print("  (prime, earlier hit, middle hit, middle increment, hit, middle balance, balance):", pair)
    if reuse_19 is not None:
        print("  p=19 balance (old, phase):", reuse_19)
    return finish, hits


if __name__ == "__main__":
    table = residue_tables()
    finish, hits = print_summary("direct", 355_723, table)
    last, segments = record_segments(finish + 3)
    assert last == finish + 1 and segments[-1] == (finish, hits)

    record = 22_933_441
    for expected in (22_933_441, 45_895_573, 91_793_059, 183_616_423, 367_232_911):
        assert record == expected
        finish, _ = print_summary("replayed", record, table)
        record = finish + 1

    for record in (1_786_441, 23_613_589, 23_619_049):
        print_summary("synthetic", record, table)
