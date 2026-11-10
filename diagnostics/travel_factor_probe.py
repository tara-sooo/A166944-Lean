"""Split first-hit travel by gap, increment, and prior factor use."""

from itertools import combinations

from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


def travel_parts(record):
    finish, hits, _ = travel_probe(record)
    index, horizon = record + 2, 2 * record - 2
    short = first_prime = reused_prime = composite = 0
    last_use = {}
    reuse_windows = []

    for hit in hits:
        gap = hit - index
        increment = increment_at(hit, horizon)
        factors = list(odd_prime_divisors(increment))
        if gap <= 10:
            short += gap
        elif factors != [increment]:
            assert 3 * gap <= increment - 1
            composite += gap
        elif increment in last_use:
            reused_prime += gap
            # The last increment-1 units before the reuse are part of
            # its required intervening horizon growth.
            reuse_windows.append((horizon - (increment - 1), horizon, increment))
        else:
            first_prime += gap

        updated = horizon + increment - 1
        for factor in factors:
            if factor >= 5 and factor in last_use:
                old_start, old_end = last_use[factor]
                assert factor - 1 <= horizon - old_end
                assert gap <= horizon - old_start + 2
            last_use[factor] = (horizon, updated)
        index, horizon = hit, updated

    assert horizon == finish
    assert short + first_prime + reused_prime + composite == index - (record + 2)
    assert 3 * composite <= horizon - (2 * record - 2)
    return (short, first_prime, reused_prime, composite), reuse_windows


if __name__ == "__main__":
    for label, record in (("certified", 22_933_441), ("actual start", 45_895_573),
                          ("synthetic", 23_613_589), ("synthetic", 23_619_049)):
        parts, windows = travel_parts(record)
        short, first_prime, reused_prime, composite = parts
        print(f"{label:12} {record=:9} travel={sum(parts):5} {short=:5} "
              f"{first_prime=:5} {reused_prime=:5} {composite=:5}")
        for first, second in combinations(windows, 2):
            if first[2] != second[2] and max(first[0], second[0]) < min(first[1], second[1]):
                print(f"  overlapping reuse windows (start, end, prime): {(first, second)}")
                break
