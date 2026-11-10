"""Measure excess and reuse-window overlap on exact integer replays."""

from travel_factor_probe import travel_parts
from travel_residue_probe import increment_at, odd_prime_divisors, travel_probe


def travel_excess(record):
    finish, hits, _ = travel_probe(record)
    index, horizon = record + 2, 2 * record - 2
    seen, windows = set(), []
    remaining = short_excess = reused_excess = 0
    short_run = max_short_run = supported_run = max_supported_run = 0

    for hit in hits:
        gap = hit - index
        increment = increment_at(hit, horizon)
        factors = list(odd_prime_divisors(increment))
        width = increment - 1
        excess = 0
        if gap <= 10:
            remaining += gap
            excess = max(0, 24 * gap - width)
            assert excess == 0 or increment <= 240
            short_excess += excess
        elif factors == [increment] and increment in seen:
            remaining += gap
            excess = max(0, 24 * gap - width)
            assert excess == 0 or increment * width < 48 * (horizon + 1)
            reused_excess += excess
            windows.append((horizon - width, horizon))

        short_run = short_run + excess if gap <= 10 and excess > 0 else 0
        max_short_run = max(max_short_run, short_run)
        supported_run = supported_run + excess if 210 % increment == 0 else 0
        max_supported_run = max(max_supported_run, supported_run)
        seen.update(factors)
        index, horizon = hit, horizon + width

    growth = horizon - (2 * record - 2)
    assert horizon == finish
    assert 24 * remaining <= growth + short_excess + reused_excess
    assert max_supported_run <= 72 * (210 - 1)
    parts, _ = travel_parts(record)
    assert remaining == parts[0] + parts[2]

    max_overlap = 0
    for x, _ in windows:
        widths = sorted(end - start for start, end in windows if start <= x < end)
        assert all(widths[i] >= 2 * widths[i - 2] for i in range(2, len(widths)))
        max_overlap = max(max_overlap, len(widths))

    return growth, short_excess, reused_excess, max_short_run, max_supported_run, max_overlap


if __name__ == "__main__":
    for label, record in (("certified", 22_933_441), ("actual start", 45_895_573),
                          ("synthetic", 23_613_589), ("synthetic", 23_619_049)):
        growth, short, reuse, short_run, run210, overlap = travel_excess(record)
        print(f"{label:12} {record=:9} {growth=:6} excess={short + reuse:6} "
              f"{short=:5} {reuse=:6} {short_run=:4} {run210=:4} {overlap=}")
