"""Reproduce the cost caps and finite pair counts for rebalanced requests."""

from itertools import combinations_with_replacement
from math import gcd, lcm

from rebalanced_potential_probe import ALLOWANCES, rebalanced_potential
from travel_mod210_probe import P, clipped_hit, residue_tables
from travel_reuse_overlap_probe import contained_window_margins, replay


def least_factor(increment):
    return next((f for f in range(3, increment, 2) if increment % f == 0), increment)


def coarse_cap(increment):
    factor = least_factor(increment)
    if increment in ALLOWANCES:
        return ALLOWANCES[increment]
    if factor == increment and increment <= 31:
        return 37 * increment + 1047
    travel_cap = 240 if factor == increment else 48 * factor
    return max(0, 1047 + travel_cap - 11 * increment)


def period(increment):
    return lcm(P, 2 * increment)


def deficient_pairs(caps):
    return {
        (e, f)
        for e, f in combinations_with_replacement(sorted(caps), 2)
        if min(caps[e], caps[f]) > 0 and 2 * max(period(e), period(f)) < 3 * (caps[e] + caps[f])
    }


def first_hit_cap(increment, potential, clipped, *, horizons=None):
    cap = 0
    clip = gcd(increment, P)
    max_gap = 2 * least_factor(increment)
    for (start, horizon), before in potential.items():
        if horizons is not None and horizon not in horizons:
            continue
        hit = clipped[start, horizon]
        if clip > 1:
            if hit is None or hit[1] != clip:
                continue
            gaps = (hit[0],)
        else:
            stop = max_gap if hit is None else min(max_gap, hit[0] - 1)
            gaps = range(1, stop + 1)
        for gap in gaps:
            after = potential[(start + gap) % P, (horizon + increment - 1) % P]
            cap = max(cap, 24 * gap + after - before - 11 * (increment - 1))
    return cap


def twenty_three_offset_margin(potential):
    horizons = [c for c in range(0, P, 2) if gcd(c - 1, P) == gcd(c + 1, P) == 1]
    caps = {c: 862 + max(potential[r, (c + 22) % P] for r in range(P)) for c in horizons}
    margin = min(
        2 * (period(23) + 22 + (d - c - 22) % P) - 3 * (caps[c] + caps[d])
        for c in horizons for d in horizons
    )
    return caps, margin


def main():
    potential = rebalanced_potential()
    clipped = {state: clipped_hit(*state) for state in potential}
    admissible = [e for e in range(3, 160, 2) if P % e]
    coarse = {e: coarse_cap(e) for e in admissible}
    assert max(coarse.values()) == 2194
    preselected = {e: cap for e, cap in coarse.items() if 0 < cap and 2 * period(e) < 3 * (cap + 2194)}
    assert len(preselected) == 23
    pairs = deficient_pairs(preselected)
    assert len(pairs) == 72
    increments = sorted({e for pair in pairs for e in pair})
    caps = {e: first_hit_cap(e, potential, clipped) for e in increments}
    refined = deficient_pairs(caps)
    assert len(refined) == 35
    print(f"First-hit cost caps: {caps}")
    print(f"Width bound: {max((3 * (caps[e] + caps[f]) - 1) // 2 for e, f in refined)}")
    print(f"Credit sufficient for any pair: {max(caps[e] + caps[f] - 2 * max(period(e), period(f)) // 3 for e, f in refined)}")
    by_horizon, margin = twenty_three_offset_margin(potential)
    assert margin == 90
    refined.remove((23, 23))
    print(f"Increment 23 horizon caps: {by_horizon}; minimum margin for two long 23s: {margin}")
    other_horizons = set(range(0, P, 2)) - {22}
    assert first_hit_cap(63, potential, clipped, horizons=other_horizons) == 0
    close_horizons = {(22 - offset) % P for offset in range(8, 35, 2)}
    close_cap = first_hit_cap(9, potential, clipped, horizons=close_horizons)
    assert close_cap == 266
    assert 3 * (close_cap + caps[63]) <= 2 * (period(9) + 8)
    assert 3 * (caps[9] + caps[63]) <= 2 * (period(63) + 62)
    refined.remove((9, 63))
    print(f"Increment 9 cost cap within 34 before positive increment 63: {close_cap}")
    print(f"Remaining pairs ({len(refined)}): {sorted(refined)}")
    windows, costs = replay(7163911, residue_tables(), rebalanced=potential)
    left, right = 14342410, 14343058
    demands = [(w.increment, w.cost) for w in windows if left <= w.left and w.right <= right]
    margins = next((growth, signed) for growth, signed, a, b in contained_window_margins(windows, costs)
                   if (a, b) == (left, right))
    assert demands == [(9, 234), (9, 231)] and margins == (-99, 7731)
    print(f"Synthetic M=7163911 on [{left},{right}): {demands=}, growth and signed margins {margins}")


if __name__ == "__main__":
    main()
