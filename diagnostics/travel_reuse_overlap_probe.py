"""Reproduce native overlap witnesses by trial division on capped replays."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import re

from travel_credit_prefix import capped_hits, is_prime
from travel_mod210_probe import P, residue_tables
from travel_residue_probe import increment_at


@dataclass(frozen=True)
class Window:
    left: int
    right: int
    increment: int
    cost: int

    @property
    def width(self):
        return self.right - self.left


def replay(record, table):
    hits, _ = capped_hits(record)
    index, horizon = record + 2, 2 * record - 2
    previous = {}
    windows, costs = [], []
    for hit in hits:
        increment = increment_at(hit, horizon)
        gap = hit - index
        updated = horizon + increment - 1
        long_prime = gap > 10 and is_prime(increment)
        key = (increment, horizon % P, hit % 2)
        old = previous.get(key) if long_prime else None
        first_gap = gap if long_prime and old is None else 0
        net = 24 * first_gap
        if P % increment:
            before = table[index % P, horizon % P][1]
            after = table[hit % P, updated % P][1]
            net = 24 * gap + after - before - 11 * (increment - 1)
            if old is not None and net > 0:
                earlier, earlier_hit = old
                assert (hit - earlier_hit) % (2 * increment) == 0
                assert horizon > earlier and (horizon - earlier) % (P * increment) == 0
                windows.append(Window(earlier, horizon, increment, net))
        if long_prime:
            previous[key] = (horizon, hit)
        costs.append((horizon, net))
        index, horizon = hit, updated
    return windows, costs


def pair_margins(windows):
    for j, later in enumerate(windows):
        for earlier in windows[:j]:
            if later.left < earlier.right:
                left = min(earlier.left, later.left)
                yield later.right - left - 2 * (earlier.cost + later.cost), earlier, later


def components(windows):
    ordered = sorted(windows, key=lambda w: w.left)
    if not ordered:
        return
    left, right, cost = ordered[0].left, ordered[0].right, ordered[0].cost
    for window in ordered[1:]:
        if window.left < right:
            right = max(right, window.right)
            cost += window.cost
        else:
            yield left, right, cost
            left, right, cost = window.left, window.right, window.cost
    yield left, right, cost


def margins_for_components(windows, costs):
    for left, right, positive in components(windows):
        enclosed = [value for horizon, value in costs if left < horizon <= right]
        negative = sum(min(0, value) for value in enclosed)
        yield right - left - 2 * (positive + negative), left, right, positive, negative, sum(enclosed)


def prefix_remainders(windows, costs):
    net = covered = count = 0
    for horizon, cost in costs:
        net += cost
        if count < len(windows) and windows[count].right == horizon:
            count += 1
            covered = sum(positive + negative for _, _, _, positive, negative, _ in
                          margins_for_components(windows[:count], costs))
        yield 3 * (net - covered)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_output")
    args = parser.parse_args()
    output = Path(args.native_output).read_text()
    table = residue_tables()

    pair_match = re.search(r"minimum overlap pair margin=(-?\d+) record=(\d+) horizon=(\d+)", output)
    assert pair_match
    expected, record, right = map(int, pair_match.groups())
    windows, costs = replay(record, table)
    pairs = list(pair_margins(windows))
    assert min(row[0] for row in pairs) == expected
    _, first, second = next(row for row in pairs if row[0] == expected and row[2].right == right)
    left = min(first.left, second.left)
    negative = sum(min(0, value) for horizon, value in costs if left < horizon <= right)
    print(f"Pair at synthetic {record}: {first}, {second}")
    print(f"  union width={right - left}, margin={expected}, negative net cost={negative}, "
          f"margin with those negative terms={expected - 2 * negative}")

    load_match = re.search(r"maximum reuse load=(\d+) scale=(\d+) record=(\d+) horizon=(\d+)", output)
    assert load_match
    expected_load, scale, load_record, cut = map(int, load_match.groups())
    if load_record != record:
        windows, _ = replay(load_record, table)
    rounded = [(w, (2 * scale * w.cost + w.width - 1) // w.width) for w in windows]
    loads = {x: sum(rate for w, rate in rounded if w.left <= x < w.right) for x in {w.left for w in windows}}
    assert max(loads.values()) == expected_load and loads[cut] == expected_load
    exact_load = sum((Fraction(2 * w.cost, w.width) for w in windows if w.left <= cut < w.right), Fraction())
    print(f"Load at synthetic {load_record} horizon={cut}: exact={exact_load}, "
          f"rounded={expected_load}/{scale}")

    component_match = re.search(r"minimum reuse component margin=(-?\d+) record=(\d+) horizon=(\d+)", output)
    if component_match:
        expected_component, component_record, right = map(int, component_match.groups())
        windows, costs = replay(component_record, table)
        rows = list(margins_for_components(windows, costs))
        assert min(row[0] for row in rows) == expected_component
        _, left, _, positive, negative, signed = next(
            row for row in rows if row[0] == expected_component and row[2] == right)
        print(f"Component at synthetic {component_record}: [{left},{right}), "
              f"positive reuse={positive}, negative={negative}, all signed={signed}, "
              f"reuse margin={expected_component}")

    thirds_match = re.search(
        r"minimum two-thirds margin=(-?\d+) record=(\d+) horizon=(\d+) prefix=(\d+)", output)
    if thirds_match:
        expected_thirds, thirds_record, right, prefix = map(int, thirds_match.groups())
        windows, costs = replay(thirds_record, table)
        rows = [(2 * (hi - lo) - 3 * (positive + negative), hi, window.right)
                for j, window in enumerate(windows)
                for _, lo, hi, positive, negative, _ in margins_for_components(windows[:j + 1], costs)]
        assert min(row[0] for row in rows) == expected_thirds
        assert (expected_thirds, right, prefix) in rows
        print(f"Two-thirds margin at synthetic {thirds_record} horizon={right} "
              f"prefix={prefix}: {expected_thirds}")

    remainder_match = re.search(r"maximum triple remainder=(\d+) record=(\d+) hit=(\d+)", output)
    if remainder_match:
        expected_remainder, remainder_record, hit = map(int, remainder_match.groups())
        if expected_remainder:
            windows, costs = replay(remainder_record, table)
            hits, _ = capped_hits(remainder_record)
            rows = list(zip(hits, prefix_remainders(windows, costs)))
            assert max(value for _, value in rows) == expected_remainder
            assert (hit, expected_remainder) in rows
            print(f"Triple remainder at synthetic {remainder_record} hit={hit}: {expected_remainder}")


if __name__ == "__main__":
    main()
