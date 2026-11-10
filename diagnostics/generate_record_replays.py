"""Print the Lean replay table used by VerifiedRecordPrefix.lean."""
from math import gcd, isqrt


def record_segments(limit):
    value, record, horizon = 2, 0, 0
    hits = []
    segments = []
    for index in range(2, limit + 1):
        increment = gcd(index if index % 2 == 0 else index - 2, value)
        value += increment
        if increment > record:
            if record > 5:
                assert index == horizon + 3 and increment == horizon + 1
                segments.append((horizon, hits))
            record, horizon, hits = increment, value - index, []
        elif record > 5 and increment > 1:
            assert index <= horizon
            horizon += increment - 1
            assert horizon == value - index
            hits.append(index)
    return record, segments


def print_lean_table(segments):
    print("private def verifiedSegments : List (Nat × Nat × List Nat) := [")
    for offset, (horizon, hits) in enumerate(segments):
        root = isqrt(horizon + 1)
        end = "," if offset + 1 < len(segments) else ""
        if len(hits) <= 8:
            print(f"  ({horizon}, {root}, [{', '.join(map(str, hits))}]){end}")
            continue
        print(f"  ({horizon}, {root}, [")
        for start in range(0, len(hits), 8):
            numbers = ", ".join(map(str, hits[start:start + 8]))
            comma = "," if start + 8 < len(hits) else ""
            print(f"    {numbers}{comma}")
        print(f"  ]){end}")
    print("]")


if __name__ == "__main__":
    last, segments = record_segments(22_933_443)
    assert last == 22_933_441
    print_lean_table(segments)
