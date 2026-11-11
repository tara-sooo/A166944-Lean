"""Reproduce the37 first-hit indices and terminal bound of the certified bridge."""

from math import isqrt

from travel_residue_probe import travel_probe


if __name__ == "__main__":
    finish, hits, _ = travel_probe(45_895_573)
    print(f"finish={finish} next_record={finish + 1} root={isqrt(finish + 1)}")
    print(f"events={len(hits)} travel={hits[-1] - 45_895_575}")
    print("private def fiftyMillionHits : List Nat := [")
    for start in range(0, len(hits), 8):
        suffix = "," if start + 8 < len(hits) else ""
        print("  " + ", ".join(map(str, hits[start:start + 8])) + suffix)
    print("]")
