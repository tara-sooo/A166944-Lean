#!/usr/bin/env python3
"""A166944: exhaustive necessary-condition tree for short selective-H runs.

Assumes a moving-horizon state (s,C) with even C and even offset
X=2*s-C in {0,2,4,6,8,10}. Every subsequent nonunit event in the
examined run has gap 1<=g<=10, odd increment 3<=e<=33, and
                 e-1 < 3*(g+1).

All genuine first-gcd runs satisfy these necessary conditions. This tool
checks every possible hit word by generalized CRT and an exact clipped-gcd
check across the *entire preceding word* each time the modulus grows.

The output is a finite arithmetic/paper certificate, NOT a Lean-kernel
proof and NOT an unrestricted proof of Cap B.
"""
from collections import Counter
from math import gcd, lcm

OFFSETS = (0, 2, 4, 6, 8, 10)
MAX_INC = 33
MAX_GAP = 10
EXPECTED_TREE_NODES = 214_780


def clipped_gcd(index_residue: int, horizon_residue: int, modulus: int) -> int:
    """Full-event gcd projected onto one modulus (which is always even)."""
    if index_residue % 2 == 0:
        return gcd(gcd(index_residue, horizon_residue - 1), modulus)
    return gcd(gcd(index_residue - 2, horizon_residue + 1), modulus)


def valid_prefix(word, first_s_residue: int, modulus: int, initial_offset: int) -> bool:
    """Recheck *all* earlier hits and intervening units under latest CRT modulus.

    If a genuine event has increment e, then gcd(actual_gcd, modulus) == e
    because modulus includes e. Every earlier genuine unit gcd projects to 1.
    """
    travel, offset = 0, initial_offset
    for gap, increment in word:
        horizon = (2 * (first_s_residue + travel) - offset) % modulus
        for h in range(1, gap):
            if clipped_gcd(first_s_residue + travel + h, horizon, modulus) != 1:
                return False
        r = first_s_residue + travel + gap
        if clipped_gcd(r, horizon, modulus) != increment:
            return False
        travel += gap
        offset += 2 * gap - (increment - 1)
    return True


def crt_join(a: int, L: int, residue: int, m: int):
    """Combine s0 == a (mod L) and s0 == residue (mod m)."""
    d = gcd(L, m)
    if (residue - a) % d:
        return None
    quotient = m // d
    new_modulus = lcm(L, m)
    if quotient == 1:
        return a, new_modulus
    step = (((residue - a) // d) * pow(L // d, -1, quotient)) % quotient
    return (a + L * step) % new_modulus, new_modulus


def enumerate_runs(initial_offset: int, initial_s_mod6: int):
    count_by_depth = Counter()
    best = {"events": (0, ()), "growth": (0, ()), "travel": (0, ())}

    def dfs(T, X, a, L, word):
        depth = len(word)
        count_by_depth[depth] += 1
        growth = 2*T + initial_offset - X
        for name, val in (("events", depth), ("growth", growth), ("travel", T)):
            if val > best[name][0]:
                best[name] = val, (T, X, a, L, word)
        # NO depth cap or state-merging: the entire constrained search tree
        # is enumerated, so different histories are never conflated.
        for gap in range(1, MAX_GAP + 1):
            r_even = (initial_s_mod6 + T + gap) % 2 == 0
            before_hit_offset = X + 2*gap
            for e in range(3, MAX_INC + 1, 2):
                if gap > 2*e or e-1 >= 3*(gap+1):
                    continue
                after_offset = before_hit_offset - (e-1)
                if after_offset < 0:
                    continue
                # Necessary e|2r-C+1 (even r) or e|2r-C-5 (odd r).
                if (before_hit_offset + (1 if r_even else -5)) % e:
                    continue
                # Necessary e|r (even r) or e|r-2 (odd r).
                required_s0 = ((0 if r_even else 2) - (T+gap)) % e
                joined = crt_join(a, L, required_s0, e)
                if joined is None:
                    continue
                a2, L2 = joined
                next_word = word + ((gap, e),)
                if not valid_prefix(next_word, a2, L2, initial_offset):
                    continue
                dfs(T+gap, after_offset, a2, L2, next_word)

    dfs(0, initial_offset, initial_s_mod6, 6, ())
    return count_by_depth, best


def actual_gcd(index, horizon):
    return gcd(index, horizon-1) if index % 2 == 0 else gcd(index-2, horizon+1)


def full_gcd_witness(start_index, offset, word):
    """Verify true, unclipped first-hit gcds at a synthetic local start."""
    s, C = start_index, 2*start_index-offset
    for i, (gap, e) in enumerate(word, 1):
        r = s + gap
        assert r <= C, (i, s, C, r)
        for j in range(s+1, r):
            assert actual_gcd(j, C) == 1, (i,j,C)
        assert actual_gcd(r, C) == e, (i,r,C,e)
        s, C = r, C+e-1
        assert 0 <= 2*s-C
    return s, C


def main():
    all_nodes = Counter()
    top = {"events": (0, None), "growth": (0, None), "travel": (0, None)}
    cache = {}
    for X in OFFSETS:
        for initial_s_mod6 in range(6):
            depth_count, best = enumerate_runs(X, initial_s_mod6)
            key = (X, initial_s_mod6)
            cache[key] = best
            all_nodes.update(depth_count)
            for name, (value, witness) in best.items():
                if value > top[name][0]:
                    top[name] = (value, (key, witness))
    assert sum(all_nodes.values()) == EXPECTED_TREE_NODES
    assert max(all_nodes) == 31
    assert {k: v[0] for k,v in top.items()} == {
        "events": 31, "growth": 234, "travel": 152}, top
    print(f'PASS: {len(OFFSETS)*6} initial offset/residue cases; '
          f'{sum(all_nodes.values())} entire-prefix CRT nodes; deepest={max(all_nodes)}')
    for name in ('events','growth','travel'):
        value, ((initial_X, residue), (T, Xend, a, modulus, word)) = top[name]
        growth = 2*T+initial_X-Xend
        print(f'PASS: global maximum {name}={value} '
              f'at X0={initial_X}, s0%6={residue}; '
              f'events={len(word)}, T={T}, G={growth}')
    # All three maxima are attained by actual first nonunit gcd paths
    # starting at synthetic local states; no record-history claim.
    for key,name,initial_s0 in [((0,4),'events',48_685_793_956),
                                ((10,2),'growth',13_500_671_025_254),
                                ((8,5),'travel',3_199_701_545)]:
        T, Xend, a, modulus, word = cache[key][name][1]
        assert initial_s0 % modulus == a
        sf, Cf = full_gcd_witness(initial_s0, key[0], word)
        assert sf - initial_s0 == T
        assert Cf - (2*initial_s0-key[0]) == 2*T+key[0]-Xend
        print(f'PASS: full-gcd synthetic sharp witness for {name}: '
              f's0={initial_s0}, steps={len(word)}, T={T}, G={Cf-(2*initial_s0-key[0])}')
    # Canonical actual record starts satisfy X0=6, s0%6=3.
    canonical = cache[(6,3)]
    assert (canonical['events'][0],canonical['growth'][0],
            canonical['travel'][0]) == (26,204,129)
    print('PASS: canonical-start tighter maxima: events<=26, Hshort<=204, T<=129')
    print('These are consecutive SHORT-H runs only; arbitrary intervening events remain OPEN.')


if __name__ == '__main__':
    main()
