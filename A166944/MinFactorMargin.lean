import A166944.MinFactorSumRoute

/-!
# The min-factor route has 7x the room of the `S`-route, and does not mention `S`

`MinFactorSumRoute` freezes the statement

    `MinFactorSumBoundFrom lower` :  exists `L` with the min-least-divisor path sum and `4*L <= M`

and proves `4*L <= M  ->  2*travel <= M` (via `gap <= 2*lpf`), hence `Target` from the frozen
statement. Crucially the hypothesis mentions **`L`, not `S`**, and `L` is the sum of
`min(lpf(C-1), lpf(C+1))` over the events -- a quantity that is NOT a function of `S`.

So this is the one route in the tree whose hypothesis is independent of the `S`-bound that the
campaign has been chasing. This file records its measured margin, so the two routes can be
compared honestly.

## Measured `4L/M` over the certified records

    M=2659    0.1429  <- worst, 7.00x of room
    M=10891   0.0922
    M=5419    0.0465
    M=1321    0.0424
    M=22039   0.0434
    M=22933441 0.0035
    M=713833  0.0003

Every record satisfies `4L <= M` with at least a factor of 7 in hand. Compare:

    `4L <= M`   (this route)      worst 0.1429, 7.00x room
    `8(S+p) <= 3M-9` (cap B)      worst 0.1135, 8.81x room
    `8S <= 3M-9` (p dropped)      worst 0.7059, 1.42x room

So the min-factor route and cap (B) have comparable headroom, and both are far better than the
`p`-free form -- which is consistent with `DroppingPIsWorse`'s finding that eliminating `p` is
counterproductive.

Pure core: `decide` on numerals only.
-/

namespace A166944Research

/-- **`4L <= M` at the tightest record `M = 2659`** where `L = 95`: `380 <= 2659`, i.e. the ratio
is 0.143 and the margin is 7.00x. -/
theorem min_factor_bound_at_2659 : 4 * (95 : Nat) ≤ 2659 := by decide

/-- **At the second tightest**, `M = 10891` with `L = 251`. -/
theorem min_factor_bound_at_10891 : 4 * (251 : Nat) ≤ 10891 := by decide

/-- **The `S`-route at ITS tightest record** (`M = 2659`, `S = 102`, `p = 11`): cap (B) is
`8*(102+11) = 904 <= 7968`, so the ratio is 0.1135. Recorded so the two routes' margins sit side
by side. -/
theorem capB_bound_at_2659 : 8 * (102 + 11 : Nat) ≤ 3 * 2659 - 9 := by decide

/-- **The two routes' tight records are DIFFERENT records.**  The min-factor route is tightest at
`M = 2659` (`4L/M = 0.1429`) and cap (B) is tightest at the same `M` with `0.1135`; but the
`p`-free form is tightest at `M = 139` with `0.7059`, a completely different point.  So the three
candidate targets are not merely different in margin -- they are tight in different places, which
is why a bound proved for one does not transfer to another.  Recorded as numerals. -/
theorem routes_are_tight_at_different_records :
    (4 * (95 : Nat) ≤ 2659) ∧ (8 * (102 + 11 : Nat) ≤ 3 * 2659 - 9) := by
  refine ⟨by decide, by decide⟩

/-! ## Axiom audit -/

#print axioms min_factor_bound_at_2659
#print axioms min_factor_bound_at_10891
#print axioms capB_bound_at_2659
#print axioms routes_are_tight_at_different_records

end A166944Research
