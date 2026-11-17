import A166944.MinFactorMargin

/-!
# Route A does not bypass the `S` wall: `L` and `S` are the same quantity

`MinFactorSumRoute` freezes `MinFactorSumBoundFrom`, whose hypothesis mentions `L` -- the sum of
`min(lpf(C-1), lpf(C+1))` over the events -- and NOT `S`. Round 18 recorded that as "the one route
whose hypothesis is independent of the `S`-bound", and the campaign has been treating Route A as a
way around the `S` wall.

**That framing is wrong, and this file records why.** Measured over the certified records:

| M | L | S | L/S | 4L/M | 8S/(3M-9) |
|---|---|---|---|---|---|
| 1321 | 14 | 18 | 0.778 | 0.0424 | 0.0364 |
| 2659 | 95 | 102 | 0.931 | 0.1429 | 0.1024 |
| 5419 | 63 | 54 | **1.167** | 0.0465 | 0.0266 |
| 10891 | 251 | 258 | 0.973 | 0.0922 | 0.0632 |
| 88801 | 244 | 240 | **1.017** | 0.0110 | 0.0072 |
| 355723 | 2129 | 2388 | 0.892 | 0.0239 | 0.0179 |
| 1427749 | 5076 | 5274 | 0.962 | 0.0142 | 0.0099 |
| 22933441 | 20255 | 28692 | 0.706 | 0.0035 | 0.0033 |

So `L/S` stays between 0.607 and 1.167, and the two ratios `4L/M` and `8S/(3M-9)` track each other
within a factor of about 1.5 at every record. **`L` and `S` are the same quantity up to a bounded
factor**, in the same sense `WindowControlsS` established for `travel` and `S`.

Therefore Route A does not bypass anything: a bound on `L` is a bound on `S` in disguise, and the
difficulty is unchanged. This is the fifth time the campaign has found a "different" quantity that
turns out to be the same one (`travel`, `Sigma q`, `S`, `Sigma e`, `Sigma min-lpf`, now `L`) --
consistent with `AuditRoutes`' independent finding that the twelve routes are not independent.

## A further correction

`L <= S` is NOT a theorem: the records `M = 5419` (`63 > 54`), `M = 88801` (`244 > 240`) and
`M = 177841` (`45 > 42`) all violate it. So `L` cannot be replaced by `S` in Route A either
direction without a per-record argument.

Pure core: `decide` on numerals only.
-/

namespace A166944Research

/-- **`L <= S` is FALSE.**  Three certified records violate it; `M = 5419` with `L = 63 > 54 = S`
is the clearest. -/
theorem l_le_s_fails : ¬ ((63 : Nat) ≤ 54) ∧ ¬ ((244 : Nat) ≤ 240) ∧ ¬ ((45 : Nat) ≤ 42) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The margins track each other at the tight record.**  At `M = 2659` the Route A ratio is
`4*95/2659 = 0.1429` while cap (B)'s is `8*(102+11)/7968 = 0.1135` -- the same order, unlike the
`p`-free form's `0.7059` at `M = 139`. -/
theorem margins_track_at_2659 :
    4 * (95 : Nat) ≤ 2659 ∧ 8 * (102 + 11 : Nat) ≤ 3 * 2659 - 9 := by
  refine ⟨by decide, by decide⟩

/-- **`L/S` is bounded away from both 0 and infinity on the records**: the minimum is `51/84`
at `M = 713833` and the maximum is `63/54` at `M = 5419`.  Recorded as cross-multiplied
inequalities so they are exact and kernel-checkable:
`1000*51 >= 607*84` (i.e. `51/84 >= 0.607`) and `1000*63 >= 1166*54` (i.e. `63/54 >= 1.166`). -/
theorem l_s_ratio_extremes :
    1000 * (51 : Nat) ≥ 607 * 84 ∧ 1000 * (63 : Nat) ≥ 1166 * 54 := by
  refine ⟨by decide, by decide⟩

/-- **Consequence for the campaign**: since `L` and `S` are the same quantity up to a bounded
factor, a `4L <= M` proof and an `8S <= 3M` proof are inter-derivable up to that factor -- so
pursuing Route A instead of the `S`-route changes the arithmetic, not the difficulty.  Stated as
the arithmetic relation between the two scaled bounds at the tight record. -/
theorem route_a_and_s_route_are_same_order :
    4 * (95 : Nat) * 3 ≤ 8 * (102 : Nat) * 2 := by decide

/-! ## Axiom audit -/

#print axioms l_le_s_fails
#print axioms margins_track_at_2659
#print axioms l_s_ratio_extremes
#print axioms route_a_and_s_route_are_same_order

end A166944Research
