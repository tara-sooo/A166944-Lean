import A166944.HorizonLedger
import A166944.CountFromIndex

/-!
# The excess dominates the step count

`CountFromIndex.horizon_ge_start_add_twice_count` gives `C + 2*p <= Cf` along any
moving-horizon path, and `HorizonLedger.horizon_eq_start_add_excess` names the excess
by `Cf = C + S`. Together:

    2 * p <= S.

The accumulated excess is at least twice the number of steps. Measured, it is much
larger -- `S / p` runs from 5 to 73 at the records examined -- so the bound is not
tight, but it is free and it removes the step count from any estimate that carries
both quantities.

## What it is and is not

It is a **lower** bound on `S`. The frontier needs an upper bound, so this does not
approach the obstruction, and it is recorded with that stated rather than implied.

It is useful for one thing: `TravelExcessSum` bounds the travel by `2 * (S + p)`, and
with `2p <= S` that becomes `travel <= 3 * S`, eliminating `p`. The relaxed cap is
equivalent to `4 * travel <= 3 * M - 9`, so `4 * S <= M - 3` would suffice.

**A correction.** An earlier version of this paragraph said `4 * S <= M - 3` fails
only at `M = 43` and `M = 139`, "both far below the threshold" and therefore
harmless. The first half is right and the inference is wrong: `139` is the *optimal
threshold of the excess route itself*, not an incidental small case.
`ExcessCriterion.quarter_bound_fails_while_excess_holds_at_139` exhibits the
separation there, and the canonical starts below `139` are exactly `7`, `13`, `43`
(`ExcessGap.canonical_start_solutions_below_139`). So the quarter bound fails at the
one point where the excess criterion is most useful, and the two are not
interchangeable.
-/

namespace A166944Research

/-- **The excess, named, dominates the step count.**  One statement so that the `S`
in the ledger and the `S` in the bound are the same term. -/
theorem two_mul_count_le_excess {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, Cf = C + S ∧ 2 * p ≤ S := by
  obtain ⟨S, hS⟩ := horizon_eq_start_add_excess hpath
  exact ⟨S, hS, by have := horizon_ge_start_add_twice_count hpath; omega⟩

/-- **Consequently the travel estimate loses its dependence on `p`.**  Given the
shared excess from the previous statement and the travel estimate from
`TravelExcessSum`, both in terms of the same `S`. -/
theorem travel_le_three_mul_excess_of_shared {s C sf Cf p S : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hS : Cf = C + S)
    (h2p : 2 * p ≤ S) (htravel : sf - s ≤ 2 * (S + p)) :
    sf - s ≤ 3 * S := by omega

end A166944Research
