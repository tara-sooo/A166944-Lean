import A166944.CanonicalTravel

/-!
# The event-count sufficient condition is FALSE above its own threshold

`CanonicalTravel.canonical_travel_bound_of_event_count` proves

    `48 * p * p + 1 < M`  =>  `2 * travel <= M`

at a canonical start.  That is a genuine implication, but its hypothesis is **not** true at
every canonical start above the threshold the tree uses (`968`).  This file records the smallest
counterexample found, as a kernel-checked fact, so that no future attempt relies on the
hypothesis holding unconditionally.

## The witness

At `M = 2659` the certified canonical replay has `p = 11` events (`sf = 2712`, `Cf = 5418`,
`S = 102`, all from the calibration table in FACTS §2 and reproduced by the jump-form engine).
Then

    48 * 11 * 11 + 1 = 5809 > 2659 = M,

so `48 p^2 + 1 < M` FAILS, even though `M = 2659 >= 968` and the conclusion `travel <= M/2`
happens to be true there (`travel = 51 <= 1329`).  The implication is therefore not the route:
it cannot be applied at this record, and the conclusion at that record has to come from
somewhere else.

## Why this matters

Three consequences, and they are the reason for keeping this file.

1. **The hypothesis is not monotone in `M`.**  `M = 2659` fails while `M = 5419` passes
   (`48 * 81 + 1 = 3889 < 5419`) and `M = 10891` passes with the same `p = 11`.  So no
   "for all large `M`" reading of the hypothesis is available without a per-record argument.
2. **`p` is not monotone in `M` either**: `p = 11` at both `M = 2659` and `M = 10891`, so a
   larger start can have the same event count and a much larger budget.
3. **The sufficient conditions are not interchangeable.**  cap (B) `4*sf <= 7*M-1` holds at
   `M = 2659` (`4*2712 = 10848 <= 18612`), so cap (B) covers a record that the event-count
   route cannot reach.  That is the concrete reason the campaign treats cap (B) as the binding
   condition rather than the count criterion.

Pure core: `decide` only.
-/

namespace A166944Research

/-- **The event-count hypothesis fails at `M = 2659`.**  `p = 11` there, so
`48 * p * p + 1 = 5809 > 2659`. -/
theorem event_count_hypothesis_fails_at_2659 :
    ¬ (48 * (11 * 11) + 1 < 2659) := by decide

/-- The certified replay data at `M = 2659`, restated so the counterexample is self-contained:
`S = Cf - (2M - 2) = 102` and `travel = sf - (M + 2) = 51`. -/
theorem replay_data_at_2659 :
    (5418 : Nat) - (2 * 2659 - 2) = 102 ∧ (2712 : Nat) - (2659 + 2) = 51 := by
  refine ⟨by decide, by decide⟩

/-- **The conclusion still holds at `M = 2659`**, so the witness really is a failure of the
*implication's hypothesis* and not of the frontier: `2 * 51 <= 2659`. -/
theorem frontier_holds_at_2659 : 2 * (51 : Nat) ≤ 2659 := by decide

/-- **cap (B) holds at `M = 2659`**, which the event-count route cannot certify: with
`sf = 2712` we have `4 * 2712 = 10848 <= 7 * 2659 - 1 = 18612`. -/
theorem capB_holds_at_2659 : 4 * (2712 : Nat) ≤ 7 * 2659 - 1 := by decide

/-- **The hypothesis is not monotone**: it passes at `M = 5419` with `p = 9`
(`48 * 81 + 1 = 3889 < 5419`) while failing at the smaller `M = 2659` with `p = 11`. -/
theorem event_count_hypothesis_holds_at_5419 : 48 * (9 * 9) + 1 < 5419 := by decide

/-! ## Axiom audit -/

#print axioms event_count_hypothesis_fails_at_2659
#print axioms replay_data_at_2659
#print axioms frontier_holds_at_2659
#print axioms capB_holds_at_2659
#print axioms event_count_hypothesis_holds_at_5419

end A166944Research
