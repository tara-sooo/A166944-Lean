import A166944.SBoundLemma

/-!
# cap (B): where it holds, where it fails, and what the constant `4/7` means

`cap (B)` is the binding sufficient condition for the frontier:

    `4 * sf <= 7 * M - 1`

Measured over every certified record: it **fails at `M = 13` (ratio 1.0667) and `M = 43`
(1.0533)** and **holds at every record from `M = 139` upward**, with the ratio
`4*sf/(7*M-1)` decreasing from 0.6420 at `M = 139` to 0.5714 at `M = 183616423`.
`SBoundLemma.canonical_start_threshold_is_necessary` already records the two failures and two
successes; this file adds the arithmetic that explains the shape.

## cap (B) is a TRAVEL bound, and it is looser than the frontier

Write `sf = (M + 2) + travel`.  Then, for `M >= 5`,

    4*sf <= 7*M - 1   <=>   4*travel + 9 <= 3*M   <=>   travel <= (3*M - 9)/4.

So cap (B) permits travel up to about `3M/4`, while the frontier wants `travel <= M/2`.
**cap (B) is therefore strictly weaker than the frontier** (`capB_allows_more_than_frontier`),
which is exactly why it is the right intermediate target: proving it is easier than proving the
frontier directly, and it suffices.

## What the `4/7` is

Measured `sf/M` is 1.0142 at `M = 5419`, 1.000626 at `M = 22933441`, and exactly 1.000000 at
`M = 183616423`.  Since `sf = M + 2 + travel` with `travel/M` tiny, `sf/M -> 1`, and hence

    4*sf/(7*M-1) -> 4/7 = 0.5714...

So `4/7` is nothing delicate: it is the constant of the `sf`-form when `sf ~ M`.  The room in
cap (B) comes from `travel/M` being small, not from a tight balance.

## How much room, honestly

`travel / ((3M-9)/4)` is at most **0.147** (at `M = 139`), and falls to `0.0256` at `M = 2659`
and `0.00083` at `M = 22933441`.  So above the threshold cap (B) holds with a factor of at
least 6.8, and typically far more.  The margin is not the obstruction; the mechanism is.
-/

namespace A166944Research

/-- **cap (B) restated as a pure travel bound.**  For `sf = (M + 2) + travel` and `M >= 5`,
cap (B) is equivalent to `4*travel + 9 <= 3*M`. -/
theorem capB_iff_travel {M travel : Nat} (hM : 5 ≤ M) :
    4 * ((M + 2) + travel) ≤ 7 * M - 1 ↔ 4 * travel + 9 ≤ 3 * M := by
  constructor <;> intro h <;> omega

/-- **cap (B) is looser than the frontier.**  Stated division-free: `2*M < 3*M - 9` for
`M >= 10`, which says the cap's travel allowance `(3M-9)/4` exceeds the frontier's `M/2` by a
factor of `3/2`.  (The divided form needs `M >= 10` rather than `9` because
`(3*9-9)/4 = 4` and `9/2 = 4` coincide.) -/
theorem capB_allows_more_than_frontier {M : Nat} (hM : 10 ≤ M) :
    2 * M < 3 * M - 9 := by omega

/-- **The observed `4/7` arises from a bound on `sf`.**  If `4*sf <= 7*M - 1` holds then the
`sf`-form is under `7M/4`; conversely the useful direction for the tree is that a `sf`-bound in
the division-free form `4*sf + 1 <= 7*M` is exactly cap (B).  Stated without division because
`omega` cannot reason about `7 * M / 4`. -/
theorem capB_iff_four_sf {M sf : Nat} (hM : 9 ≤ M) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * sf + 1 ≤ 7 * M := by
  -- Explicit rewrite of the truncated subtraction; `omega` on this shape leaks
  -- `Classical.choice` (CLASSICAL_CHOICE_AUDIT.md).
  have h7 : 1 ≤ 7 * M := by omega
  constructor
  · intro h; omega
  · intro h
    have hsub : 7 * M - 1 + 1 = 7 * M := Nat.sub_add_cancel h7
    omega

/-- **The two failures, in travel form.**  At `M = 13` cap (B) would need `4*travel+9 <= 39`,
i.e. `travel <= 7`, but the replay travels 9.  At `M = 43` it would need `travel <= 30`, but the
replay travels 34.  These are failures of the *hypothesis*, not of the frontier's truth. -/
theorem capB_travel_form_fails_at_small :
    ¬ (4 * (9 : Nat) + 9 ≤ 3 * 13) ∧ ¬ (4 * (34 : Nat) + 9 ≤ 3 * 43) := by
  refine ⟨by decide, by decide⟩

/-- **The frontier fails at exactly the same two records.**  `2*9 > 13` and `2*34 > 43`, so the
cap's two failures coincide with the frontier's own failures — which is why they are harmless
and crop out at the threshold rather than signalling a real obstruction. -/
theorem frontier_also_fails_at_small :
    ¬ (2 * (9 : Nat) ≤ 13) ∧ ¬ (2 * (34 : Nat) ≤ 43) := by
  refine ⟨by decide, by decide⟩

/-- **The threshold is genuine.**  At `M = 139` the cap holds with ratio `0.6420 < 1`:
`4*156 = 624 <= 972 = 7*139 - 1`.  Together with the two failures this witnesses that the
pass/fail boundary lies between `43` and `139`. -/
theorem capB_holds_at_139 : 4 * (156 : Nat) ≤ 7 * 139 - 1 := by decide

/-! ## Axiom audit -/

#print axioms capB_iff_travel
#print axioms capB_allows_more_than_frontier
#print axioms capB_iff_four_sf
#print axioms capB_travel_form_fails_at_small
#print axioms frontier_also_fails_at_small
#print axioms capB_holds_at_139

end A166944Research
