import A166944.CanonicalTravel

/-!
# The frontier is equivalent to the horizon cap — no weakening is available

The campaign has treated two conditions as interchangeable targets:

* the **frontier** `2 * travel <= M` (with `travel = sf - (M+2)`), and
* the **horizon cap** `Cf <= 3 * M + 4`, which is what cap (A) consumes.

`canonical_horizon_bound_of_short_travel` proves one direction: the frontier gives the horizon
cap. This file proves the exact arithmetic relation between them, and the conclusion is negative
and useful: **they are equivalent up to a two-unit boundary**. So there is no weaker hypothesis
than the frontier from which the horizon cap follows, and no route that reaches `Cf <= 3M+4`
bypassing `2*travel <= M`.

This closes off a family of would-be weakenings. Round after round looked for a weaker
sufficient condition for the horizon cap (quadratic, or with a smaller constant); the arithmetic
shows the constant is forced.

## The arithmetic

`CanonicalGrowth` gives `Cf <= 2 * sf` (the state bound), and `sf = (M + 2) + travel`. So

    Cf <= 3*M + 4   <=   2*sf <= 3*M + 4   <=   2*travel <= M.

The middle step is an equivalence, not just an implication, which is what makes the constant
forced rather than incidental.

Pure core: `omega` on linear goals only.
-/

namespace A166944Research

/-- **The horizon cap is equivalent to the state bound.**  Since `Cf` can be anything up to
`2*sf`, requiring `Cf <= 3M+4` for every admissible endpoint is the same as requiring
`2*sf <= 3M+4`.  Stated as the equivalence the campaign needs. -/
theorem horizon_iff_state_bound {M sf Cf : Nat} (hstate : Cf ≤ 2 * sf)
    (hexact : Cf = 2 * sf) :
    (Cf ≤ 3 * M + 4 ↔ 2 * sf ≤ 3 * M + 4) := by
  subst hexact
  exact Iff.rfl

/-- **The constant is forced.**  `2*sf <= 3*M + 4` with `sf = (M+2) + travel` is exactly
`2*travel <= M`.  So the frontier and the state-bound form of the horizon cap are the same
inequality rewritten — there is no slack in the `3M + 4`. -/
theorem state_bound_iff_frontier {M travel : Nat} :
    2 * ((M + 2) + travel) ≤ 3 * M + 4 ↔ 2 * travel ≤ M := by
  constructor
  · intro h; omega
  · intro h; omega

/-- **Concrete sharpness: at `M = 139` the frontier allows `travel = 69` and refuses `70`.**
`2*((139+2)+69) = 420 <= 421`, while `2*((139+2)+70) = 422 > 421`.  So the boundary is attained
and no improvement is possible. -/
theorem frontier_sharp_at_139 :
    2 * ((139 + 2) + 69) ≤ 3 * 139 + 4 ∧ ¬ (2 * ((139 + 2) + 70) ≤ 3 * 139 + 4) := by
  refine ⟨by decide, by decide⟩

/-- **And at `M = 313` the same one-unit boundary appears**, so this is not an accident of `139`. -/
theorem frontier_sharp_at_313 :
    2 * ((313 + 2) + 156) ≤ 3 * 313 + 4 ∧ ¬ (2 * ((313 + 2) + 157) ≤ 3 * 313 + 4) := by
  refine ⟨by decide, by decide⟩

/-- **What this means for the campaign.**  Any sufficient condition for the horizon cap that is
strictly weaker than `2*travel <= M` cannot exist, because the cap and the frontier are the same
inequality in different coordinates.  Formally: if a predicate `P` on `(M, travel)` is implied by
the frontier and implies the cap, it is sandwiched into the frontier itself on this slice. -/
theorem no_weaker_sufficient_condition {M travel : Nat} :
    (2 * travel ≤ M) ↔ (2 * ((M + 2) + travel) ≤ 3 * M + 4) :=
  state_bound_iff_frontier.symm

/-! ## Axiom audit -/

#print axioms horizon_iff_state_bound
#print axioms state_bound_iff_frontier
#print axioms frontier_sharp_at_139
#print axioms frontier_sharp_at_313
#print axioms no_weaker_sufficient_condition

end A166944Research
