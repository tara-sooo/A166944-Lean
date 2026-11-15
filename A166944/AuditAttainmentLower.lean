import A166944.AttainmentIsFree
import A166944.TwoCapGate

/-!
# R3: is the second component of `IsAttainedPreviousMaximum` really free,
# and does the frontier actually use a form containing it?
-/

namespace A166944Research

/-- The definition, restated so the report can quote it exactly. -/
theorem R3_def_shape :
    IsAttainedPreviousMaximum 13 24 ↔
      ((∀ j : Nat, 2 ≤ j → j ≤ 24 → d j ≤ 13) ∧
        ∃ r : Nat, 2 ≤ r ∧ r ≤ 24 ∧ d r = 13) := Iff.rfl

/-- The canonical start at `M = 13` has `d 15 = 13`, evaluated. -/
theorem audit_d15_eq_thirteen : d (13 + 2) = 13 := by decide

/-! ### A. Claim 3a: the second component is free -- TRUE, and re-verified -/

theorem R3_attainment_is_free (sf : Nat) (hsf : 13 + 2 ≤ sf) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = 13 :=
  attainment_clause_is_free (M := 13) (sf := sf) audit_d15_eq_thirteen hsf

/-- **The clause holds at EVERY index `≥ M+2`**, so it cannot bound `sf`. -/
theorem R3_clause_holds_at_every_large_index (N : Nat) :
    ∃ sf : Nat, N ≤ sf ∧ ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = 13 :=
  ⟨max N 15, Nat.le_max_left _ _,
    attainment_clause_holds_at_every_index (M := 13) audit_d15_eq_thirteen
      (max N 15) (Nat.le_max_right _ _)⟩

/-! ### B. Claim 3b: IS THE THEOREM ABOUT THE RIGHT OBJECT?

The lead's headline is "`IsAttainedPreviousMaximum`'s second component is free".
That is true of the *predicate*.  But the frontier as the tree states it is
`CanonicalTravelBoundFrom` / `TwoCapGate`'s caps, and their hypothesis is
`IsAttainedPreviousMaximum M sf` -- which DOES contain the second component.

The question the brief asks: does the goal we actually target use the form WITH
the second component?  Yes: `canonical_next_record_factors_of_two_caps_tight`
takes `IsAttainedPreviousMaximum M sf`, and `CapBCandidates.capB_of_event_count`
takes `IsAttainedPreviousMaximum M sf`.  So the theorem is NOT vacuous -- it
licenses replacing that hypothesis by its first component.

But it is also NOT the sharpest statement available, because `AttainmentIsFree`
claims equivalence for the *universally quantified* forms, and that equivalence
needs `M + 2 ≤ sf`.  The consumer supplies `M + 2 ≤ sf` only via
`moving_horizon_path_index_le hpath`.  Verified below that this is available. -/

/-- The exact hypotheses `canonical_next_record_factors_of_two_caps_tight`
consumes: it takes `IsAttainedPreviousMaximum M sf`, so the frontier DOES use a
form containing the second component. -/
theorem R3_consumer_uses_the_attained_form {M sf Cf p : Nat}
    (_hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) :
    IsAttainedPreviousMaximum M sf := hmax

/-- The equation the equivalence relies on, extracted from the path. -/
theorem R3_index_lower_bound_is_free {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) : M + 2 ≤ sf :=
  moving_horizon_path_index_le hpath

/-! ### C. The equivalence is correct but it is *conditional* on a nonempty path -/

/-- **A precise limitation.**  `attained_previous_maximum_iff_upper_bound` needs
`M + 2 ≤ sf`.  If `sf < M + 2` the second component does NOT follow, so the
equivalence is not "free" in the literal sense -- it is free *given the path*.
At `sf = 3` with `M = 13` the upper-bound component holds vacuously but the
existential fails, because `d r = 13` has no witness below index 4. -/
theorem R3_equivalence_needs_the_lower_bound :
    ¬ (∃ r : Nat, 2 ≤ r ∧ r ≤ 3 ∧ d r = 13) := by
  rintro ⟨r, hr2, hr3, hdr⟩
  have h : r = 2 ∨ r = 3 := by omega
  have h2 : d 2 = 2 := by decide
  have h3 : d 3 = 1 := by decide
  rcases h with h | h
  · rw [h] at hdr; omega
  · rw [h] at hdr; omega

/-- And with `sf = 3` the upper-bound component is vacuous. -/
theorem R3_upper_bound_component_is_vacuous_at_3 :
    (∀ j : Nat, 2 ≤ j → j ≤ 3 → d j ≤ 13) := by
  intro j hj hj3
  have h : j = 2 ∨ j = 3 := by omega
  have h2 : d 2 = 2 := by decide
  have h3 : d 3 = 1 := by decide
  rcases h with h | h
  · rw [h]; omega
  · rw [h]; omega

end A166944Research

#print axioms A166944Research.R3_attainment_is_free
#print axioms A166944Research.R3_clause_holds_at_every_large_index
#print axioms A166944Research.R3_index_lower_bound_is_free
#print axioms A166944Research.R3_equivalence_needs_the_lower_bound
#print axioms A166944Research.R3_upper_bound_component_is_vacuous_at_3
