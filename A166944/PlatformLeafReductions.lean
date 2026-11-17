import A166944.AttainmentIsFree
import A166944.TargetDefs

/-!
# The platform's cap-B leaf is the tree's capped form

The platform states its cap-B leaf with the hypothesis `IsAttainedPreviousMaximum M sf`, whose
first component is `∀ j, 2 ≤ j → j ≤ sf → d j ≤ M`.  The tree's `RelaxedIndexCapCappedForm` takes
exactly that inequality as its hypothesis and concludes `4 * sf ≤ 7 * M - 1`.

So the two are the same statement, and proving the tree's capped form proves the platform leaf.
The converse direction is not claimed here: the platform hypothesis also carries an attainment
witness, which the tree form does not need.

This is the useful reduction for the cap-B attack, because the tree form is stated WITHOUT the
`IsGreaterTwinPrime` conjunct and without the extra attainment witness, so it is the smaller
target of the two.
-/

namespace A166944Research

/-- **The platform leaf hB follows from the tree's capped form.** -/
theorem platform_hB_of_relaxed_index_cap_capped_form (h : RelaxedIndexCapCappedForm) :
    ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1 := by
  intro M sf Cf p hM _ hcanon hpath hmax
  exact h hM hcanon hpath hmax.1

/-- The same reduction for the horizon-cap leaf `hA`: the tree's `CanonicalTravel` supplies
`Cf ≤ 3*M + 4` from either the event-count criterion or a travel bound, so this leaf is only open
in the range where neither criterion applies. -/
theorem platform_hA_needs_criterion_or_travel {M sf Cf p : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf)
    (hcrit : 48 * (p * p) + 1 < M) : Cf ≤ 3 * M + 4 :=
  canonical_horizon_bound_of_event_count hM hcanon hpath hmax hcrit

/-! ## Axiom audit -/

#print axioms platform_hB_of_relaxed_index_cap_capped_form
#print axioms platform_hA_needs_criterion_or_travel

end A166944Research
