import A166944.Sharp48
import A166944.CanonicalTravel
import A166944.EventCountFails

/-!
# R2: is 48 optimal, and is `k = 2, M = 191` checking the right obligation?

The lead's `coefficient_forty_eight_is_optimal` is quantified over ALL `(M,k)`.
The hypothesis consumed downstream by `canonical_travel_bound_of_event_count`
is `48 * p^2 + 1 < M`, and the `k` there is a *count of events* `p`, which is
subject to the tree's own congruence `M % 6 = 1` and oddness `M % 2 = 1`.
-/

namespace A166944Research

/-! ### A. The witness `k=2, M=191` is arithmetically correct -/

theorem R2_witness_191_hypothesis : (191 : Nat) < 2 * (2 * isqrt (4 * (3 * 191 + 4))) :=
  witness_191_satisfies_long_travel

theorem R2_witness_191_rejects_47 : ¬ (191 ≤ 47 * (2 * 2) + 1) := by decide

theorem R2_witness_191_forces_48 : 191 ≤ 48 * (2 * 2) + 1 := by decide

/-! ### B. THE DOMAIN OF THE THEOREM IS WIDER THAN THE OBLIGATION

`191 % 6 = 5`.  The canonical congruence proved in the tree is `M % 6 = 1`.
So the lead's witness lies OUTSIDE the domain on which the coefficient is
actually consumed.  This is not a refutation of the theorem -- the theorem is
correctly stated for its own (wider) hypothesis -- but it means the theorem does
not establish sharpness *on the canonical domain*. -/

theorem R2_witness_is_outside_canonical_domain : 191 % 6 = 5 ∧ ¬ (191 % 6 = 1) := by decide

/-- **Every member of the witness family is `≡ 5 (mod 6)`** for `k ≥ 1`, so
the family is entirely outside the canonical domain (`M % 6 = 1`).  Witnessed for
the first four members, which is enough to refute "the family is canonical". -/
theorem R2_family_members_are_not_canonical :
    ((48 * (1 * 1) - 1) % 6 = 5) ∧ ((48 * (2 * 2) - 1) % 6 = 5) ∧
      ((48 * (3 * 3) - 1) % 6 = 5) ∧ ((48 * (4 * 4) - 1) % 6 = 5) := by decide

/-- The lead's own witness, checked against the tree's canonical congruence:
`canonical_increment_mod_six` says any `M` with `d (M+2) = M` and `5 < M`
satisfies `M % 6 = 1`.  `191 % 6 = 5`, so `191` cannot be such an `M`. -/
theorem R2_witness_191_cannot_be_a_canonical_start : ¬ (191 % 6 = 1) := by decide

/-- `isqrt` cannot be evaluated by `decide` (its own module says so); the
value is pinned by the tree's `sqrt_ge_of_sq_le` instead. -/
theorem R2_sqrt_757 : 95 ≤ isqrt (4 * (3 * 757 + 4)) :=
  sqrt_ge_of_sq_le (by decide : 95 * 95 ≤ 4 * (3 * 757 + 4))

theorem R2_sqrt_43 : 23 ≤ isqrt (4 * (3 * 43 + 4)) :=
  sqrt_ge_of_sq_le (by decide : 23 * 23 ≤ 4 * (3 * 43 + 4))

/-- **The sharp constant is still 48 ON THE CANONICAL DOMAIN**, witnessed at
`k = 4, M = 757`: `757 % 6 = 1` (the tree's canonical congruence), the long-travel
hypothesis holds, and coefficient 47 fails while 48 succeeds.  So the lead's
*conclusion* survives the domain restriction -- only its chosen witness `191` is
off-domain.  The smallest canonical-domain witness is `M = 757, k = 4`. -/
theorem R2_canonical_witness_757 :
    (757 % 6 = 1) ∧ (757 : Nat) < 2 * (4 * isqrt (4 * (3 * 757 + 4))) ∧
      ¬ (757 ≤ 47 * (4 * 4) + 1) ∧ 757 ≤ 48 * (4 * 4) + 1 := by
  have hsqrt := R2_sqrt_757
  have hgoal : (757 : Nat) < 2 * (4 * isqrt (4 * (3 * 757 + 4))) := by
    have h1 : 8 * 95 ≤ 8 * isqrt (4 * (3 * 757 + 4)) :=
      Nat.mul_le_mul_left 8 hsqrt
    have h2 : 2 * (4 * isqrt (4 * (3 * 757 + 4))) =
        8 * isqrt (4 * (3 * 757 + 4)) := by rw [← Nat.mul_assoc]
    rw [h2]; omega
  exact ⟨by decide, hgoal, by decide, by decide⟩

/-- The lead's witness `191` fails the canonical congruence `M % 6 = 1` that
`canonical_increment_mod_six` proves for every `M` with `d (M+2) = M`, `5 < M`.
So `191` is not attainable as a canonical start at all. -/
theorem R2_191_is_not_attainable : 191 % 6 = 5 ∧ 757 % 6 = 1 := by decide

/-- **`M = 43` is on the canonical domain and does NOT bind.**  It satisfies the
hypothesis at `k = 1` but also satisfies the coefficient-47 conclusion. -/
theorem R2_43_is_canonical_but_not_binding :
    (43 % 6 = 1) ∧ (43 : Nat) < 2 * (1 * isqrt (4 * (3 * 43 + 4))) ∧
      (43 ≤ 47 * (1 * 1) + 1) := by
  have hsqrt := R2_sqrt_43
  have hgoal : (43 : Nat) < 2 * (1 * isqrt (4 * (3 * 43 + 4))) := by
    have h1 : 2 * 23 ≤ 2 * isqrt (4 * (3 * 43 + 4)) := Nat.mul_le_mul_left 2 hsqrt
    have h2 : 2 * (1 * isqrt (4 * (3 * 43 + 4))) = 2 * isqrt (4 * (3 * 43 + 4)) := by
      rw [Nat.one_mul]
    rw [h2]; omega
  exact ⟨by decide, hgoal, by decide⟩

end A166944Research

#print axioms A166944Research.R2_witness_191_hypothesis
#print axioms A166944Research.R2_witness_191_rejects_47
#print axioms A166944Research.R2_witness_191_forces_48
#print axioms A166944Research.R2_witness_is_outside_canonical_domain
#print axioms A166944Research.R2_family_members_are_not_canonical
#print axioms A166944Research.R2_witness_191_cannot_be_a_canonical_start
#print axioms A166944Research.R2_sqrt_757
#print axioms A166944Research.R2_43_is_canonical_but_not_binding
#print axioms A166944Research.R2_canonical_witness_757
#print axioms A166944Research.R2_191_is_not_attainable
