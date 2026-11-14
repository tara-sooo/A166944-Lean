import A166944.AbsoluteIndex

namespace A166944Research

/-! Concrete refutations of the two relaxed critical-configuration candidates.

The canonical critical configuration requires `d s` to be a NEW RECORD. Relaxing
the record condition leaves exactly two realisations in the recurrence up to
2,000,000, at `s = 18` and `s = 66`, and both have composite `d s`
(`9 = 3^2` and `33 = 3 * 11`). Here we check that neither is a record.

These are the concrete halves of the general statement "a composite difference
is never a running maximum".
-/

-- d 18 = 9, and 9 is not a record because d 15 = 13 > 9
theorem not_record_at_18 : ¬ (d 18 = 9 ∧ ∀ k : Nat, 2 ≤ k → k < 18 → d k < 9) := by
  intro h
  have h13 : d 15 = 13 := by decide
  have := h.2 15 (by decide) (by decide)
  omega

-- d 66 = 33, and 33 is not a record because d 45 = 43 > 33
theorem not_record_at_66 : ¬ (d 66 = 33 ∧ ∀ k : Nat, 2 ≤ k → k < 66 → d k < 33) := by
  intro h
  have h43 : d 45 = 43 := by decide
  have := h.2 45 (by decide) (by decide)
  omega

-- the positivity check: these really are the values, so the refutations are not vacuous
theorem d18_is_nine : d 18 = 9 := by decide
theorem d66_is_thirtythree : d 66 = 33 := by decide
theorem d15_is_thirteen : d 15 = 13 := by decide
theorem d45_is_fortythree : d 45 = 43 := by decide

end A166944Research
