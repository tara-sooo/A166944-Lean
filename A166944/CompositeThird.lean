import A166944.CompositeProbe

namespace A166944Research

set_option maxRecDepth 100000

/-! The third composite difference below 200, handled the same way.

`CompositeProbe.lean` refutes `s = 18` and `s = 66`. A light scan over
`2 <= n <= 200` finds exactly three composite values of `d n` -- 9 (n = 18),
33 (n = 66) and 25 (n = 150) -- and each has an earlier index carrying a
strictly larger difference, which is what the record clause forbids. This file
closes the third one so the sweep to 200 is complete at the value level.

  d 150 = 25, and 25 is not a record because d 141 = 139 > 25
-/

theorem d150_is_twentyfive : d 150 = 25 := by decide
theorem d141_is_hundredthirtynine : d 141 = 139 := by decide

theorem not_record_at_150 : ¬ (d 150 = 25 ∧ ∀ k : Nat, 2 ≤ k → k < 150 → d k < 25) := by
  intro h
  have h141 : d 141 = 139 := by decide
  have := h.2 141 (by decide) (by decide)
  omega

/-- The three composite differences below 200, with their refutations. -/
theorem composite_below_200_closed :
    (d 18 = 9 ∧ d 15 = 13) ∧ (d 66 = 33 ∧ d 45 = 43) ∧ (d 150 = 25 ∧ d 141 = 139) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end A166944Research
