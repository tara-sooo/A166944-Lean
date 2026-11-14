import A166944.CompSweep1000

namespace A166944Research

/-!
# The record structure above 200

`313` (at n = 315) and `661` (at n = 663) are genuinely NEW RUNNING MAXIMA, so
they are not refutable by the "earlier larger value" pattern used for 18/66/150.
What holds instead is the positive record statement: every earlier index carries
a strictly smaller difference.

Note the structural law `d n = n - 2` at every record from n = 5 on:
3 = 5-2, 7 = 9-2, 13 = 15-2, 43 = 45-2, 139 = 141-2, 313 = 315-2, 661 = 663-2.
-/

set_option maxRecDepth 300000

/-- Every `k < 315` (with `2 <= k`) has a difference strictly below `313`. -/
theorem threehundredthirteen_is_record :
    ∀ k ∈ List.range 315, 2 ≤ k → d k < 313 := by decide

/-- Every `k < 663` (with `2 <= k`) has a difference strictly below `661`. -/
theorem sixhundredsixtyone_is_record :
    ∀ k ∈ List.range 663, 2 ≤ k → d k < 661 := by decide

/-- `315` realises the pattern `d n = n - 2` and is a record. -/
theorem record_at_315 :
    d 315 = 313 ∧ ∀ k ∈ List.range 315, 2 ≤ k → d k < 313 :=
  ⟨d315_is_threehundredthirteen, threehundredthirteen_is_record⟩

/-- `663` realises the pattern `d n = n - 2` and is a record. -/
theorem record_at_663 :
    d 663 = 661 ∧ ∀ k ∈ List.range 663, 2 ≤ k → d k < 661 :=
  ⟨d663_is_sixhundredsixtyone, sixhundredsixtyone_is_record⟩

/-- `661` beats the earlier record `313`, and `313` beats `139`. -/
theorem record_chain_above_200 : d 141 = 139 ∧ d 315 = 313 ∧ d 663 = 661 :=
  ⟨d141_is_hundredthirtynine, d315_is_threehundredthirteen,
    d663_is_sixhundredsixtyone⟩

end A166944Research
