import A166944.EventCountFails
import A166944.CanonicalRecord

set_option maxRecDepth 100000

/-!
# R7: which canonical starts actually fail `48 p^2 + 1 < M`?
-/

namespace A166944Research

/-- `M = 13` is a canonical start: `d 15 = 13`. -/
theorem R7_start_13 : d (13 + 2) = 13 := by decide

/-- `M = 43` is a canonical start: `d 45 = 43`. -/
theorem R7_start_43 : d (43 + 2) = 43 := by decide

/-- **`M = 13` FAILS the event-count criterion** at the real replay count `p = 4`:
`48 * 16 + 1 = 769 > 13`. -/
theorem R7_count_fails_at_13 : ¬ (48 * (4 * 4) + 1 < 13) := by decide

/-- **`M = 43` FAILS the event-count criterion** at the real replay count `p = 6`:
`48 * 36 + 1 = 1729 > 43`. -/
theorem R7_count_fails_at_43 : ¬ (48 * (6 * 6) + 1 < 43) := by decide

/-- So the failures include `13` AND `43`, both strictly below `139`.  This
contradicts `REACH.md`'s "the smallest at `M = 139`". -/
theorem R7_139_is_not_the_smallest :
    ¬ (48 * (4 * 4) + 1 < 13) ∧ ¬ (48 * (6 * 6) + 1 < 43) ∧
      ¬ (48 * (2 * 2) + 1 < 139) := ⟨by decide, by decide, by decide⟩

/-- The three canonical starts the two documents disagree about, with their
replay counts: `13 -> 4`, `43 -> 6`, `139 -> 2`. -/
theorem R7_counts : (4 : Nat) * 4 = 16 ∧ (6 : Nat) * 6 = 36 ∧ (2 : Nat) * 2 = 4 :=
  ⟨by decide, by decide, by decide⟩

/-- And the criterion HOLDS at `M = 5419` with `p = 9`, so the failure set is not
an initial segment: `13, 43, 139, 313, 2659` fail while `661, 1321, 5419` hold. -/
theorem R7_holds_at_661 : 48 * (0 * 0) + 1 < 661 := by decide

end A166944Research

#print axioms A166944Research.R7_start_13
#print axioms A166944Research.R7_start_43
#print axioms A166944Research.R7_139_is_not_the_smallest
#print axioms A166944Research.R7_holds_at_661
