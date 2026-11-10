import A166944.TargetDefs
import A166944.VerifiedRecordPrefix

/-!
# Bounded A166944 twin-primality theorem

This module connects the verified divisibility checks to the exact
prime predicate of the project's A166944 target.
-/

namespace A166944Research

private theorem prime_of_no_proper_factor {N : Nat} (hN : 2 ≤ N)
    (hfree : NoProperFactor N) : N.Prime :=
  Nat.prime_def_lt'.2 ⟨hN, fun f hf hlt => hfree ⟨f, hlt⟩ hf⟩

/-- The A166944 twin-primality statement for every strict record greater
than five and at most the last verified record value. -/
theorem target_for_records_le_22933441 {R : Nat}
    (hR : 5 < R) (hbound : R ≤ 22933441) (hrecord : IsDifferenceRecord R) :
    IsGreaterTwinPrime R := by
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  obtain ⟨_, hminus, hplus⟩ := record_index_and_factors_of_le_22933441 hR hbound hn hd hprior
  exact ⟨prime_of_no_proper_factor (by omega) hplus, prime_of_no_proper_factor (by omega) hminus⟩

end A166944Research
