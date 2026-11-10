import A166944.RecordBarrier
import Mathlib.Data.Nat.Prime.Defs

/-!
# A166944 primality target definitions

This file contains the prime-dependent part of the target. It is intentionally
separate from `ResearchDefs.lean` so that most Termux proof-search iterations
on recurrence structure do not import Mathlib's prime theory.

Import this file only when the current proof genuinely needs `Nat.Prime`.
-/

namespace A166944Research

def IsGreaterTwinPrime (p : ℕ) : Prop := p.Prime ∧ (p - 2).Prime

def Target : Prop :=
  ∀ R : ℕ, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R

/-- The original conjecture would imply arbitrarily large twin-prime pairs. -/
theorem unbounded_greater_twin_primes_of_target (hTarget : Target) (M : ℕ) :
    ∃ R : ℕ, M < R ∧ IsGreaterTwinPrime R := by
  obtain ⟨R, hlarge, hrecord⟩ := difference_records_unbounded (M + 5)
  exact ⟨R, by omega, hTarget R (by omega) hrecord⟩

end A166944Research
