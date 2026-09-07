import A166944.ResearchDefs
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

end A166944Research
