import A166944.ResearchDefs
import A166944.TargetDefs
import FormalConjectures.OEIS.«166944»

/-!
# Bridge to the canonical Formal Conjectures definitions

This file is intended primarily for clean CI verification. It proves that the
lightweight Termux definitions agree with the pinned Formal Conjectures source.
-/

namespace A166944Research

theorem a_eq_formalConjectures (n : ℕ) :
    a n = OeisA166944.a n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih1 =>
      simp [a, OeisA166944.a, ih1]

theorem d_eq_formalConjectures (n : ℕ) :
    d n = OeisA166944.d n := by
  simp [d, OeisA166944.d, a_eq_formalConjectures]

theorem isDifferenceRecord_iff_formalConjectures (R : ℕ) :
    IsDifferenceRecord R ↔ OeisA166944.IsDifferenceRecord R := by
  simp [IsDifferenceRecord, OeisA166944.IsDifferenceRecord, d_eq_formalConjectures]

theorem isGreaterTwinPrime_iff_formalConjectures (p : ℕ) :
    IsGreaterTwinPrime p ↔ OeisA166944.IsGreaterTwinPrime p := by
  rfl

end A166944Research
