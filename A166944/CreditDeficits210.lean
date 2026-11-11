import A166944.CreditWindows210

/-! # Minimal deficient windows for interval credits -/

open Finset

namespace A166944Research

def CreditWindowDeficit210 {n m : Nat} (demand : Fin n → Nat) (supply : Fin m → Nat)
    (time : Fin m → Nat) (left right : Fin n → Nat) (a b : Nat) : Prop :=
  (∑ j ∈ creditWindowSources210 time a b, supply j) <
    ∑ i ∈ creditWindowRequests210 left right a b, demand i

/-- Failure of interval Hall has a deficient window of least length;
every strictly smaller contained window has sufficient capacity. -/
theorem credit_minimal_deficit_window210 {n m : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (failure : ¬ CreditHallCondition210 demand supply (fun i j => left i ≤ time j ∧ time j ≤ right i)) :
    ∃ a b : Nat, a ≤ b ∧ CreditWindowDeficit210 demand supply time left right a b ∧
      ∀ a' b' : Nat, a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) →
        ¬ CreditWindowDeficit210 demand supply time left right a' b' := by
  classical
  have hex : ∃ a b : Nat, a ≤ b ∧ CreditWindowDeficit210 demand supply time left right a b := by
    by_contra h
    apply failure
    apply credit_hall_of_windows210 valid
    intro a b hab
    have hn : ¬ CreditWindowDeficit210 demand supply time left right a b := fun hd => h ⟨a, b, hab, hd⟩
    exact Nat.le_of_not_gt hn
  have hwidth : ∃ width : Nat, ∃ a b : Nat, a ≤ b ∧ b - a = width ∧
      CreditWindowDeficit210 demand supply time left right a b := by
    obtain ⟨a, b, hab, hd⟩ := hex
    exact ⟨b - a, a, b, hab, rfl, hd⟩
  obtain ⟨a, b, hab, heq, hdeficit⟩ := Nat.find_spec hwidth
  refine ⟨a, b, hab, hdeficit, ?_⟩
  intro a' b' ha' hab' hb' hproper hd'
  have hsmall : b' - a' < Nat.find hwidth := by omega
  have hmin := Nat.find_min' hwidth ⟨a', b', hab', rfl, hd'⟩
  omega

end A166944Research
