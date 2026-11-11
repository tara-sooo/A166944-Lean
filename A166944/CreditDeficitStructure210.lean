import A166944.CreditDeficits210

/-!
# Boundary requests and crossing requests in a minimal deficient window

Every interior cut must be crossed by a positive request. Otherwise
the two proper subwindows can be paid independently, contradicting
minimality. Positive requests also determine both window endpoints.
-/

open Finset

namespace A166944Research

theorem minimal_credit_deficit_crosses_every_cut210 {n m a b : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (deficit : CreditWindowDeficit210 demand supply time left right a b)
    (minimal : ∀ a' b' : Nat, a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) →
      ¬ CreditWindowDeficit210 demand supply time left right a' b')
    (t : Nat) (hat : a ≤ t) (htb : t < b) :
    ∃ i ∈ creditWindowRequests210 left right a b,
      0 < demand i ∧ left i ≤ t ∧ t < right i := by
  classical
  by_contra hcross
  let L := creditWindowRequests210 left right a t
  let R := creditWindowRequests210 left right (t + 1) b
  let I := creditWindowRequests210 left right a b
  have hsub : L ∪ R ⊆ I := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have h := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, by omega⟩
    · have h := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, h.2⟩
  have hdisjoint : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h := (Finset.mem_filter.mp hi).2
    have h' := (Finset.mem_filter.mp hj).2
    have hv := valid i
    omega
  have hzero (i : Fin n) (hi : i ∈ I) (hmissing : i ∉ L ∪ R) : demand i = 0 := by
    have h := (Finset.mem_filter.mp hi).2
    have hright : t < right i := by
      by_contra hn
      apply hmissing
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, by omega⟩)
    have hleft : left i ≤ t := by
      by_contra hn
      apply hmissing
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, h.2⟩)
    by_contra hz
    exact hcross ⟨i, hi, by omega, hleft, hright⟩
  have hsum : (∑ i ∈ I, demand i) = (∑ i ∈ L, demand i) + ∑ i ∈ R, demand i := by
    rw [← Finset.sum_union hdisjoint]
    symm
    exact Finset.sum_subset hsub (fun i hi hn => hzero i hi hn)
  have hsL := Nat.le_of_not_gt (minimal a t (Nat.le_refl _) hat (by omega) (Or.inr htb))
  have hsR := Nat.le_of_not_gt (minimal (t + 1) b (by omega) (by omega) (Nat.le_refl _) (Or.inl (by omega)))
  let SL := creditWindowSources210 time a t
  let SR := creditWindowSources210 time (t + 1) b
  have hsdisjoint : Disjoint SL SR := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have h := (Finset.mem_filter.mp hj).2
    have h' := (Finset.mem_filter.mp hk).2
    omega
  have hsunion : SL ∪ SR = creditWindowSources210 time a b := by
    ext j
    simp only [SL, SR, creditWindowSources210, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have hsourceSum : (∑ j ∈ SL, supply j) + (∑ j ∈ SR, supply j) =
      ∑ j ∈ creditWindowSources210 time a b, supply j := by
    rw [← Finset.sum_union hsdisjoint, hsunion]
  change (∑ j ∈ creditWindowSources210 time a b, supply j) < ∑ i ∈ I, demand i at deficit
  change (∑ i ∈ L, demand i) ≤ ∑ j ∈ SL, supply j at hsL
  change (∑ i ∈ R, demand i) ≤ ∑ j ∈ SR, supply j at hsR
  omega

theorem minimal_credit_deficit_has_boundary_requests210 {n m a b : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (hab : a ≤ b) (deficit : CreditWindowDeficit210 demand supply time left right a b)
    (minimal : ∀ a' b' : Nat, a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) →
      ¬ CreditWindowDeficit210 demand supply time left right a' b') :
    (∃ i ∈ creditWindowRequests210 left right a b, 0 < demand i ∧ left i = a) ∧
    (∃ k ∈ creditWindowRequests210 left right a b, 0 < demand k ∧ right k = b) := by
  classical
  by_cases hlt : a < b
  · obtain ⟨i, hi, hpos, hleft, _⟩ :=
      minimal_credit_deficit_crosses_every_cut210 valid deficit minimal a (Nat.le_refl _) hlt
    obtain ⟨k, hk, hkpos, _, hkright⟩ :=
      minimal_credit_deficit_crosses_every_cut210 valid deficit minimal (b - 1) (by omega) (by omega)
    have hiBounds := (Finset.mem_filter.mp hi).2
    have hkBounds := (Finset.mem_filter.mp hk).2
    exact ⟨⟨i, hi, hpos, by omega⟩, ⟨k, hk, hkpos, by omega⟩⟩
  · have heq : a = b := by omega
    have hsum : 0 < ∑ i ∈ creditWindowRequests210 left right a b, demand i :=
      (Nat.zero_le _).trans_lt deficit
    obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hsum
    have hiBounds := (Finset.mem_filter.mp hi).2
    have hv := valid i
    exact ⟨⟨i, hi, hpos, by omega⟩, ⟨i, hi, hpos, by omega⟩⟩

end A166944Research
