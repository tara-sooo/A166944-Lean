import A166944.CreditHall210
import Mathlib.Data.Finset.Max

/-!
# Time-window criterion for phase credits

Each request can use precisely the sources whose timestamps lie in its
closed interval. Weighted Hall is equivalent to testing contiguous windows:
all requests confined to a window must fit its source capacity. Source
timestamps need not be distinct and zero capacities are permitted.
-/

open Finset

namespace A166944Research

def creditWindowRequests210 {n : Nat} (left right : Fin n → Nat) (a b : Nat) :
    Finset (Fin n) := Finset.univ.filter (fun i => a ≤ left i ∧ right i ≤ b)

def creditWindowSources210 {m : Nat} (time : Fin m → Nat) (a b : Nat) :
    Finset (Fin m) := Finset.univ.filter (fun j => a ≤ time j ∧ time j ≤ b)

def CreditWindowCondition210 {n m : Nat} (demand : Fin n → Nat) (supply : Fin m → Nat)
    (time : Fin m → Nat) (left right : Fin n → Nat) : Prop :=
  ∀ a b : Nat, a ≤ b →
    (∑ i ∈ creditWindowRequests210 left right a b, demand i) ≤
      ∑ j ∈ creditWindowSources210 time a b, supply j

/-- Only the at most `n*n` windows with request endpoints need to be tested. -/
def CreditEndpointWindowCondition210 {n m : Nat} (demand : Fin n → Nat) (supply : Fin m → Nat)
    (time : Fin m → Nat) (left right : Fin n → Nat) : Prop :=
  ∀ i k : Fin n, left i ≤ right k →
    (∑ r ∈ creditWindowRequests210 left right (left i) (right k), demand r) ≤
      ∑ j ∈ creditWindowSources210 time (left i) (right k), supply j

theorem credit_windows_of_hall210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat}
    (hall : CreditHallCondition210 demand supply (fun i j => left i ≤ time j ∧ time j ≤ right i)) :
    CreditWindowCondition210 demand supply time left right := by
  classical
  intro a b _
  apply (hall (creditWindowRequests210 left right a b)).trans
  apply Finset.sum_le_sum_of_subset
  intro j hj
  obtain ⟨i, hi, hij⟩ := Finset.mem_biUnion.mp hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hij' : left i ≤ time j ∧ time j ≤ right i := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.1.trans hij'.1, hij'.2.trans hi'.2⟩

theorem credit_hall_of_endpoint_windows210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (windows : CreditEndpointWindowCondition210 demand supply time left right) :
    CreditHallCondition210 demand supply (fun i j => left i ≤ time j ∧ time j ≤ right i) := by
  classical
  let eligible := fun i j => left i ≤ time j ∧ time j ≤ right i
  let neighbors := eligibleCreditSources210 eligible
  have hmem (requests : Finset (Fin n)) (j : Fin m) :
      j ∈ neighbors requests ↔ ∃ i ∈ requests, left i ≤ time j ∧ time j ≤ right i := by
    simp [neighbors, eligibleCreditSources210, eligible]
  intro requests
  change (∑ i ∈ requests, demand i) ≤ ∑ j ∈ neighbors requests, supply j
  refine Finset.strongInductionOn requests ?_
  intro requests ih
  rcases requests.eq_empty_or_nonempty with hempty | hne
  · simp [hempty, neighbors, eligibleCreditSources210]
  obtain ⟨iL, hiL, hlo⟩ := Finset.exists_min_image requests left hne
  obtain ⟨iR, hiR, hhi⟩ := Finset.exists_max_image requests right hne
  have hbounds : left iL ≤ right iR := (valid iL).trans (hhi iL hiL)
  by_cases covered : ∀ j : Fin m, left iL ≤ time j → time j ≤ right iR → j ∈ neighbors requests
  · have hrequests : requests ⊆ creditWindowRequests210 left right (left iL) (right iR) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo i hi, hhi i hi⟩
    have hsources : creditWindowSources210 time (left iL) (right iR) ⊆ neighbors requests := by
      intro j hj
      exact covered j (Finset.mem_filter.mp hj).2.1 (Finset.mem_filter.mp hj).2.2
    exact (Finset.sum_le_sum_of_subset hrequests).trans
      ((windows iL iR hbounds).trans (Finset.sum_le_sum_of_subset hsources))
  · push Not at covered
    obtain ⟨gap, hgapL, hgapR, hgap⟩ := covered
    have split (i : Fin n) (hi : i ∈ requests) : right i < time gap ∨ time gap < left i := by
      by_contra h
      apply hgap
      exact (hmem requests gap).mpr ⟨i, hi, by omega, by omega⟩
    let before := requests.filter (fun i => right i < time gap)
    let after := requests.filter (fun i => time gap < left i)
    have hbefore : before ⊂ requests := by
      apply Finset.filter_ssubset.mpr
      exact ⟨iR, hiR, by omega⟩
    have hafter : after ⊂ requests := by
      apply Finset.filter_ssubset.mpr
      exact ⟨iL, hiL, by omega⟩
    have hdisjoint : Disjoint before after := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hbi := (Finset.mem_filter.mp hi).2
      have hai := (Finset.mem_filter.mp hj).2
      have hv := valid i
      omega
    have hunion : before ∪ after = requests := by
      ext i
      constructor
      · intro hi
        rcases Finset.mem_union.mp hi with h | h
        · exact (Finset.mem_filter.mp h).1
        · exact (Finset.mem_filter.mp h).1
      · intro hi
        rcases split i hi with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h⟩)
    have hsourceDisjoint : Disjoint (neighbors before) (neighbors after) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      obtain ⟨i, hi, hij⟩ := (hmem before j).mp hj
      obtain ⟨k, hk, hkj⟩ := (hmem after j).mp hk
      have hbi := (Finset.mem_filter.mp hi).2
      have hak := (Finset.mem_filter.mp hk).2
      omega
    have hsourceUnion : neighbors before ∪ neighbors after = neighbors requests := by
      ext j
      simp only [Finset.mem_union, hmem]
      constructor
      · rintro (⟨i, hi, hij⟩ | ⟨i, hi, hij⟩)
        · exact ⟨i, (Finset.mem_filter.mp hi).1, hij⟩
        · exact ⟨i, (Finset.mem_filter.mp hi).1, hij⟩
      · rintro ⟨i, hi, hij⟩
        rcases split i hi with h | h
        · exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, hij⟩
        · exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, hij⟩
    calc
      (∑ i ∈ requests, demand i) = (∑ i ∈ before, demand i) + ∑ i ∈ after, demand i := by
        rw [← hunion, Finset.sum_union hdisjoint]
      _ ≤ (∑ j ∈ neighbors before, supply j) + ∑ j ∈ neighbors after, supply j :=
        Nat.add_le_add (ih before hbefore) (ih after hafter)
      _ = ∑ j ∈ neighbors requests, supply j := by
        rw [← Finset.sum_union hsourceDisjoint, hsourceUnion]

theorem credit_hall_of_windows210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (windows : CreditWindowCondition210 demand supply time left right) :
    CreditHallCondition210 demand supply (fun i j => left i ≤ time j ∧ time j ≤ right i) := by
  exact credit_hall_of_endpoint_windows210 valid (fun i k h => windows (left i) (right k) h)

theorem credit_windows_iff_hall210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i) :
    CreditWindowCondition210 demand supply time left right ↔
      CreditHallCondition210 demand supply (fun i j => left i ≤ time j ∧ time j ≤ right i) :=
  ⟨credit_hall_of_windows210 valid, credit_windows_of_hall210⟩

theorem credit_endpoint_windows_iff_allocation210 {n m : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i) :
    CreditEndpointWindowCondition210 demand supply time left right ↔
      ∃ allocation : Fin n → Fin m → Nat,
        (∀ i j, 0 < allocation i j → left i ≤ time j ∧ time j ≤ right i) ∧
        (∀ i, (∑ j, allocation i j) = demand i) ∧
        (∀ j, (∑ i, allocation i j) ≤ supply j) := by
  constructor
  · intro windows
    exact credit_allocation_of_hall210 (credit_hall_of_endpoint_windows210 valid windows)
  · intro allocation
    have windows := credit_windows_of_hall210 (credit_hall_iff_allocation210.mpr allocation)
    exact fun i k h => windows (left i) (right k) h

theorem funded_phase_credit_allocation_of_windows210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (startup : Finset (Fin n)) (unique : Set.InjOn key (startup : Set (Fin n)))
    (cap : ∀ i ∈ startup, (cost i).toNat ≤ 29613) (supply : Fin m → Nat)
    (funding : (∑ j, supply j) ≤ (∑ i, (-cost i).toNat) + multiplier * first)
    (windows : CreditWindowCondition210 (fun i => if i ∈ startup then 0 else (cost i).toNat)
      supply time left right) :
    Nonempty (FundedPhaseCreditAllocation210 cost key
      (fun i j => left i ≤ time j ∧ time j ≤ right i) first multiplier) := by
  exact funded_phase_credit_allocation_of_hall210 startup unique cap supply funding
    (credit_hall_of_windows210 valid windows)

theorem funded_phase_credit_allocation_of_endpoint_windows210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (startup : Finset (Fin n)) (unique : Set.InjOn key (startup : Set (Fin n)))
    (cap : ∀ i ∈ startup, (cost i).toNat ≤ 29613) (supply : Fin m → Nat)
    (funding : (∑ j, supply j) ≤ (∑ i, (-cost i).toNat) + multiplier * first)
    (windows : CreditEndpointWindowCondition210 (fun i => if i ∈ startup then 0 else (cost i).toNat)
      supply time left right) :
    Nonempty (FundedPhaseCreditAllocation210 cost key
      (fun i j => left i ≤ time j ∧ time j ≤ right i) first multiplier) := by
  exact funded_phase_credit_allocation_of_hall210 startup unique cap supply funding
    (credit_hall_of_endpoint_windows210 valid windows)

theorem funded_phase_balance_of_endpoint_windows210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)}
    {time : Fin m → Nat} {left right : Fin n → Nat} (valid : ∀ i, left i ≤ right i)
    (startup : Finset (Fin n)) (unique : Set.InjOn key (startup : Set (Fin n)))
    (cap : ∀ i ∈ startup, (cost i).toNat ≤ 29613) (supply : Fin m → Nat)
    (funding : (∑ j, supply j) ≤ (∑ i, (-cost i).toNat) + multiplier * first)
    (windows : CreditEndpointWindowCondition210 (fun i => if i ∈ startup then 0 else (cost i).toNat)
      supply time left right) :
    (∑ i, cost i) ≤ ((smallPhaseStartupBound210 + multiplier * first : Nat) : Int) := by
  obtain ⟨certificate⟩ := funded_phase_credit_allocation_of_endpoint_windows210
    valid startup unique cap supply funding windows
  exact funded_phase_credit_allocation_bound210 certificate

end A166944Research
