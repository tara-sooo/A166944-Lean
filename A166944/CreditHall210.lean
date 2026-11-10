import A166944.FundedPhaseCredits210
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Hall's condition for phase-credit allocation

Expand integer demands and capacities into individual units, apply the
finite Hall theorem, and count the assigned units in each row and column.
The resulting criterion includes competing requests for the same source.
-/

open Finset

namespace A166944Research

noncomputable def eligibleCreditSources210 {n m : Nat} (eligible : Fin n → Fin m → Prop)
    (requests : Finset (Fin n)) : Finset (Fin m) := by
  classical
  exact requests.biUnion (fun i => Finset.univ.filter (eligible i))

def CreditHallCondition210 {n m : Nat} (demand : Fin n → Nat) (supply : Fin m → Nat)
    (eligible : Fin n → Fin m → Prop) : Prop :=
  ∀ requests : Finset (Fin n), (∑ i ∈ requests, demand i) ≤
    ∑ j ∈ eligibleCreditSources210 eligible requests, supply j

theorem credit_allocation_of_hall210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {eligible : Fin n → Fin m → Prop} (hall : CreditHallCondition210 demand supply eligible) :
    ∃ allocation : Fin n → Fin m → Nat,
      (∀ i j, 0 < allocation i j → eligible i j) ∧
      (∀ i, (∑ j, allocation i j) = demand i) ∧
      (∀ j, (∑ i, allocation i j) ≤ supply j) := by
  classical
  let RequestUnit := (i : Fin n) × Fin (demand i)
  let SourceUnit := (j : Fin m) × Fin (supply j)
  let choices (unit : RequestUnit) : Finset SourceUnit := Finset.univ.filter (fun source => eligible unit.1 source.1)
  have hunit (units : Finset RequestUnit) : units.card ≤ (units.biUnion choices).card := by
    let requests := units.image Sigma.fst
    let sources := eligibleCreditSources210 eligible requests
    have hsub : units ⊆ requests.sigma (fun i => (Finset.univ : Finset (Fin (demand i)))) := by
      intro unit hunit
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem Sigma.fst hunit, Finset.mem_univ _⟩
    have hleft : units.card ≤ ∑ i ∈ requests, demand i := by
      have h := Finset.card_le_card hsub
      rw [Finset.card_sigma] at h
      simpa only [Finset.card_univ, Fintype.card_fin] using h
    have heq : units.biUnion choices = sources.sigma (fun j => (Finset.univ : Finset (Fin (supply j)))) := by
      ext source
      constructor
      · intro hsource
        obtain ⟨unit, hunit, hchoice⟩ := Finset.mem_biUnion.mp hsource
        have he := (Finset.mem_filter.mp hchoice).2
        exact Finset.mem_sigma.mpr ⟨Finset.mem_biUnion.mpr
          ⟨unit.1, Finset.mem_image_of_mem Sigma.fst hunit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩,
          Finset.mem_univ _⟩
      · intro hsource
        obtain ⟨j, hj, hchoice⟩ := Finset.mem_biUnion.mp (Finset.mem_sigma.mp hsource).1
        obtain ⟨unit, hunit, heq⟩ := Finset.mem_image.mp hj
        apply Finset.mem_biUnion.mpr
        refine ⟨unit, hunit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa only [heq] using (Finset.mem_filter.mp hchoice).2
    rw [heq, Finset.card_sigma]
    simpa only [Finset.card_univ, Fintype.card_fin] using hleft.trans (hall requests)
  obtain ⟨matching, hinj, hmatch⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hunit
  let allocation (i : Fin n) (j : Fin m) :=
    ((Finset.univ : Finset (Fin (demand i))).filter (fun k => (matching ⟨i, k⟩).1 = j)).card
  refine ⟨allocation, ?_, ?_, ?_⟩
  · intro i j hpos
    obtain ⟨unit, hunit⟩ := Finset.card_pos.mp hpos
    have he := (Finset.mem_filter.mp (hmatch ⟨i, unit⟩)).2
    rwa [(Finset.mem_filter.mp hunit).2] at he
  · intro i
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (demand i))) (Finset.univ : Finset (Fin m))
      (fun k => (matching ⟨i, k⟩).1)
    simpa only [allocation, Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin] using h
  · intro j
    let column := (Finset.univ : Finset RequestUnit).filter (fun unit => (matching unit).1 = j)
    have hcolumn : column = Finset.univ.sigma (fun i =>
        (Finset.univ : Finset (Fin (demand i))).filter (fun k => (matching ⟨i, k⟩).1 = j)) := by
      ext unit
      rcases unit with ⟨i, k⟩
      constructor
      · intro h
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩⟩
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_sigma.mp h).2).2⟩
    have hsum : (∑ i, allocation i j) = column.card := by
      rw [hcolumn, Finset.card_sigma]
    have hsub : column.image matching ⊆ ({j} : Finset (Fin m)).sigma
        (fun j => (Finset.univ : Finset (Fin (supply j)))) := by
      intro source hsource
      obtain ⟨unit, hunit, rfl⟩ := Finset.mem_image.mp hsource
      exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr (Finset.mem_filter.mp hunit).2, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_sigma] at hcard
    simpa only [hsum, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin] using hcard

theorem credit_hall_of_allocation210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {eligible : Fin n → Fin m → Prop} {allocation : Fin n → Fin m → Nat}
    (allowed : ∀ i j, 0 < allocation i j → eligible i j)
    (paid : ∀ i, demand i ≤ ∑ j, allocation i j)
    (capacity : ∀ j, (∑ i, allocation i j) ≤ supply j) :
    CreditHallCondition210 demand supply eligible := by
  classical
  intro requests
  have hzero (i : Fin n) (hi : i ∈ requests) (j : Fin m)
      (hj : j ∉ eligibleCreditSources210 eligible requests) : allocation i j = 0 := by
    by_cases h : 0 < allocation i j
    · exact False.elim (hj (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, allowed i j h⟩⟩))
    · omega
  calc
    (∑ i ∈ requests, demand i) ≤ ∑ i ∈ requests, ∑ j, allocation i j := Finset.sum_le_sum (fun i _ => paid i)
    _ = ∑ j, ∑ i ∈ requests, allocation i j := Finset.sum_comm
    _ = ∑ j ∈ eligibleCreditSources210 eligible requests, ∑ i ∈ requests, allocation i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact Finset.sum_eq_zero (fun i hi => hzero i hi j hj)
    _ ≤ ∑ j ∈ eligibleCreditSources210 eligible requests, supply j := by
      apply Finset.sum_le_sum
      intro j _
      exact (Finset.sum_le_sum_of_subset (Finset.subset_univ requests)).trans (capacity j)

theorem credit_hall_iff_allocation210 {n m : Nat} {demand : Fin n → Nat} {supply : Fin m → Nat}
    {eligible : Fin n → Fin m → Prop} :
    CreditHallCondition210 demand supply eligible ↔
      ∃ allocation : Fin n → Fin m → Nat,
        (∀ i j, 0 < allocation i j → eligible i j) ∧
        (∀ i, (∑ j, allocation i j) = demand i) ∧
        (∀ j, (∑ i, allocation i j) ≤ supply j) := by
  constructor
  · exact credit_allocation_of_hall210
  · rintro ⟨allocation, allowed, paid, capacity⟩
    exact credit_hall_of_allocation210 allowed (fun i => (paid i).ge) capacity

theorem funded_phase_credit_allocation_of_hall210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop}
    (startup : Finset (Fin n)) (unique : Set.InjOn key (startup : Set (Fin n)))
    (cap : ∀ i ∈ startup, (cost i).toNat ≤ 29613) (supply : Fin m → Nat)
    (funding : (∑ j, supply j) ≤ (∑ i, (-cost i).toNat) + multiplier * first)
    (hall : CreditHallCondition210 (fun i => if i ∈ startup then 0 else (cost i).toNat) supply eligible) :
    Nonempty (FundedPhaseCreditAllocation210 cost key eligible first multiplier) := by
  classical
  obtain ⟨allocation, allowed, paid, capacity⟩ := credit_allocation_of_hall210 hall
  exact ⟨⟨startup, unique, cap, supply, allocation, allowed,
    fun i hi => by simpa only [if_neg hi] using (paid i).ge, capacity, funding⟩⟩

end A166944Research
