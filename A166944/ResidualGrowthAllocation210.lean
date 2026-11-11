import A166944.ResidualReuseOverlap210

/-! # Bounding reuse charges on a common horizon interval -/

open Finset

namespace A166944Research

def growthWindowLoad210 {ι : Type*} (requests : Finset ι)
    (windows : ι → Finset Nat) (rate : ι → Nat) (x : Nat) : Nat :=
  ∑ i ∈ requests.filter (fun i => x ∈ windows i), rate i

/-- With nonnegative rates, the total load attains a maximum at a
left endpoint. At any point, move to the latest left endpoint among
its active windows. Those windows are all still active there. -/
theorem growth_window_load_of_left_endpoints210 {ι : Type*} [DecidableEq ι]
    (requests : Finset ι) (left right rate : ι → Nat) (scale : Nat)
    (hcheck : ∀ i ∈ requests,
      growthWindowLoad210 requests (fun j => Finset.Ico (left j) (right j)) rate (left i) ≤ scale)
    (x : Nat) : growthWindowLoad210 requests (fun j => Finset.Ico (left j) (right j)) rate x ≤ scale := by
  let active := requests.filter (fun j => x ∈ Finset.Ico (left j) (right j))
  change (∑ j ∈ active, rate j) ≤ scale
  by_cases he : active.Nonempty
  · have hne : (active.image left).Nonempty := he.image _
    obtain ⟨i, hi, hmax⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    have hxi := (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).2).1
    have hsub : active ⊆ requests.filter (fun j => left i ∈ Finset.Ico (left j) (right j)) := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hright := (Finset.mem_Ico.mp hj'.2).2
      have hleft := Finset.le_max' _ _ (Finset.mem_image_of_mem left hj)
      rw [← hmax] at hleft
      exact Finset.mem_filter.mpr ⟨hj'.1, Finset.mem_Ico.mpr ⟨hleft, hxi.trans_lt hright⟩⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)).trans
      (hcheck i (Finset.mem_filter.mp hi).1)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
    exact Nat.zero_le _

/-- Count each growth unit once, with a scaled load from all windows
covering it. A rate may overestimate an interval's required density. -/
theorem growth_window_capacity210 {ι : Type*} [DecidableEq ι]
    (requests : Finset ι) (growth : Finset Nat) (windows : ι → Finset Nat)
    (rate demand : ι → Nat) {scale : Nat} (positiveScale : 0 < scale)
    (inside : ∀ i ∈ requests, windows i ⊆ growth)
    (paid : ∀ i ∈ requests, scale * demand i ≤ rate i * (windows i).card)
    (load : ∀ x ∈ growth, growthWindowLoad210 requests windows rate x ≤ scale) :
    (∑ i ∈ requests, demand i) ≤ growth.card := by
  have hrow (i : ι) (hi : i ∈ requests) : rate i * (windows i).card =
      ∑ x ∈ growth, if x ∈ windows i then rate i else 0 := by
    have hfilter : growth.filter (fun x => x ∈ windows i) = windows i := by
      ext x
      exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨inside i hi h, h⟩⟩
    rw [← Finset.sum_filter, hfilter]
    simp [Nat.mul_comm]
  have hscaled : scale * (∑ i ∈ requests, demand i) ≤ scale * growth.card := by
    calc
      _ = ∑ i ∈ requests, scale * demand i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ requests, rate i * (windows i).card := Finset.sum_le_sum paid
      _ = ∑ i ∈ requests, ∑ x ∈ growth, if x ∈ windows i then rate i else 0 :=
        Finset.sum_congr rfl hrow
      _ = ∑ x ∈ growth, growthWindowLoad210 requests windows rate x := by
        rw [Finset.sum_comm]
        simp only [growthWindowLoad210, Finset.sum_filter]
      _ ≤ ∑ _x ∈ growth, scale := Finset.sum_le_sum load
      _ = _ := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hscaled positiveScale

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- The selected events draw on the common growth interval. The
remaining sum is signed, so it retains the negative contributions. -/
theorem net_cost_bound_of_window_load {C Cf scale : Nat} {remainder : Int}
    (selected : Finset (Fin n)) (windows : Fin n → Finset Nat) (rate : Fin n → Nat)
    (positiveScale : 0 < scale) (inside : ∀ i ∈ selected, windows i ⊆ Finset.Ico C Cf)
    (paid : ∀ i ∈ selected,
      scale * (2 * (trace.event i).netCost.toNat) ≤ rate i * (windows i).card)
    (load : ∀ x ∈ Finset.Ico C Cf, growthWindowLoad210 selected windows rate x ≤ scale)
    (rest : 2 * (∑ i ∈ Finset.univ \ selected, (trace.event i).netCost) ≤ remainder) :
    2 * (((24 * first : Nat) : Int) + balance) ≤ ((Cf - C : Nat) : Int) + remainder := by
  have hcapacity := growth_window_capacity210 selected (Finset.Ico C Cf) windows rate
    (fun i => 2 * (trace.event i).netCost.toNat) positiveScale inside paid load
  rw [Nat.card_Ico, ← Finset.mul_sum] at hcapacity
  have hpos : (∑ i ∈ selected, (trace.event i).netCost) ≤
      ((∑ i ∈ selected, (trace.event i).netCost.toNat : Nat) : Int) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => by omega)
  have hsplit := Finset.sum_sdiff (f := fun i => (trace.event i).netCost)
    (Finset.subset_univ selected)
  rw [trace.sum_net_cost] at hsplit
  omega

def eventsInGrowthBlock (left right : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun i => left < (trace.event i).horizon ∧ (trace.event i).horizon ≤ right)

theorem growth_block_events_disjoint {a b c e : Nat}
    (h : Disjoint (Finset.Ico a b) (Finset.Ico c e)) :
    Disjoint (trace.eventsInGrowthBlock a b) (trace.eventsInGrowthBlock c e) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hl := (Finset.mem_filter.mp hi).2
  have hr := (Finset.mem_filter.mp hj).2
  have hx : (trace.event i).horizon - 1 ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hy : (trace.event i).horizon - 1 ∈ Finset.Ico c e :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  exact (Finset.disjoint_left.mp h) hx hy

/-- Use [left,right) for growth and a subset of (left,right] for costs.
Both are disjoint across the same blocks, including when endpoints
touch. The selected costs retain their negative terms. -/
theorem net_cost_bound_of_disjoint_growth_blocks {ι : Type*} [DecidableEq ι]
    {C Cf charge capacity : Nat} {remainder : Int}
    (blocks : Finset ι) (left right : ι → Nat) (events : ι → Finset (Fin n))
    (disjoint : (blocks : Set ι).PairwiseDisjoint (fun b => Finset.Ico (left b) (right b)))
    (inside : ∀ b ∈ blocks, Finset.Ico (left b) (right b) ⊆ Finset.Ico C Cf)
    (eventInside : ∀ b ∈ blocks, events b ⊆ trace.eventsInGrowthBlock (left b) (right b))
    (paid : ∀ b ∈ blocks, (charge : Int) *
      (∑ i ∈ events b, (trace.event i).netCost) ≤
      (capacity : Int) * ((right b - left b : Nat) : Int))
    (rest : (charge : Int) *
      (∑ i ∈ Finset.univ \ blocks.biUnion events, (trace.event i).netCost) ≤ remainder) :
    (charge : Int) * (((24 * first : Nat) : Int) + balance) ≤
      (capacity : Int) * ((Cf - C : Nat) : Int) + remainder := by
  let growth := fun b => Finset.Ico (left b) (right b)
  have hevents : (blocks : Set ι).PairwiseDisjoint events := by
    intro b hb b' hb' hne
    exact (trace.growth_block_events_disjoint (disjoint hb hb' hne)).mono
      (eventInside b hb) (eventInside b' hb')
  have hinside : blocks.biUnion growth ⊆ Finset.Ico C Cf := by
    intro x hx
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
    exact inside b hb hx
  have hcard := Finset.card_le_card hinside
  rw [Finset.card_biUnion disjoint, Nat.card_Ico] at hcard
  have hbound : (charge : Int) * (∑ i ∈ blocks.biUnion events, (trace.event i).netCost) ≤
      (capacity : Int) * ((Cf - C : Nat) : Int) := by
    rw [Finset.sum_biUnion hevents, Finset.mul_sum]
    calc
      _ ≤ ∑ b ∈ blocks, (capacity : Int) * ((right b - left b : Nat) : Int) :=
        Finset.sum_le_sum paid
      _ = (capacity : Int) * ((∑ b ∈ blocks, (growth b).card : Nat) : Int) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        simp only [growth, Nat.card_Ico]
      _ ≤ _ := Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by omega)
  have hsplit := Finset.sum_sdiff (f := fun i => (trace.event i).netCost)
    (Finset.subset_univ (blocks.biUnion events))
  rw [trace.sum_net_cost] at hsplit
  rw [← hsplit, mul_add]
  omega

end ResidualPhaseTrace210

end A166944Research
