import A166944.ResidualSmallAdjusted210
import A166944.ResidualSmallReusePairs210

/-! # Interval credits with two units per horizon coordinate -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def growthRequestRight (i : Fin n) : Nat := (trace.event i).horizon - 1

/-- A request of zero demand can use a singleton at its right endpoint. -/
def growthRequestLeft (anchor : Fin n → Fin n) (i : Fin n) : Nat :=
  min (trace.event (anchor i)).horizon (trace.growthRequestRight i)

theorem growth_request_left_of_order {anchor : Fin n → Fin n} {i : Fin n} (order : anchor i < i) :
    trace.growthRequestLeft anchor i = (trace.event (anchor i)).horizon := by
  have h := trace.horizon_strict_mono order
  change (trace.event (anchor i)).horizon < (trace.event i).horizon at h
  unfold growthRequestLeft growthRequestRight
  exact min_eq_left (by omega)

def growthRequests (anchor : Fin n → Fin n) (a b : Nat) : Finset (Fin n) :=
  creditWindowRequests210 (trace.growthRequestLeft anchor) trace.growthRequestRight a (b - 1)

def growthWindowCredit (cost : Fin n → Int) (a b : Nat) : Nat :=
  2 * (b - a) + 3 * (∑ i ∈ trace.eventsInGrowthBlock a b, (-cost i).toNat)

def GrowthDeficit (anchor : Fin n → Fin n) (demand : Fin n → Nat) (cost : Fin n → Int) (a b : Nat) : Prop :=
  trace.growthWindowCredit cost a b < 3 * (∑ i ∈ trace.growthRequests anchor a b, demand i)

def GrowthWindows (anchor : Fin n → Fin n) (demand : Fin n → Nat) (cost : Fin n → Int) : Prop :=
  ∀ a b, a < b → ¬ trace.GrowthDeficit anchor demand cost a b

private def growthSourceTime (B : Nat) (j : Fin (B + n)) : Nat :=
  Fin.addCases (fun k : Fin B => k.val) trace.growthRequestRight j

private def growthSourceSupply (B : Nat) (cost : Fin n → Int) (j : Fin (B + n)) : Nat :=
  Fin.addCases (fun _ : Fin B => 2) (fun i => 3 * (-cost i).toNat) j

private theorem growth_window_capacity {B a c : Nat} (hB : c < B) (cost : Fin n → Int) :
    (∑ j ∈ creditWindowSources210 (trace.growthSourceTime B) a c, growthSourceSupply B cost j) =
      trace.growthWindowCredit cost a (c + 1) := by
  rw [creditWindowSources210, Finset.sum_filter, Fin.sum_univ_add]
  simp only [growthSourceTime, growthSourceSupply, Fin.addCases_left, Fin.addCases_right]
  have hfirst : (∑ j : Fin B, if a ≤ j.val ∧ j.val ≤ c then 2 else 0) = 2 * (c + 1 - a) := by
    rw [Fin.sum_univ_eq_sum_range (fun x => if a ≤ x ∧ x ≤ c then 2 else 0), ← Finset.sum_filter]
    have hfilter : ((Finset.range B).filter fun x => a ≤ x ∧ x ≤ c) = Finset.Ico a (c + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter, Finset.sum_const, Nat.card_Ico]
    simp [Nat.mul_comm]
  have hsecond : (∑ i : Fin n, if a ≤ trace.growthRequestRight i ∧ trace.growthRequestRight i ≤ c then
      3 * (-cost i).toNat else 0) = 3 * (∑ i ∈ trace.eventsInGrowthBlock a (c + 1), (-cost i).toNat) := by
    have hfilter : (Finset.univ.filter fun i => a ≤ trace.growthRequestRight i ∧ trace.growthRequestRight i ≤ c) =
        trace.eventsInGrowthBlock a (c + 1) := by
      apply Finset.ext
      intro i
      have hp := (trace.event i).step.1.1
      have hC := (trace.event i).step.1.2.2
      constructor
      · intro hi
        have h := (Finset.mem_filter.mp hi).2
        change a ≤ (trace.event i).horizon - 1 ∧ (trace.event i).horizon - 1 ≤ c at h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      · intro hi
        have h := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          change a ≤ (trace.event i).horizon - 1 ∧ (trace.event i).horizon - 1 ≤ c
          omega⟩
    rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
  rw [hfirst, hsecond]
  rfl

private theorem growth_deficit_iff_closed {B a c : Nat} (hB : c < B)
    (anchor : Fin n → Fin n) (demand : Fin n → Nat) (cost : Fin n → Int) :
    CreditWindowDeficit210 (fun i => 3 * demand i) (growthSourceSupply B cost)
      (trace.growthSourceTime B) (trace.growthRequestLeft anchor) trace.growthRequestRight a c ↔
      trace.GrowthDeficit anchor demand cost a (c + 1) := by
  unfold CreditWindowDeficit210 GrowthDeficit growthRequests
  rw [trace.growth_window_capacity hB, Finset.mul_sum]
  simp

structure MinimalGrowthDeficit (anchor : Fin n → Fin n) (demand : Fin n → Nat) (cost : Fin n → Int)
    (a b : Nat) : Prop where
  nonempty : a < b
  deficit : trace.GrowthDeficit anchor demand cost a b
  minimal : ∀ a' b', a ≤ a' → a' < b' → b' ≤ b → (a < a' ∨ b' < b) →
    ¬ trace.GrowthDeficit anchor demand cost a' b'
  left_boundary : ∃ i ∈ trace.growthRequests anchor a b, 0 < demand i ∧ trace.growthRequestLeft anchor i = a
  right_boundary : ∃ i ∈ trace.growthRequests anchor a b, 0 < demand i ∧ trace.growthRequestRight i + 1 = b
  crosses : ∀ t, a < t → t < b → ∃ i ∈ trace.growthRequests anchor a b,
    0 < demand i ∧ trace.growthRequestLeft anchor i < t ∧ t ≤ trace.growthRequestRight i

/-- The interval Hall machinery applies to growth plus negative cost.
Use the closed integer window `[a,b-1]` for the half-open growth window. -/
theorem minimal_growth_deficit_of_failure (anchor : Fin n → Fin n) (demand : Fin n → Nat)
    (cost : Fin n → Int) (failure : ¬ trace.GrowthWindows anchor demand cost) :
    ∃ a b, trace.MinimalGrowthDeficit anchor demand cost a b := by
  have hex : ∃ lo hi, lo < hi ∧ trace.GrowthDeficit anchor demand cost lo hi := by
    by_contra h
    exact failure (fun a b hab hd => h ⟨a, b, hab, hd⟩)
  obtain ⟨lo, hi, hlt, hbad⟩ := hex
  let B := max hi (D sf + 1)
  have hright (i : Fin n) : trace.growthRequestRight i < B := by
    have hD := D_le_of_le (trace.hit_le i)
    have hup := (trace.event i).step.2.2.2.2.2.2.1
    have hg := (trace.event i).step.2.2.2.2.2.2.2.1
    have hB : D sf + 1 ≤ B := le_max_right _ _
    unfold growthRequestRight
    omega
  let demand3 (i : Fin n) := 3 * demand i
  let supply := growthSourceSupply B cost
  let time := trace.growthSourceTime B
  let left := trace.growthRequestLeft anchor
  let right := trace.growthRequestRight
  have valid (i : Fin n) : left i ≤ right i := min_le_right _ _
  have htranslate {a b : Nat} (hb : b < B) :
      CreditWindowDeficit210 demand3 supply time left right a b ↔
        trace.GrowthDeficit anchor demand cost a (b + 1) :=
    trace.growth_deficit_iff_closed hb anchor demand cost
  have hfail : ¬ CreditHallCondition210 demand3 supply (fun i j => left i ≤ time j ∧ time j ≤ right i) := by
    intro hall
    have hgood := credit_windows_of_hall210 hall lo (hi - 1) (by omega)
    have hhi : hi ≤ B := le_max_left _ _
    have hclose := (htranslate (a := lo) (b := hi - 1) (by omega)).mpr (by
      rwa [show hi - 1 + 1 = hi by omega])
    exact Nat.not_le_of_gt hclose hgood
  obtain ⟨a, c, hac, hdef, hmin⟩ := credit_minimal_deficit_window210 valid hfail
  obtain ⟨⟨i, hi', hip, hleft⟩, ⟨k, hk, hkp, hright'⟩⟩ :=
    minimal_credit_deficit_has_boundary_requests210 valid hac hdef hmin
  have hC : c < B := hright' ▸ hright k
  refine ⟨a, c + 1, ⟨by omega, (htranslate hC).mp hdef, ?_, ?_, ?_, ?_⟩⟩
  · intro a' b' ha' hab' hb' proper hd
    have hclose := (htranslate (a := a') (b := b' - 1) (by omega)).mpr (by
      rwa [show b' - 1 + 1 = b' by omega])
    exact hmin a' (b' - 1) ha' (by omega) (by omega) (by omega) hclose
  · exact ⟨i, by simpa [growthRequests] using hi', by dsimp [demand3] at hip; omega, hleft⟩
  · exact ⟨k, by simpa [growthRequests] using hk, by dsimp [demand3] at hkp; omega,
      congrArg (· + 1) hright'⟩
  · intro t hat htc
    obtain ⟨j, hj, hjp, hjl, hjr⟩ := minimal_credit_deficit_crosses_every_cut210
      valid hdef hmin (t - 1) (by omega) (by omega)
    exact ⟨j, by simpa [growthRequests] using hj, by dsimp [demand3] at hjp; omega,
      by change left j < t; omega, by change t ≤ right j; omega⟩

/-- The two proper windows pay their own requests. Only requests that
cross the cut can account for a deficit in the combined window. -/
theorem minimal_growth_deficit_cut_bound {anchor : Fin n → Fin n} {demand : Fin n → Nat}
    {cost : Fin n → Int} {a t b : Nat} (minimal : trace.MinimalGrowthDeficit anchor demand cost a b)
    (hat : a < t) (htb : t < b) :
    3 * (∑ i ∈ trace.growthRequests anchor a b, demand i) ≤ trace.growthWindowCredit cost a b +
      3 * (∑ i ∈ (trace.growthRequests anchor a b).filter
        (fun i => trace.growthRequestLeft anchor i < t ∧ t ≤ trace.growthRequestRight i), demand i) := by
  have h₁ := Nat.le_of_not_gt (minimal.minimal a t le_rfl hat (by omega) (Or.inr htb))
  have h₂ := Nat.le_of_not_gt (minimal.minimal t b (by omega) htb le_rfl (Or.inl hat))
  have hreq : (∑ i ∈ trace.growthRequests anchor a b, demand i) =
      (∑ i ∈ trace.growthRequests anchor a t, demand i) +
      (∑ i ∈ trace.growthRequests anchor t b, demand i) +
      (∑ i ∈ (trace.growthRequests anchor a b).filter
        (fun i => trace.growthRequestLeft anchor i < t ∧ t ≤ trace.growthRequestRight i), demand i) := by
    simp only [growthRequests, creditWindowRequests210, Finset.filter_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hvalid : trace.growthRequestLeft anchor i ≤ trace.growthRequestRight i := min_le_right _ _
    split <;> split <;> split <;> split <;> omega
  have hdisj : Disjoint (trace.eventsInGrowthBlock a t) (trace.eventsInGrowthBlock t b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hleft := (Finset.mem_filter.mp hi).2
    have hright := (Finset.mem_filter.mp hj).2
    omega
  have hsplit : trace.eventsInGrowthBlock a t ∪ trace.eventsInGrowthBlock t b = trace.eventsInGrowthBlock a b := by
    ext i
    simp only [eventsInGrowthBlock, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsum := Finset.sum_union (f := fun i => (-cost i).toNat) hdisj
  rw [hsplit] at hsum
  have hcredit : trace.growthWindowCredit cost a b =
      trace.growthWindowCredit cost a t + trace.growthWindowCredit cost t b := by
    unfold growthWindowCredit
    omega
  rw [hreq, hcredit]
  omega

theorem growth_window_inside_of_request {anchor : Fin n → Fin n} {i : Fin n} {a b : Nat}
    (ordered : anchor i < i) (hi : i ∈ trace.growthRequests anchor a b) :
    trace.growthWindow (anchor i) i ⊆ Finset.Ico a b := by
  have ⟨hl, hr⟩ := (Finset.mem_filter.mp hi).2
  rw [trace.growth_request_left_of_order ordered] at hl
  change (trace.event i).horizon - 1 ≤ b - 1 at hr
  have hs := (trace.event i).step.1.1
  have hh := (trace.event i).step.1.2.2
  intro x hx
  have ⟨hx₁, hx₂⟩ := Finset.mem_Ico.mp hx
  exact Finset.mem_Ico.mpr ⟨hl.trans hx₁, by omega⟩

theorem sum_positive_requests (requests : Finset (Fin n)) (demand : Fin n → Nat) :
    (∑ i ∈ requests, demand i) = ∑ i ∈ requests.filter (fun i => 0 < demand i), demand i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split <;> omega

def longReuseDemand (i : Fin n) : Nat :=
  if trace.ReusedLong i ∧ ¬ d (trace.event i).hit ∣ 210 then (trace.event i).scaledNetCost.toNat else 0

private theorem long_reuse_demand_spec {i : Fin n} (positive : 0 < trace.longReuseDemand i) :
    trace.PrimeReuse (trace.anchor i) i ∧ trace.longReuseDemand i = (trace.event i).scaledNetCost.toNat := by
  by_cases h : trace.ReusedLong i ∧ ¬ d (trace.event i).hit ∣ 210
  · simp only [longReuseDemand, if_pos h]
    have ⟨horder, hkey⟩ := trace.anchor_of_seen_long h.1.1 h.1.2
    exact ⟨⟨horder, hkey, h.1.1.2, h.2⟩, trivial⟩
  · simp [longReuseDemand, h] at positive

private theorem growth_window_credit_eq_scaled (a b : Nat) :
    trace.growthWindowCredit (fun i => (trace.event i).scaledNetCost) a b =
      2 * (b - a) + 3 * trace.scaledGrowthCredit (Finset.Ico a b) := by
  have hfilter : trace.eventsInGrowthBlock a b =
      Finset.univ.filter (fun i => (trace.event i).horizon - 1 ∈ Finset.Ico a b) := by
    ext i
    have h₁ := (trace.event i).step.1.1
    have h₂ := (trace.event i).step.1.2.2
    simp only [eventsInGrowthBlock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    omega
  simp only [growthWindowCredit, scaledGrowthCredit, hfilter]

/-- A deficit with just two positive long-prime requests has one of
the small first-hit prime pairs, including after adding enclosed credit. -/
theorem classify_two_long_growth_requests210 {a b : Nat}
    (deficit : trace.GrowthDeficit trace.anchor trace.longReuseDemand
      (fun i => (trace.event i).scaledNetCost) a b)
    (count : ((trace.growthRequests trace.anchor a b).filter (fun i => 0 < trace.longReuseDemand i)).card = 2) :
    ∃ i j : Fin n, i ≠ j ∧ (d (trace.event i).hit, d (trace.event j).hit) ∈ firstHitReuseDeficitPairs210 ∧
      b - a ≤ 5276 := by
  let requests := trace.growthRequests trace.anchor a b
  obtain ⟨i, j, hne, hpair⟩ := Finset.card_eq_two.mp count
  change requests.filter (fun i => 0 < trace.longReuseDemand i) = {i, j} at hpair
  have hmᵢ : i ∈ requests.filter (fun i => 0 < trace.longReuseDemand i) := by rw [hpair]; simp
  have hmⱼ : j ∈ requests.filter (fun i => 0 < trace.longReuseDemand i) := by rw [hpair]; simp
  have ⟨hi, hposᵢ⟩ := Finset.mem_filter.mp hmᵢ
  have ⟨hj, hposⱼ⟩ := Finset.mem_filter.mp hmⱼ
  have ⟨pi, hcᵢ⟩ := trace.long_reuse_demand_spec hposᵢ
  have ⟨pj, hcⱼ⟩ := trace.long_reuse_demand_spec hposⱼ
  have hi' := trace.growth_window_inside_of_request pi.ordered hi
  have hj' := trace.growth_window_inside_of_request pj.ordered hj
  have hsum : (∑ k ∈ requests, trace.longReuseDemand k) = trace.longReuseDemand i + trace.longReuseDemand j := by
    rw [sum_positive_requests requests trace.longReuseDemand, hpair, Finset.sum_pair hne]
  have hbad : trace.growthWindowCredit (fun k => (trace.event k).scaledNetCost) a b <
      3 * (∑ k ∈ requests, trace.longReuseDemand k) := deficit
  rw [trace.growth_window_credit_eq_scaled, hsum, hcᵢ, hcⱼ] at hbad
  rcases le_total (d (trace.event i).hit) (d (trace.event j).hit) with h | h
  · obtain ⟨hm, hb⟩ := trace.first_hit_two_reuse_deficit210 pi pj h (Finset.union_subset hi' hj') hbad
    exact ⟨i, j, hne, hm, hb⟩
  · rw [Nat.add_comm (trace.event i).scaledNetCost.toNat] at hbad
    obtain ⟨hm, hb⟩ := trace.first_hit_two_reuse_deficit210 pj pi h (Finset.union_subset hj' hi') hbad
    exact ⟨j, i, hne.symm, hm, hb⟩

theorem event_horizon_between (i : Fin n) :
    D s ≤ (trace.event i).horizon ∧ (trace.event i).horizon < D sf := by
  have hs := D_le_of_le (trace.start_ge i)
  have hf := D_le_of_le (trace.hit_le i)
  have h₁ := (trace.event i).step.1.2.1
  have h₂ := (trace.event i).step.2.2.2.2.2.2.1
  have h₃ := (trace.event i).step.2.2.2.2.2.2.2.1
  omega

abbrev AdjustedGrowthWindows : Prop :=
  trace.GrowthWindows trace.adjustedAnchor trace.adjustedDemand (fun i => (trace.event i).adjustedCost)

/-- For a single positive request in a minimal adjusted deficit, the
endpoints are its own. This also bounds the possible enclosed credit. -/
theorem singleton_adjusted_growth_deficit210 {a b : Nat}
    (minimal : trace.MinimalGrowthDeficit trace.adjustedAnchor trace.adjustedDemand
      (fun i => (trace.event i).adjustedCost) a b)
    (count : ((trace.growthRequests trace.adjustedAnchor a b).filter (fun i => 0 < trace.adjustedDemand i)).card = 1) :
    ∃ i : Fin n, i ∈ trace.growthRequests trace.adjustedAnchor a b ∧ 0 < trace.adjustedDemand i ∧
      ((d (trace.event i).hit = 9 ∧ (b - a = 630 ∨ b - a = 1260) ∧
          trace.growthWindowCredit (fun i => (trace.event i).adjustedCost) a b < 2937) ∨
        (d (trace.event i).hit = 25 ∧ b - a = 1050 ∧
          trace.growthWindowCredit (fun i => (trace.event i).adjustedCost) a b < 2217)) := by
  let requests := trace.growthRequests trace.adjustedAnchor a b
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp count
  change requests.filter (fun i => 0 < trace.adjustedDemand i) = {i} at hi
  have hm : i ∈ requests.filter (fun i => 0 < trace.adjustedDemand i) := by rw [hi]; simp
  have ⟨hiReq, hiPos⟩ := Finset.mem_filter.mp hm
  obtain ⟨j, hj, hjPos, hjLeft⟩ := minimal.left_boundary
  obtain ⟨k, hk, hkPos, hkRight⟩ := minimal.right_boundary
  have hsame (l : Fin n) (hl : l ∈ requests) (hlPos : 0 < trace.adjustedDemand l) : l = i := by
    have hl' : l ∈ requests.filter (fun j => 0 < trace.adjustedDemand j) :=
      Finset.mem_filter.mpr ⟨hl, hlPos⟩
    rw [hi, Finset.mem_singleton] at hl'
    exact hl'
  rw [hsame j hj hjPos] at hjLeft
  rw [hsame k hk hkPos] at hkRight
  rw [trace.growth_request_left_of_order (trace.adjusted_demand_anchor hiPos).1] at hjLeft
  have hH := (trace.event i).step.1.2.2
  unfold growthRequestRight at hkRight
  have hwidth : (trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon = b - a := by omega
  have hbad : trace.growthWindowCredit (fun i => (trace.event i).adjustedCost) a b <
      3 * (∑ i ∈ requests, trace.adjustedDemand i) := minimal.deficit
  rw [sum_positive_requests requests trace.adjustedDemand, hi, Finset.sum_singleton] at hbad
  have hshort : 2 * (b - a) < 3 * trace.adjustedDemand i := by
    unfold growthWindowCredit at hbad
    omega
  have hsmall := trace.adjusted_request_shortfall210 hiPos (by rw [hwidth]; exact hshort)
  rw [hwidth] at hsmall
  refine ⟨i, hiReq, hiPos, ?_⟩
  rcases hsmall with ⟨h9, hw, hc⟩ | ⟨h25, hw, hc⟩
  · exact Or.inl ⟨h9, hw, by omega⟩
  · exact Or.inr ⟨h25, hw, by omega⟩

theorem cost_demand_le_growth_and_credit {cost : Fin n → Int}
    (windows : trace.GrowthWindows (trace.costAnchor cost) (trace.costDemand cost) cost) :
    3 * (∑ i, trace.costDemand cost i) ≤ 2 * (D sf - D s) +
      3 * (∑ i, (-cost i).toNat) := by
  by_cases hlt : D s < D sf
  · have h := Nat.le_of_not_gt (windows (D s) (D sf) hlt)
    have hsum : (∑ i ∈ trace.growthRequests (trace.costAnchor cost) (D s) (D sf), trace.costDemand cost i) =
        ∑ i, trace.costDemand cost i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_contra hn
      have hp : 0 < trace.costDemand cost i := Nat.pos_of_ne_zero hn
      have ⟨horder, _⟩ := trace.cost_demand_anchor hp
      apply hi
      apply Finset.mem_filter.mpr
      have ha := (trace.event_horizon_between (trace.costAnchor cost i)).1
      have hb := (trace.event_horizon_between i).2
      exact ⟨Finset.mem_univ _, by rwa [trace.growth_request_left_of_order horder],
        by unfold growthRequestRight; omega⟩
    have hpaid : 3 * (∑ i ∈ trace.growthRequests (trace.costAnchor cost) (D s) (D sf), trace.costDemand cost i) ≤
        2 * (D sf - D s) + 3 * (∑ i ∈ trace.eventsInGrowthBlock (D s) (D sf),
          (-cost i).toNat) := h
    rw [hsum] at hpaid
    have hcredit : (∑ i ∈ trace.eventsInGrowthBlock (D s) (D sf), (-cost i).toNat) ≤
        ∑ i, (-cost i).toNat :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  · have hz (i : Fin n) : trace.costDemand cost i = 0 := by
      have := trace.event_horizon_between i
      omega
    simp [hz]

theorem adjusted_demand_le_growth_and_credit (windows : trace.AdjustedGrowthWindows) :
    3 * (∑ i, trace.adjustedDemand i) ≤ 2 * (D sf - D s) +
      3 * (∑ i, (-(trace.event i).adjustedCost).toNat) :=
  trace.cost_demand_le_growth_and_credit windows

theorem sum_signed_cost_le_growth_of_windows {cost : Fin n → Int}
    (windows : trace.GrowthWindows (trace.costAnchor cost) (trace.costDemand cost) cost) :
    3 * (∑ i, cost i) ≤ ((3 * trace.costStartupSum cost + 2 * (D sf - D s) : Nat) : Int) := by
  have hpaid := trace.cost_demand_le_growth_and_credit windows
  have hsum : (∑ i, cost i) = ((∑ i, (cost i).toNat : Nat) : Int) -
      ((∑ i, (-cost i).toNat : Nat) : Int) := by
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  rw [hsum, trace.sum_cost_positive]
  omega

/-- When all nonstartup requests fit their growth windows, the only
separate positive allowances are first travel and the finite startup sum. -/
theorem scaled_net_cost_le_of_adjusted_windows (windows : trace.AdjustedGrowthWindows) :
    3 * (∑ i, (trace.event i).scaledNetCost) ≤
      ((72 * trace.scaledFirstTravel + 13954356 + 2 * (D sf - D s) : Nat) : Int) := by
  have hcost := trace.sum_signed_cost_le_growth_of_windows windows
  have hstart := trace.adjusted_startup_cost_le
  change 3 * (∑ i, (trace.event i).adjustedCost) ≤
    ((3 * trace.adjustedStartupCost + 2 * (D sf - D s) : Nat) : Int) at hcost
  rw [trace.sum_scaled_net_cost_split]
  omega

end

end A166944Research.ResidualPhaseTrace210

namespace A166944Research

/-- The actual first-crossing gap can be used with the separated first
travel. The window condition and the first-travel budget remain hypotheses. -/
theorem scaled_crossing_budget_of_adjusted_windows210 {M s C r p first : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (windows : trace.AdjustedGrowthWindows)
    (firstBudget : 72 * trace.scaledFirstTravel + 13954356 + 2 * (C - (2 * M - 2)) +
      72 * (r - s) + 3525 ≤ 3 * M) :
    (∑ i, (trace.event i).scaledNetCost) + (24 * (r - s) + 1175 : Nat) ≤ (M : Int) := by
  have hpath := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact hpath.2.2.2.1
    | succ _ => exact hpath.1.2.1
  have hend := (moving_horizon_path_endpoint hpath).2.1
  have hcost := trace.scaled_net_cost_le_of_adjusted_windows windows
  rw [hstart, hend] at hcost
  omega

/-- A uniform allowance uses the short-prefix horizon bound and the
square-root bound on the crossing gap. -/
theorem scaled_crossing_budget_of_adjusted_first_bound210 {M s C r p first : Nat} {balance : Int}
    (hM : 50000000 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (windows : trace.AdjustedGrowthWindows)
    (firstBudget : 64 * (72 * trace.scaledFirstTravel + 13957891) ≤ 61 * M) :
    (∑ i, (trace.event i).scaledNetCost) + (24 * (r - s) + 1175 : Nat) ≤ (M : Int) := by
  apply scaled_crossing_budget_of_adjusted_windows210 ledger trace windows
  have hpath := residual_phase_balances210_path ledger
  have hC := canonical_horizon_bound_of_short_travel hpath short
  have hstate := moving_horizon_path_endpoint hpath
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hModd : M % 2 = 1 := canonical ▸ d_mod_two_eq_one_of_three_le (by omega)
  have hQ := fifty_million_sqrt_budget hM
  omega

/-- The adjusted windows suffice at large enough records by the
sublinear first-phase theorem. The threshold here is existential. -/
theorem scaled_crossing_budget_of_adjusted_windows_eventually210 :
    ∃ threshold : Nat, ∀ {M s C r p first : Nat} {balance : Int},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
        (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M → r - s ≤ Nat.sqrt (4 * (3 * M + 4)) →
      ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance, trace.AdjustedGrowthWindows →
        (∑ i, (trace.event i).scaledNetCost) + (24 * (r - s) + 1175 : Nat) ≤ (M : Int) := by
  obtain ⟨B, hB⟩ := canonical_first_prime_phase_travel_sublinear 420 128 (by decide)
  refine ⟨max 50000000 B, ?_⟩
  intro M s C r p first balance hM hcanon hledger hshort hgap trace hwindows
  have h50 : 50000000 ≤ M := (le_max_left 50000000 B).trans hM
  have hlarge := (le_max_right 50000000 B).trans hM
  obtain ⟨_, hphase⟩ := residual_phase_balances210_original hledger
  have hfirst : 128 * first ≤ M := hB hlarge hcanon hphase hshort
  have hscaled := (Nat.mul_le_mul_left 128 trace.scaled_first_travel_le).trans hfirst
  have hconstant : 64 * 13957891 ≤ 25 * M :=
    (by decide : 64 * 13957891 ≤ 25 * 50000000).trans (Nat.mul_le_mul_left 25 h50)
  have hF : 64 * (72 * trace.scaledFirstTravel + 13957891) ≤ 61 * M := by
    rw [Nat.mul_add, ← Nat.mul_assoc, show 64 * 72 = 36 * 128 by decide, Nat.mul_assoc,
      show 61 = 36 + 25 by decide, Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left 36 hscaled) hconstant
  exact scaled_crossing_budget_of_adjusted_first_bound210 h50 hcanon hledger hshort hgap trace hwindows hF

end A166944Research
