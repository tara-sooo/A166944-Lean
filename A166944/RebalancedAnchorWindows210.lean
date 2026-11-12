import A166944.RebalancedCreditIntervals210

/-! # Placing rebalanced demands across their full anchor intervals -/

open Finset

namespace A166944Research

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def rebalancedAnchorCredit (i : Fin n) : Nat :=
  trace.rebalancedCreditAfter (trace.costAnchor trace.rebalancedCosts i)

def rebalancedAnchorInterval (i : Fin n) : Finset Nat :=
  Ico (trace.rebalancedAnchorCredit i) (trace.rebalancedCreditAfter i)

def rebalancedAnchorRequests (a b : Nat) : Finset (Fin n) :=
  univ.filter fun i => 0 < trace.rebalancedDemand i ∧
    a ≤ trace.rebalancedAnchorCredit i ∧ trace.rebalancedCreditAfter i ≤ b

def RebalancedAnchorDeficit (a b : Nat) : Prop :=
  b - a < 3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i)

def RebalancedAnchorWindows : Prop :=
  ∀ a b, a < b → b ≤ trace.rebalancedTotalCredit → ¬ trace.RebalancedAnchorDeficit a b

/-- The number of credit units reserved by one full phase period. -/
def rebalancedPhasePeriodWidth (i : Fin n) : Nat :=
  2 * Nat.lcm 210 (2 * d (trace.event i).hit)

private theorem rebalanced_phase_period_fits_anchor {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    trace.rebalancedPhasePeriodWidth i ≤ trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i := by
  obtain ⟨order, key⟩ := trace.cost_demand_anchor positive
  exact trace.same_key_rebalanced_credit_period order key

private theorem rebalanced_demand_le_phase_period {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    3 * trace.rebalancedDemand i ≤ trace.rebalancedPhasePeriodWidth i :=
  trace.rebalanced_request_pays_period210 positive

theorem rebalanced_phase_period_width_of_long {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (long : trace.ReusedLong i) :
    trace.rebalancedPhasePeriodWidth i = 420 * d (trace.event i).hit := by
  let e := d (trace.event i).hit
  have hcost := trace.cost_demand_eq_cost positive
  change trace.rebalancedDemand i = (trace.event i).rebalancedCost.toNat at hcost
  have hpos : 0 < (trace.event i).rebalancedCost := by omega
  have hu := (trace.event i).rebalanced_cost_positive_unsupported hpos
  have he : 1 < e := (trace.event i).step.2.2.2.1
  have hp := prime_of_no_proper_factor (by omega : 2 ≤ e) long.1.2
  have hcop := Nat.Coprime.coprime_dvd_left (by decide : 105 ∣ 210)
    ((hp.coprime_iff_not_dvd.mpr hu).symm)
  change 2 * Nat.lcm (2 * 105) (2 * e) = 420 * e
  rw [Nat.lcm_mul_left, hcop.lcm_eq_mul, ← Nat.mul_assoc, ← Nat.mul_assoc]

private theorem rebalanced_credit_after_positive (i : Fin n) : 0 < trace.rebalancedCreditAfter i := by
  have hC := (trace.event_horizon_between i).1
  have hu := moving_horizon_step_update (trace.event i).step
  have he := (trace.event i).step.2.2.2.1
  unfold rebalancedCreditAfter
  omega

private def closedAnchorRight (i : Fin n) : Nat := trace.rebalancedCreditAfter i - 1

private def closedAnchorLeft (i : Fin n) : Nat := min (trace.rebalancedAnchorCredit i) (trace.closedAnchorRight i)

private theorem closed_anchor_left_of_positive {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    trace.closedAnchorLeft i = trace.rebalancedAnchorCredit i := by
  have hfit := (trace.rebalanced_demand_le_phase_period positive).trans
    (trace.rebalanced_phase_period_fits_anchor positive)
  unfold closedAnchorLeft closedAnchorRight
  exact min_eq_left (by omega)

private theorem rebalanced_anchor_demand_sum {a b : Nat} (hb : 0 < b) :
    (∑ i ∈ creditWindowRequests210 trace.closedAnchorLeft trace.closedAnchorRight a (b - 1),
      (3 * trace.rebalancedDemand i)) =
      3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) := by
  let requests := creditWindowRequests210 trace.closedAnchorLeft trace.closedAnchorRight a (b - 1)
  have hfilter : requests.filter (fun i => 0 < 3 * trace.rebalancedDemand i) =
      trace.rebalancedAnchorRequests a b := by
    ext i
    simp only [requests, creditWindowRequests210, rebalancedAnchorRequests, mem_filter, mem_univ, true_and]
    by_cases h : 0 < trace.rebalancedDemand i
    · have hC := trace.rebalanced_credit_after_positive i
      rw [trace.closed_anchor_left_of_positive h]
      unfold closedAnchorRight
      omega
    · omega
  have hsum := sum_positive_requests requests (fun i => 3 * trace.rebalancedDemand i)
  rw [hfilter] at hsum
  rw [Finset.mul_sum]
  exact hsum

private theorem rebalanced_anchor_supply_sum {a b : Nat} (hab : a < b) (hB : b ≤ trace.rebalancedTotalCredit) :
    (∑ _j ∈ creditWindowSources210 (fun j : Fin trace.rebalancedTotalCredit => j.val) a (b - 1), (1 : Nat)) =
      b - a := by
  rw [creditWindowSources210, Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun x => if a ≤ x ∧ x ≤ b - 1 then (1 : Nat) else 0), ← Finset.sum_filter]
  have hfilter : (range trace.rebalancedTotalCredit).filter (fun x => a ≤ x ∧ x ≤ b - 1) = Ico a b := by
    ext x
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, Finset.sum_const, Nat.card_Ico]
  simp

def RebalancedAnchorAllocation : Prop :=
  ∃ allocation : Fin n → Fin trace.rebalancedTotalCredit → Nat,
    (∀ i j, 0 < allocation i j →
      trace.rebalancedAnchorCredit i ≤ j.val ∧ j.val < trace.rebalancedCreditAfter i) ∧
    (∀ i, (∑ j, allocation i j) = 3 * trace.rebalancedDemand i) ∧
    (∀ j, (∑ i, allocation i j) ≤ 1)

/-- Testing all anchored windows is equivalent to allowing arbitrary
placement of demand units between their actual anchors and endpoints. -/
theorem rebalanced_anchor_windows_iff_allocation210 :
    trace.RebalancedAnchorWindows ↔ trace.RebalancedAnchorAllocation := by
  constructor
  · intro windows
    have hendpoints : CreditEndpointWindowCondition210 (fun i => 3 * trace.rebalancedDemand i)
        (fun _ : Fin trace.rebalancedTotalCredit => (1 : Nat)) Fin.val
        trace.closedAnchorLeft trace.closedAnchorRight := by
      intro i k hle
      let a := trace.closedAnchorLeft i
      let b := trace.rebalancedCreditAfter k
      have hpos := trace.rebalanced_credit_after_positive k
      change a ≤ b - 1 at hle
      have hab : a < b := by omega
      have hb := trace.rebalanced_credit_after_le_total k
      have hpay := Nat.le_of_not_gt (windows a b hab hb)
      change 3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) ≤ b - a at hpay
      rw [← trace.rebalanced_anchor_demand_sum (a := a) (Nat.zero_le a |>.trans_lt hab),
        ← trace.rebalanced_anchor_supply_sum hab hb] at hpay
      exact hpay
    obtain ⟨allocation, allowed, paid, capacity⟩ := (credit_endpoint_windows_iff_allocation210
      (fun i => min_le_right (trace.rebalancedAnchorCredit i) (trace.closedAnchorRight i))).mp hendpoints
    refine ⟨allocation, ?_, paid, capacity⟩
    intro i j hpos
    have hj := Finset.single_le_sum (f := allocation i) (fun _ _ => Nat.zero_le _) (mem_univ j)
    rw [paid i] at hj
    have hp : 0 < trace.rebalancedDemand i := by omega
    have ⟨hl, hr⟩ := allowed i j hpos
    change trace.closedAnchorLeft i ≤ j.val at hl
    rw [trace.closed_anchor_left_of_positive hp] at hl
    have hb := trace.rebalanced_credit_after_positive i
    unfold closedAnchorRight at hr
    exact ⟨hl, by omega⟩
  · rintro ⟨allocation, allowed, paid, capacity⟩ a b hab hb
    have hall := credit_hall_of_allocation210
      (eligible := fun i j => trace.closedAnchorLeft i ≤ j.val ∧ j.val ≤ trace.closedAnchorRight i)
      (allocation := allocation)
      (fun i j hpos => by
        obtain ⟨hl, hr⟩ := allowed i j hpos
        exact ⟨(min_le_left _ _).trans hl, by unfold closedAnchorRight; omega⟩)
      (fun i => (paid i).ge) capacity
    have h := credit_windows_of_hall210 hall a (b - 1) (by omega)
    rw [trace.rebalanced_anchor_demand_sum (Nat.zero_le a |>.trans_lt hab),
      trace.rebalanced_anchor_supply_sum hab hb] at h
    exact Nat.not_lt_of_ge h

private def terminalPhasePeriod (i : Fin n) : Finset Nat :=
  Ico (trace.rebalancedCreditAfter i - trace.rebalancedPhasePeriodWidth i) (trace.rebalancedCreditAfter i)

private theorem terminal_phase_period_card {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    (trace.terminalPhasePeriod i).card = trace.rebalancedPhasePeriodWidth i := by
  have h := (trace.rebalanced_phase_period_fits_anchor positive).trans (Nat.sub_le _ _)
  rw [terminalPhasePeriod, Nat.card_Ico]
  omega

private theorem terminal_phase_period_inside {a b : Nat} {i : Fin n}
    (inside : i ∈ trace.rebalancedAnchorRequests a b) : trace.terminalPhasePeriod i ⊆ Ico a b := by
  obtain ⟨hp, ha, hb⟩ := (mem_filter.mp inside).2
  have hfit := trace.rebalanced_phase_period_fits_anchor hp
  intro x hx
  simp only [terminalPhasePeriod, mem_Ico] at hx
  exact mem_Ico.mpr ⟨by omega, hx.2.trans_le hb⟩

private theorem same_key_terminal_phase_periods_disjoint {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    Disjoint (trace.terminalPhasePeriod i) (trace.terminalPhasePeriod j) := by
  have h := trace.same_key_rebalanced_credit_period order key
  change trace.rebalancedPhasePeriodWidth j ≤ _ at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [terminalPhasePeriod, mem_Ico] at hx hy
  omega

private theorem sum_card_le_credit_window {a b : Nat} (selected : Finset (Fin n))
    (interval : Fin n → Finset Nat) (disjoint : (selected : Set (Fin n)).PairwiseDisjoint interval)
    (inside : ∀ i ∈ selected, interval i ⊆ Ico a b) :
    (∑ i ∈ selected, (interval i).card) ≤ b - a := by
  rw [← Finset.card_biUnion disjoint, ← Nat.card_Ico]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr inside)

/-- The full periods of any number of contained requests on one
phase key fit disjointly in their containing credit window. -/
theorem rebalanced_anchor_periods_fit_on_key210 {a b : Nat}
    (selected : Finset (Fin n)) (inside : selected ⊆ trace.rebalancedAnchorRequests a b)
    (key : Nat × Fin 420) (same : ∀ i ∈ selected, (trace.event i).phaseKey = key) :
    (∑ i ∈ selected, trace.rebalancedPhasePeriodWidth i) ≤ b - a := by
  have hdisjoint : (selected : Set (Fin n)).PairwiseDisjoint trace.terminalPhasePeriod := by
    intro i hi j hj hne
    have hk := (same i hi).trans (same j hj).symm
    rcases lt_or_gt_of_ne hne with order | order
    · exact trace.same_key_terminal_phase_periods_disjoint order hk
    · exact (trace.same_key_terminal_phase_periods_disjoint order hk.symm).symm
  calc
    _ = ∑ i ∈ selected, (trace.terminalPhasePeriod i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (trace.terminal_phase_period_card (mem_filter.mp (inside hi)).2.1).symm
    _ ≤ _ := sum_card_le_credit_window selected trace.terminalPhasePeriod hdisjoint
      (fun _ hi => trace.terminal_phase_period_inside (inside hi))

/-- The latest long anchor lies at or after every previous long
request of that key, so the full credit windows remain disjoint. -/
theorem same_key_long_anchor_intervals_disjoint210 {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey)
    (longI : trace.ReusedLong i) (longJ : trace.ReusedLong j) :
    Disjoint (trace.rebalancedAnchorInterval i) (trace.rebalancedAnchorInterval j) := by
  have ha := trace.earlier_long_le_anchor order longI.1 longJ.1 key
  have h := trace.rebalanced_credit_after_monotone ha
  have hanchor : trace.costAnchor trace.rebalancedCosts j = trace.anchor j := by
    rw [costAnchor, if_pos longJ]
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [rebalancedAnchorInterval, rebalancedAnchorCredit, mem_Ico] at hx hy
  rw [hanchor] at hy
  exact (not_lt_of_ge (h.trans hy.1)) hx.2

theorem rebalanced_long_anchor_widths_fit_on_key210 {a b : Nat}
    (selected : Finset (Fin n)) (inside : selected ⊆ trace.rebalancedAnchorRequests a b)
    (long : ∀ i ∈ selected, trace.ReusedLong i)
    (key : Nat × Fin 420) (same : ∀ i ∈ selected, (trace.event i).phaseKey = key) :
    (∑ i ∈ selected, (trace.rebalancedAnchorInterval i).card) ≤ b - a := by
  have hdisjoint : (selected : Set (Fin n)).PairwiseDisjoint trace.rebalancedAnchorInterval := by
    intro i hi j hj hne
    have hk := (same i hi).trans (same j hj).symm
    rcases lt_or_gt_of_ne hne with order | order
    · exact trace.same_key_long_anchor_intervals_disjoint210 order hk (long i hi) (long j hj)
    · exact (trace.same_key_long_anchor_intervals_disjoint210 order hk.symm (long j hj) (long i hi)).symm
  apply sum_card_le_credit_window selected trace.rebalancedAnchorInterval hdisjoint
  intro i hi x hx
  obtain ⟨_, ha, hb⟩ := (mem_filter.mp (inside hi)).2
  obtain ⟨hl, hr⟩ := mem_Ico.mp hx
  exact mem_Ico.mpr ⟨ha.trans hl, hr.trans_le hb⟩

def rebalancedAnchorKeys (selected : Finset (Fin n)) : Finset (Nat × Fin 420) :=
  selected.image fun i => (trace.event i).phaseKey

/-- Each key can be charged at a different fraction of the common
window capacity. The sum of the fractions must be at most one. -/
theorem rebalanced_anchor_pay_of_key_rates210 {a b scale : Nat}
    (selected : Finset (Fin n)) (positiveScale : 0 < scale)
    (rate : Nat × Fin 420 → Nat) (width : Fin n → Nat)
    (widthFits : ∀ key ∈ trace.rebalancedAnchorKeys selected,
      (∑ i ∈ selected with (trace.event i).phaseKey = key, width i) ≤ b - a)
    (localPay : ∀ i ∈ selected, scale * (3 * trace.rebalancedDemand i) ≤
      rate (trace.event i).phaseKey * width i)
    (rateSum : (∑ key ∈ trace.rebalancedAnchorKeys selected, rate key) ≤ scale) :
    3 * (∑ i ∈ selected, trace.rebalancedDemand i) ≤ b - a := by
  let key (i : Fin n) := (trace.event i).phaseKey
  let keys := trace.rebalancedAnchorKeys selected
  apply Nat.le_of_mul_le_mul_left _ positiveScale
  calc
    _ = ∑ i ∈ selected, scale * (3 * trace.rebalancedDemand i) := by simp only [Finset.mul_sum]
    _ = ∑ k ∈ keys, ∑ i ∈ selected with key i = k, scale * (3 * trace.rebalancedDemand i) :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem key hi) _).symm
    _ ≤ ∑ k ∈ keys, rate k * (b - a) := by
      apply Finset.sum_le_sum
      intro k hk
      let fiber := selected.filter fun i => key i = k
      have hsame (i : Fin n) (hi : i ∈ fiber) : key i = k := (mem_filter.mp hi).2
      have hfit : (∑ i ∈ fiber, width i) ≤ b - a := widthFits k hk
      calc
        _ ≤ ∑ i ∈ fiber, rate k * width i := by
          apply Finset.sum_le_sum
          intro i hi
          have h := localPay i (mem_filter.mp hi).1
          change _ ≤ rate (key i) * _ at h
          rwa [hsame i hi] at h
        _ = rate k * (∑ i ∈ fiber, width i) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ hfit
    _ = (∑ k ∈ keys, rate k) * (b - a) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ rateSum

theorem rebalanced_anchor_pay_of_three_large_keys210 {a b : Nat}
    (selected : Finset (Fin n)) (inside : selected ⊆ trace.rebalancedAnchorRequests a b)
    (few : (trace.rebalancedAnchorKeys selected).card ≤ 3)
    (large : ∀ i ∈ selected, trace.ReusedLong i ∧ 109 ≤ d (trace.event i).hit) :
    3 * (∑ i ∈ selected, trace.rebalancedDemand i) ≤ b - a := by
  apply trace.rebalanced_anchor_pay_of_key_rates210 selected (by decide : 0 < 3) (fun _ => 1)
    trace.rebalancedPhasePeriodWidth
  · intro key _
    exact trace.rebalanced_anchor_periods_fit_on_key210 _ ((Finset.filter_subset _ _).trans inside) key
      (fun _ hi => (mem_filter.mp hi).2)
  · intro i hi
    have hp := (mem_filter.mp (inside hi)).2.1
    have hcost : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
      trace.rebalanced_demand_linear_cap hp
    obtain ⟨hlong, hlarge⟩ := large i hi
    rw [trace.rebalanced_phase_period_width_of_long hp hlong]
    omega
  · simpa using few

def rebalancedAnchorNegativeCost (i : Fin n) : Nat :=
  ∑ k ∈ Ioc (trace.costAnchor trace.rebalancedCosts i) i, trace.rebalancedNegativeCost k

def rebalancedAnchorGrowth (i : Fin n) : Nat :=
  (trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon

theorem rebalanced_anchor_width_eq_growth_and_negative210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    (trace.rebalancedAnchorInterval i).card = 2 * trace.rebalancedAnchorGrowth i +
      3 * trace.rebalancedAnchorNegativeCost i := by
  let a := trace.costAnchor trace.rebalancedCosts i
  obtain ⟨order, key⟩ := trace.cost_demand_anchor positive
  have hincrement := congrArg Prod.fst key
  change d (trace.event a).hit = d (trace.event i).hit at hincrement
  have ha := moving_horizon_step_update (trace.event a).step
  have hi := moving_horizon_step_update (trace.event i).step
  have h := trace.rebalanced_credit_distance order.le
  change trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i =
    2 * ((trace.event i).nextHorizon - (trace.event a).nextHorizon) +
      3 * trace.rebalancedAnchorNegativeCost i at h
  rw [rebalancedAnchorInterval, Nat.card_Ico, h]
  change 2 * ((trace.event i).nextHorizon - (trace.event a).nextHorizon) + _ =
    2 * ((trace.event i).horizon - (trace.event a).horizon) + _
  rw [hi, ha, hincrement, Nat.add_sub_add_right]

theorem rebalanced_anchor_pay_of_long_key_rates210 {a b scale : Nat}
    (selected : Finset (Fin n)) (inside : selected ⊆ trace.rebalancedAnchorRequests a b)
    (positiveScale : 0 < scale) (rate : Nat × Fin 420 → Nat)
    (long : ∀ i ∈ selected, trace.ReusedLong i)
    (localPay : ∀ i ∈ selected, scale * (3 * trace.rebalancedDemand i) ≤
      rate (trace.event i).phaseKey * (trace.rebalancedAnchorInterval i).card)
    (rateSum : (∑ key ∈ trace.rebalancedAnchorKeys selected, rate key) ≤ scale) :
    3 * (∑ i ∈ selected, trace.rebalancedDemand i) ≤ b - a := by
  apply trace.rebalanced_anchor_pay_of_key_rates210 selected positiveScale rate _ _ localPay rateSum
  intro key _
  exact trace.rebalanced_long_anchor_widths_fit_on_key210 _
    ((Finset.filter_subset _ _).trans inside) (fun i hi => long i (mem_filter.mp hi).1) key
    (fun _ hi => (mem_filter.mp hi).2)

/-- Four long phase keys fit if each reuse has enough negative cost
between its own anchor and its endpoint to pay the extra fraction. -/
theorem rebalanced_anchor_pay_of_four_long_keys210 {a b : Nat}
    (selected : Finset (Fin n)) (inside : selected ⊆ trace.rebalancedAnchorRequests a b)
    (few : (trace.rebalancedAnchorKeys selected).card ≤ 4)
    (long : ∀ i ∈ selected, trace.ReusedLong i)
    (negative : ∀ i ∈ selected, 8 * d (trace.event i).hit + 4188 ≤ trace.rebalancedAnchorNegativeCost i) :
    3 * (∑ i ∈ selected, trace.rebalancedDemand i) ≤ b - a := by
  apply trace.rebalanced_anchor_pay_of_long_key_rates210 selected inside (by decide : 0 < 4) (fun _ => 1) long
  · intro i hi
    have hp := (mem_filter.mp (inside hi)).2.1
    have hcost : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
      trace.rebalanced_demand_linear_cap hp
    obtain ⟨order, key⟩ := trace.cost_demand_anchor hp
    have h := trace.same_key_rebalanced_credit_period_with_negative order key
    change trace.rebalancedPhasePeriodWidth i + 3 * trace.rebalancedAnchorNegativeCost i ≤
      trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i at h
    rw [trace.rebalanced_phase_period_width_of_long hp (long i hi)] at h
    simp only [one_mul, rebalancedAnchorInterval, Nat.card_Ico]
    have hnegative := negative i hi
    omega
  · simpa using few

theorem rebalanced_anchor_deficit_has_four_large_keys210 {a b : Nat}
    (deficit : trace.RebalancedAnchorDeficit a b)
    (large : ∀ i ∈ trace.rebalancedAnchorRequests a b, trace.ReusedLong i ∧ 109 ≤ d (trace.event i).hit) :
    4 ≤ (trace.rebalancedAnchorKeys (trace.rebalancedAnchorRequests a b)).card := by
  by_contra h
  exact Nat.not_lt_of_ge (trace.rebalanced_anchor_pay_of_three_large_keys210 _
    (Finset.Subset.refl _) (by omega) large) deficit

/-- A deficit among at most four large long phase keys needs a request
with just one phase period of growth and too little negative credit. -/
theorem rebalanced_anchor_four_key_deficit_has_one_period210 {a b : Nat}
    (deficit : trace.RebalancedAnchorDeficit a b)
    (few : (trace.rebalancedAnchorKeys (trace.rebalancedAnchorRequests a b)).card ≤ 4)
    (large : ∀ i ∈ trace.rebalancedAnchorRequests a b, trace.ReusedLong i ∧ 32 ≤ d (trace.event i).hit) :
    ∃ i ∈ trace.rebalancedAnchorRequests a b,
      trace.rebalancedAnchorGrowth i = 210 * d (trace.event i).hit ∧
      trace.rebalancedAnchorNegativeCost i < 8 * d (trace.event i).hit + 4188 := by
  let requests := trace.rebalancedAnchorRequests a b
  have hwitness : ∃ i ∈ requests, (trace.rebalancedAnchorInterval i).card < 12 * trace.rebalancedDemand i := by
    by_contra h
    push Not at h
    have hpay := trace.rebalanced_anchor_pay_of_long_key_rates210 requests (Finset.Subset.refl _)
      (by decide : 0 < 4) (fun _ => 1) (fun i hi => (large i hi).1)
      (fun i hi => by have hp := h i hi; simp only [one_mul]; omega) (by simpa using few)
    exact Nat.not_lt_of_ge hpay deficit
  obtain ⟨i, hi, hwidth⟩ := hwitness
  obtain ⟨hlong, he⟩ := large i hi
  let e := d (trace.event i).hit
  change 32 ≤ e at he
  have hp := (mem_filter.mp hi).2.1
  have hcost : trace.rebalancedDemand i ≤ 37 * e + 1047 := trace.rebalanced_demand_linear_cap hp
  have hlcm := trace.rebalanced_phase_period_width_of_long hp hlong
  unfold rebalancedPhasePeriodWidth at hlcm
  have heq : Nat.lcm 210 (2 * d (trace.event i).hit) = 210 * e := by omega
  have ⟨hdiv, hmin⟩ := trace.rebalanced_request_period210 hp
  rw [heq] at hdiv hmin
  change (210 * e) ∣ trace.rebalancedAnchorGrowth i at hdiv
  change 210 * e ≤ trace.rebalancedAnchorGrowth i at hmin
  rw [trace.rebalanced_anchor_width_eq_growth_and_negative210 hp] at hwidth
  have hlt : trace.rebalancedAnchorGrowth i < 420 * e := by omega
  obtain ⟨m, hm⟩ := hdiv
  have hone : m = 1 := by
    by_contra hn
    by_cases hz : m = 0
    · simp [hz] at hm
      omega
    · have h := Nat.mul_le_mul_left (210 * e) (show 2 ≤ m by omega)
      rw [← hm] at h
      omega
  have hg : trace.rebalancedAnchorGrowth i = 210 * e := by simpa [hone] using hm
  exact ⟨i, hi, hg, by omega⟩

theorem rebalanced_anchor_deficit_has_two_keys210 {a b : Nat}
    (deficit : trace.RebalancedAnchorDeficit a b) :
    2 ≤ (trace.rebalancedAnchorKeys (trace.rebalancedAnchorRequests a b)).card := by
  let requests := trace.rebalancedAnchorRequests a b
  by_contra h
  change ¬ 2 ≤ (trace.rebalancedAnchorKeys requests).card at h
  have hpay : 3 * (∑ i ∈ requests, trace.rebalancedDemand i) ≤ b - a := by
    apply trace.rebalanced_anchor_pay_of_key_rates210 requests (by decide : 0 < 1) (fun _ => 1)
      trace.rebalancedPhasePeriodWidth
    · intro key _
      exact trace.rebalanced_anchor_periods_fit_on_key210 _ (Finset.filter_subset _ _) key
        (fun _ hi => (mem_filter.mp hi).2)
    · intro i hi
      simpa only [one_mul] using trace.rebalanced_demand_le_phase_period (mem_filter.mp hi).2.1
    · simpa using (show (trace.rebalancedAnchorKeys requests).card ≤ 1 by omega)
  exact Nat.not_lt_of_ge hpay deficit

private theorem rebalanced_anchor_demand_ceiling {a b L : Nat}
    (hL : 4 ≤ L) (ceiling : ∀ i ∈ trace.rebalancedAnchorRequests a b,
      trace.ReusedLong i → d (trace.event i).hit ≤ L) :
    3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) ≤
      (trace.rebalancedAnchorRequests a b).card * (111 * L + 3141) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _i ∈ trace.rebalancedAnchorRequests a b, (111 * L + 3141) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := (mem_filter.mp hi).2.1
      by_cases hl : trace.ReusedLong i
      · have hc : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
          trace.rebalanced_demand_linear_cap hp
        have he := ceiling i hi hl
        omega
      · have hc : trace.rebalancedDemand i ≤ 1166 := (trace.rebalanced_demand_nonlong_bounds hp hl).2
        omega
    _ = _ := by simp

theorem rebalanced_anchor_deficit_long_bounds_of_few210 {a b : Nat} {i : Fin n}
    (deficit : trace.RebalancedAnchorDeficit a b) (inside : i ∈ trace.rebalancedAnchorRequests a b)
    (long : trace.ReusedLong i) :
    ((trace.rebalancedAnchorRequests a b).card ≤ 2 → d (trace.event i).hit ≤ 31) ∧
      ((trace.rebalancedAnchorRequests a b).card ≤ 3 → d (trace.event i).hit ≤ 107) := by
  let requests := trace.rebalancedAnchorRequests a b
  let longRequests := requests.filter trace.ReusedLong
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image longRequests (fun k => d (trace.event k).hit)
    ⟨i, mem_filter.mpr ⟨inside, long⟩⟩
  let L := d (trace.event j).hit
  have hiL : d (trace.event i).hit ≤ L := hmax i (mem_filter.mpr ⟨inside, long⟩)
  have ⟨hjreq, hjlong⟩ := mem_filter.mp hj
  have ⟨hp, ha, hb⟩ := (mem_filter.mp hjreq).2
  have hperiod := trace.rebalanced_phase_period_fits_anchor hp
  rw [trace.rebalanced_phase_period_width_of_long hp hjlong] at hperiod
  have hspan : 420 * L ≤ b - a := by omega
  have hceil (k : Fin n) (hk : k ∈ requests) (hklong : trace.ReusedLong k) :
      d (trace.event k).hit ≤ L := hmax k (mem_filter.mpr ⟨hk, hklong⟩)
  have htest {q : Nat} (hcard : requests.card ≤ q) (hL : 4 ≤ L) : 420 * L < q * (111 * L + 3141) := by
    have hsum := trace.rebalanced_anchor_demand_ceiling hL hceil
    have hbound := Nat.mul_le_mul_right (111 * L + 3141) hcard
    change b - a < 3 * (∑ i ∈ requests, trace.rebalancedDemand i) at deficit
    exact (hspan.trans_lt deficit).trans_le (hsum.trans hbound)
  constructor
  · intro few
    by_contra h
    have ht := htest few (by omega)
    omega
  · intro few
    by_contra h
    have ht := htest few (by omega)
    have hr : 3 ≤ (trace.event i).hit := by
      have := (trace.event i).step.1.1
      have := (trace.event i).step.2.1
      omega
    have hodd := d_mod_two_eq_one_of_three_le hr
    omega

theorem rebalanced_anchor_small_deficit_bounds210 {a b : Nat}
    (deficit : trace.RebalancedAnchorDeficit a b) (few : (trace.rebalancedAnchorRequests a b).card ≤ 3) :
    b - a ≤ 45053 ∧ ∀ i ∈ trace.rebalancedAnchorRequests a b, d (trace.event i).hit ≤ 159 := by
  have hlong (i : Fin n) (hi : i ∈ trace.rebalancedAnchorRequests a b) (long : trace.ReusedLong i) :
      d (trace.event i).hit ≤ 107 := (trace.rebalanced_anchor_deficit_long_bounds_of_few210 deficit hi long).2 few
  have hsum := trace.rebalanced_anchor_demand_ceiling (by decide : 4 ≤ 107) hlong
  refine ⟨?_, ?_⟩
  · change b - a < 3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) at deficit
    omega
  · intro i hi
    by_cases hl : trace.ReusedLong i
    · exact (hlong i hi hl).trans (by decide)
    · exact (trace.rebalanced_demand_nonlong_bounds (mem_filter.mp hi).2.1 hl).1

theorem rebalanced_small_anchor_deficit_intervening_bounds210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j k : Fin n} (inside : i < k) (beforeEnd : k ≤ j)
    (deficit : trace.RebalancedAnchorDeficit (trace.rebalancedCreditAfter i) (trace.rebalancedCreditAfter j))
    (few : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter i) (trace.rebalancedCreditAfter j)).card ≤ 3) :
    let event := trace.event k
    d event.hit ≤ 22527 ∧ event.hit - event.start ≤ 45054 ∧
      (339 ≤ d event.hit → 3 * (event.hit - event.start + 1) ≤ d event.hit - 1 → d event.hit ≤ 4371) := by
  dsimp only
  have hw := (trace.rebalanced_anchor_small_deficit_bounds210 deficit few).1
  have hdistance := trace.rebalanced_credit_distance_eq_sum210 delta (inside.le.trans beforeEnd)
  have hlocal := Finset.single_le_sum
    (f := fun l => 2 * (d (trace.event l).hit - 1) + 3 * trace.rebalancedNegativeCost l)
    (fun _ _ => Nat.zero_le _) (mem_Ioc.mpr ⟨inside, beforeEnd⟩)
  rw [← hdistance] at hlocal
  have hg := moving_horizon_step_gap_le_twice_increment (trace.event k).step
  refine ⟨by omega, by omega, ?_⟩
  intro large smallGap
  have hu : ¬ d (trace.event k).hit ∣ 210 := by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 210) hd
    omega
  have hnet := (trace.event k).rebalanced_net_cost_le_outside_large_gaps210 hu smallGap
  have hcost := (trace.event k).rebalanced_cost_le_net
  have hr : 3 ≤ (trace.event k).hit := by
    have := (trace.event k).step.1.1
    have := (trace.event k).step.2.1
    omega
  have hodd := d_mod_two_eq_one_of_three_le hr
  change 2 * (d (trace.event k).hit - 1) + 3 * (-(trace.event k).rebalancedCost).toNat ≤ _ at hlocal
  omega

/-- A deficient window can be shrunk to endpoints of positive
requests, preserving every request it contains. -/
theorem rebalanced_anchor_deficit_has_endpoints210 {a b : Nat}
    (deficit : trace.RebalancedAnchorDeficit a b) :
    ∃ i ∈ trace.rebalancedAnchorRequests a b, ∃ j ∈ trace.rebalancedAnchorRequests a b,
      trace.rebalancedAnchorCredit i < trace.rebalancedCreditAfter j ∧
        trace.RebalancedAnchorDeficit (trace.rebalancedAnchorCredit i) (trace.rebalancedCreditAfter j) := by
  let requests := trace.rebalancedAnchorRequests a b
  have hsum : 0 < ∑ k ∈ requests, trace.rebalancedDemand k := by
    change b - a < 3 * (∑ k ∈ requests, trace.rebalancedDemand k) at deficit
    omega
  obtain ⟨k, hk, _⟩ := Finset.sum_pos_iff.mp hsum
  have hne : requests.Nonempty := ⟨k, hk⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image requests trace.rebalancedAnchorCredit hne
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image requests trace.rebalancedCreditAfter hne
  have ⟨hpos, ha, _⟩ := (mem_filter.mp hi).2
  have hb := (mem_filter.mp hj).2.2.2
  have hfit := (trace.rebalanced_demand_le_phase_period hpos).trans
    (trace.rebalanced_phase_period_fits_anchor hpos)
  have hright := hmax i hi
  have hset : trace.rebalancedAnchorRequests (trace.rebalancedAnchorCredit i) (trace.rebalancedCreditAfter j) =
      requests := by
    ext x
    constructor
    · intro hx
      obtain ⟨hp, hl, hr⟩ := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨mem_univ _, hp, ha.trans hl, hr.trans hb⟩
    · intro hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.1, hmin x hx, hmax x hx⟩
  refine ⟨i, hi, j, hj, by omega, ?_⟩
  unfold RebalancedAnchorDeficit
  rw [hset]
  change b - a < 3 * (∑ k ∈ requests, trace.rebalancedDemand k) at deficit
  omega

theorem rebalanced_credit_debt_nonpos_of_anchor_windows210 (windows : trace.RebalancedAnchorWindows) :
    trace.rebalancedCreditDebt ≤ 0 := by
  obtain ⟨allocation, _, paid, capacity⟩ := trace.rebalanced_anchor_windows_iff_allocation210.mp windows
  have h : 3 * (∑ i, trace.rebalancedDemand i) ≤ trace.rebalancedTotalCredit := by
    calc
      _ = ∑ i, ∑ j, allocation i j := by rw [Finset.mul_sum]; simp only [paid]
      _ = ∑ j, ∑ i, allocation i j := Finset.sum_comm
      _ ≤ ∑ _j : Fin trace.rebalancedTotalCredit, (1 : Nat) :=
        Finset.sum_le_sum (fun j _ => capacity j)
      _ = _ := by simp
  unfold rebalancedCreditDebt
  omega

theorem rebalanced_anchor_deficit_of_positive_credit_debt210 (debt : 0 < trace.rebalancedCreditDebt) :
    ∃ i j : Fin n, 0 < trace.rebalancedDemand i ∧ 0 < trace.rebalancedDemand j ∧
      trace.rebalancedAnchorCredit i < trace.rebalancedCreditAfter j ∧
      trace.RebalancedAnchorDeficit (trace.rebalancedAnchorCredit i) (trace.rebalancedCreditAfter j) ∧
      2 ≤ (trace.rebalancedAnchorKeys
        (trace.rebalancedAnchorRequests (trace.rebalancedAnchorCredit i) (trace.rebalancedCreditAfter j))).card := by
  have h : ¬ trace.RebalancedAnchorWindows := by
    intro windows
    exact (not_lt_of_ge (trace.rebalanced_credit_debt_nonpos_of_anchor_windows210 windows)) debt
  unfold RebalancedAnchorWindows at h
  push Not at h
  obtain ⟨a, b, _, _, deficit⟩ := h
  obtain ⟨i, hi, j, hj, order, hdef⟩ := trace.rebalanced_anchor_deficit_has_endpoints210 deficit
  exact ⟨i, j, (mem_filter.mp hi).2.1, (mem_filter.mp hj).2.1, order, hdef,
    trace.rebalanced_anchor_deficit_has_two_keys210 hdef⟩

end

end ResidualPhaseTrace210

theorem rebalanced_crossing_signed_of_anchor_windows210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper) (firstBudget : 10 * firstUpper ≤ 3 * M)
    (windows : trace.RebalancedAnchorWindows) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have hcredit := trace.rebalanced_credit_debt_nonpos_of_anchor_windows210 windows
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace firstBound (by omega)

theorem rebalanced_first_crossing_has_positive_credit_debt210
    {M s C r C' p first : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (step : IsMovingHorizonStep s C r C')
    (short : 2 * (s - (M + 2)) ≤ M) (cross : M < 2 * (r - (M + 2)))
    (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (firstBudget : 10 * trace.totalCappedFirstPayment ≤ 3 * M) :
    0 < trace.rebalancedCreditDebt := by
  by_contra h
  have hlower := (rebalanced_first_crossing_growth_constraints210 (by omega) canonical ledger
    step short cross trace delta).2.2
  have hupper := rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace
    (Nat.le_refl trace.totalCappedFirstPayment) (by omega)
  exact (not_lt_of_ge hlower) hupper

end A166944Research
