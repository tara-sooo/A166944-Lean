import A166944.TravelRebalanced210
import A166944.ResidualGrowthWindows210

/-! # Rebalanced costs and a smaller charge for first travel -/

open Finset

namespace A166944Research

namespace ResidualPhaseEvent210

abbrev rebalancedNetCost (event : ResidualPhaseEvent210) : Int := event.potentialNetCost rebalancedPotential210

/-- A first gap is charged separately only up to the positive net cost
of that event. Negative net costs stay available as credit. -/
def cappedFirstPayment (event : ResidualPhaseEvent210) : Nat :=
  min (24 * event.scaledFirstGap) event.rebalancedNetCost.toNat

def rebalancedCost (event : ResidualPhaseEvent210) : Int :=
  event.rebalancedNetCost - (event.cappedFirstPayment : Int)

theorem rebalanced_cost_le_net (event : ResidualPhaseEvent210) : event.rebalancedCost ≤ event.rebalancedNetCost := by
  unfold rebalancedCost
  omega

theorem rebalanced_net_cost_le_of_unsupported (event : ResidualPhaseEvent210) (hu : ¬ d event.hit ∣ 210) :
    event.rebalancedNetCost ≤ ((24 * (event.hit - event.start) + 1036 : Nat) : Int) -
      11 * ((d event.hit - 1 : Nat) : Int) := by
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  exact event.potential_net_cost_le_of_unsupported (rebalanced_potential210_le _ _ heven) hu

theorem rebalanced_cost_positive_unsupported (event : ResidualPhaseEvent210) (h : 0 < event.rebalancedCost) :
    ¬ d event.hit ∣ 210 := by
  intro hd
  simp [rebalancedCost, cappedFirstPayment, potentialNetCost, hd] at h

theorem rebalanced_cost_le_of_positive (event : ResidualPhaseEvent210) (positive : 0 < event.rebalancedCost) :
    event.rebalancedCost ≤ (24 * (event.hit - event.start) + 1036 : Nat) -
      11 * ((d event.hit - 1 : Nat) : Int) - (24 * event.firstGap : Nat) := by
  have hu := event.rebalanced_cost_positive_unsupported positive
  have hraw := event.rebalanced_net_cost_le_of_unsupported hu
  have hp : 24 * event.scaledFirstGap ≤ event.rebalancedNetCost.toNat := by
    by_contra h
    have hle : event.rebalancedNetCost.toNat ≤ 24 * event.scaledFirstGap := by omega
    simp only [rebalancedCost, cappedFirstPayment, min_eq_right hle] at positive
    omega
  rw [rebalancedCost, cappedFirstPayment, min_eq_left hp, scaledFirstGap, if_neg hu]
  omega

theorem rebalanced_net_cost_positive_part_le (event : ResidualPhaseEvent210) :
    event.rebalancedNetCost.toNat ≤ 37 * d event.hit + 1047 := by
  by_cases hd : d event.hit ∣ 210
  · simp [potentialNetCost, hd]
  · have h := event.rebalanced_net_cost_le_of_unsupported hd
    have hgap := moving_horizon_step_gap_le_twice_increment event.step
    omega

theorem rebalanced_net_cost_exception_le (event : ResidualPhaseEvent210)
    (exception : d event.hit ∈ rebalancedExceptions210) :
    event.rebalancedNetCost.toNat ≤ rebalancedAllowance210 (d event.hit) := by
  by_cases hd : d event.hit ∣ 210
  · simp [potentialNetCost, hd]
  · have h := moving_horizon_rebalanced_exception210 event.step exception
    change (event.potentialNetCost rebalancedPotential210).toNat ≤ _
    rw [potentialNetCost, if_neg hd]
    omega

/-- The signed net cost, including the first payment, is at most 146 times
the horizon growth at the event. -/
theorem rebalanced_net_cost_le_growth210 (event : ResidualPhaseEvent210) :
    event.rebalancedNetCost ≤ 146 * ((d event.hit - 1 : Nat) : Int) := by
  by_cases hlarge : 11 ≤ d event.hit
  · have hcost := event.rebalanced_net_cost_positive_part_le
    omega
  have hhit : 3 ≤ event.hit := by
    have := event.step.1.1
    have := event.step.2.1
    omega
  have hodd := d_mod_two_eq_one_of_three_le hhit
  have hnonunit := event.step.2.2.2.1
  by_cases h9 : d event.hit = 9
  · have hexception : d event.hit ∈ rebalancedExceptions210 := by
      rw [h9]
      decide
    have hcost := event.rebalanced_net_cost_exception_le hexception
    rw [h9, show rebalancedAllowance210 9 = 315 by decide] at hcost
    omega
  · have hdiv : d event.hit ∣ 210 := by
      have hsmall : d event.hit = 3 ∨ d event.hit = 5 ∨ d event.hit = 7 := by omega
      rcases hsmall with h | h | h <;> rw [h] <;> decide
    have hzero : event.rebalancedNetCost = 0 := by simp [potentialNetCost, hdiv]
    omega

theorem capped_first_payment_le_gap_cost (event : ResidualPhaseEvent210) :
    event.cappedFirstPayment ≤ 24 * (event.hit - event.start) + 1036 - 11 * (d event.hit - 1) := by
  by_cases hd : d event.hit ∣ 210
  · simp [cappedFirstPayment, potentialNetCost, hd]
  · have hraw := event.rebalanced_net_cost_le_of_unsupported hd
    have hp := min_le_right (24 * event.scaledFirstGap) event.rebalancedNetCost.toNat
    change event.cappedFirstPayment ≤ _ at hp
    omega

/-- The first payment is bounded by the actual gap and by the positive
cost after subtracting the event's own horizon growth. -/
theorem capped_first_payment_le_cofactor (event : ResidualPhaseEvent210) :
    let e := d event.hit
    let g := min (2 * e) (2 * (event.horizon + 1) / e)
    event.cappedFirstPayment ≤ min (24 * g) (24 * g + 1036 - 11 * (e - 1)) := by
  let e := d event.hit
  let g := min (2 * e) (2 * (event.horizon + 1) / e)
  change event.cappedFirstPayment ≤ min (24 * g) (24 * g + 1036 - 11 * (e - 1))
  have he : 1 < e := event.step.2.2.2.1
  have hproduct := moving_horizon_step_gap_mul_increment_le_twice_horizon event.step
  have hgap₂ : event.hit - event.start ≤ 2 * (event.horizon + 1) / e :=
    (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr hproduct
  have hgap : event.hit - event.start ≤ g :=
    Nat.le_min.mpr ⟨moving_horizon_step_gap_le_twice_increment event.step, hgap₂⟩
  have hf : event.firstGap ≤ event.hit - event.start := by
    unfold firstGap firstLongPrimePhaseGap
    split <;> omega
  refine Nat.le_min.mpr ⟨?_, ?_⟩
  · have hp := (min_le_left (24 * event.scaledFirstGap) event.rebalancedNetCost.toNat)
    have hs := event.scaled_first_gap_le
    change event.cappedFirstPayment ≤ _ at hp
    omega
  · have hp := event.capped_first_payment_le_gap_cost
    change _ ≤ 24 * g + 1036 - 11 * (d event.hit - 1)
    omega

theorem capped_first_payment_zero_of_cofactor (event : ResidualPhaseEvent210)
    (small : 48 * (event.horizon + 1) + 1036 * d event.hit ≤ 11 * (d event.hit - 1) * d event.hit) :
    event.cappedFirstPayment = 0 := by
  let e := d event.hit
  let g := min (2 * e) (2 * (event.horizon + 1) / e)
  have hp : event.cappedFirstPayment ≤ 24 * g + 1036 - 11 * (e - 1) :=
    event.capped_first_payment_le_cofactor.trans (min_le_right _ _)
  have he : 1 < e := event.step.2.2.2.1
  have hg : g * e ≤ 2 * (event.horizon + 1) :=
    (Nat.mul_le_mul_right e (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have hmul : (24 * g + 1036) * e ≤ (11 * (e - 1)) * e := by
    change 48 * (event.horizon + 1) + 1036 * e ≤ 11 * (e - 1) * e at small
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  have h := Nat.le_of_mul_le_mul_right hmul (by omega : 0 < e)
  omega

end ResidualPhaseEvent210

set_option maxRecDepth 16384 in
theorem rebalanced_startup_weight_total210 : startupWeightSumAtCap210 1036 = 4054512 := by
  decide +kernel

private theorem rebalanced_regular_period_pays210 : ∀ e : Fin 160, 1 < e.val → e.val % 2 = 1 →
    ¬ e.val ∣ 210 → e.val ∉ rebalancedExceptions210 →
    3 * startupWeightAtCap210 1036 e.val ≤ 2 * Nat.lcm 210 (2 * e.val) := by
  decide +kernel

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

abbrev rebalancedCosts : Fin n → Int := fun i => (trace.event i).rebalancedCost

def totalCappedFirstPayment : Nat := ∑ i, (trace.event i).cappedFirstPayment

theorem total_capped_first_payment_le : trace.totalCappedFirstPayment ≤ 24 * trace.scaledFirstTravel := by
  rw [totalCappedFirstPayment, scaledFirstTravel, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => min_le_left _ _

theorem sum_rebalanced_net_cost_split :
    (∑ i, (trace.event i).rebalancedNetCost) = (trace.totalCappedFirstPayment : Int) + ∑ i, trace.rebalancedCosts i := by
  rw [totalCappedFirstPayment, Nat.cast_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [rebalancedCosts, ResidualPhaseEvent210.rebalancedCost]; omega

theorem rebalanced_startup_cost_le : trace.costStartupSum trace.rebalancedCosts ≤ 4054512 := by
  rw [← rebalanced_startup_weight_total210]
  exact trace.cost_startup_sum_le_at_cap trace.rebalancedCosts (by decide)
    (fun i h => (trace.event i).rebalanced_cost_positive_unsupported h)
    (fun i h => (trace.event i).rebalanced_cost_le_of_positive h)

theorem rebalanced_request_period210 {i : Fin n} (positive : 0 < trace.costDemand trace.rebalancedCosts i) :
    Nat.lcm 210 (2 * d (trace.event i).hit) ∣
      (trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon ∧
    Nat.lcm 210 (2 * d (trace.event i).hit) ≤
      (trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon := by
  obtain ⟨order, key⟩ := trace.cost_demand_anchor positive
  let interval := trace.samePhaseInterval order key
  have h := (same_phase_credit_interval_constraints210 interval).2
  rw [interval.same_increment] at h
  exact ⟨h.1, h.2.1⟩

/-- The last full phase period alone can pay each individual request. -/
theorem rebalanced_request_pays_period210 {i : Fin n} (positive : 0 < trace.costDemand trace.rebalancedCosts i) :
    3 * trace.costDemand trace.rebalancedCosts i ≤ 2 * Nat.lcm 210 (2 * d (trace.event i).hit) := by
  have hcost := trace.cost_demand_eq_cost positive
  change trace.costDemand trace.rebalancedCosts i = (trace.event i).rebalancedCost.toNat at hcost
  have hpos : 0 < (trace.event i).rebalancedCost := by omega
  have hu := (trace.event i).rebalanced_cost_positive_unsupported hpos
  have hle := (trace.event i).rebalanced_cost_le_net
  obtain ⟨horder, hkey⟩ := trace.cost_demand_anchor positive
  by_cases hl : trace.ReusedLong i
  · have reuse : trace.PrimeReuse (trace.costAnchor trace.rebalancedCosts i) i := ⟨horder, hkey, hl.1.2, hu⟩
    have hp := trace.unsupported_prime_ge_eleven reuse
    have prime := prime_of_no_proper_factor (by omega : 1 < d (trace.event i).hit) hl.1.2
    have hcop := Nat.Coprime.coprime_dvd_left (by decide : 105 ∣ 210)
      ((prime.coprime_iff_not_dvd.mpr hu).symm)
    have hperiod : Nat.lcm 210 (2 * d (trace.event i).hit) = 210 * d (trace.event i).hit := by
      change Nat.lcm (2 * 105) (2 * d (trace.event i).hit) = _
      rw [Nat.lcm_mul_left, hcop.lcm_eq_mul, ← Nat.mul_assoc]
    have hbound := (trace.event i).rebalanced_net_cost_positive_part_le
    rw [hperiod]
    omega
  let e := d (trace.event i).hit
  change 3 * trace.costDemand trace.rebalancedCosts i ≤ 2 * Nat.lcm 210 (2 * e)
  by_cases hex : e ∈ rebalancedExceptions210
  · have hp := (trace.event i).rebalanced_net_cost_exception_le hex
    have hhalf := Nat.div_mul_le_self (Nat.lcm 210 (2 * e)) 2
    change (trace.event i).rebalancedNetCost.toNat ≤ Nat.lcm 210 (2 * e) / 2 at hp
    omega
  have hb := adjusted_phase_cost_weight_of_bound210 (trace.event i) (by decide : 1036 ≤ 1120)
    hl hpos ((trace.event i).rebalanced_cost_le_of_positive hpos)
  have he := (trace.event i).step.2.2.2.1
  have hr : 3 ≤ (trace.event i).hit := by
    have := (trace.event i).step.1.1
    have := (trace.event i).step.2.1
    omega
  have hperiod := rebalanced_regular_period_pays210 ⟨e, by have := hb.1; omega⟩ he
    (d_mod_two_eq_one_of_three_le hr) hu hex
  change 3 * startupWeightAtCap210 1036 e ≤ 2 * Nat.lcm 210 (2 * e) at hperiod
  have hbound : (trace.event i).rebalancedCost.toNat ≤ startupWeightAtCap210 1036 e := hb.2
  omega

/-- Every individual rebalanced request fits in its growth window,
including the composite increments 9 and 25. -/
theorem rebalanced_request_fits210 {i : Fin n} (positive : 0 < trace.costDemand trace.rebalancedCosts i) :
    3 * trace.costDemand trace.rebalancedCosts i ≤
      2 * ((trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon) :=
  (trace.rebalanced_request_pays_period210 positive).trans
    (Nat.mul_le_mul_left 2 (trace.rebalanced_request_period210 positive).2)

abbrev RebalancedGrowthWindows : Prop :=
  trace.GrowthWindows (trace.costAnchor trace.rebalancedCosts) (trace.costDemand trace.rebalancedCosts)
    trace.rebalancedCosts

theorem rebalanced_deficit_has_multiple_requests210 {a b : Nat}
    (deficit : trace.GrowthDeficit (trace.costAnchor trace.rebalancedCosts) (trace.costDemand trace.rebalancedCosts)
      trace.rebalancedCosts a b) :
    2 ≤ ((trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b).filter
      (fun i => 0 < trace.costDemand trace.rebalancedCosts i)).card := by
  let demand := trace.costDemand trace.rebalancedCosts
  let requests := trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b
  let positive := requests.filter (fun i => 0 < demand i)
  have hbad : trace.growthWindowCredit trace.rebalancedCosts a b < 3 * (∑ i ∈ requests, demand i) := deficit
  rw [sum_positive_requests requests demand] at hbad
  change _ < 3 * (∑ i ∈ positive, demand i) at hbad
  change 2 ≤ positive.card
  by_contra h
  have hsmall : positive.card = 0 ∨ positive.card = 1 := by omega
  rcases hsmall with hzero | hone
  · simp [Finset.card_eq_zero.mp hzero] at hbad
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    have hm : i ∈ positive := by simp [hi]
    have ⟨hreq, hp⟩ := Finset.mem_filter.mp hm
    have hfits := trace.rebalanced_request_fits210 hp
    have ⟨horder, _⟩ := trace.cost_demand_anchor hp
    have hcard := Finset.card_le_card (trace.growth_window_inside_of_request horder hreq)
    simp only [growthWindow, Nat.card_Ico] at hcard
    rw [hi, Finset.sum_singleton] at hbad
    unfold growthWindowCredit at hbad
    change 3 * demand i ≤ _ at hfits
    omega

theorem rebalanced_net_cost_le_of_windows (windows : trace.RebalancedGrowthWindows) :
    3 * (∑ i, (trace.event i).rebalancedNetCost) ≤
      ((3 * trace.totalCappedFirstPayment + 12163536 + 2 * (D sf - D s) : Nat) : Int) := by
  have hcost := trace.sum_signed_cost_le_growth_of_windows windows
  have hstart := trace.rebalanced_startup_cost_le
  rw [trace.sum_rebalanced_net_cost_split]
  omega

end

end ResidualPhaseTrace210

/-- The capped payment and the actual crossing gap give a sufficient
budget on this prefix. The window inequalities remain a hypothesis. -/
theorem rebalanced_crossing_budget_of_windows210 {M s C r p first : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (windows : trace.RebalancedGrowthWindows)
    (firstBudget : 3 * trace.totalCappedFirstPayment + 12163536 + 2 * (C - (2 * M - 2)) +
      72 * (r - s) + 3273 ≤ 3 * M) :
    (∑ i, (trace.event i).rebalancedNetCost) + (24 * (r - s) + 1091 : Nat) ≤ (M : Int) := by
  have hpath := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact hpath.2.2.2.1
    | succ _ => exact hpath.1.2.1
  have hend := (moving_horizon_path_endpoint hpath).2.1
  have hcost := trace.rebalanced_net_cost_le_of_windows windows
  rw [hstart, hend] at hcost
  omega

theorem rebalanced_crossing_budget_of_first_bound210 {M s C r p first : Nat} {balance : Int}
    (hM : 50000000 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (windows : trace.RebalancedGrowthWindows)
    (firstBudget : 64 * (3 * trace.totalCappedFirstPayment + 12166819) ≤ 61 * M) :
    (∑ i, (trace.event i).rebalancedNetCost) + (24 * (r - s) + 1091 : Nat) ≤ (M : Int) := by
  apply rebalanced_crossing_budget_of_windows210 ledger trace windows
  have hpath := residual_phase_balances210_path ledger
  have hC := canonical_horizon_bound_of_short_travel hpath short
  have hstate := moving_horizon_path_endpoint hpath
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hModd : M % 2 = 1 := canonical ▸ d_mod_two_eq_one_of_three_le (by omega)
  have hQ := fifty_million_sqrt_budget hM
  omega

abbrev RebalancedCrossingBudgetCondition210 : Prop :=
  PotentialCrossingBudgetCondition210 ResidualPhaseEvent210.rebalancedNetCost 1091

theorem target_of_rebalanced_crossing_budget_condition210 (bound : RebalancedCrossingBudgetCondition210) : Target :=
  target_of_twin_travel_from_fifty_million (twin_travel_of_potential_crossing_budget_condition210
    rebalanced_potential210_le moving_horizon_rebalanced_supported210 bound)

theorem unbounded_twin_primes_of_rebalanced_crossing_budget_condition210
    (bound : RebalancedCrossingBudgetCondition210) (N : Nat) :
    ∃ R : Nat, N < R ∧ IsGreaterTwinPrime R :=
  unbounded_greater_twin_primes_of_target (target_of_rebalanced_crossing_budget_condition210 bound) N

end A166944Research
