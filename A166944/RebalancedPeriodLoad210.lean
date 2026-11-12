import A166944.RebalancedComponentGrowth210
import Mathlib.Algebra.Order.Floor.Div

/-! # Weighted overlap of phase periods -/

open Finset

namespace A166944Research
namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- Spread the scaled demand over its full terminal period, rounding
the load per unit up in sixtieths. -/
def rebalancedPeriodWeight (i : Fin n) : Nat :=
  (60 * (3 * trace.rebalancedDemand i)) ⌈/⌉ trace.rebalancedPhasePeriodWidth i

private theorem rebalanced_phase_period_width_pos (i : Fin n) : 0 < trace.rebalancedPhasePeriodWidth i := by
  have he := (trace.event i).step.2.2.2.1
  unfold rebalancedPhasePeriodWidth
  exact Nat.mul_pos (by decide) (Nat.lcm_pos (by decide) (by omega))

theorem rebalanced_period_weight_le210 {i : Fin n} {rate : Nat}
    (bound : 60 * (3 * trace.rebalancedDemand i) ≤ rate * trace.rebalancedPhasePeriodWidth i) :
    trace.rebalancedPeriodWeight i ≤ rate := by
  unfold rebalancedPeriodWeight
  exact (ceilDiv_le_iff_le_mul (trace.rebalanced_phase_period_width_pos i)).2
    (by simpa only [Nat.mul_comm (trace.rebalancedPhasePeriodWidth i) rate] using bound)

theorem rebalanced_period_weight_le_of_long109_210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (long : trace.ReusedLong i) (large : 109 ≤ d (trace.event i).hit) :
    trace.rebalancedPeriodWeight i ≤ 20 := by
  apply trace.rebalanced_period_weight_le210
  have h : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
    trace.rebalanced_demand_linear_cap positive
  rw [trace.rebalanced_phase_period_width_of_long positive long]
  omega

theorem rebalanced_period_weight_le_of_long143_210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (long : trace.ReusedLong i) (large : 143 ≤ d (trace.event i).hit) :
    trace.rebalancedPeriodWeight i ≤ 19 := by
  apply trace.rebalanced_period_weight_le210
  have h : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
    trace.rebalanced_demand_linear_cap positive
  rw [trace.rebalanced_phase_period_width_of_long positive long]
  omega

theorem rebalanced_period_weight_le_of_long393_210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (long : trace.ReusedLong i) (large : 393 ≤ d (trace.event i).hit) :
    trace.rebalancedPeriodWeight i ≤ 17 := by
  apply trace.rebalanced_period_weight_le210
  have h : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
    trace.rebalanced_demand_linear_cap positive
  rw [trace.rebalanced_phase_period_width_of_long positive long]
  omega

private def nonlongDemandCap (e : Nat) : Nat :=
  if e ∈ rebalancedPairIncrements210 then min (startupWeightAtCap210 1036 e) (rebalancedPairCostCap210 e)
  else startupWeightAtCap210 1036 e

set_option maxRecDepth 16384 in
private theorem nonlong_period_cap_checked :
    ∀ e : Fin 160, 1 < e.val → e.val % 2 = 1 → ¬ e.val ∣ 210 →
      60 * (3 * nonlongDemandCap e.val) ≤ 46 * (2 * Nat.lcm 210 (2 * e.val)) := by
  decide +kernel

theorem rebalanced_period_weight_le_of_nonlong210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (nonlong : ¬ trace.ReusedLong i) :
    trace.rebalancedPeriodWeight i ≤ 46 := by
  let event := trace.event i
  let e := d event.hit
  have hcost := trace.cost_demand_eq_cost positive
  change trace.rebalancedDemand i = event.rebalancedCost.toNat at hcost
  have hpositive : 0 < event.rebalancedCost := by omega
  have hstartup := (adjusted_phase_cost_weight_of_bound210 event (by decide : 1036 ≤ 1120)
    nonlong hpositive (event.rebalanced_cost_le_of_positive hpositive)).2
  have hcap : trace.rebalancedDemand i ≤ nonlongDemandCap e := by
    unfold nonlongDemandCap
    split
    · rename_i h
      exact Nat.le_min.mpr ⟨hcost.trans_le hstartup, hcost.trans_le (event.rebalanced_cost_le_pair_cap210 hpositive h)⟩
    · exact hcost.trans_le hstartup
  have hsmall : e ≤ 159 := (trace.rebalanced_demand_nonlong_bounds positive nonlong).1
  have hodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le (by have := event.step.1.1; have := event.step.2.1; omega)
  have htested := nonlong_period_cap_checked ⟨e, by omega⟩ event.step.2.2.2.1 hodd
    (event.rebalanced_cost_positive_unsupported hpositive)
  exact trace.rebalanced_period_weight_le210
    ((Nat.mul_le_mul_left 60 (Nat.mul_le_mul_left 3 hcap)).trans htested)

def rebalancedPeriodsAt (w : Fin n × Fin n) (x : Nat) : Finset (Fin n) :=
  (trace.rebalancedComponentRequests w).filter fun i => x ∈ trace.rebalancedGrowthPeriod i

def rebalancedPeriodLoad (w : Fin n × Fin n) (x : Nat) : Nat :=
  ∑ i ∈ trace.rebalancedPeriodsAt w x, trace.rebalancedPeriodWeight i

def rebalancedPeriodExcess (w : Fin n × Fin n) : Nat :=
  ∑ x ∈ Ico (2 * (trace.event w.1).nextHorizon) (2 * (trace.event w.2).nextHorizon),
    (trace.rebalancedPeriodLoad w x - 85)

theorem rebalanced_period_keys_injective_at210 (w : Fin n × Fin n) (x : Nat) :
    Set.InjOn (fun i => (trace.event i).phaseKey) (trace.rebalancedPeriodsAt w x : Set (Fin n)) := by
  intro i hi j hj key
  by_contra hne
  have hxi := (mem_filter.mp hi).2
  have hxj := (mem_filter.mp hj).2
  rcases lt_or_gt_of_ne hne with h | h
  · exact (Finset.disjoint_left.mp (trace.rebalanced_growth_periods_disjoint_of_same_key210 h key)) hxi hxj
  · exact (Finset.disjoint_left.mp (trace.rebalanced_growth_periods_disjoint_of_same_key210 h key.symm)) hxj hxi

theorem sum_rebalanced_period_load210 (w : Fin n × Fin n) :
    (∑ x ∈ Ico (2 * (trace.event w.1).nextHorizon) (2 * (trace.event w.2).nextHorizon),
      trace.rebalancedPeriodLoad w x) =
      ∑ i ∈ trace.rebalancedComponentRequests w,
        trace.rebalancedPhasePeriodWidth i * trace.rebalancedPeriodWeight i := by
  let window := Ico (2 * (trace.event w.1).nextHorizon) (2 * (trace.event w.2).nextHorizon)
  simp only [rebalancedPeriodLoad, rebalancedPeriodsAt, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ x ∈ window, if x ∈ trace.rebalancedGrowthPeriod i then trace.rebalancedPeriodWeight i else 0) = _
  rw [← Finset.sum_filter]
  have hsubset := trace.rebalanced_growth_period_subset210 (l := w.1) (r := w.2) hi
  have hfilter : window.filter (· ∈ trace.rebalancedGrowthPeriod i) = trace.rebalancedGrowthPeriod i := by
    ext x
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hsubset h, h⟩⟩
  rw [hfilter, Finset.sum_const, trace.rebalanced_growth_period_card210 (mem_filter.mp hi).2.1]
  simp

def rebalancedPeriodGrowthDebt (w : Fin n × Fin n) : Int :=
  ((∑ i ∈ trace.rebalancedComponentRequests w,
    trace.rebalancedPhasePeriodWidth i * trace.rebalancedPeriodWeight i : Nat) : Int) -
    120 * trace.rebalancedWindowGrowth w.1 w.2

theorem rebalanced_component_growth_debt_scaled_le_period_debt210 (w : Fin n × Fin n) :
    60 * trace.rebalancedComponentGrowthDebt w ≤ trace.rebalancedPeriodGrowthDebt w := by
  have hload : 60 * (3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i)) ≤
      ∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedPhasePeriodWidth i * trace.rebalancedPeriodWeight i := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (ceilDiv_le_iff_le_mul (trace.rebalanced_phase_period_width_pos i)).1
      (show trace.rebalancedPeriodWeight i ≤ trace.rebalancedPeriodWeight i from le_rfl)
  unfold rebalancedComponentGrowthDebt rebalancedPeriodGrowthDebt
  omega

theorem rebalanced_period_debt_le_excess210 (w : Fin n × Fin n) :
    trace.rebalancedPeriodGrowthDebt w ≤
      (50 * trace.rebalancedWindowGrowth w.1 w.2 + trace.rebalancedPeriodExcess w : Nat) := by
  let window := Ico (2 * (trace.event w.1).nextHorizon) (2 * (trace.event w.2).nextHorizon)
  have hcard : window.card = 2 * trace.rebalancedWindowGrowth w.1 w.2 := by
    rw [show window = _ from rfl, Nat.card_Ico, rebalancedWindowGrowth, Nat.mul_sub]
  have hcap : (∑ x ∈ window, trace.rebalancedPeriodLoad w x) ≤
      85 * window.card + trace.rebalancedPeriodExcess w := by
    calc
      _ ≤ ∑ x ∈ window, (85 + (trace.rebalancedPeriodLoad w x - 85)) :=
        Finset.sum_le_sum fun x _ => by omega
      _ = _ := by simp [rebalancedPeriodExcess, window, Finset.sum_add_distrib, Nat.mul_comm]
  rw [trace.sum_rebalanced_period_load210] at hcap
  unfold rebalancedPeriodGrowthDebt
  omega

theorem rebalanced_component_growth_debt_scaled_le_period_excess210 (w : Fin n × Fin n) :
    60 * trace.rebalancedComponentGrowthDebt w ≤
      (50 * trace.rebalancedWindowGrowth w.1 w.2 + trace.rebalancedPeriodExcess w : Nat) :=
  (trace.rebalanced_component_growth_debt_scaled_le_period_debt210 w).trans (trace.rebalanced_period_debt_le_excess210 w)

/-- A nonempty set of covering periods has a latest left endpoint.
Every period covering x covers that endpoint too. -/
theorem rebalanced_period_load_le_of_start_bounds210 (w : Fin n × Fin n) {rate : Nat}
    (bounds : ∀ i ∈ trace.rebalancedComponentRequests w,
      trace.rebalancedPeriodLoad w (trace.rebalancedGrowthPeriodStart i) ≤ rate) (x : Nat) :
    trace.rebalancedPeriodLoad w x ≤ rate := by
  let covering := trace.rebalancedPeriodsAt w x
  rcases covering.eq_empty_or_nonempty with h | h
  · simp [rebalancedPeriodLoad, ← show covering = trace.rebalancedPeriodsAt w x from rfl, h]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image covering trace.rebalancedGrowthPeriodStart h
  have ⟨hreq, hxi⟩ := mem_filter.mp hi
  have hsubset : covering ⊆ trace.rebalancedPeriodsAt w (trace.rebalancedGrowthPeriodStart i) := by
    intro j hj
    have ⟨hjr, hxj⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hjr, mem_Ico.mpr ⟨hmax j hj, (mem_Ico.mp hxi).1.trans_lt (mem_Ico.mp hxj).2⟩⟩
  exact (Finset.sum_le_sum_of_subset hsubset).trans (bounds i hreq)

theorem rebalanced_period_excess_eq_zero_of_start_bounds210 (w : Fin n × Fin n)
    (bounds : ∀ i ∈ trace.rebalancedComponentRequests w,
      trace.rebalancedPeriodLoad w (trace.rebalancedGrowthPeriodStart i) ≤ 85) :
    trace.rebalancedPeriodExcess w = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  exact Nat.sub_eq_zero_of_le (trace.rebalanced_period_load_le_of_start_bounds210 w bounds x)

/-- Five simultaneously active periods of sufficiently large long
reuses fit the rate even when the window has many more keys. -/
theorem rebalanced_period_excess_eq_zero_of_five_long_overlaps210 (w : Fin n × Fin n)
    (large : ∀ i ∈ trace.rebalancedComponentRequests w, trace.ReusedLong i ∧ 393 ≤ d (trace.event i).hit)
    (depth : ∀ i ∈ trace.rebalancedComponentRequests w,
      (trace.rebalancedPeriodsAt w (trace.rebalancedGrowthPeriodStart i)).card ≤ 5) :
    trace.rebalancedPeriodExcess w = 0 := by
  apply trace.rebalanced_period_excess_eq_zero_of_start_bounds210 w
  intro i hi
  let covering := trace.rebalancedPeriodsAt w (trace.rebalancedGrowthPeriodStart i)
  calc
    _ ≤ ∑ _j ∈ covering, (17 : Nat) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hreq, _⟩ := mem_filter.mp hj
      obtain ⟨hlong, he⟩ := large j hreq
      exact trace.rebalanced_period_weight_le_of_long393_210 (mem_filter.mp hreq).2.1 hlong he
    _ = 17 * covering.card := by simp [Nat.mul_comm]
    _ ≤ 85 := Nat.mul_le_mul_left 17 (depth i hi)

theorem rebalanced_period_load_le_mixed_count210 (w : Fin n × Fin n) (x : Nat)
    (large : ∀ i ∈ trace.rebalancedPeriodsAt w x, trace.ReusedLong i → 143 ≤ d (trace.event i).hit) :
    trace.rebalancedPeriodLoad w x ≤
      19 * ((trace.rebalancedPeriodsAt w x).filter trace.ReusedLong).card +
      46 * ((trace.rebalancedPeriodsAt w x).filter fun i => ¬ trace.ReusedLong i).card := by
  let active := trace.rebalancedPeriodsAt w x
  let long := active.filter trace.ReusedLong
  let nonlong := active.filter fun i => ¬ trace.ReusedLong i
  have hlong : (∑ i ∈ long, trace.rebalancedPeriodWeight i) ≤ 19 * long.card := by
    calc
      _ ≤ ∑ _i ∈ long, (19 : Nat) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hin, hl⟩ := mem_filter.mp hi
        have hp := (mem_filter.mp (mem_filter.mp hin).1).2.1
        exact trace.rebalanced_period_weight_le_of_long143_210 hp hl (large i hin hl)
      _ = _ := by simp [Nat.mul_comm]
  have hnonlong : (∑ i ∈ nonlong, trace.rebalancedPeriodWeight i) ≤ 46 * nonlong.card := by
    calc
      _ ≤ ∑ _i ∈ nonlong, (46 : Nat) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hin, hn⟩ := mem_filter.mp hi
        exact trace.rebalanced_period_weight_le_of_nonlong210 (mem_filter.mp (mem_filter.mp hin).1).2.1 hn
      _ = _ := by simp [Nat.mul_comm]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := active) trace.ReusedLong trace.rebalancedPeriodWeight
  change (∑ i ∈ long, trace.rebalancedPeriodWeight i) + (∑ i ∈ nonlong, trace.rebalancedPeriodWeight i) =
    trace.rebalancedPeriodLoad w x at hsplit
  change _ ≤ 19 * long.card + 46 * nonlong.card
  omega

/-- Two large long periods and one other period can share a
coordinate, independent of how many keys the whole window uses. -/
theorem rebalanced_period_excess_eq_zero_of_mixed_overlaps210 (w : Fin n × Fin n)
    (large : ∀ i ∈ trace.rebalancedComponentRequests w, trace.ReusedLong i → 143 ≤ d (trace.event i).hit)
    (depth : ∀ i ∈ trace.rebalancedComponentRequests w,
      let active := trace.rebalancedPeriodsAt w (trace.rebalancedGrowthPeriodStart i)
      (active.filter trace.ReusedLong).card ≤ 2 ∧ (active.filter fun j => ¬ trace.ReusedLong j).card ≤ 1) :
    trace.rebalancedPeriodExcess w = 0 := by
  apply trace.rebalanced_period_excess_eq_zero_of_start_bounds210 w
  intro i hi
  have h := trace.rebalanced_period_load_le_mixed_count210 w (trace.rebalancedGrowthPeriodStart i)
    (fun j hj => large j (mem_filter.mp hj).1)
  have ⟨h2, h1⟩ := depth i hi
  omega

/-- Keep the signed period surplus when it improves the previous
allowance. All negative costs are credited once. -/
def rebalancedPeriodCreditAllowance (cover : trace.RebalancedAnchorComponents) : Int :=
  (∑ w ∈ cover.windows, min (60 * (trace.rebalancedComponentGrowthAllowance w : Int))
    (trace.rebalancedPeriodGrowthDebt w)) -
    120 * cover.unusedGrowth - 180 * ((∑ i, trace.rebalancedNegativeCost i : Nat) : Int)

theorem rebalanced_credit_debt_scaled_le_period_allowance210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    60 * trace.rebalancedCreditDebt ≤ trace.rebalancedPeriodCreditAllowance cover := by
  have hlocal (w : Fin n × Fin n) :
      60 * trace.rebalancedComponentGrowthDebt w ≤
        min (60 * (trace.rebalancedComponentGrowthAllowance w : Int)) (trace.rebalancedPeriodGrowthDebt w) := by
    have h := trace.rebalanced_component_growth_debt_le_allowance210 w
    exact le_min (by omega) (trace.rebalanced_component_growth_debt_scaled_le_period_debt210 w)
  have hsum := Finset.sum_le_sum (s := cover.windows) (fun w _ => hlocal w)
  rw [← Finset.mul_sum] at hsum
  rw [trace.rebalanced_credit_debt_eq_growth_debts210 cover delta]
  unfold rebalancedPeriodCreditAllowance
  omega

theorem rebalanced_credit_debt_scaled_le_horizon_and_period_excess210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    60 * trace.rebalancedCreditDebt ≤ (50 * (D sf - D s) + (∑ w ∈ cover.windows, trace.rebalancedPeriodExcess w) : Nat) -
      170 * (cover.unusedGrowth : Int) - 180 * ((∑ i, trace.rebalancedNegativeCost i : Nat) : Int) := by
  have hdebt := trace.rebalanced_credit_debt_scaled_le_period_allowance210 cover delta
  have hgrowth := trace.sum_rebalanced_component_growth_le210 cover delta
  have hsum : (∑ w ∈ cover.windows, min (60 * (trace.rebalancedComponentGrowthAllowance w : Int))
      (trace.rebalancedPeriodGrowthDebt w)) ≤
      (50 * (∑ w ∈ cover.windows, trace.rebalancedWindowGrowth w.1 w.2) +
        ∑ w ∈ cover.windows, trace.rebalancedPeriodExcess w : Nat) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Nat.cast_sum]
    exact Finset.sum_le_sum fun w _ => (min_le_right _ _).trans (trace.rebalanced_period_debt_le_excess210 w)
  unfold rebalancedPeriodCreditAllowance RebalancedAnchorComponents.unusedGrowth at hdebt
  unfold RebalancedAnchorComponents.unusedGrowth
  omega

end
end ResidualPhaseTrace210

theorem rebalanced_crossing_signed_of_period_and_first_gap_budget210
    {M s C r p first : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (cover : trace.RebalancedAnchorComponents)
    (budget : trace.rebalancedPeriodCreditAllowance cover +
      (180 * (13887360 + 37 * trace.growthAtHighFirstPayments 338 +
        48 * (trace.highFirstPaymentEvents 338).card + 1036 * (trace.highFirstPaymentRunEnds 338).card) : Nat) -
        4320 * (trace.highFirstPaymentGapShortfall 338 : Int) ≤ (54 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have hdebt := trace.rebalanced_credit_debt_scaled_le_period_allowance210 cover delta
  have hfirst := trace.rebalanced_first_payment_bound_of_gap_shortfall_at_338210
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace le_rfl (by omega)

/-- At sufficiently large records, a bounded integral of the overload
above 85 sixtieths suffices for the signed crossing bound. -/
theorem rebalanced_crossing_signed_of_period_excess_eventually210 :
    ∃ threshold : Nat, ∀ {M s C r p first : Nat} {balance : Int},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
        (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M → r - s ≤ Nat.sqrt (4 * (3 * M + 4)) →
      ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
        (∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) →
        ∀ cover : trace.RebalancedAnchorComponents,
          (∑ w ∈ cover.windows, trace.rebalancedPeriodExcess w) + 300 ≤ 2 * M →
          (∑ i, (trace.event i).rebalancedNetCost) +
            (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
              ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  obtain ⟨B, hB⟩ := canonical_first_prime_phase_travel_sublinear 420 2160 (by decide)
  refine ⟨max 367232911 B, ?_⟩
  intro M s C r p first balance hM canonical ledger short gap trace delta cover excess
  obtain ⟨_, phase⟩ := residual_phase_balances210_original ledger
  have hfirst : 2160 * first ≤ M := hB ((le_max_right 367232911 B).trans hM) canonical phase short
  have hpay : trace.totalCappedFirstPayment ≤ 24 * first :=
    trace.total_capped_first_payment_le.trans (Nat.mul_le_mul_left 24 trace.scaled_first_travel_le)
  have path := residual_phase_balances210_path ledger
  have hC := canonical_horizon_bound_of_short_travel path short
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hdebt := trace.rebalanced_credit_debt_scaled_le_horizon_and_period_excess210 cover delta
  rw [hstart, hend] at hdebt
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 ((le_max_left 367232911 B).trans hM)
    canonical ledger short gap trace le_rfl (by omega)

end A166944Research
