import A166944.RebalancedAnchorComponents210

/-! # Component allowances from horizon growth and negative costs -/

open Finset

namespace A166944Research
namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def rebalancedGrowthPeriodStart (i : Fin n) : Nat :=
  2 * (trace.event i).nextHorizon - trace.rebalancedPhasePeriodWidth i

def rebalancedGrowthPeriod (i : Fin n) : Finset Nat :=
  Ico (trace.rebalancedGrowthPeriodStart i) (2 * (trace.event i).nextHorizon)

private theorem growth_period_fits_anchor {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    trace.rebalancedPhasePeriodWidth i ≤
      2 * ((trace.event i).nextHorizon -
        (trace.event (trace.costAnchor trace.rebalancedCosts i)).nextHorizon) := by
  obtain ⟨order, phase⟩ := trace.cost_demand_anchor positive
  have h := trace.same_key_period_le_post_growth210 order phase
  unfold rebalancedPhasePeriodWidth rebalancedWindowGrowth at *
  omega

theorem rebalanced_growth_period_card210 {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    (trace.rebalancedGrowthPeriod i).card = trace.rebalancedPhasePeriodWidth i := by
  have h := trace.growth_period_fits_anchor positive
  rw [rebalancedGrowthPeriod, rebalancedGrowthPeriodStart, Nat.card_Ico]
  omega

theorem rebalanced_growth_period_subset210 {l r i : Fin n}
    (inside : i ∈ trace.rebalancedAnchorRequests
      (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)) :
    trace.rebalancedGrowthPeriod i ⊆ Ico (2 * (trace.event l).nextHorizon) (2 * (trace.event r).nextHorizon) := by
  have ⟨positive, hleft, hright⟩ := (mem_filter.mp inside).2
  have ha : (trace.event l).nextHorizon ≤ (trace.event (trace.costAnchor trace.rebalancedCosts i)).nextHorizon :=
    trace.rebalanced_next_horizon_mono210 (trace.rebalanced_credit_after_strict_mono210.le_iff_le.mp hleft)
  have hb : (trace.event i).nextHorizon ≤ (trace.event r).nextHorizon :=
    trace.rebalanced_next_horizon_mono210 (trace.rebalanced_credit_after_strict_mono210.le_iff_le.mp hright)
  intro x hx
  simp only [rebalancedGrowthPeriod, rebalancedGrowthPeriodStart, mem_Ico] at hx ⊢
  have h := trace.growth_period_fits_anchor positive
  exact ⟨by omega, by omega⟩

theorem rebalanced_growth_periods_disjoint_of_same_key210 {i j : Fin n} (order : i < j)
    (phase : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    Disjoint (trace.rebalancedGrowthPeriod i) (trace.rebalancedGrowthPeriod j) := by
  have hperiod := trace.same_key_period_le_post_growth210 order phase
  change _ ≤ (trace.event j).nextHorizon - (trace.event i).nextHorizon at hperiod
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [rebalancedGrowthPeriod, rebalancedGrowthPeriodStart, mem_Ico, rebalancedPhasePeriodWidth] at hx hy
  omega

/-- The terminal periods of requests on one key fit even when only
horizon growth is counted as capacity. -/
theorem rebalanced_anchor_growth_periods_fit_on_key210 {l r : Fin n}
    (selected : Finset (Fin n))
    (inside : selected ⊆ trace.rebalancedAnchorRequests
      (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r))
    (key : Nat × Fin 420) (same : ∀ i ∈ selected, (trace.event i).phaseKey = key) :
    (∑ i ∈ selected, trace.rebalancedPhasePeriodWidth i) ≤ 2 * trace.rebalancedWindowGrowth l r := by
  have hdisjoint : (selected : Set (Fin n)).PairwiseDisjoint trace.rebalancedGrowthPeriod := by
    intro i hi j hj hne
    have hkey := (same i hi).trans (same j hj).symm
    rcases lt_or_gt_of_ne hne with order | order
    · exact trace.rebalanced_growth_periods_disjoint_of_same_key210 order hkey
    · exact (trace.rebalanced_growth_periods_disjoint_of_same_key210 order hkey.symm).symm
  calc
    _ = ∑ i ∈ selected, (trace.rebalancedGrowthPeriod i).card :=
      Finset.sum_congr rfl fun i hi => (trace.rebalanced_growth_period_card210 (mem_filter.mp (inside hi)).2.1).symm
    _ = (selected.biUnion trace.rebalancedGrowthPeriod).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Ico (2 * (trace.event l).nextHorizon) (2 * (trace.event r).nextHorizon)).card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ hi => trace.rebalanced_growth_period_subset210 (inside hi)))
    _ = _ := by rw [Nat.card_Ico, rebalancedWindowGrowth, Nat.mul_sub]

private theorem rebalanced_anchor_growth_bound_of_long_keys {l r : Fin n} {scale rate keys : Nat}
    (few : (trace.rebalancedAnchorKeys (trace.rebalancedComponentRequests (l, r))).card ≤ keys)
    (long : ∀ i ∈ trace.rebalancedComponentRequests (l, r), trace.ReusedLong i)
    (localRate : ∀ i ∈ trace.rebalancedComponentRequests (l, r),
      scale * (111 * d (trace.event i).hit + 3141) ≤ rate * (420 * d (trace.event i).hit)) :
    scale * (3 * (∑ i ∈ trace.rebalancedComponentRequests (l, r), trace.rebalancedDemand i)) ≤
      (rate * keys) * (2 * trace.rebalancedWindowGrowth l r) := by
  let requests := trace.rebalancedComponentRequests (l, r)
  have h := trace.rebalanced_anchor_demand_scaled_le_of_key_rates210 requests
    (fun _ => rate) trace.rebalancedPhasePeriodWidth
    (fun key _ => trace.rebalanced_anchor_growth_periods_fit_on_key210 _ (filter_subset _ _) key
      (fun _ hi => (mem_filter.mp hi).2)) (scale := scale)
  have hlocal (i : Fin n) (hi : i ∈ requests) :
      scale * (3 * trace.rebalancedDemand i) ≤ rate * trace.rebalancedPhasePeriodWidth i := by
    have hp := (mem_filter.mp hi).2.1
    have hcost : trace.rebalancedDemand i ≤ 37 * d (trace.event i).hit + 1047 :=
      trace.rebalanced_demand_linear_cap hp
    rw [trace.rebalanced_phase_period_width_of_long hp (long i hi)]
    exact (Nat.mul_le_mul_left scale (by omega)).trans (localRate i hi)
  have hsum : (∑ _k ∈ trace.rebalancedAnchorKeys requests, rate) ≤ rate * keys := by
    calc
      _ = (trace.rebalancedAnchorKeys requests).card * rate := by simp
      _ ≤ keys * rate := Nat.mul_le_mul_right rate few
      _ = _ := Nat.mul_comm _ _
  exact (h hlocal).trans (Nat.mul_le_mul_right _ hsum)

theorem rebalanced_anchor_growth_bound_of_four_long_keys210 {l r : Fin n}
    (few : (trace.rebalancedAnchorKeys (trace.rebalancedComponentRequests (l, r))).card ≤ 4)
    (large : ∀ i ∈ trace.rebalancedComponentRequests (l, r), trace.ReusedLong i ∧ 109 ≤ d (trace.event i).hit) :
    3 * (3 * (∑ i ∈ trace.rebalancedComponentRequests (l, r), trace.rebalancedDemand i)) ≤
      8 * trace.rebalancedWindowGrowth l r := by
  have h := trace.rebalanced_anchor_growth_bound_of_long_keys (scale := 3) (rate := 1)
    few (fun i hi => (large i hi).1) (fun i hi => by have := (large i hi).2; omega)
  omega

theorem rebalanced_anchor_growth_bound_of_five_long_keys210 {l r : Fin n}
    (few : (trace.rebalancedAnchorKeys (trace.rebalancedComponentRequests (l, r))).card ≤ 5)
    (large : ∀ i ∈ trace.rebalancedComponentRequests (l, r), trace.ReusedLong i ∧ 393 ≤ d (trace.event i).hit) :
    6 * (3 * (∑ i ∈ trace.rebalancedComponentRequests (l, r), trace.rebalancedDemand i)) ≤
      17 * trace.rebalancedWindowGrowth l r := by
  have h := trace.rebalanced_anchor_growth_bound_of_long_keys (scale := 60) (rate := 17)
    few (fun i hi => (large i hi).1) (fun i hi => by have := (large i hi).2; omega)
  omega

def rebalancedComponentGrowthDebt (w : Fin n × Fin n) : Int :=
  3 * ((∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i : Nat) : Int) -
    2 * trace.rebalancedWindowGrowth w.1 w.2

def RebalancedAnchorComponents.unusedGrowth (cover : trace.RebalancedAnchorComponents) : Nat :=
  D sf - D s - ∑ w ∈ cover.windows, trace.rebalancedWindowGrowth w.1 w.2

private theorem rebalanced_component_events_disjoint (cover : trace.RebalancedAnchorComponents) :
    (cover.windows : Set (Fin n × Fin n)).PairwiseDisjoint (fun w => Ioc w.1 w.2) := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hi
  obtain ⟨hlo', hhi'⟩ := mem_Ioc.mp hj
  let j := max u.1 v.1
  have hjt : j < i := max_lt hlo hlo'
  have mono := trace.rebalanced_credit_after_strict_mono210
  exact (Finset.disjoint_left.mp (cover.disjoint hu hv hne))
    (mem_Ico.mpr ⟨mono.monotone (le_max_left _ _), mono (hjt.trans_le hhi)⟩)
    (mem_Ico.mpr ⟨mono.monotone (le_max_right _ _), mono (hjt.trans_le hhi')⟩)

private theorem rebalanced_selected_component_growth_eq_sum (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s)
    {windows : Finset (Fin n × Fin n)} (selected : windows ⊆ cover.windows) :
    (∑ w ∈ windows, trace.rebalancedWindowGrowth w.1 w.2) =
      ∑ i ∈ windows.biUnion (fun w => Ioc w.1 w.2), (d (trace.event i).hit - 1) := by
  have hdisjoint : (windows : Set (Fin n × Fin n)).PairwiseDisjoint (fun w => Ioc w.1 w.2) :=
    fun _ hu _ hv hne => trace.rebalanced_component_events_disjoint cover (selected hu) (selected hv) hne
  calc
    _ = ∑ w ∈ windows, ∑ i ∈ Ioc w.1 w.2, (d (trace.event i).hit - 1) :=
      Finset.sum_congr rfl fun w hw =>
        (trace.rebalanced_sum_growth_between_hits210 delta (cover.ordered w (selected hw)).le).symm
    _ = _ := (Finset.sum_biUnion hdisjoint).symm

theorem sum_rebalanced_component_growth_le210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    (∑ w ∈ cover.windows, trace.rebalancedWindowGrowth w.1 w.2) ≤ D sf - D s := by
  rw [trace.rebalanced_selected_component_growth_eq_sum cover delta (Finset.Subset.refl _)]
  calc
    _ ≤ ∑ i, (d (trace.event i).hit - 1) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := trace.sum_horizon_growth_of_delta210 delta

/-- Growth spent on a component is counted once. All negative costs
remain available in the sum over the entire prefix. -/
theorem rebalanced_credit_debt_eq_growth_debts210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    trace.rebalancedCreditDebt = (∑ w ∈ cover.windows, trace.rebalancedComponentGrowthDebt w) -
      2 * (cover.unusedGrowth : Int) - 3 * ((∑ i, trace.rebalancedNegativeCost i : Nat) : Int) := by
  have hgrowth := trace.sum_rebalanced_component_growth_le210 cover delta
  unfold rebalancedCreditDebt rebalancedTotalCredit rebalancedComponentGrowthDebt RebalancedAnchorComponents.unusedGrowth
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum,
    trace.sum_rebalanced_component_demands210 cover]
  omega

def rebalancedComponentGrowthAllowance (w : Fin n × Fin n) : Nat :=
  let requests := trace.rebalancedComponentRequests w
  let growth := trace.rebalancedWindowGrowth w.1 w.2
  if trace.rebalancedComponentGrowthDebt w ≤ 0 then 0
  else if requests.card = 2 then min 4052 (7 * growth / 4)
  else if requests.card = 3 then min 8368 (18 * growth / 5)
  else if (trace.rebalancedAnchorKeys requests).card ≤ 4 ∧
      (∀ i ∈ requests, trace.ReusedLong i ∧ 109 ≤ d (trace.event i).hit) then 2 * growth / 3
  else if (trace.rebalancedAnchorKeys requests).card ≤ 5 ∧
      (∀ i ∈ requests, trace.ReusedLong i ∧ 393 ≤ d (trace.event i).hit) then 5 * growth / 6
  else (trace.rebalancedComponentGrowthDebt w).toNat

theorem rebalanced_component_growth_debt_le_allowance210 (w : Fin n × Fin n) :
    trace.rebalancedComponentGrowthDebt w ≤ (trace.rebalancedComponentGrowthAllowance w : Int) := by
  rcases w with ⟨l, r⟩
  dsimp only [rebalancedComponentGrowthAllowance]
  let requests := trace.rebalancedComponentRequests (l, r)
  let growth := trace.rebalancedWindowGrowth l r
  let cost := 3 * (∑ i ∈ requests, trace.rebalancedDemand i)
  have hdebt : trace.rebalancedComponentGrowthDebt (l, r) = (cost : Int) - 2 * growth := by
    rfl
  split
  · rename_i h
    exact h
  rename_i positive
  rw [hdebt] at positive
  have deficit : 2 * growth < cost := by omega
  split
  · rename_i hcard
    change requests.card = 2 at hcard
    change _ ≤ ((min 4052 (7 * growth / 4) : Nat) : Int)
    rw [hdebt, min_def]
    obtain ⟨_, hshort, hrate, _⟩ := trace.rebalanced_anchor_pair_raw_deficit_bounds210 deficit hcard
    change cost ≤ 2 * growth + 4052 at hshort
    change 4 * cost ≤ 15 * growth at hrate
    split <;> omega
  · split
    · rename_i hcard
      change requests.card = 3 at hcard
      change _ ≤ ((min 8368 (18 * growth / 5) : Nat) : Int)
      rw [hdebt, min_def]
      obtain ⟨_, hshort, hrate, _⟩ := trace.rebalanced_anchor_triple_raw_deficit_bounds210 deficit hcard
      change cost ≤ 2 * growth + 8368 at hshort
      change 5 * cost ≤ 28 * growth at hrate
      split <;> omega
    · split
      · rename_i h4
        have h := trace.rebalanced_anchor_growth_bound_of_four_long_keys210 h4.1 h4.2
        change 3 * cost ≤ 8 * growth at h
        change _ ≤ ((2 * growth / 3 : Nat) : Int)
        rw [hdebt]
        omega
      · split
        · rename_i h5
          have h := trace.rebalanced_anchor_growth_bound_of_five_long_keys210 h5.1 h5.2
          change 6 * cost ≤ 17 * growth at h
          change _ ≤ ((5 * growth / 6 : Nat) : Int)
          rw [hdebt]
          omega
        · omega

def rebalancedComponentGrowthAdjustment (cover : trace.RebalancedAnchorComponents) : Int :=
  ((∑ w ∈ cover.windows, trace.rebalancedComponentGrowthAllowance w : Nat) : Int) -
    2 * (cover.unusedGrowth : Int) - 3 * ((∑ i, trace.rebalancedNegativeCost i : Nat) : Int)

theorem rebalanced_credit_debt_le_growth_allowance210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    trace.rebalancedCreditDebt ≤ trace.rebalancedComponentGrowthAdjustment cover := by
  have h := Finset.sum_le_sum (s := cover.windows)
    (fun w _ => trace.rebalanced_component_growth_debt_le_allowance210 w)
  rw [← Nat.cast_sum] at h
  rw [trace.rebalanced_credit_debt_eq_growth_debts210 cover delta]
  unfold rebalancedComponentGrowthAdjustment
  omega

private def growthDeficitWindowsBelow (cover : trace.RebalancedAnchorComponents) (L : Nat) :
    Finset (Fin n × Fin n) :=
  cover.windows.filter fun w =>
    0 < trace.rebalancedComponentGrowthDebt w ∧ trace.rebalancedWindowGrowth w.1 w.2 < L

def RebalancedAnchorComponents.deficitGrowthBelow {trace : ResidualPhaseTrace210 s sf [] n first balance}
    (cover : trace.RebalancedAnchorComponents) (L : Nat) : Nat :=
  ∑ w ∈ trace.growthDeficitWindowsBelow cover L, trace.rebalancedWindowGrowth w.1 w.2

theorem rebalanced_small_growth_deficit_width_le210 {w : Fin n × Fin n}
    (positive : 0 < trace.rebalancedComponentGrowthDebt w)
    (card : (trace.rebalancedComponentRequests w).card = 2 ∨ (trace.rebalancedComponentRequests w).card = 3) :
    trace.rebalancedWindowGrowth w.1 w.2 ≤ 21638 := by
  unfold rebalancedComponentGrowthDebt at positive
  have hdef : 2 * trace.rebalancedWindowGrowth w.1 w.2 <
      3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) := by omega
  rcases card with h2 | h3
  · have h := (trace.rebalanced_anchor_pair_raw_deficit_bounds210 hdef h2).1
    change 3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) ≤ 10188 at h
    omega
  · have h := (trace.rebalanced_anchor_triple_raw_deficit_bounds210 hdef h3).1
    change 3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) ≤ 43278 at h
    omega

/-- Growth inside a window shorter than the increment cutoff cannot
contribute to the tail of the first-payment estimate. -/
theorem growth_at_high_first_payments_add_deficit_growth_le210
    (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s)
    (L : Nat) :
    trace.growthAtHighFirstPayments L + cover.deficitGrowthBelow L ≤ D sf - D s := by
  let small := trace.growthDeficitWindowsBelow cover L
  let inside := small.biUnion fun w => Ioc w.1 w.2
  let high := trace.highFirstPaymentEvents L
  have hdisjoint : Disjoint high inside := by
    rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨w, hw, hiw⟩ := mem_biUnion.mp hj
    have hlarge := (mem_filter.mp hi).2.2
    have hw' := (mem_filter.mp hw).1
    have h := Finset.single_le_sum (f := fun k => d (trace.event k).hit - 1)
      (fun _ _ => Nat.zero_le _) hiw
    rw [trace.rebalanced_sum_growth_between_hits210 delta (cover.ordered w hw').le] at h
    change d (trace.event i).hit - 1 ≤ trace.rebalancedWindowGrowth w.1 w.2 at h
    have hsmall := (mem_filter.mp hw).2.2
    omega
  have hsubset : small ⊆ cover.windows := Finset.filter_subset _ _
  unfold growthAtHighFirstPayments RebalancedAnchorComponents.deficitGrowthBelow
  rw [trace.rebalanced_selected_component_growth_eq_sum cover delta hsubset]
  change (∑ i ∈ high, (d (trace.event i).hit - 1)) +
    (∑ i ∈ inside, (d (trace.event i).hit - 1)) ≤ _
  rw [← Finset.sum_union hdisjoint, ← trace.sum_horizon_growth_of_delta210 delta]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem refined_rebalanced_first_payment_bound_after_growth_deficits210
    (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s)
    {L U : Nat} (cutoff : 338 ≤ L) (horizon : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ refinedFirstPaymentGrowthBound210 L U
      (min trace.growthAtLargeGaps (D sf - D s - cover.deficitGrowthBelow L)) := by
  have h := trace.growth_at_high_first_payments_add_deficit_growth_le210 cover delta L
  have hhigh := trace.growth_at_high_first_payments_le_large_gaps210 cutoff
  have hmin := Nat.le_min.mpr ⟨hhigh, (by omega :
    trace.growthAtHighFirstPayments L ≤ D sf - D s - cover.deficitGrowthBelow L)⟩
  apply (trace.refined_rebalanced_first_payment_bound_of_high_growth210 L U (by omega) horizon).trans
  unfold refinedFirstPaymentGrowthBound210
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_left _ hmin)) _

end
end ResidualPhaseTrace210

theorem rebalanced_crossing_signed_of_component_growth_allowance210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (cover : trace.RebalancedAnchorComponents)
    (allowance : 10 * (3 * (firstUpper : Int) + trace.rebalancedComponentGrowthAdjustment cover) ≤ (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have h := trace.rebalanced_credit_debt_le_growth_allowance210 cover delta
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace firstBound (by omega)

theorem rebalanced_crossing_signed_of_joint_growth_budget210
    {M s C r p first L : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (cutoff : 338 ≤ L) (cover : trace.RebalancedAnchorComponents)
    (budget : 10 * (3 * (refinedFirstPaymentGrowthBound210 L C
      (min trace.growthAtLargeGaps (C - (2 * M - 2) - cover.deficitGrowthBelow L)) : Int) +
      trace.rebalancedComponentGrowthAdjustment cover) ≤ (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hU (i : Fin p) : (trace.event i).horizon ≤ C := hend ▸ (trace.event_horizon_between i).2.le
  have h := trace.refined_rebalanced_first_payment_bound_after_growth_deficits210 cover delta cutoff hU
  rw [hstart, hend] at h
  exact rebalanced_crossing_signed_of_component_growth_allowance210 hM canonical ledger short gap trace delta h cover budget

theorem rebalanced_crossing_signed_of_first_high_growth_at_338210
    {M s C r p first : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (budget : 10 * trace.rebalancedCreditDebt + 1230 * (trace.growthAtHighFirstPayments 338 : Int) +
      416620800 ≤ (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have hend := (moving_horizon_path_endpoint (residual_phase_balances210_path ledger)).2.1
  have hU (i : Fin p) : (trace.event i).horizon ≤ C := hend ▸ (trace.event_horizon_between i).2.le
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace
    (trace.rebalanced_first_payment_bound_at_338210 C hU) (by omega)

end A166944Research
