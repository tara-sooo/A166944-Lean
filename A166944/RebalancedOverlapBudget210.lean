import A166944.RebalancedFirstPaymentBudget210

/-! # A prefix budget for rebalanced demand intervals and signed credit -/

open Finset

namespace A166944Research

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

abbrev rebalancedDemand : Fin n → Nat := trace.costDemand trace.rebalancedCosts

def rebalancedTerminalWidth (i : Fin n) : Nat :=
  (3 * trace.rebalancedDemand i + 1) / 2

def rebalancedTerminalWindow (i : Fin n) : Finset Nat :=
  Ico ((trace.event i).horizon - trace.rebalancedTerminalWidth i) (trace.event i).horizon

private theorem rebalanced_terminal_width_le_period (i : Fin n) :
    trace.rebalancedTerminalWidth i ≤ Nat.lcm 210 (2 * d (trace.event i).hit) := by
  by_cases h : 0 < trace.rebalancedDemand i
  · have hpaid := trace.rebalanced_request_pays_period210 h
    change 3 * trace.rebalancedDemand i ≤ _ at hpaid
    unfold rebalancedTerminalWidth
    omega
  · have hz : trace.rebalancedDemand i = 0 := by omega
    simp [rebalancedTerminalWidth, hz]

private theorem rebalanced_terminal_width_le_window (i : Fin n) :
    trace.rebalancedTerminalWidth i ≤
      (trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon := by
  by_cases h : 0 < trace.rebalancedDemand i
  · exact (trace.rebalanced_terminal_width_le_period i).trans (trace.rebalanced_request_period210 h).2
  · have hz : trace.rebalancedDemand i = 0 := by omega
    simp [rebalancedTerminalWidth, hz]

theorem rebalanced_terminal_window_inside (i : Fin n) :
    trace.rebalancedTerminalWindow i ⊆ trace.growthWindow (trace.costAnchor trace.rebalancedCosts i) i := by
  have hwidth := trace.rebalanced_terminal_width_le_window i
  intro x hx
  simp only [rebalancedTerminalWindow, mem_Ico] at hx
  simp only [growthWindow, mem_Ico]
  omega

private theorem card_rebalanced_terminal_window (i : Fin n) :
    (trace.rebalancedTerminalWindow i).card = trace.rebalancedTerminalWidth i := by
  rw [rebalancedTerminalWindow, Nat.card_Ico]
  have hwidth := (trace.rebalanced_terminal_width_le_window i).trans (Nat.sub_le _ _)
  omega

theorem same_key_rebalanced_terminal_windows_disjoint {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    Disjoint (trace.rebalancedTerminalWindow i) (trace.rebalancedTerminalWindow j) := by
  let interval := trace.samePhaseInterval order key
  have hperiod := (same_phase_credit_interval_constraints210 interval).2.2.1
  rw [interval.same_increment] at hperiod
  have hwidth := (trace.rebalanced_terminal_width_le_period j).trans hperiod
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [rebalancedTerminalWindow, mem_Ico] at hx hy
  change trace.rebalancedTerminalWidth j ≤ (trace.event j).horizon - (trace.event i).horizon at hwidth
  omega

def rebalancedDemandUnion : Finset Nat := univ.biUnion trace.rebalancedTerminalWindow

theorem rebalanced_demand_union_subset :
    trace.rebalancedDemandUnion ⊆ Ico (D s) (D sf) := by
  intro x hx
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
  have ⟨hleft, hright⟩ := mem_Ico.mp (trace.rebalanced_terminal_window_inside i hi)
  exact mem_Ico.mpr ⟨(trace.event_horizon_between _).1.trans hleft,
    hright.trans (trace.event_horizon_between i).2⟩

theorem card_rebalanced_demand_union_le :
    trace.rebalancedDemandUnion.card ≤ D sf - D s := by
  rw [← Nat.card_Ico]
  exact card_le_card trace.rebalanced_demand_union_subset

/-- Each coordinate used by multiple demands contributes one unit for
each covering interval after the first. -/
def rebalancedOverlapWidth : Nat :=
  (∑ i, trace.rebalancedTerminalWidth i) - trace.rebalancedDemandUnion.card

theorem rebalanced_overlap_width_eq_sum_multiplicities :
    trace.rebalancedOverlapWidth = ∑ x ∈ trace.rebalancedDemandUnion,
      ((univ.filter fun i => x ∈ trace.rebalancedTerminalWindow i).card - 1) := by
  let U := trace.rebalancedDemandUnion
  let covering (x : Nat) := univ.filter fun i => x ∈ trace.rebalancedTerminalWindow i
  have hsum : (∑ i, trace.rebalancedTerminalWidth i) = ∑ x ∈ U, (covering x).card := by
    calc
      _ = ∑ i, ∑ x ∈ U, if x ∈ trace.rebalancedTerminalWindow i then (1 : Nat) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter, ← trace.card_rebalanced_terminal_window i]
        have hf : U.filter (fun x => x ∈ trace.rebalancedTerminalWindow i) =
            trace.rebalancedTerminalWindow i := by
          ext x
          simp only [mem_filter]
          exact ⟨And.right, fun h => ⟨mem_biUnion.mpr ⟨i, mem_univ _, h⟩, h⟩⟩
        rw [hf]
        simp
      _ = _ := by rw [Finset.sum_comm]; simp [covering]
  have hcover (x : Nat) (hx : x ∈ U) : 1 ≤ (covering x).card := by
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hxi⟩⟩
  have hsplit : (∑ x ∈ U, ((covering x).card - 1)) + U.card = ∑ x ∈ U, (covering x).card := by
    calc
      _ = (∑ x ∈ U, ((covering x).card - 1)) + ∑ _x ∈ U, (1 : Nat) := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x hx => Nat.sub_add_cancel (hcover x hx)
  change (∑ i, trace.rebalancedTerminalWidth i) - U.card = ∑ x ∈ U, ((covering x).card - 1)
  omega

theorem rebalanced_overlap_width_zero_of_disjoint_keys
    (disjoint : ∀ i j : Fin n, (trace.event i).phaseKey ≠ (trace.event j).phaseKey →
      Disjoint (trace.rebalancedTerminalWindow i) (trace.rebalancedTerminalWindow j)) :
    trace.rebalancedOverlapWidth = 0 := by
  have hdisjoint : (↑(univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      trace.rebalancedTerminalWindow := by
    intro i _ j _ hne
    by_cases hk : (trace.event i).phaseKey = (trace.event j).phaseKey
    · rcases lt_or_gt_of_ne hne with hij | hji
      · exact trace.same_key_rebalanced_terminal_windows_disjoint hij hk
      · exact (trace.same_key_rebalanced_terminal_windows_disjoint hji hk.symm).symm
    · exact disjoint i j hk
  unfold rebalancedOverlapWidth rebalancedDemandUnion
  rw [Finset.card_biUnion hdisjoint]
  simp only [trace.card_rebalanced_terminal_window, Nat.sub_self]

/-- Right endpoint of the latest earlier positive request with a
different key, or zero if there is none. -/
def rebalancedPriorDifferentHorizon (i : Fin n) : Nat :=
  (univ.filter fun j => j < i ∧ 0 < trace.rebalancedDemand j ∧
    (trace.event j).phaseKey ≠ (trace.event i).phaseKey).sup (fun j => (trace.event j).horizon)

/-- Duplicate width can only come from the part of each interval
that extends back beyond the latest earlier request of another key. -/
theorem rebalanced_overlap_width_le_prior_different :
    trace.rebalancedOverlapWidth ≤ ∑ i, (trace.rebalancedTerminalWidth i -
      ((trace.event i).horizon - trace.rebalancedPriorDifferentHorizon i)) := by
  let suffix (i : Fin n) :=
    Ico (max ((trace.event i).horizon - trace.rebalancedTerminalWidth i)
      (trace.rebalancedPriorDifferentHorizon i)) (trace.event i).horizon
  have hsub (i : Fin n) : suffix i ⊆ trace.rebalancedTerminalWindow i := by
    intro x hx
    obtain ⟨hl, hr⟩ := mem_Ico.mp hx
    exact mem_Ico.mpr ⟨(le_max_left _ _).trans hl, hr⟩
  have hordered {i j : Fin n} (hij : i < j) : Disjoint (suffix i) (suffix j) := by
    by_cases hk : (trace.event i).phaseKey = (trace.event j).phaseKey
    · exact (trace.same_key_rebalanced_terminal_windows_disjoint hij hk).mono (hsub i) (hsub j)
    · rw [Finset.disjoint_left]
      intro x hx hy
      have hpos : 0 < trace.rebalancedDemand i := by
        by_contra h
        have hz : trace.rebalancedDemand i = 0 := by omega
        have hm := hsub i hx
        simp [rebalancedTerminalWindow, rebalancedTerminalWidth, hz] at hm
      have hi : (trace.event i).horizon ≤ trace.rebalancedPriorDifferentHorizon j :=
        Finset.le_sup (f := fun k => (trace.event k).horizon)
          (mem_filter.mpr ⟨mem_univ _, hij, hpos, hk⟩)
      have hxlt := (mem_Ico.mp hx).2
      have hyle := (le_max_right _ _).trans (mem_Ico.mp hy).1
      exact (not_lt_of_ge (hi.trans hyle)) hxlt
  have hdisjoint : (↑(univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint suffix := by
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hordered hij
    · exact (hordered hji).symm
  have hcard : (∑ i, (suffix i).card) ≤ trace.rebalancedDemandUnion.card := by
    rw [← Finset.card_biUnion hdisjoint]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨i, hi, hsub i hxi⟩
  have hsplit : (∑ i, trace.rebalancedTerminalWidth i) = (∑ i, (suffix i).card) +
      ∑ i, (trace.rebalancedTerminalWidth i -
        ((trace.event i).horizon - trace.rebalancedPriorDifferentHorizon i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hw := (trace.rebalanced_terminal_width_le_window i).trans (Nat.sub_le _ _)
    rw [show (suffix i).card = (trace.event i).horizon -
      max ((trace.event i).horizon - trace.rebalancedTerminalWidth i)
        (trace.rebalancedPriorDifferentHorizon i) from Nat.card_Ico _ _]
    rw [max_def]
    split <;> omega
  unfold rebalancedOverlapWidth
  omega

theorem rebalanced_demand_width_identity :
    3 * (∑ i, trace.rebalancedDemand i) + (∑ i, trace.rebalancedDemand i % 2) =
      2 * (trace.rebalancedDemandUnion.card + trace.rebalancedOverlapWidth) := by
  have hcard := Finset.card_biUnion_le (s := univ) (t := trace.rebalancedTerminalWindow)
  simp only [trace.card_rebalanced_terminal_window] at hcard
  change trace.rebalancedDemandUnion.card ≤ _ at hcard
  have hwidth : trace.rebalancedDemandUnion.card + trace.rebalancedOverlapWidth =
      ∑ i, trace.rebalancedTerminalWidth i := by
    unfold rebalancedOverlapWidth
    omega
  rw [hwidth, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by unfold rebalancedTerminalWidth; omega

private def rebalancedEventsInsideUnion : Finset (Fin n) :=
  univ.filter fun i => trace.growthRequestRight i ∈ trace.rebalancedDemandUnion

def rebalancedUnionCredit : Nat :=
  ∑ i ∈ trace.rebalancedEventsInsideUnion, (-trace.rebalancedCosts i).toNat

private def rebalancedLargeIncrementCredit (i : Fin n) : Nat :=
  let event := trace.event i
  if 339 ≤ d event.hit ∧ 3 * (event.hit - event.start + 1) ≤ d event.hit - 1 then
    3 * (d event.hit - 1) - 1012
  else 0

private theorem rebalanced_large_increment_credit_le (i : Fin n) :
    trace.rebalancedLargeIncrementCredit i ≤ (-trace.rebalancedCosts i).toNat := by
  unfold rebalancedLargeIncrementCredit
  dsimp only
  split
  · rename_i h
    have hu : ¬ d (trace.event i).hit ∣ 210 := by
      intro hd
      have he := Nat.le_of_dvd (by decide : 0 < 210) hd
      have := h.1
      omega
    have hnet := (trace.event i).rebalanced_net_cost_le_outside_large_gaps210 hu h.2
    have hcost := (trace.event i).rebalanced_cost_le_net
    change _ ≤ (-(trace.event i).rebalancedCost).toNat
    omega
  · exact Nat.zero_le _

/-- Each large increment with a small relative gap guarantees negative
cost. Use it here only when the event is outside the demand union. -/
def rebalancedOutsideCredit : Nat :=
  ∑ i ∈ univ \ trace.rebalancedEventsInsideUnion, trace.rebalancedLargeIncrementCredit i

theorem rebalanced_union_and_outside_credit_le :
    trace.rebalancedUnionCredit + trace.rebalancedOutsideCredit ≤ ∑ i, (-trace.rebalancedCosts i).toNat := by
  have hsum := Finset.sum_sdiff (f := fun i => (-trace.rebalancedCosts i).toNat)
    (Finset.subset_univ trace.rebalancedEventsInsideUnion)
  have hout : trace.rebalancedOutsideCredit ≤
      ∑ i ∈ univ \ trace.rebalancedEventsInsideUnion, (-trace.rebalancedCosts i).toNat :=
    Finset.sum_le_sum fun i _ => trace.rebalanced_large_increment_credit_le i
  unfold rebalancedUnionCredit
  omega

/-- For increments at least 507 with a small relative gap, the
available negative credit covers at least the growth at those events. -/
theorem rebalanced_large_increment_growth_le_credit :
    (∑ i ∈ univ.filter (fun i => 507 ≤ d (trace.event i).hit ∧
      3 * ((trace.event i).hit - (trace.event i).start + 1) ≤ d (trace.event i).hit - 1),
        (d (trace.event i).hit - 1)) ≤ trace.rebalancedUnionCredit + trace.rebalancedOutsideCredit := by
  calc
    _ ≤ ∑ i, trace.rebalancedLargeIncrementCredit i := by
      refine (Finset.sum_le_sum ?_).trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      intro i hi
      obtain ⟨he, hgap⟩ := (mem_filter.mp hi).2
      rw [rebalancedLargeIncrementCredit, if_pos ⟨by omega, hgap⟩]
      omega
    _ = trace.rebalancedOutsideCredit + ∑ i ∈ trace.rebalancedEventsInsideUnion,
        trace.rebalancedLargeIncrementCredit i :=
      (Finset.sum_sdiff (Finset.subset_univ trace.rebalancedEventsInsideUnion)).symm
    _ ≤ _ := by
      rw [Nat.add_comm trace.rebalancedUnionCredit]
      exact Nat.add_le_add_left (Finset.sum_le_sum fun i _ => trace.rebalanced_large_increment_credit_le i) _

/-- Charge duplicate width, then subtract unused growth, rounding and
the negative costs available from the prefix. -/
def rebalancedOverlapAdjustment : Int :=
  2 * (trace.rebalancedOverlapWidth : Int) -
    2 * ((D sf - D s - trace.rebalancedDemandUnion.card : Nat) : Int) -
    ((∑ i, trace.rebalancedDemand i % 2 : Nat) : Int) -
    3 * ((trace.rebalancedUnionCredit + trace.rebalancedOutsideCredit : Nat) : Int)

theorem rebalanced_net_cost_le_of_overlap210 :
    3 * (∑ i, (trace.event i).rebalancedNetCost) ≤
      (3 * trace.totalCappedFirstPayment + 12163536 + 2 * (D sf - D s) : Nat) +
        trace.rebalancedOverlapAdjustment := by
  have hsplit : (∑ i, trace.rebalancedCosts i) =
      ((∑ i, (trace.rebalancedCosts i).toNat : Nat) : Int) -
        ((∑ i, (-trace.rebalancedCosts i).toNat : Nat) : Int) := by
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  have hpositive := trace.sum_cost_positive trace.rebalancedCosts
  change _ = trace.costStartupSum trace.rebalancedCosts + ∑ i, trace.rebalancedDemand i at hpositive
  have hstartup := trace.rebalanced_startup_cost_le
  have hwidth := trace.rebalanced_demand_width_identity
  have hcredit := trace.rebalanced_union_and_outside_credit_le
  have hunion := trace.card_rebalanced_demand_union_le
  rw [trace.sum_rebalanced_net_cost_split, hsplit]
  unfold rebalancedOverlapAdjustment
  omega

/-- Sufficient budget with the actual growth, crossing gap, and
potentials at the two endpoints. -/
def RebalancedCrossingPrefixBudget (M g firstUpper : Nat) : Prop :=
  (3 * firstUpper + 12163536 + 35 * (D sf - D s) + 72 * g +
      3 * rebalancedPotential210 s (D s) : Nat) + trace.rebalancedOverlapAdjustment <
    ((36 * (M + 1) + 3 * rebalancedPotential210 sf (D sf) : Nat) : Int)

end

end ResidualPhaseTrace210

/-- Convert the budget on a canonical prefix to the strict reverse of
the signed inequality forced by an actual first crossing. -/
theorem rebalanced_crossing_signed_of_prefix_budget210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (budget : trace.RebalancedCrossingPrefixBudget M (r - s) firstUpper) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hcost := trace.rebalanced_net_cost_le_of_overlap210
  unfold ResidualPhaseTrace210.RebalancedCrossingPrefixBudget at budget
  rw [hstart, hend] at hcost budget
  omega

theorem rebalanced_crossing_signed_of_refined_cutoff210
    {M s C r p first L : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance) (hL : 338 ≤ L)
    (budget : trace.RebalancedCrossingPrefixBudget M (r - s)
      (refinedFirstPaymentCutoffBound210 L C trace.growthAtLargeGaps)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have hend := (moving_horizon_path_endpoint (residual_phase_balances210_path ledger)).2.1
  have hU (i : Fin p) : (trace.event i).horizon ≤ C := hend ▸ (trace.event_horizon_between i).2.le
  exact rebalanced_crossing_signed_of_prefix_budget210 ledger trace
    (trace.refined_rebalanced_first_payment_bound210 L C hL hU) budget

/-- A single prefix budget gives the strict signed bound needed at an
actual first crossing. The first-payment upper bound can use the phase
cutoff or the exact first-payment sum. -/
theorem rebalanced_crossing_signed_of_overlap_budget210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 50000000 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (budget : 64 * ((3 * firstUpper + 12166819 : Nat) + trace.rebalancedOverlapAdjustment) ≤ (61 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hstate := moving_horizon_path_endpoint path
  have hC := canonical_horizon_bound_of_short_travel path short
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hModd := canonical ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
  have hgap := (Nat.mul_le_mul_left 1536 gap).trans (fifty_million_sqrt_budget hM)
  have hcost := trace.rebalanced_net_cost_le_of_overlap210
  rw [hstart, hstate.2.1] at hcost
  have hV := rebalanced_potential210_le (M + 2) (2 * M - 2) (by omega)
  omega

/-- The prefix budget restricted to the candidates from the finite
certificates and the two necessary growth bounds. -/
def RebalancedOverlapCrossingCondition210 : Prop :=
  ∀ {M s C r C' p first : Nat} {balance : Int},
    367232911 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance →
    IsMovingHorizonStep s C r C' → 2 * (s - (M + 2)) ≤ M → M < 2 * (r - (M + 2)) →
    r - s ≤ Nat.sqrt (4 * (3 * M + 4)) → IsAttainedPreviousMaximum M r →
    ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
      (∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) →
      M < 5 * (C - (2 * M - 2)) + 2 * (r - s) + 2 →
      M < 13 * trace.growthAtLargeGaps + 6 * (r - s) + 16 →
      trace.RebalancedCrossingPrefixBudget M (r - s) trace.totalCappedFirstPayment

theorem target_of_rebalanced_overlap_crossings210 (budget : RebalancedOverlapCrossingCondition210) : Target := by
  apply target_of_rebalanced_remaining_crossings210
  intro M s C r C' p first balance hM htwin canonical ledger step short crossing gap max trace delta growth large
  exact rebalanced_crossing_signed_of_prefix_budget210 ledger trace (Nat.le_refl _)
    (budget hM htwin canonical ledger step short crossing gap max trace delta growth large)

end A166944Research
