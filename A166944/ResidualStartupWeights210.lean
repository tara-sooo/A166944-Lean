import A166944.ResidualIntervalBudget210
import A166944.ResidualAdjustedCosts210

/-! # Startup bounds by increment and reachable phase -/

open Finset

namespace A166944Research

private def startupDivisor210 (e : Nat) : Option Nat :=
  [3, 5, 7, 11, 13].find? (fun f => decide (f < e ∧ f ∣ e))

private def startupTravelCap210 (e : Nat) : Nat :=
  (startupDivisor210 e).elim 240 (fun f => 48 * f)

def residualStartupWeight210 (e : Nat) : Nat :=
  min 1478 (1326 + startupTravelCap210 e - 11 * e)

set_option maxRecDepth 16384 in
private theorem startup_divisor_none_prime :
    ∀ e : Fin 170, 1 < e.val → e.val % 2 = 1 → startupDivisor210 e.val = none →
      NoProperFactor e.val := by
  decide +kernel

private theorem startup_gap_le_travel_cap (event : ResidualPhaseEvent210)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen))
    (hsize : d event.hit ≤ 169) :
    24 * (event.hit - event.start) ≤ startupTravelCap210 (d event.hit) + 24 * event.firstGap := by
  let e := d event.hit
  have he : 1 < e := event.step.2.2.2.1
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have heodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  change e ≤ 169 at hsize
  change _ ≤ startupTravelCap210 e + _
  cases hdiv : startupDivisor210 e with
  | none =>
    have hp : NoProperFactor e := startup_divisor_none_prime ⟨e, by omega⟩ he heodd hdiv
    simp only [startupTravelCap210, hdiv, Option.elim_none]
    by_cases hg : 10 < event.hit - event.start
    · have hfirst : IsFirstLongPrimePhase residualHorizonPhase210 event.seen event.start event.horizon event.hit :=
        ⟨hg, hp, fun h => hnew ⟨⟨hg, hp⟩, h⟩⟩
      simp only [ResidualPhaseEvent210.firstGap, firstLongPrimePhaseGap, if_pos hfirst]
      omega
    · omega
  | some f =>
    have hf := List.find?_some hdiv
    have hfd : f < e ∧ f ∣ e := of_decide_eq_true hf
    have hmem : f ∈ [3, 5, 7, 11, 13] := List.mem_of_find?_eq_some hdiv
    have hf1 : 1 < f := by simp at hmem; omega
    have hle := moving_horizon_step_gap_le_twice_increment_factor event.step hf1 hfd.2
    simp only [startupTravelCap210, hdiv, Option.elim_some]
    omega

theorem residual_phase_startup_weight210 (event : ResidualPhaseEvent210)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen))
    (hpos : 0 < event.cost) :
    event.cost.toNat ≤ residualStartupWeight210 (d event.hit) := by
  have hbounds := residual_phase_startup_bounds210 (phase := residualHorizonPhase210)
    (seen := event.seen) event.step (fun ⟨hg, hp, hs⟩ => hnew ⟨⟨hg, hp⟩, hs⟩) hpos
  change d event.hit ≤ 169 ∧ event.cost.toNat ≤ 1478 at hbounds
  have hgap := startup_gap_le_travel_cap event hnew hbounds.1
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds event.hit event.nextHorizon heven).2
  have hraw := event.positive_unsupported hpos
  refine Nat.le_min.mpr ⟨hbounds.2, ?_⟩
  simp only [ResidualPhaseEvent210.cost, residualPhaseSeparatorBalance210, if_neg hraw]
  unfold ResidualPhaseEvent210.firstGap at hgap
  omega

private def startupPhaseSlots210 (e : Nat) : Nat := 2 * (210 / (2 * Nat.gcd e 210))

set_option maxRecDepth 16384 in
theorem residual_startup_weight_total210 :
    (∑ e ∈ residualStartupIncrements210, startupPhaseSlots210 e * residualStartupWeight210 e) =
      6181254 := by
  unfold residualStartupIncrements210
  decide +kernel

private theorem gcd_of_event_odd (event : ResidualPhaseEvent210) :
    Nat.gcd (d event.hit) 210 % 2 = 1 := by
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have h := d_mod_two_eq_one_of_three_le hr
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (d event.hit) 210
  rw [hk, Nat.mul_mod] at h
  by_contra he
  have hz : Nat.gcd (d event.hit) 210 % 2 = 0 := by omega
  simp [hz] at h

private theorem twice_gcd_dvd_210 (event : ResidualPhaseEvent210) :
    2 * Nat.gcd (d event.hit) 210 ∣ 210 := by
  let g := Nat.gcd (d event.hit) 210
  have hg : g % 2 = 1 := gcd_of_event_odd event
  have hc : Nat.Coprime 2 g := by
    change Nat.gcd 2 g = 1
    rw [Nat.gcd_rec, hg, Nat.gcd_one_left]
  exact hc.mul_dvd_of_dvd_of_dvd (by decide : 2 ∣ 210) (Nat.gcd_dvd_right _ _)

private theorem horizon_mod_twice_gcd (event : ResidualPhaseEvent210) :
    event.horizon % (2 * Nat.gcd (d event.hit) 210) =
      if Nat.gcd (d event.hit) 210 = 1 then 0
      else if event.hit % 2 = 0 then Nat.gcd (d event.hit) 210 + 1
      else Nat.gcd (d event.hit) 210 - 1 := by
  let g := Nat.gcd (d event.hit) 210
  have hg : g % 2 = 1 := gcd_of_event_odd event
  by_cases h : g = 1
  · have heven := event.step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le event.step.1.1
    change event.horizon % (2 * g) = if g = 1 then 0 else _
    simp [h, heven]
  · have hgt : 2 < g := by omega
    have hd : g ∣ d event.hit := Nat.gcd_dvd_left _ _
    change event.horizon % (2 * g) = if g = 1 then 0 else _
    rcases moving_horizon_factor_event_residues event.step hgt hd with
      ⟨hp, _, hC⟩ | ⟨hp, _, hC⟩
    · simp only [if_neg h, if_pos hp]
      exact hC
    · have hno : event.hit % 2 ≠ 0 := by omega
      simp only [if_neg h, if_neg hno]
      exact hC

private def startupPhaseIndex210 (event : ResidualPhaseEvent210) : Nat :=
  2 * (event.horizon % 210 / (2 * Nat.gcd (d event.hit) 210)) + event.hit % 2

private theorem startup_phase_index_lt (event : ResidualPhaseEvent210) :
    startupPhaseIndex210 event < startupPhaseSlots210 (d event.hit) := by
  let P := 2 * Nat.gcd (d event.hit) 210
  let c := event.horizon % 210
  have hc : c < 210 := Nat.mod_lt _ (by decide)
  have hd : P ∣ 210 := twice_gcd_dvd_210 event
  have hq : c / P < 210 / P := by
    by_contra h
    have hmul := Nat.mul_le_mul_right P (Nat.le_of_not_gt h)
    rw [Nat.div_mul_cancel hd] at hmul
    have := Nat.div_mul_le_self c P
    omega
  change 2 * (c / P) + event.hit % 2 < 2 * (210 / P)
  omega

private theorem startup_phase_index_eq {a b : ResidualPhaseEvent210}
    (he : d a.hit = d b.hit) (hi : startupPhaseIndex210 a = startupPhaseIndex210 b) :
    a.horizon % 210 = b.horizon % 210 ∧ a.hit % 2 = b.hit % 2 := by
  let P := 2 * Nat.gcd (d a.hit) 210
  have hP : P ∣ 210 := twice_gcd_dvd_210 a
  unfold startupPhaseIndex210 at hi
  rw [← he] at hi
  change 2 * (a.horizon % 210 / P) + a.hit % 2 =
    2 * (b.horizon % 210 / P) + b.hit % 2 at hi
  have hp : a.hit % 2 = b.hit % 2 := by omega
  have hq : a.horizon % 210 / P = b.horizon % 210 / P := by omega
  have ha := horizon_mod_twice_gcd a
  have hb := horizon_mod_twice_gcd b
  rw [← he, ← hp] at hb
  have hm : a.horizon % P = b.horizon % P := ha.trans hb.symm
  have hma := Nat.mod_mod_of_dvd a.horizon hP
  have hmb := Nat.mod_mod_of_dvd b.horizon hP
  rw [← hma, ← hmb] at hm
  have hs := Nat.div_add_mod (a.horizon % 210) P
  rw [hq, hm, Nat.div_add_mod] at hs
  exact ⟨hs.symm, hp⟩

private def adjustedStartupIncrements210 : Finset Nat :=
  (Finset.range 160).filter fun e => 1 < e ∧ e % 2 = 1 ∧ ¬ e ∣ 210

def startupWeightAtCap210 (cap e : Nat) : Nat := cap + 11 + startupTravelCap210 e - 11 * e

abbrev adjustedStartupWeight210 : Nat → Nat := startupWeightAtCap210 1120

theorem adjusted_phase_cost_weight_of_bound210 (event : ResidualPhaseEvent210) {cap : Nat} {cost : Int}
    (hcap : cap ≤ 1120)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen))
    (hpos : 0 < cost)
    (hcost : cost ≤ (24 * (event.hit - event.start) + cap : Nat) -
      11 * ((d event.hit - 1 : Nat) : Int) - (24 * event.firstGap : Nat)) :
    d event.hit ≤ 159 ∧ cost.toNat ≤ startupWeightAtCap210 cap (d event.hit) := by
  have he := event.step.2.2.2.1
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have hodd := d_mod_two_eq_one_of_three_le hr
  have hsize : d event.hit ≤ 159 := by
    by_cases hg : 10 < event.hit - event.start
    · by_cases hp : NoProperFactor (d event.hit)
      · have hfirst : IsFirstLongPrimePhase residualHorizonPhase210 event.seen event.start event.horizon event.hit :=
          ⟨hg, hp, fun h => hnew ⟨⟨hg, hp⟩, h⟩⟩
        simp only [ResidualPhaseEvent210.firstGap, firstLongPrimePhaseGap, if_pos hfirst] at hcost
        omega
      · have hseven := moving_horizon_long_composite_seven_growth event.step hg hp
        have hup := moving_horizon_step_update event.step
        have h280 : d event.hit ≤ 280 := by omega
        obtain ⟨f, hf, hd, hsquare⟩ := exists_small_factor_of_composite hp
        have hf16 : f ≤ 16 := by
          by_contra h
          have hf17 : 17 ≤ f := by omega
          have := Nat.mul_le_mul hf17 hf17
          omega
        have hfodd : f % 2 = 1 := by
          by_contra h
          have hz : f % 2 = 0 := by omega
          obtain ⟨k, hk⟩ := hd
          rw [hk, Nat.mul_mod, hz] at hodd
          simp at hodd
        have hf13 : f ≤ 13 := by
          by_contra h
          have h15 : f = 15 := by omega
          have hd3 : 3 ∣ d event.hit := (show 3 ∣ f by rw [h15]; decide).trans hd
          have hgap := moving_horizon_step_gap_le_twice_increment_factor event.step (by decide : 1 < 3) hd3
          omega
        have hgap := moving_horizon_step_gap_le_twice_increment_factor event.step hf hd
        omega
    · omega
  refine ⟨hsize, ?_⟩
  have hgap := startup_gap_le_travel_cap event hnew (by omega)
  unfold startupWeightAtCap210
  omega

theorem adjusted_phase_cost_weight210 (event : ResidualPhaseEvent210)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen))
    (hpos : 0 < event.adjustedCost) :
    d event.hit ≤ 159 ∧ event.adjustedCost.toNat ≤ adjustedStartupWeight210 (d event.hit) :=
  adjusted_phase_cost_weight_of_bound210 event le_rfl hnew hpos
    (event.adjusted_cost_le_of_unsupported (event.adjusted_cost_positive_unsupported hpos))

def startupWeightSumAtCap210 (cap : Nat) : Nat :=
  ∑ e ∈ adjustedStartupIncrements210, startupPhaseSlots210 e * startupWeightAtCap210 cap e

set_option maxRecDepth 16384 in
theorem adjusted_startup_weight_total210 :
    (∑ e ∈ adjustedStartupIncrements210, startupPhaseSlots210 e * adjustedStartupWeight210 e) =
      4651452 := by
  unfold adjustedStartupIncrements210
  decide +kernel

set_option maxHeartbeats 800000 in
private theorem startup_sum_le_of_weights {n : Nat} (events : Fin n → ResidualPhaseEvent210)
    (selected : Finset (Fin n)) (increments : Finset Nat) (cost : Fin n → Nat) (weight : Nat → Nat)
    (allowed : ∀ i ∈ selected, d (events i).hit ∈ increments)
    (distinct : Set.InjOn (fun i => (events i).phaseKey) (selected : Set (Fin n)))
    (bounded : ∀ i ∈ selected, cost i ≤ weight (d (events i).hit)) :
    (∑ i ∈ selected, cost i) ≤ ∑ e ∈ increments, startupPhaseSlots210 e * weight e := by
  classical
  let codes := increments.sigma (fun e => Finset.range (startupPhaseSlots210 e))
  let encode (i : Fin n) : Σ _e : Nat, Nat :=
    ⟨d (events i).hit, startupPhaseIndex210 (events i)⟩
  have hsubset : selected.image encode ⊆ codes := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sigma.mpr ⟨allowed i hi, Finset.mem_range.mpr (startup_phase_index_lt (events i))⟩
  have hinj : Set.InjOn encode (selected : Set (Fin n)) := by
    intro i hi j hj h
    have he := congrArg Sigma.fst h
    have hidx := congrArg (fun x : Σ _e : Nat, Nat => x.2) h
    change d (events i).hit = d (events j).hit at he
    obtain ⟨hC, hp⟩ := startup_phase_index_eq he hidx
    apply distinct hi hj
    refine Prod.ext he ?_
    apply Fin.ext
    change 2 * ((events i).horizon % 210) + (events i).hit % 2 =
      2 * ((events j).horizon % 210) + (events j).hit % 2
    rw [hC, hp]
  calc
    (∑ i ∈ selected, cost i) ≤ ∑ i ∈ selected, weight (encode i).1 := Finset.sum_le_sum bounded
    _ = ∑ x ∈ selected.image encode, weight x.1 :=
      by rw [Finset.sum_image hinj]
    _ ≤ ∑ x ∈ codes, weight x.1 := Finset.sum_le_sum_of_subset hsubset
    _ = ∑ e ∈ increments, startupPhaseSlots210 e * weight e := by
      unfold codes
      simp [Finset.sum_sigma, Finset.sum_const, Finset.card_range]

/-- For a fixed increment, the actual horizon parity leaves at most
210 reachable keys. The tighter gcd count is used for startup weights. -/
theorem phase_sum_le_of_weights210 {n : Nat} (events : Fin n → ResidualPhaseEvent210)
    (selected : Finset (Fin n)) (increments : Finset Nat) (cost : Fin n → Nat) (weight : Nat → Nat)
    (allowed : ∀ i ∈ selected, d (events i).hit ∈ increments)
    (distinct : Set.InjOn (fun i => (events i).phaseKey) (selected : Set (Fin n)))
    (bounded : ∀ i ∈ selected, cost i ≤ weight (d (events i).hit)) :
    (∑ i ∈ selected, cost i) ≤ 210 * (∑ e ∈ increments, weight e) := by
  apply (startup_sum_le_of_weights events selected increments cost weight allowed distinct bounded).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hg : 0 < Nat.gcd e 210 := Nat.gcd_pos_of_pos_right _ (by decide)
  have h₂ := Nat.mul_le_mul_right (210 / (2 * Nat.gcd e 210)) (by omega : 2 ≤ 2 * Nat.gcd e 210)
  rw [Nat.mul_comm (2 * Nat.gcd e 210)] at h₂
  exact Nat.mul_le_mul_right _ (h₂.trans (Nat.div_mul_le_self _ _))

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

theorem refined_startup_cost_le : trace.startupCost ≤ 6181254 := by
  rw [← residual_startup_weight_total210]
  apply startup_sum_le_of_weights trace.event trace.startup residualStartupIncrements210
    (fun i => (trace.event i).cost.toNat) residualStartupWeight210
  · intro i hi
    have hb := (trace.startup_bounds hi).1
    have hr : 3 ≤ (trace.event i).hit := by
      have := (trace.event i).step.1.1
      have := (trace.event i).step.2.1
      omega
    unfold residualStartupIncrements210
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (trace.event i).step.2.2.2.1,
      d_mod_two_eq_one_of_three_le hr, (trace.event i).positive_unsupported (trace.startup_positive hi)⟩
  · intro i hi j hj h
    change (trace.event i).phaseKey = (trace.event j).phaseKey at h
    apply trace.startup_unique hi hj
    apply Fin.ext
    change (420 * (trace.event i).phaseKey.1 + (trace.event i).phaseKey.2.val) % (631 * 420) =
      (420 * (trace.event j).phaseKey.1 + (trace.event j).phaseKey.2.val) % (631 * 420)
    rw [h]
  · intro i hi
    exact residual_phase_startup_weight210 (trace.event i) (trace.startup_not_reused_long hi)
      (trace.startup_positive hi)

theorem cost_startup_sum_le_at_cap (cost : Fin n → Int) {cap : Nat} (hcap : cap ≤ 1120)
    (unsupported : ∀ i, 0 < cost i → ¬ d (trace.event i).hit ∣ 210)
    (bound : ∀ i, 0 < cost i → cost i ≤ (24 * ((trace.event i).hit - (trace.event i).start) + cap : Nat) -
      11 * ((d (trace.event i).hit - 1 : Nat) : Int) - (24 * (trace.event i).firstGap : Nat)) :
    trace.costStartupSum cost ≤ startupWeightSumAtCap210 cap := by
  have hweights {i : Fin n} (hi : i ∈ trace.costStartup cost) :=
    adjusted_phase_cost_weight_of_bound210 (trace.event i) hcap (trace.cost_startup_not_reused hi)
      (trace.cost_startup_positive hi) (bound i (trace.cost_startup_positive hi))
  apply startup_sum_le_of_weights trace.event (trace.costStartup cost) adjustedStartupIncrements210
    (fun i => (cost i).toNat) (startupWeightAtCap210 cap)
  · intro i hi
    have hb := (hweights hi).1
    have hr : 3 ≤ (trace.event i).hit := by
      have := (trace.event i).step.1.1
      have := (trace.event i).step.2.1
      omega
    unfold adjustedStartupIncrements210
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (trace.event i).step.2.2.2.1,
      d_mod_two_eq_one_of_three_le hr, unsupported i (trace.cost_startup_positive hi)⟩
  · intro i hi j hj h
    exact trace.cost_startup_unique hi hj h
  · intro i hi
    exact (hweights hi).2

theorem adjusted_startup_cost_le : trace.adjustedStartupCost ≤ 4651452 := by
  rw [← adjusted_startup_weight_total210]
  exact trace.cost_startup_sum_le_at_cap (fun i => (trace.event i).adjustedCost) (by decide)
    (fun i h => (trace.event i).adjusted_cost_positive_unsupported h)
    (fun i h => (trace.event i).adjusted_cost_le_of_unsupported
      ((trace.event i).adjusted_cost_positive_unsupported h))

end ResidualPhaseTrace210

/-- The startup bound leaves this much room in the uniform two-thirds
crossing estimate for first gaps and the other signed residual costs. -/
theorem crossing_budget_of_refined_startup210 {M s C r p first : Nat} {balance : Int}
    (hM : 50000000 ≤ M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M)
    (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (rest : 3 * (((24 * first : Nat) : Int) + ∑ i ∈ Finset.univ \ trace.startup, (trace.event i).cost) ≤
      2 * ((C - (2 * M - 2) : Nat) : Int) + 29108531) :
    ((24 * (first + (r - s)) + 1315 : Nat) : Int) + balance ≤ M := by
  apply crossing_budget_of_two_thirds_growth210 hM ledger short gap
  have hsplit := Finset.sum_sdiff (f := fun i => (trace.event i).cost) (Finset.subset_univ trace.startup)
  rw [trace.sum_cost] at hsplit
  have hstartup : (∑ i ∈ trace.startup, (trace.event i).cost) = (trace.startupCost : Int) := by
    rw [ResidualPhaseTrace210.startupCost, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i hi => (Int.toNat_of_nonneg (trace.startup_positive hi).le).symm
  have hbound := trace.refined_startup_cost_le
  omega

end A166944Research
