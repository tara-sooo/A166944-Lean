import A166944.ResidualIntervalBudget210
import A166944.TwinCrossingBudget210

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

theorem residual_phase_startup_weight210 (event : ResidualPhaseEvent210)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen))
    (hpos : 0 < event.cost) :
    event.cost.toNat ≤ residualStartupWeight210 (d event.hit) := by
  let e := d event.hit
  have he : 1 < e := event.step.2.2.2.1
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have heodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hbounds := residual_phase_startup_bounds210 (phase := residualHorizonPhase210)
    (seen := event.seen) event.step (fun ⟨hg, hp, hs⟩ => hnew ⟨⟨hg, hp⟩, hs⟩) hpos
  change e ≤ 169 ∧ event.cost.toNat ≤ 1478 at hbounds
  have hgap : 24 * (event.hit - event.start - event.firstGap) ≤ startupTravelCap210 e := by
    cases hdiv : startupDivisor210 e with
    | none =>
      have hp : NoProperFactor e := startup_divisor_none_prime ⟨e, by omega⟩ he heodd hdiv
      simp only [startupTravelCap210, hdiv, Option.elim_none]
      by_cases hg : 10 < event.hit - event.start
      · have hfirst : IsFirstLongPrimePhase residualHorizonPhase210 event.seen
            event.start event.horizon event.hit :=
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
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds event.hit event.nextHorizon heven).2
  have hraw := event.positive_unsupported hpos
  refine Nat.le_min.mpr ⟨hbounds.2, ?_⟩
  simp only [ResidualPhaseEvent210.cost, residualPhaseSeparatorBalance210, if_neg hraw]
  change 1 < d event.hit at he
  change 24 * (event.hit - event.start - event.firstGap) ≤ startupTravelCap210 (d event.hit) at hgap
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

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

set_option maxHeartbeats 800000 in
theorem refined_startup_cost_le : trace.startupCost ≤ 6181254 := by
  classical
  let codes := residualStartupIncrements210.sigma (fun e => Finset.range (startupPhaseSlots210 e))
  let encode (i : Fin n) : Σ _e : Nat, Nat :=
    ⟨d (trace.event i).hit, startupPhaseIndex210 (trace.event i)⟩
  have hsubset : trace.startup.image encode ⊆ codes := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hb := (trace.startup_bounds hi).1
    have hpos := trace.startup_positive hi
    have hstep := (trace.event i).step.2.2.2.1
    have hr : 3 ≤ (trace.event i).hit := by
      have := (trace.event i).step.1.1
      have := (trace.event i).step.2.1
      omega
    have he : d (trace.event i).hit ∈ residualStartupIncrements210 := by
      unfold residualStartupIncrements210
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hstep,
        d_mod_two_eq_one_of_three_le hr, (trace.event i).positive_unsupported hpos⟩
    exact Finset.mem_sigma.mpr ⟨he, Finset.mem_range.mpr (startup_phase_index_lt (trace.event i))⟩
  have hinj : Set.InjOn encode (trace.startup : Set (Fin n)) := by
    intro i hi j hj h
    have he := congrArg Sigma.fst h
    have hidx := congrArg (fun x : Σ _e : Nat, Nat => x.2) h
    change d (trace.event i).hit = d (trace.event j).hit at he
    obtain ⟨hC, hp⟩ := startup_phase_index_eq he hidx
    apply trace.startup_unique hi hj
    apply Fin.ext
    change (420 * d (trace.event i).hit + (2 * ((trace.event i).horizon % 210) + (trace.event i).hit % 2)) %
        (631 * 420) =
      (420 * d (trace.event j).hit + (2 * ((trace.event j).horizon % 210) + (trace.event j).hit % 2)) %
        (631 * 420)
    rw [he, hC, hp]
  calc
    trace.startupCost ≤ ∑ i ∈ trace.startup, residualStartupWeight210 (encode i).1 :=
      Finset.sum_le_sum fun i hi =>
        residual_phase_startup_weight210 (trace.event i) (trace.startup_not_reused_long hi)
          (trace.startup_positive hi)
    _ = ∑ x ∈ trace.startup.image encode, residualStartupWeight210 x.1 :=
      by rw [Finset.sum_image hinj]
    _ ≤ ∑ x ∈ codes, residualStartupWeight210 x.1 := Finset.sum_le_sum_of_subset hsubset
    _ = 6181254 := by
      unfold codes
      rw [Finset.sum_sigma]
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using residual_startup_weight_total210

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
