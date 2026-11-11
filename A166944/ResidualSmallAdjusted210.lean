import A166944.ResidualStartupWeights210

/-! # Single-window bounds for the additional adjusted requests -/

namespace A166944Research

private def residueCost210 (e C r gap : Nat) : Int :=
  (24 * gap : Nat) + (scaledPotential210 r (C + e - 1) : Int) -
    (scaledPotential210 (r + 210 - gap) C : Int) - 11 * ((e - 1 : Nat) : Int)

private def checkFactorResidues210 (e q f r0 C0 cap : Nat) : Bool :=
  (List.range (210 / (2 * q))).all fun s =>
    (List.range (210 / (2 * q))).all fun c =>
      (List.range' 1 (2 * f)).all fun gap =>
        decide (residueCost210 e (2 * q * c + C0) (2 * q * s + r0) gap ≤ (cap : Int))

private def checkBothFactorResidues210 (e q f cap : Nat) : Bool :=
  checkFactorResidues210 e q f 0 (q + 1) cap && checkFactorResidues210 e q f (q + 2) (q - 1) cap

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem small_adjusted_residue_checks210 :
    checkBothFactorResidues210 9 3 3 979 = true ∧
      checkBothFactorResidues210 25 5 5 739 = true ∧
      checkBothFactorResidues210 45 15 3 84 = true ∧
      checkBothFactorResidues210 63 21 3 108 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem scaled_cost_le_of_factor_checks (event : ResidualPhaseEvent210) {e q f cap : Nat}
    (he : d event.hit = e) (hq : 2 < q) (hqd : q ∣ e) (hperiod : 2 * q ∣ 210)
    (hf : 1 < f) (hfd : f ∣ e) (hgapCap : 2 * f ≤ 210) (hu : ¬ e ∣ 210)
    (checked : checkBothFactorResidues210 e q f cap = true) : event.scaledNetCost ≤ (cap : Int) := by
  let gap := event.hit - event.start
  have hgap : gap ≤ 2 * f := moving_horizon_step_gap_le_twice_increment_factor event.step hf (he ▸ hfd)
  have hsr := event.step.2.1
  have hgpos : 0 < gap := by unfold gap; omega
  have hquot (x : Nat) : x % 210 / (2 * q) < 210 / (2 * q) := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * q)).mpr
    rw [Nat.div_mul_cancel hperiod]
    exact Nat.mod_lt _ (by decide)
  have at_residues {r0 C0 : Nat} (hr : event.hit % (2 * q) = r0) (hC : event.horizon % (2 * q) = C0)
      (valid : checkFactorResidues210 e q f r0 C0 cap = true) :
      residueCost210 e (event.horizon % 210) (event.hit % 210) gap ≤ (cap : Int) := by
    have hr' := (Nat.mod_mod_of_dvd event.hit hperiod).trans hr
    have hC' := (Nat.mod_mod_of_dvd event.horizon hperiod).trans hC
    have hb₁ := List.all_eq_true.mp valid (event.hit % 210 / (2 * q)) (List.mem_range.mpr (hquot event.hit))
    have hb₂ := List.all_eq_true.mp hb₁ (event.horizon % 210 / (2 * q))
      (List.mem_range.mpr (hquot event.horizon))
    have hb₃ := List.all_eq_true.mp hb₂ gap (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hrEq := Nat.div_add_mod (event.hit % 210) (2 * q)
    have hCEq := Nat.div_add_mod (event.horizon % 210) (2 * q)
    rw [hr'] at hrEq
    rw [hC'] at hCEq
    simpa only [hrEq, hCEq] using (of_decide_eq_true hb₃)
  have hchecks : checkFactorResidues210 e q f 0 (q + 1) cap = true ∧
      checkFactorResidues210 e q f (q + 2) (q - 1) cap = true := by
    simpa only [checkBothFactorResidues210, Bool.and_eq_true] using checked
  have hcap : residueCost210 e (event.horizon % 210) (event.hit % 210) gap ≤ (cap : Int) := by
    rcases moving_horizon_factor_event_residues event.step hq (he ▸ hqd) with h | h
    · exact at_residues h.2.1 h.2.2 hchecks.1
    · exact at_residues h.2.1 h.2.2 hchecks.2
  have hupdate := moving_horizon_step_update event.step
  rw [he] at hupdate
  have hepos : 1 < e := he ▸ event.step.2.2.2.1
  have hCmod : (event.horizon % 210 + e - 1) % 210 = event.nextHorizon % 210 := by omega
  have hsmod : (event.hit % 210 + 210 - gap) % 210 = event.start % 210 := by
    have hgapEq : gap = event.hit - event.start := rfl
    omega
  unfold residueCost210 scaledPotential210 supportedPotential210 at hcap
  simp only [Nat.mod_mod, hCmod, hsmod] at hcap
  rw [ResidualPhaseEvent210.scaledNetCost, if_neg (he ▸ hu), he]
  exact hcap

private def adjustedRepeatCostCap210 : Nat → Nat
  | 9 => 979
  | 25 => 739
  | 45 => 84
  | 63 => 108
  | e => adjustedStartupWeight210 e

private theorem adjusted_repeat_cost_cap (event : ResidualPhaseEvent210)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen)) (positive : 0 < event.adjustedCost) :
    event.adjustedCost.toNat ≤ adjustedRepeatCostCap210 (d event.hit) := by
  have hweight := (adjusted_phase_cost_weight210 event hnew positive).2
  have hle : event.adjustedCost ≤ event.scaledNetCost := by unfold ResidualPhaseEvent210.adjustedCost; omega
  by_cases h9 : d event.hit = 9
  · have hcap := scaled_cost_le_of_factor_checks event h9 (by decide : 2 < 3) (by decide) (by decide)
      (by decide : 1 < 3) (by decide) (by decide) (by decide) small_adjusted_residue_checks210.1
    rw [h9, adjustedRepeatCostCap210]
    omega
  by_cases h25 : d event.hit = 25
  · have hcap := scaled_cost_le_of_factor_checks event h25 (by decide : 2 < 5) (by decide) (by decide)
      (by decide : 1 < 5) (by decide) (by decide) (by decide) small_adjusted_residue_checks210.2.1
    rw [h25, adjustedRepeatCostCap210]
    omega
  by_cases h45 : d event.hit = 45
  · have hcap := scaled_cost_le_of_factor_checks event h45 (by decide : 2 < 15) (by decide) (by decide)
      (by decide : 1 < 3) (by decide) (by decide) (by decide) small_adjusted_residue_checks210.2.2.1
    rw [h45, adjustedRepeatCostCap210]
    omega
  by_cases h63 : d event.hit = 63
  · have hcap := scaled_cost_le_of_factor_checks event h63 (by decide : 2 < 21) (by decide) (by decide)
      (by decide : 1 < 3) (by decide) (by decide) (by decide) small_adjusted_residue_checks210.2.2.2
    rw [h63, adjustedRepeatCostCap210]
    omega
  simpa [adjustedRepeatCostCap210, h9, h25, h45, h63] using hweight

private theorem adjusted_repeat_period_pays210 : ∀ e : Fin 160, 1 < e.val → e.val % 2 = 1 →
    ¬ e.val ∣ 210 → e.val ≠ 9 → e.val ≠ 25 →
    3 * adjustedRepeatCostCap210 e.val ≤ 2 * Nat.lcm 210 (2 * e.val) := by
  decide +kernel

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- Only increment 9 or 25 can need extra credit for a single adjusted
request. Its width must be one of the indicated multiples of its period. -/
theorem adjusted_request_shortfall210 {i : Fin n} (positive : 0 < trace.adjustedDemand i)
    (deficit : 2 * ((trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon) <
      3 * trace.adjustedDemand i) :
    (d (trace.event i).hit = 9 ∧
      ((trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon = 630 ∨
        (trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon = 1260) ∧
      trace.adjustedDemand i ≤ 979) ∨
    (d (trace.event i).hit = 25 ∧
      (trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon = 1050 ∧
      trace.adjustedDemand i ≤ 739) := by
  have hcost := trace.adjusted_demand_eq_cost positive
  have hpos : 0 < (trace.event i).adjustedCost := by omega
  have hu := (trace.event i).adjusted_cost_positive_unsupported hpos
  obtain ⟨horder, hkey⟩ := trace.adjusted_demand_anchor positive
  have hnew : ¬ trace.ReusedLong i := by
    intro hl
    have hpay := trace.prime_reuse_scaled_net_cost_two_thirds
      (show trace.PrimeReuse (trace.adjustedAnchor i) i from ⟨horder, hkey, hl.1.2, hu⟩)
    simp only [growthWindow, Nat.card_Ico] at hpay
    rw [(trace.event i).adjusted_cost_of_long_reuse hl.2] at hcost
    omega
  let w := trace.samePhaseInterval horder hkey
  have ⟨_, hperiod, hwidth, _⟩ := same_phase_credit_interval_constraints210 w
  rw [w.same_increment] at hperiod hwidth
  let e := d (trace.event i).hit
  let width := (trace.event i).horizon - (trace.event (trace.adjustedAnchor i)).horizon
  change Nat.lcm 210 (2 * e) ∣ width at hperiod
  change Nat.lcm 210 (2 * e) ≤ width at hwidth
  change 2 * width < _ at deficit
  have hcap : trace.adjustedDemand i ≤ adjustedRepeatCostCap210 e :=
    hcost ▸ adjusted_repeat_cost_cap (trace.event i) hnew hpos
  change (e = 9 ∧ (width = 630 ∨ width = 1260) ∧ _) ∨ (e = 25 ∧ width = 1050 ∧ _)
  by_cases h9 : e = 9
  · rw [h9] at hcap hperiod hwidth
    change trace.adjustedDemand i ≤ 979 at hcap
    change 630 ∣ width at hperiod
    change 630 ≤ width at hwidth
    obtain ⟨k, hk⟩ := hperiod
    exact Or.inl ⟨h9, by omega, hcap⟩
  by_cases h25 : e = 25
  · rw [h25] at hcap hperiod hwidth
    change trace.adjustedDemand i ≤ 739 at hcap
    change 1050 ∣ width at hperiod
    change 1050 ≤ width at hwidth
    obtain ⟨k, hk⟩ := hperiod
    exact Or.inr ⟨h25, by omega, hcap⟩
  have he := (trace.event i).step.2.2.2.1
  have hsize := (adjusted_phase_cost_weight210 (trace.event i) hnew hpos).1
  have hr : 3 ≤ (trace.event i).hit := by
    have := (trace.event i).step.1.1
    have := (trace.event i).step.2.1
    omega
  have hp := adjusted_repeat_period_pays210 ⟨e, by omega⟩ he (d_mod_two_eq_one_of_three_le hr) hu h9 h25
  change 3 * adjustedRepeatCostCap210 e ≤ 2 * Nat.lcm 210 (2 * e) at hp
  omega

end ResidualPhaseTrace210

end A166944Research
