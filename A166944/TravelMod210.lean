import A166944.TravelClip210
import A166944.TravelMod210Data

/-!
# A checked residue model for runs supported on 210

A supported event and all preceding unit steps agree with the gcd
clipped to 210. The finite calculation checks the remaining excess
and a potential after charging twice the horizon growth.
-/

namespace A166944Research

private def upperStepExcess (gap e : Nat) : Nat := 24 * gap - (e - 1)

private def residueBudget210 (s c : Nat) : Nat × Nat :=
  let row := (residueRows210[c / 2]?).getD (1, 0)
  let entry := row.2 >>> (22 * (s % row.1))
  (entry % 2048, (entry >>> 11) % 2048)

def supportedExcessCap210 (s C : Nat) : Nat := (residueBudget210 (s % 210) (C % 210)).1

def supportedPotential210 (s C : Nat) : Nat := (residueBudget210 (s % 210) (C % 210)).2

private def checkResidue210 (s c : Nat) : Bool :=
  let here := residueBudget210 s c
  (Nat.ble here.1 1316 && Nat.ble here.2 1260) &&
    match firstClippedHit210 s c with
    | none => true
    | some (gap, e) =>
        let after := residueBudget210 ((s + gap) % 210) ((c + e - 1) % 210)
        let step := upperStepExcess gap e
        Nat.ble (step + after.1) here.1 && Nat.ble (step + after.2) (2 * (e - 1) + here.2)

private def checkResidueRow210 (h : Nat) : Bool :=
  (List.range 210).all (fun s => checkResidue210 s (2 * h))

private def checkResidueBand210 (start : Nat) : Bool :=
  (List.range' start 15).all checkResidueRow210

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem residue_bands210_checked :
    checkResidueBand210 0 = true ∧ checkResidueBand210 15 = true ∧
    checkResidueBand210 30 = true ∧ checkResidueBand210 45 = true ∧
    checkResidueBand210 60 = true ∧ checkResidueBand210 75 = true ∧
    checkResidueBand210 90 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem all_residues210_checked : (List.range 105).all checkResidueRow210 = true := by
  have hs : List.range 105 = List.range' 0 15 ++ List.range' 15 15 ++ List.range' 30 15 ++
      List.range' 45 15 ++ List.range' 60 15 ++ List.range' 75 15 ++ List.range' 90 15 := by decide
  obtain ⟨h0, h15, h30, h45, h60, h75, h90⟩ := residue_bands210_checked
  unfold checkResidueBand210 at h0 h15 h30 h45 h60 h75 h90
  rw [hs]
  simp only [List.all_append, h0, h15, h30, h45, h60, h75, h90, Bool.and_self]

private theorem residue210_checked {s c : Nat} (hs : s < 210) (hc : c < 210) (hce : c % 2 = 0) :
    checkResidue210 s c = true := by
  have hh := List.all_eq_true.mp all_residues210_checked (c / 2) (List.mem_range.mpr (by omega))
  unfold checkResidueRow210 at hh
  have h := List.all_eq_true.mp hh s (List.mem_range.mpr hs)
  rwa [show 2 * (c / 2) = c by omega] at h

private theorem state210_checked (s C : Nat) (heven : C % 2 = 0) :
    checkResidue210 (s % 210) (C % 210) = true :=
  residue210_checked (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by omega)

theorem supported_excess_and_potential210_bounds (s C : Nat) (heven : C % 2 = 0) :
    supportedExcessCap210 s C ≤ 1316 ∧ supportedPotential210 s C ≤ 1260 := by
  have h := state210_checked s C heven
  simp only [checkResidue210, Bool.and_eq_true, Nat.ble_eq] at h
  exact h.1

theorem supported_budgets210_attained :
    supportedExcessCap210 23 110 = 1316 ∧ supportedPotential210 23 110 = 1260 := by
  decide +kernel

private theorem moving_horizon_supported210_table_budgets {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    upperStepExcess (r - s) (d r) + supportedExcessCap210 r C' ≤ supportedExcessCap210 s C ∧
    upperStepExcess (r - s) (d r) + supportedPotential210 r C' ≤
      2 * (d r - 1) + supportedPotential210 s C := by
  have hce : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hhit := first_clipped_hit210_of_supported hstep hdiv
  have h := state210_checked s C hce
  simp only [checkResidue210, hhit, Bool.and_eq_true, Nat.ble_eq] at h
  have hsr := hstep.2.1
  have hup := moving_horizon_step_update hstep
  have he := hstep.2.2.2.1
  have hsm : (s % 210 + (r - s)) % 210 = r % 210 := by omega
  have hcm : (C % 210 + d r - 1) % 210 = C' % 210 := by omega
  rw [hsm, hcm] at h
  exact h.2

/-- The potential accounts for the full gap of a supported first hit. -/
theorem moving_horizon_supported210_travel_potential {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    24 * (r - s) + supportedPotential210 r C' ≤ 3 * (d r - 1) + supportedPotential210 s C := by
  have hpot := (moving_horizon_supported210_table_budgets hstep hdiv).2
  unfold upperStepExcess at hpot
  omega

/-- Both table bounds apply to a genuine supported step. The table
charges even prime increments that are being used for the first time. -/
theorem moving_horizon_supported210_step_budgets {s C r C' : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    shortOrReusedTravelExcess seen (r - s) (d r) + supportedExcessCap210 r C' ≤ supportedExcessCap210 s C ∧
    shortOrReusedTravelExcess seen (r - s) (d r) + supportedPotential210 r C' ≤
      2 * (d r - 1) + supportedPotential210 s C := by
  obtain ⟨hcap, hpot⟩ := moving_horizon_supported210_table_budgets hstep hdiv
  have hgap : shortOrReusedTravelGap seen (r - s) (d r) ≤ r - s := by
    unfold shortOrReusedTravelGap
    split <;> omega
  have hle : shortOrReusedTravelExcess seen (r - s) (d r) ≤ upperStepExcess (r - s) (d r) := by
    unfold shortOrReusedTravelExcess upperStepExcess
    omega
  exact ⟨by omega, by omega⟩

theorem moving_horizon_supported210_block_budget {s C sf Cf q remaining excess : Nat} {seen : List Nat}
    (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess)
    (hdiv : ∀ j : Nat, s < j → j ≤ sf → d j ∣ 210) :
    excess + supportedExcessCap210 sf Cf ≤ supportedExcessCap210 s C := by
  induction q generalizing s C seen remaining excess with
  | zero =>
    obtain ⟨⟨rfl, rfl, _⟩, _, rfl⟩ := hledger
    simp
  | succ q ih =>
    obtain ⟨r, C', rest, tailExcess, hstep, htail, _, hexcess⟩ := hledger
    have hsr := hstep.2.1
    have hrf := (moving_horizon_travel_excess_bounds htail).1
    have hcost := (moving_horizon_supported210_step_budgets (seen := seen) hstep (hdiv r hsr hrf)).1
    have htailCost := ih htail (fun j hj hjf => hdiv j (by omega) hjf)
    omega

theorem moving_horizon_supported210_block_excess_le_1316 {s C sf Cf q remaining excess : Nat} {seen : List Nat}
    (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess)
    (hdiv : ∀ j : Nat, s < j → j ≤ sf → d j ∣ 210) : excess ≤ 1316 := by
  have hstart : IsMovingHorizonState s C := by
    cases q with
    | zero => exact hledger.1.2.2
    | succ q => obtain ⟨_, _, _, _, hstep, _⟩ := hledger; exact hstep.1
  have hce : C % 2 = 0 := hstart.2.1 ▸ D_mod_two_eq_zero_of_two_le hstart.1
  have hcap := (supported_excess_and_potential210_bounds s C hce).1
  have h := moving_horizon_supported210_block_budget hledger hdiv
  omega

/-- The positive part of the net cost at a separating event. The
within-block inequality pays for all events whose increments divide 210. -/
def separatorCharge210 (seen : List Nat) (s C r C' : Nat) : Nat :=
  if d r ∣ 210 then 0 else
    shortOrReusedTravelExcess seen (r - s) (d r) + supportedPotential210 r C' -
      (2 * (d r - 1) + supportedPotential210 s C)

theorem separator_charge210_zero_of_large_no_excess {s C r C' : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (he : 631 ≤ d r)
    (hzero : shortOrReusedTravelExcess seen (r - s) (d r) = 0) :
    separatorCharge210 seen s C r C' = 0 := by
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce : C' % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  unfold separatorCharge210
  split <;> omega

theorem separator_charge210_positive_cases {s C r C' U : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (hU : C ≤ U)
    (hcharge : 0 < separatorCharge210 seen s C r C') :
    ¬ d r ∣ 210 ∧ (d r ≤ 630 ∨
      (10 < r - s ∧ NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor seen (d r) ∧
        d r * (d r - 1) < 48 * (U + 1))) := by
  have hdiv : ¬ d r ∣ 210 := by
    intro h
    rw [separatorCharge210, if_pos h] at hcharge
    omega
  refine ⟨hdiv, ?_⟩
  by_cases he : d r ≤ 630
  · exact Or.inl he
  · have hpos : 0 < shortOrReusedTravelExcess seen (r - s) (d r) := by
      by_cases hz : shortOrReusedTravelExcess seen (r - s) (d r) = 0
      · have hzero := separator_charge210_zero_of_large_no_excess hstep (by omega) hz
        omega
      · omega
    rcases moving_horizon_positive_excess_cases hstep hU hpos with h | h
    · have := h.2
      omega
    · exact Or.inr h

private theorem moving_horizon_step_separator210_bound {s C r C' : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    shortOrReusedTravelExcess seen (r - s) (d r) + supportedPotential210 r C' ≤
      2 * (d r - 1) + supportedPotential210 s C + separatorCharge210 seen s C r C' := by
  unfold separatorCharge210
  split
  · rename_i hdiv
    simpa only [Nat.add_zero] using (moving_horizon_supported210_step_budgets (seen := seen) hstep hdiv).2
  · omega

def HasMovingHorizonSeparatorCharges210 (s C sf Cf : Nat) (seen : List Nat) : Nat → Nat → Prop
  | 0, charge => HasMovingHorizonPathTo s C sf Cf 0 ∧ charge = 0
  | q + 1, charge =>
      ∃ r C' tail, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonSeparatorCharges210 r C' sf Cf (d r :: seen) q tail ∧
        charge = separatorCharge210 seen s C r C' + tail

/-- The only step costs left after telescoping the potential are the
positive separator charges. -/
theorem moving_horizon_excess_by_separator_charges210 {s C sf Cf q remaining excess : Nat} {seen : List Nat}
    (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess) :
    ∃ charge, HasMovingHorizonSeparatorCharges210 s C sf Cf seen q charge ∧
      excess + supportedPotential210 sf Cf ≤ 2 * (Cf - C) + supportedPotential210 s C + charge := by
  induction q generalizing s C seen remaining excess with
  | zero =>
    obtain ⟨⟨rfl, rfl, hstate⟩, _, rfl⟩ := hledger
    exact ⟨0, ⟨⟨rfl, rfl, hstate⟩, rfl⟩, by simp⟩
  | succ q ih =>
    obtain ⟨r, C', rest, tailExcess, hstep, htail, _, hexcess⟩ := hledger
    obtain ⟨charge, hcharge, htailCost⟩ := ih htail
    have hC' := (moving_horizon_travel_excess_bounds htail).2.1
    have hup := moving_horizon_step_update hstep
    have hstepCost := moving_horizon_step_separator210_bound (seen := seen) hstep
    exact ⟨_, ⟨r, C', charge, hstep, hcharge, rfl⟩, by omega⟩

theorem canonical_first_crossing_requires_separator_charges210 {M sf Cf q : Nat}
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ s C r C' p first charge : Nat,
      HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) s C [] p first ∧
      HasMovingHorizonSeparatorCharges210 (M + 2) (2 * M - 2) s C [] p charge ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      12 * M + supportedPotential210 s C <
        24 * (first + (r - s)) + 11 * (C - (2 * M - 2)) + supportedPotential210 (M + 2) (2 * M - 2) + charge ∧
      M < 24 * (first + (r - s)) + 1315 + charge := by
  obtain ⟨s, C, r, C', p, _, first, excess, hledger, _, hfirst, hstep, hr, hp,
    hshort, hcross, hG, hg, hdist⟩ := canonical_first_travel_crossing_excess hcanon hpath hlong
  obtain ⟨charge, hcharge, hE⟩ := moving_horizon_excess_by_separator_charges210 hledger
  have hV := (supported_excess_and_potential210_bounds (M + 2) (2 * M - 2) (by omega)).2
  exact ⟨s, C, r, C', p, first, charge, hfirst, hcharge, hstep, hr, hp, hshort, hcross, hg,
    by omega, by omega⟩

end A166944Research
