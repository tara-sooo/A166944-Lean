import A166944.TravelClip210
import A166944.TravelRebalanced210Data

/-! # A potential that pays the small composite requests locally -/

namespace A166944Research

def rebalancedExceptions210 : List Nat := [9, 25, 45, 63]

def rebalancedAllowance210 (e : Nat) : Nat := Nat.lcm 210 (2 * e) / 2

def rebalancedPotential210 (s C : Nat) : Nat :=
  let row := (rebalancedRows210[(C % 210) / 2]?).getD (1, 0)
  (row.2 >>> (11 * ((s % 210) % row.1))) % 2048

private def rebalancedStepFits210 (s c gap e allowance : Nat) : Bool :=
  Nat.ble (24 * gap + rebalancedPotential210 (s + gap) (c + e - 1))
    (11 * (e - 1) + rebalancedPotential210 s c + allowance)

def rebalancedClippedCostCaps210 : Nat → List (Nat × Nat)
  | 3 => [(9, 315), (27, 525), (33, 402), (39, 492)]
  | 5 => [(25, 525), (55, 360), (65, 204)]
  | 7 => [(49, 402), (77, 264), (91, 0)]
  | 15 => [(45, 204), (75, 20)]
  | 21 => [(63, 128)]
  | _ => []

private def rebalancedExtraFits210 (s c gap clip : Nat) : Bool :=
  (rebalancedClippedCostCaps210 clip).all fun (e, cap) => rebalancedStepFits210 s c gap e cap

private def checkRebalancedResidue210 (s c : Nat) : Bool :=
  Nat.ble (rebalancedPotential210 s c) 1036 &&
    match firstClippedHit210 s c with
    | none => true
    | some (gap, clip) =>
      rebalancedStepFits210 s c gap clip 0 && rebalancedExtraFits210 s c gap clip

private def checkRebalancedRow210 (h : Nat) : Bool :=
  (List.range 210).all fun s => checkRebalancedResidue210 s (2 * h)

private def checkRebalancedBand210 (start : Nat) : Bool :=
  (List.range' start 15).all checkRebalancedRow210

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem rebalanced_bands_checked210 :
    checkRebalancedBand210 0 = true ∧ checkRebalancedBand210 15 = true ∧
      checkRebalancedBand210 30 = true ∧ checkRebalancedBand210 45 = true ∧
      checkRebalancedBand210 60 = true ∧ checkRebalancedBand210 75 = true ∧
      checkRebalancedBand210 90 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem all_rebalanced_residues_checked210 : (List.range 105).all checkRebalancedRow210 = true := by
  have hs : List.range 105 = List.range' 0 15 ++ List.range' 15 15 ++
      List.range' 30 15 ++ List.range' 45 15 ++ List.range' 60 15 ++
      List.range' 75 15 ++ List.range' 90 15 := by decide
  obtain ⟨h0, h15, h30, h45, h60, h75, h90⟩ := rebalanced_bands_checked210
  unfold checkRebalancedBand210 at h0 h15 h30 h45 h60 h75 h90
  rw [hs]
  simp only [List.all_append, h0, h15, h30, h45, h60, h75, h90, Bool.and_self]

private theorem rebalanced_state_checked210 (s C : Nat) (heven : C % 2 = 0) :
    checkRebalancedResidue210 (s % 210) (C % 210) = true := by
  have hh := List.all_eq_true.mp all_rebalanced_residues_checked210 ((C % 210) / 2)
    (List.mem_range.mpr (by omega))
  unfold checkRebalancedRow210 at hh
  have h := List.all_eq_true.mp hh (s % 210) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rwa [show 2 * ((C % 210) / 2) = C % 210 by omega] at h

theorem rebalanced_potential210_le (s C : Nat) (heven : C % 2 = 0) : rebalancedPotential210 s C ≤ 1036 := by
  have h := rebalanced_state_checked210 s C heven
  simp only [checkRebalancedResidue210, Bool.and_eq_true, Nat.ble_eq] at h
  simpa only [rebalancedPotential210, Nat.mod_mod] using h.1

private theorem rebalanced_step_bound_of_check210 {s C r C' allowance : Nat}
    (step : IsMovingHorizonStep s C r C')
    (h : rebalancedStepFits210 (s % 210) (C % 210) (r - s) (d r) allowance = true) :
    24 * (r - s) + rebalancedPotential210 r C' ≤
      11 * (d r - 1) + rebalancedPotential210 s C + allowance := by
  have hup := moving_horizon_step_update step
  have hsr := step.2.1
  have he := step.2.2.2.1
  have hsm : (s % 210 + (r - s)) % 210 = r % 210 := by omega
  have hcm : (C % 210 + d r - 1) % 210 = C' % 210 := by omega
  simp only [rebalancedStepFits210, Nat.ble_eq, rebalancedPotential210, hsm, hcm, Nat.mod_mod] at h
  exact h

theorem moving_horizon_rebalanced_supported210 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (supported : d r ∣ 210) :
    24 * (r - s) + rebalancedPotential210 r C' ≤ 11 * (d r - 1) + rebalancedPotential210 s C := by
  have hhit := first_clipped_hit210_of_supported step supported
  have heven := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have h := rebalanced_state_checked210 s C heven
  simp only [checkRebalancedResidue210, hhit, Bool.and_eq_true] at h
  simpa only [Nat.add_zero] using rebalanced_step_bound_of_check210 step h.2.1

theorem moving_horizon_rebalanced_clipped_cost_cap210 {s C r C' cap : Nat}
    (step : IsMovingHorizonStep s C r C')
    (hclip : 1 < Nat.gcd (d r) 210)
    (entry : (d r, cap) ∈ rebalancedClippedCostCaps210 (Nat.gcd (d r) 210)) :
    24 * (r - s) + rebalancedPotential210 r C' ≤
      11 * (d r - 1) + rebalancedPotential210 s C + cap := by
  have hhit := first_clipped_hit210_of_nonunit step hclip
  have heven := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have h := rebalanced_state_checked210 s C heven
  simp only [checkRebalancedResidue210, hhit, Bool.and_eq_true] at h
  apply rebalanced_step_bound_of_check210 step
  have hf := h.2.2
  exact List.all_eq_true.mp hf (d r, cap) entry

/-- The four composite charges fit in half of their shortest phase
period, using only this local first-hit bound. -/
theorem moving_horizon_rebalanced_exception210 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (exception : d r ∈ rebalancedExceptions210) :
    24 * (r - s) + rebalancedPotential210 r C' ≤
      11 * (d r - 1) + rebalancedPotential210 s C + rebalancedAllowance210 (d r) := by
  have hcap {e cap : Nat} (he : d r = e) (hc : 1 < Nat.gcd e 210)
      (hm : (e, cap) ∈ rebalancedClippedCostCaps210 (Nat.gcd e 210))
      (hl : cap ≤ rebalancedAllowance210 e) :
      24 * (r - s) + rebalancedPotential210 r C' ≤
        11 * (d r - 1) + rebalancedPotential210 s C + rebalancedAllowance210 (d r) := by
    have h := moving_horizon_rebalanced_clipped_cost_cap210 step (he ▸ hc) (he ▸ hm)
    rw [← he] at hl
    omega
  simp only [rebalancedExceptions210, List.mem_cons, List.not_mem_nil, or_false] at exception
  rcases exception with he | he | he | he
  · exact hcap (cap := 315) he (by decide) (by decide) (by decide)
  · exact hcap (cap := 525) he (by decide) (by decide) (by decide)
  · exact hcap (cap := 204) he (by decide) (by decide) (by decide)
  · exact hcap (cap := 128) he (by decide) (by decide) (by decide)

end A166944Research
