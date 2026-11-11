import A166944.FundedPhaseCredits210

/-!
# Stronger separating balances from composite-gap savings

Long composite gaps need seven units of horizon growth per 24 units
of travel, rather than the previous allowance of nine. The two saved
units allow separating events to be charged four times their growth
without changing the total travel coefficient eleven.
-/

open Finset

namespace A166944Research

def chargedPhaseSeparatorBalance210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r C' : Nat) : Int :=
  if d r ∣ 210 then 0 else
    (longPrimePhaseExcess phase seen s C r : Int) + (supportedPotential210 r C' : Int) -
      (supportedPotential210 s C : Int) - 4 * ((d r - 1 : Nat) : Int)

theorem charged_phase_balance210_le_original {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)} :
    chargedPhaseSeparatorBalance210 phase seen s C r C' ≤
      primePhaseSeparatorBalance210 phase seen s C r C' := by
  unfold chargedPhaseSeparatorBalance210 primePhaseSeparatorBalance210
  split <;> omega

theorem charged_phase_balance210_le_increment {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    chargedPhaseSeparatorBalance210 phase seen s C r C' ≤ 43 * (d r : Int) + 1265 := by
  have hgap := moving_horizon_step_gap_le_twice_increment hstep
  have hE : longPrimePhaseExcess phase seen s C r ≤ 48 * d r - (d r - 1) := by
    unfold longPrimePhaseExcess
    split
    · omega
    · unfold shortOrReusedTravelExcess shortOrReusedTravelGap
      split <;> omega
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  unfold chargedPhaseSeparatorBalance210
  split <;> omega

/-- Above 315, every positive charged balance must be a repeated long
prime phase. This also bounds startup events in the charged policy. -/
theorem charged_phase_balance210_positive_large {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') (he : 315 < d r)
    (hpositive : 0 < chargedPhaseSeparatorBalance210 phase seen s C r C') :
    10 < r - s ∧ NoProperFactor (d r) ∧ (d r, phase C r) ∈ seen ∧
      d r * (d r - 1) < 48 * (C + 1) := by
  classical
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  have hE : 0 < longPrimePhaseExcess phase seen s C r := by
    unfold chargedPhaseSeparatorBalance210 at hpositive
    split at hpositive <;> omega
  have hf : ¬ IsFirstLongPrimePhase phase seen s C r := by
    intro hf
    rw [longPrimePhaseExcess, if_pos hf] at hE
    omega
  rw [longPrimePhaseExcess, if_neg hf] at hE
  rcases moving_horizon_positive_excess_cases hstep (Nat.le_refl C) hE with h | ⟨hg, hp, _, hsize⟩
  · have := h.2
    omega
  · exact ⟨hg, hp, Classical.byContradiction (fun hn => hf ⟨hg, hp, hn⟩), hsize⟩

theorem charged_phase_balance210_startup_cap {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C')
    (hnew : (d r, phase C r) ∉ seen)
    (hpositive : 0 < chargedPhaseSeparatorBalance210 phase seen s C r C') :
    d r ≤ 315 ∧ (chargedPhaseSeparatorBalance210 phase seen s C r C').toNat ≤ 14810 := by
  have hsmall : d r ≤ 315 := by
    by_contra h
    exact hnew (charged_phase_balance210_positive_large hstep (by omega) hpositive).2.2.1
  have hbound := charged_phase_balance210_le_increment (phase := phase) (seen := seen) hstep
  exact ⟨hsmall, by omega⟩

def HasMovingHorizonChargedPhaseBalances210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (s C sf Cf : Nat) (seen : List (Nat × Fin slots)) : Nat → Nat → Int → Prop
  | 0, first, balance => HasMovingHorizonPathTo s C sf Cf 0 ∧ first = 0 ∧ balance = 0
  | q + 1, first, balance =>
      ∃ r C' tailFirst tailBalance, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonChargedPhaseBalances210 phase r C' sf Cf (recordLongPrimePhase phase seen s C r)
          q tailFirst tailBalance ∧
        first = firstLongPrimePhaseGap phase seen s C r + tailFirst ∧
        balance = chargedPhaseSeparatorBalance210 phase seen s C r C' + tailBalance

theorem charged_phase_balances210_original {slots s C sf Cf q first : Nat} {balance : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hledger : HasMovingHorizonChargedPhaseBalances210 phase s C sf Cf seen q first balance) :
    ∃ original : Int, HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first original := by
  induction q generalizing s C seen first balance with
  | zero => exact ⟨0, hledger.1, hledger.2.1, rfl⟩
  | succ q ih =>
    obtain ⟨r, C', tailFirst, tailBalance, hstep, htail, hfirst, _⟩ := hledger
    obtain ⟨original, horiginal⟩ := ih htail
    exact ⟨_, r, C', tailFirst, original, hstep, horiginal, hfirst, rfl⟩

private theorem charged_phase_step_budget210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    ((24 * (r - s) + supportedPotential210 r C' : Nat) : Int) ≤
      ((24 * firstLongPrimePhaseGap phase seen s C r + 11 * (C' - C) +
        supportedPotential210 s C : Nat) : Int) + chargedPhaseSeparatorBalance210 phase seen s C r C' := by
  have hup := moving_horizon_step_update hstep
  let excess := longPrimePhaseExcess phase seen s C r
  have htravel : 24 * (r - s) ≤ 24 * firstLongPrimePhaseGap phase seen s C r + 7 * (C' - C) + excess := by
    by_cases hf : IsFirstLongPrimePhase phase seen s C r
    · simp only [firstLongPrimePhaseGap, if_pos hf]
      omega
    · simp only [firstLongPrimePhaseGap, excess, longPrimePhaseExcess, if_neg hf]
      by_cases h : r - s ≤ 10 ∨ NoProperFactor (d r)
      · have hnot : ¬ IsNewIncrementFactor [d r] (d r) := fun hn => hn _ (by simp) (Nat.dvd_refl _)
        have hgap : r - s ≤ 10 ∨ (NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor [d r] (d r)) :=
          h.imp_right (fun hp => ⟨hp, hnot⟩)
        rw [shortOrReusedTravelExcess, shortOrReusedTravelGap, if_pos hgap]
        omega
      · have hg := moving_horizon_long_composite_seven_growth hstep
          (by omega : 10 < r - s) (fun hp => h (Or.inr hp))
        omega
  have hnet : (excess : Int) + (supportedPotential210 r C' : Int) ≤
      ((4 * (C' - C) + supportedPotential210 s C : Nat) : Int) +
        chargedPhaseSeparatorBalance210 phase seen s C r C' := by
    by_cases hdiv : d r ∣ 210
    · have htable := (moving_horizon_supported210_step_budgets (seen := [d r]) hstep hdiv).2
      have hle : excess ≤ shortOrReusedTravelExcess [d r] (r - s) (d r) := by
        unfold excess longPrimePhaseExcess
        split <;> omega
      simp only [chargedPhaseSeparatorBalance210, if_pos hdiv, Int.add_zero]
      omega
    · simp only [chargedPhaseSeparatorBalance210, if_neg hdiv, excess]
      omega
  omega

/- The exact residual-travel balance retains still more of the local
slack. It is available for a subsequent allocation construction. -/
def residualPhaseSeparatorBalance210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r C' : Nat) : Int :=
  if d r ∣ 210 then 0 else
    ((24 * ((r - s) - firstLongPrimePhaseGap phase seen s C r) : Nat) : Int) +
      (supportedPotential210 r C' : Int) - (supportedPotential210 s C : Int) -
      11 * ((d r - 1 : Nat) : Int)

theorem residual_phase_balance210_le_charged {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    residualPhaseSeparatorBalance210 phase seen s C r C' ≤
      chargedPhaseSeparatorBalance210 phase seen s C r C' := by
  have hbudget := charged_phase_step_budget210 (phase := phase) (seen := seen) hstep
  have hup := moving_horizon_step_update hstep
  have hfirst : firstLongPrimePhaseGap phase seen s C r ≤ r - s := by
    unfold firstLongPrimePhaseGap
    split <;> omega
  by_cases hdiv : d r ∣ 210
  · simp [residualPhaseSeparatorBalance210, chargedPhaseSeparatorBalance210, hdiv]
  · simp only [residualPhaseSeparatorBalance210, if_neg hdiv]
    omega

theorem residual_phase_step_budget210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    ((24 * (r - s) + supportedPotential210 r C' : Nat) : Int) ≤
      ((24 * firstLongPrimePhaseGap phase seen s C r + 11 * (C' - C) +
        supportedPotential210 s C : Nat) : Int) + residualPhaseSeparatorBalance210 phase seen s C r C' := by
  by_cases hdiv : d r ∣ 210
  · have h := charged_phase_step_budget210 (phase := phase) (seen := seen) hstep
    simpa only [chargedPhaseSeparatorBalance210, residualPhaseSeparatorBalance210, if_pos hdiv] using h
  · have hup := moving_horizon_step_update hstep
    have hfirst : firstLongPrimePhaseGap phase seen s C r ≤ r - s := by
      unfold firstLongPrimePhaseGap
      split <;> omega
    simp only [residualPhaseSeparatorBalance210, if_neg hdiv]
    omega

theorem moving_horizon_charged_phase_balances210 {slots s C sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (seen : List (Nat × Fin slots))
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ first : Nat, ∃ balance : Int,
      HasMovingHorizonChargedPhaseBalances210 phase s C sf Cf seen q first balance ∧
      ((24 * (sf - s) + supportedPotential210 sf Cf : Nat) : Int) ≤
        ((24 * first + 11 * (Cf - C) + supportedPotential210 s C : Nat) : Int) + balance := by
  induction q generalizing s C seen with
  | zero =>
    obtain ⟨rfl, rfl, hs⟩ := hpath
    exact ⟨0, 0, ⟨⟨rfl, rfl, hs⟩, rfl, rfl⟩, by simp⟩
  | succ q ih =>
    obtain ⟨_, r, C', hstep, htail⟩ := hpath
    obtain ⟨first, balance, hledger, hcost⟩ := ih (recordLongPrimePhase phase seen s C r) htail
    have hlocal := charged_phase_step_budget210 (phase := phase) (seen := seen) hstep
    have hr := hstep.2.1
    have hrf := moving_horizon_path_index_le htail
    have hCC' := moving_horizon_step_update hstep
    have hC'f := (moving_horizon_path_gap_le_three_growth htail).2.1
    exact ⟨_, _, ⟨r, C', first, balance, hstep, hledger, rfl, rfl⟩, by omega⟩

theorem canonical_first_crossing_requires_charged_phase_balances210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ (s C r C' p first : Nat) (balance : Int),
      HasMovingHorizonChargedPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      (M : Int) < ((24 * (first + (r - s)) + 1315 : Nat) : Int) + balance := by
  obtain ⟨s, C, r, C', p, _, _, _, hledger, _, hfirst, hstep, hr, hp, hshort, hcross, hG, hg, _⟩ :=
    canonical_first_travel_crossing_excess hcanon hpath hlong
  obtain ⟨first, balance, hphase, hcost⟩ :=
    moving_horizon_charged_phase_balances210 phase [] (moving_horizon_first_use_travel_path hfirst)
  have hV := (supported_excess_and_potential210_bounds (M + 2) (2 * M - 2) (by omega)).2
  have hsf := (moving_horizon_travel_excess_bounds hledger).1
  have hsr := hstep.2.1
  exact ⟨s, C, r, C', p, first, balance, hphase, hstep, hr, hp, hshort, hcross, hg, by omega⟩

theorem canonical_travel_bound_of_charged_phase_budget210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hbudget : ∀ {s C p first : Nat} {balance : Int},
      HasMovingHorizonChargedPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M →
      ((24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 1315 : Nat) : Int) + balance ≤ M) :
    2 * (sf - (M + 2)) ≤ M := by
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, balance, hphase, _, _, _, hs, _, hgap, hcross⟩ :=
      canonical_first_crossing_requires_charged_phase_balances210 phase hcanon hpath (by omega)
    have hle := hbudget hphase hs
    omega

end A166944Research
