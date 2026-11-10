import A166944.TravelPhases210

/-!
# Signed budgets across several separating events

The remainder below the next multiple of 210 accounts for growth at
supported events. Each separating event contributes one bounded reset
and its own excess. This also bounds a complete same-phase reuse interval.
-/

namespace A166944Research

/-- Supported steps stay below the same next positive multiple of 210. -/
theorem moving_horizon_supported210_remainder {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    (C' - C) + (C - 1) % 210 = (C' - 1) % 210 := by
  let ceiling := 210 * ((C - 1) / 210 + 1)
  have hs := hstep.1.1
  have hCpos : 0 < C := by have := hstep.1.2.2; omega
  have hpart := Nat.div_add_mod (C - 1) 210
  have hceilDiv : 210 ∣ ceiling := ⟨(C - 1) / 210 + 1, rfl⟩
  have hceilEven : ceiling % 2 = 0 := by simp [ceiling, Nat.mul_mod]
  have hceil : C ≤ ceiling := by dsimp [ceiling]; omega
  have hbound := D_le_even_multiple_of_interval hs (Nat.le_of_lt hstep.2.1) hceilEven
    (hstep.1.2.1.symm ▸ hceil) (fun j hj hjr => by
      apply Nat.dvd_trans _ hceilDiv
      by_cases heq : j = r
      · simpa only [heq] using hdiv
      · rw [hstep.2.2.2.2.1 j hj (by omega)]
        exact Nat.one_dvd _)
  rw [← hstep.2.2.2.2.2.2.1] at hbound
  have hgrowth := moving_horizon_step_update hstep
  have hpart' := Nat.div_add_mod (C' - 1) 210
  dsimp [ceiling] at hbound
  omega

/-- One pair for each separator, recording its exact excess and balance. -/
def HasMovingHorizonPhaseSeparatorCosts210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (s C sf Cf : Nat) (seen : List (Nat × Fin slots)) : Nat → List (Nat × Int) → Prop
  | 0, costs => HasMovingHorizonPathTo s C sf Cf 0 ∧ costs = []
  | q + 1, costs =>
      ∃ r C' rest, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonPhaseSeparatorCosts210 phase r C' sf Cf
          (recordLongPrimePhase phase seen s C r) q rest ∧
        costs = if d r ∣ 210 then rest else
          (longPrimePhaseExcess phase seen s C r,
            primePhaseSeparatorBalance210 phase seen s C r C') :: rest

theorem moving_horizon_phase_separator_costs210 {slots s C sf Cf q first : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)} {separators : Int}
    (hledger : HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first separators) :
    ∃ costs : List (Nat × Int), HasMovingHorizonPhaseSeparatorCosts210 phase s C sf Cf seen q costs ∧
      (costs.map Prod.snd).sum = separators := by
  induction q generalizing s C seen first separators with
  | zero =>
    obtain ⟨hpath, _, rfl⟩ := hledger
    exact ⟨[], ⟨hpath, rfl⟩, rfl⟩
  | succ q ih =>
    obtain ⟨r, C', tailFirst, tailSeparators, hstep, htail, _, hsum⟩ := hledger
    obtain ⟨costs, hcost, htotal⟩ := ih htail
    by_cases hdiv : d r ∣ 210
    · refine ⟨costs, ⟨r, C', costs, hstep, hcost, by simp only [if_pos hdiv]⟩, ?_⟩
      simpa only [primePhaseSeparatorBalance210, if_pos hdiv, Int.zero_add, ← htotal] using hsum.symm
    · refine ⟨(longPrimePhaseExcess phase seen s C r,
        primePhaseSeparatorBalance210 phase seen s C r C') :: costs,
        ⟨r, C', costs, hstep, hcost, by simp only [if_neg hdiv]⟩, ?_⟩
      simpa only [List.map_cons, List.sum_cons, htotal] using hsum.symm

theorem moving_horizon_phase_separator_costs210_path {slots s C sf Cf q : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)} {costs : List (Nat × Int)}
    (hcost : HasMovingHorizonPhaseSeparatorCosts210 phase s C sf Cf seen q costs) :
    HasMovingHorizonPathTo s C sf Cf q := by
  induction q generalizing s C seen costs with
  | zero => exact hcost.1
  | succ q ih =>
    obtain ⟨r, C', _, hstep, htail, _⟩ := hcost
    exact ⟨hstep.1, r, C', hstep, ih htail⟩

/-- Keep the endpoint remainders while summing. Supported steps incur
no reset. Each separator incurs at most `1260 + 2*209`. -/
theorem moving_horizon_phase_separator_remainder_budget210 {slots s C sf Cf q : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)} {costs : List (Nat × Int)}
    (hcost : HasMovingHorizonPhaseSeparatorCosts210 phase s C sf Cf seen q costs) :
    (costs.map Prod.snd).sum + 2 * ((Cf - C : Nat) : Int) + 2 * (((C - 1) % 210 : Nat) : Int) ≤
      (((costs.map Prod.fst).sum : Nat) : Int) + 2 * (((Cf - 1) % 210 : Nat) : Int) +
        1678 * (costs.length : Int) := by
  induction q generalizing s C seen costs with
  | zero =>
    obtain ⟨⟨_, rfl, _⟩, rfl⟩ := hcost
    simp
  | succ q ih =>
    obtain ⟨r, C', rest, hstep, htail, hcosts⟩ := hcost
    have hbound := ih htail
    have hC'f := (moving_horizon_path_gap_le_three_growth
      (moving_horizon_phase_separator_costs210_path htail)).2.1
    have hup := moving_horizon_step_update hstep
    by_cases hdiv : d r ∣ 210
    · have hrem := moving_horizon_supported210_remainder hstep hdiv
      simp only [if_pos hdiv] at hcosts
      subst costs
      omega
    · have hst := hstep.2.2.2.2.2.2.2.2
      have hce := hst.2.1 ▸ D_mod_two_eq_zero_of_two_le hst.1
      have hV := (supported_excess_and_potential210_bounds r C' hce).2
      have hbal : primePhaseSeparatorBalance210 phase seen s C r C' ≤
          (longPrimePhaseExcess phase seen s C r : Int) + 1260 - 2 * ((C' - C : Nat) : Int) := by
        simp only [primePhaseSeparatorBalance210, if_neg hdiv]
        omega
      simp only [if_neg hdiv] at hcosts
      subst costs
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem moving_horizon_phase_separator_block_budget210 {slots s C sf Cf q : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)} {costs : List (Nat × Int)}
    (hcost : HasMovingHorizonPhaseSeparatorCosts210 phase s C sf Cf seen q costs) :
    (costs.map Prod.snd).sum ≤ (((costs.map Prod.fst).sum : Nat) : Int) +
      1678 * (costs.length : Int) + 418 - 2 * ((Cf - C : Nat) : Int) := by
  have h := moving_horizon_phase_separator_remainder_budget210 hcost
  omega

/-- All separators strictly between the two equal phases are included
in one block, so the estimate also includes their nonzero excesses. -/
theorem moving_horizon_prime_phase_reuse_block_budget210
    {slots P p s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' q : Nat}
    {phase : Nat → Nat → Fin slots} {seen₁ seen₂ : List (Nat × Fin slots)}
    {costs : List (Nat × Int)}
    (h₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁') (h₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (hbetween : HasMovingHorizonPhaseSeparatorCosts210 phase r₁ C₁' s₂ C₂ seen₁ q costs)
    (hP : 0 < P) (hp : 2 < p) (he₁ : d r₁ = p) (he₂ : d r₂ = p)
    (hphase : primeHorizonPhase P hP C₁ r₁ = primeHorizonPhase P hP C₂ r₂) :
    (costs.map Prod.snd).sum + primePhaseSeparatorBalance210 phase seen₂ s₂ C₂ r₂ C₂' ≤
      (((costs.map Prod.fst).sum : Nat) : Int) + 1678 * (costs.length : Int) +
        1679 + 47 * (p : Int) - 2 * (Nat.lcm P (2 * p) : Int) := by
  have hcodes := congrArg Fin.val hphase
  change 2 * (C₁ % P) + r₁ % 2 = 2 * (C₂ % P) + r₂ % 2 at hcodes
  have hpath := moving_horizon_phase_separator_costs210_path hbetween
  have horder := moving_horizon_path_index_le hpath
  obtain ⟨_, hneed, _⟩ := moving_horizon_same_phase_reuse_requires_separator h₁ h₂ horder
    hP hp he₁ (he₂.symm ▸ Nat.dvd_refl p) (by omega) (by omega)
  have hup₁ := moving_horizon_step_update h₁
  have hblock := moving_horizon_phase_separator_block_budget210 hbetween
  have hgap := moving_horizon_step_gap_le_twice_increment h₂
  have hE : longPrimePhaseExcess phase seen₂ s₂ C₂ r₂ ≤ 48 * p - (p - 1) := by
    unfold longPrimePhaseExcess
    split
    · omega
    · unfold shortOrReusedTravelExcess shortOrReusedTravelGap
      split <;> omega
  have hst := h₂.2.2.2.2.2.2.2.2
  have hce := hst.2.1 ▸ D_mod_two_eq_zero_of_two_le hst.1
  have hV := (supported_excess_and_potential210_bounds r₂ C₂' hce).2
  have hlast : primePhaseSeparatorBalance210 phase seen₂ s₂ C₂ r₂ C₂' ≤ 45 * (p : Int) + 1263 := by
    unfold primePhaseSeparatorBalance210
    split <;> omega
  omega

/-- Any number `k` of zero-excess separators can be paid jointly
when the returning prime satisfies `5*(k+1) ≤ p`. -/
theorem moving_horizon_zero_excess_reuse_block_nonpos210
    {slots p s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' q : Nat}
    {phase : Nat → Nat → Fin slots} {seen₁ seen₂ : List (Nat × Fin slots)}
    {costs : List (Nat × Int)}
    (h₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁') (h₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (hbetween : HasMovingHorizonPhaseSeparatorCosts210 phase r₁ C₁' s₂ C₂ seen₁ q costs)
    (hcop : Nat.Coprime 210 p) (he₁ : d r₁ = p) (he₂ : d r₂ = p)
    (hphase : primeHorizonPhase 210 (by decide) C₁ r₁ = primeHorizonPhase 210 (by decide) C₂ r₂)
    (hzero : (costs.map Prod.fst).sum = 0) (hcount : 5 * (costs.length + 1) ≤ p) :
    (costs.map Prod.snd).sum + primePhaseSeparatorBalance210 phase seen₂ s₂ C₂ r₂ C₂' ≤ 0 := by
  have hp : 2 < p := by omega
  have hbound := moving_horizon_prime_phase_reuse_block_budget210 (seen₂ := seen₂) h₁ h₂ hbetween
    (by decide : 0 < 210) hp he₁ he₂ hphase
  have hpPeriod : p ∣ Nat.lcm 210 (2 * p) :=
    Nat.dvd_trans ⟨2, Nat.mul_comm 2 p⟩ (Nat.dvd_lcm_right _ _)
  have hperiod := hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left 210 (2 * p)) hpPeriod
  have hwidth := Nat.le_of_dvd (Nat.lcm_pos (by decide : 0 < 210) (by omega : 0 < 2 * p)) hperiod
  rw [hzero] at hbound
  omega

/-- Concatenation makes the credited blocks disjoint. An uncredited
separator contributes its positive part to the remaining budget. -/
inductive HasPhaseSeparatorCreditCover210 : List (Nat × Int) → Nat → Prop
  | empty : HasPhaseSeparatorCreditCover210 [] 0
  | residual {head : Nat × Int} {tail : List (Nat × Int)} {budget : Nat}
      (htail : HasPhaseSeparatorCreditCover210 tail budget) :
      HasPhaseSeparatorCreditCover210 (head :: tail) (head.2.toNat + budget)
  | credited {block tail : List (Nat × Int)} {budget : Nat}
      (hblock : (block.map Prod.snd).sum ≤ 0)
      (htail : HasPhaseSeparatorCreditCover210 tail budget) :
      HasPhaseSeparatorCreditCover210 (block ++ tail) budget

theorem phase_separator_credit_cover_bound210 {costs : List (Nat × Int)} {budget : Nat}
    (hcover : HasPhaseSeparatorCreditCover210 costs budget) :
    (costs.map Prod.snd).sum ≤ (budget : Int) := by
  induction hcover with
  | empty => simp
  | residual htail ih =>
    simp only [List.map_cons, List.sum_cons]
    omega
  | credited hblock htail ih =>
    rw [List.map_append, List.sum_append]
    omega

end A166944Research
