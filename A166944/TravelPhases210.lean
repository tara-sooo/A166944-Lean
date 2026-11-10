import A166944.ReuseCongruences
import A166944.TravelFirstUse
import A166944.TravelMod210

/-!
# Discounting the first long gap in each prime phase

A fixed finite set of phase labels still allows a sublinear first-use
budget. Subsequent long gaps pay the signed separator balance only
after the same prime and phase have both occurred at a long gap.
-/

open Finset

namespace A166944Research

def primeHorizonPhase (P : Nat) (hP : 0 < P) (C r : Nat) : Fin (2 * P) :=
  ⟨2 * (C % P) + r % 2, by have := Nat.mod_lt C hP; omega⟩

abbrev IsFirstLongPrimePhase {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r : Nat) : Prop :=
  10 < r - s ∧ NoProperFactor (d r) ∧ (d r, phase C r) ∉ seen

def recordLongPrimePhase {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r : Nat) : List (Nat × Fin slots) :=
  if 10 < r - s ∧ NoProperFactor (d r) then (d r, phase C r) :: seen else seen

def firstLongPrimePhaseGap {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r : Nat) : Nat :=
  if IsFirstLongPrimePhase phase seen s C r then r - s else 0

def longPrimePhaseExcess {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r : Nat) : Nat :=
  if IsFirstLongPrimePhase phase seen s C r then 0
  else shortOrReusedTravelExcess [d r] (r - s) (d r)

def primePhaseSeparatorBalance210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (seen : List (Nat × Fin slots)) (s C r C' : Nat) : Int :=
  if d r ∣ 210 then 0 else
    (longPrimePhaseExcess phase seen s C r : Int) + (supportedPotential210 r C' : Int) -
      (supportedPotential210 s C : Int) - 2 * ((d r - 1 : Nat) : Int)

theorem prime_phase_balance210_positive_large {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') (he : 630 < d r)
    (hpositive : 0 < primePhaseSeparatorBalance210 phase seen s C r C') :
    10 < r - s ∧ NoProperFactor (d r) ∧ (d r, phase C r) ∈ seen ∧
      d r * (d r - 1) < 48 * (C + 1) := by
  classical
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  have hE : 0 < longPrimePhaseExcess phase seen s C r := by
    unfold primePhaseSeparatorBalance210 at hpositive
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

/-- If a single zero-excess separator lies between two copies of the
same prime phase, its negative balance pays for the later prime event. -/
theorem moving_horizon_prime_phase_pair_budget210
    {slots p s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' s₃ C₃ r₃ C₃' : Nat}
    {phase : Nat → Nat → Fin slots} {seen₂ seen₃ : List (Nat × Fin slots)}
    (h₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁') (h₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (h₃ : IsMovingHorizonStep s₃ C₃ r₃ C₃') (h₁₂ : r₁ ≤ s₂) (h₂₃ : r₂ ≤ s₃)
    (hp : 11 ≤ p) (hcop : Nat.Coprime 210 p) (he₁ : d r₁ = p) (he₃ : d r₃ = p)
    (hphase : primeHorizonPhase 210 (by decide) C₁ r₁ = primeHorizonPhase 210 (by decide) C₃ r₃)
    (hleft : ∀ j : Nat, r₁ < j → j ≤ s₂ → d j ∣ 210)
    (hright : ∀ j : Nat, r₂ < j → j ≤ s₃ → d j ∣ 210) :
    209 * p ≤ d r₂ + 416 ∧
      (longPrimePhaseExcess phase seen₂ s₂ C₂ r₂ = 0 →
        primePhaseSeparatorBalance210 phase seen₂ s₂ C₂ r₂ C₂' +
          primePhaseSeparatorBalance210 phase seen₃ s₃ C₃ r₃ C₃' ≤ 3357 - 373 * (p : Int)) := by
  have hcodes := congrArg Fin.val hphase
  change 2 * (C₁ % 210) + r₁ % 2 = 2 * (C₃ % 210) + r₃ % 2 at hcodes
  have hr₂ := h₂.2.1
  have h₁₃ : r₁ ≤ s₃ := by omega
  obtain ⟨hperiod, hle, _⟩ := moving_horizon_same_phase_reuse_requires_separator h₁ h₃ h₁₃
    (by decide : 0 < 210) (by omega : 2 < p) he₁ (he₃.symm ▸ Nat.dvd_refl p) (by omega) (by omega)
  have hpPeriod : p ∣ Nat.lcm 210 (2 * p) :=
    Nat.dvd_trans ⟨2, Nat.mul_comm 2 p⟩ (Nat.dvd_lcm_right _ _)
  have hwidth := hcop.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_trans (Nat.dvd_lcm_left _ _) hperiod) (Nat.dvd_trans hpPeriod hperiod)
  have hpos := Nat.lcm_pos (by decide : 0 < 210) (by omega : 0 < 2 * p)
  have hneed := Nat.le_of_dvd (by omega : 0 < C₃ - C₁) hwidth
  have hst₁ := h₁.2.2.2.2.2.2.2.2
  have hst₂ := h₂.2.2.2.2.2.2.2.2
  have hst₃ := h₃.2.2.2.2.2.2.2.2
  have hG₁ := D_growth_lt_of_common_even_multiple hst₁.1 h₁₂ (by decide : 0 < 210) (by decide) hleft
  have hG₂ := D_growth_lt_of_common_even_multiple hst₂.1 h₂₃ (by decide : 0 < 210) (by decide) hright
  rw [hst₁.2.1, h₂.1.2.1] at hG₁
  rw [hst₂.2.1, h₃.1.2.1] at hG₂
  have hup₁ := moving_horizon_step_update h₁
  have hup₂ := moving_horizon_step_update h₂
  have hsize : 209 * p ≤ d r₂ + 416 := by omega
  refine ⟨hsize, ?_⟩
  intro hzero
  have hdiv₂ : ¬ d r₂ ∣ 210 := fun hd => by have := Nat.le_of_dvd (by decide : 0 < 210) hd; omega
  have hce₂ := hst₂.2.1 ▸ D_mod_two_eq_zero_of_two_le hst₂.1
  have hce₃ := hst₃.2.1 ▸ D_mod_two_eq_zero_of_two_le hst₃.1
  have hV₂ := (supported_excess_and_potential210_bounds r₂ C₂' hce₂).2
  have hV₃ := (supported_excess_and_potential210_bounds r₃ C₃' hce₃).2
  have hmid : primePhaseSeparatorBalance210 phase seen₂ s₂ C₂ r₂ C₂' ≤
      1260 - 2 * ((d r₂ - 1 : Nat) : Int) := by
    simp only [primePhaseSeparatorBalance210, if_neg hdiv₂, hzero]
    omega
  have hgap := moving_horizon_step_gap_le_twice_increment h₃
  have hE₃ : longPrimePhaseExcess phase seen₃ s₃ C₃ r₃ ≤ 48 * p - (p - 1) := by
    unfold longPrimePhaseExcess
    split
    · omega
    · unfold shortOrReusedTravelExcess shortOrReusedTravelGap
      split <;> omega
  have hlast : primePhaseSeparatorBalance210 phase seen₃ s₃ C₃ r₃ C₃' ≤ 45 * (p : Int) + 1263 := by
    unfold primePhaseSeparatorBalance210
    split <;> omega
  omega

def HasMovingHorizonPhaseBalances210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (s C sf Cf : Nat) (seen : List (Nat × Fin slots)) : Nat → Nat → Int → Prop
  | 0, first, separators => HasMovingHorizonPathTo s C sf Cf 0 ∧ first = 0 ∧ separators = 0
  | q + 1, first, separators =>
      ∃ r C' tailFirst tailSeparators, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonPhaseBalances210 phase r C' sf Cf (recordLongPrimePhase phase seen s C r)
          q tailFirst tailSeparators ∧
        first = firstLongPrimePhaseGap phase seen s C r + tailFirst ∧
        separators = primePhaseSeparatorBalance210 phase seen s C r C' + tailSeparators

theorem moving_horizon_phase_balances210_path {slots s C sf Cf q first : Nat} {separators : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hcost : HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first separators) :
    HasMovingHorizonPathTo s C sf Cf q := by
  induction q generalizing s C seen first separators with
  | zero => exact hcost.1
  | succ q ih =>
    obtain ⟨r, C', _, _, hstep, htail, _, _⟩ := hcost
    exact ⟨hstep.1, r, C', hstep, ih htail⟩

private theorem moving_horizon_phase_step_budget210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    ((24 * (r - s) + supportedPotential210 r C' : Nat) : Int) ≤
      ((24 * firstLongPrimePhaseGap phase seen s C r + 11 * (C' - C) +
        supportedPotential210 s C : Nat) : Int) + primePhaseSeparatorBalance210 phase seen s C r C' := by
  have hup := moving_horizon_step_update hstep
  let excess := longPrimePhaseExcess phase seen s C r
  have htravel : 24 * (r - s) ≤ 24 * firstLongPrimePhaseGap phase seen s C r + 9 * (C' - C) + excess := by
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
      · have hg := moving_horizon_long_composite_gap_le_growth hstep
          (by omega : 10 < r - s) (fun hp => h (Or.inr hp))
        omega
  have hnet : (excess : Int) + (supportedPotential210 r C' : Int) ≤
      ((2 * (C' - C) + supportedPotential210 s C : Nat) : Int) +
        primePhaseSeparatorBalance210 phase seen s C r C' := by
    by_cases hdiv : d r ∣ 210
    · have htable := (moving_horizon_supported210_step_budgets (seen := [d r]) hstep hdiv).2
      have hle : excess ≤ shortOrReusedTravelExcess [d r] (r - s) (d r) := by
        unfold excess longPrimePhaseExcess
        split <;> omega
      simp only [primePhaseSeparatorBalance210, if_pos hdiv, Int.add_zero]
      omega
    · simp only [primePhaseSeparatorBalance210, if_neg hdiv, excess]
      omega
  omega

theorem moving_horizon_phase_balances210 {slots s C sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (seen : List (Nat × Fin slots))
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ first : Nat, ∃ separators : Int,
      HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first separators ∧
      ((24 * (sf - s) + supportedPotential210 sf Cf : Nat) : Int) ≤
        ((24 * first + 11 * (Cf - C) + supportedPotential210 s C : Nat) : Int) + separators := by
  induction q generalizing s C seen with
  | zero =>
    obtain ⟨rfl, rfl, hs⟩ := hpath
    exact ⟨0, 0, ⟨⟨rfl, rfl, hs⟩, rfl, rfl⟩, by simp⟩
  | succ q ih =>
    obtain ⟨_, r, C', hstep, htail⟩ := hpath
    obtain ⟨first, separators, hledger, hcost⟩ := ih (recordLongPrimePhase phase seen s C r) htail
    have hlocal := moving_horizon_phase_step_budget210 (phase := phase) (seen := seen) hstep
    have hr := hstep.2.1
    have hrf := moving_horizon_path_index_le htail
    have hCC' := moving_horizon_step_update hstep
    have hC'f := (moving_horizon_path_gap_le_three_growth htail).2.1
    exact ⟨_, _, ⟨r, C', first, separators, hstep, hledger, rfl, rfl⟩, by omega⟩

private def unusedPrimePhases {slots : Nat} (L : Nat) (seen : List (Nat × Fin slots)) :
    Finset (Nat × Fin slots) := ((Nat.primesLE L).product univ).filter (· ∉ seen)

private theorem unused_prime_phases_cons_subset {slots L : Nat} {seen : List (Nat × Fin slots)}
    (key : Nat × Fin slots) : unusedPrimePhases L (key :: seen) ⊆ unusedPrimePhases L seen := by
  intro a ha
  obtain ⟨hmem, hnew⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hmem, fun hm => hnew (List.mem_cons_of_mem key hm)⟩

private theorem unused_prime_phases_sum_cons_add {slots L : Nat} {seen : List (Nat × Fin slots)}
    {key : Nat × Fin slots} (he : key ∈ unusedPrimePhases L seen) :
    (∑ a ∈ unusedPrimePhases L (key :: seen), a.1) + key.1 ≤ ∑ a ∈ unusedPrimePhases L seen, a.1 := by
  have hnot : key ∉ unusedPrimePhases L (key :: seen) := by simp [unusedPrimePhases]
  have hsub := Finset.insert_subset he (unused_prime_phases_cons_subset key)
  have hsum := Finset.sum_le_sum_of_subset (f := Prod.fst) hsub
  rwa [Finset.sum_insert hnot, Nat.add_comm] at hsum

private theorem moving_horizon_prime_phase_weighted_bound {slots s C sf Cf q first L U : Nat}
    {separators : Int} {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hcost : HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first separators) (hU : Cf ≤ U) :
    C ≤ Cf ∧ (L * (L + 1)) * first ≤
      (L * (L + 1)) * (2 * ∑ a ∈ unusedPrimePhases L seen, a.1) + 2 * (U + 1) * (Cf - C) := by
  induction q generalizing s C seen first separators with
  | zero =>
    obtain ⟨⟨_, rfl, _⟩, rfl, _⟩ := hcost
    simp
  | succ q ih =>
    obtain ⟨r, C', rest, _, hstep, htail, htotal, _⟩ := hcost
    obtain ⟨hC'f, hbound⟩ := ih htail
    have hup := moving_horizon_step_update hstep
    refine ⟨by omega, ?_⟩
    let W := L * (L + 1)
    let K := 2 * (U + 1)
    let nowSum := ∑ a ∈ unusedPrimePhases L seen, a.1
    let nextSum := ∑ a ∈ unusedPrimePhases L (recordLongPrimePhase phase seen s C r), a.1
    change W * rest ≤ W * (2 * nextSum) + K * (Cf - C') at hbound
    change W * first ≤ W * (2 * nowSum) + K * (Cf - C)
    have hgrowth : K * (Cf - C) = K * (Cf - C') + K * (C' - C) := by
      rw [← Nat.mul_add, show Cf - C' + (C' - C) = Cf - C by omega]
    have hsub : nextSum ≤ nowSum := by
      apply Finset.sum_le_sum_of_subset (f := Prod.fst)
      unfold recordLongPrimePhase
      split
      · exact unused_prime_phases_cons_subset _
      · exact Finset.Subset.rfl
    have hpay := Nat.mul_le_mul_left W (Nat.mul_le_mul_left 2 hsub)
    by_cases hf : IsFirstLongPrimePhase phase seen s C r
    · simp only [firstLongPrimePhaseGap, if_pos hf] at htotal
      rw [htotal, Nat.mul_add, hgrowth]
      by_cases hsmall : d r ≤ L
      · have hp := Nat.prime_def_lt'.mpr ⟨hstep.2.2.2.1,
          fun f hf' hlt => hf.2.1 ⟨f, hlt⟩ hf'⟩
        have hmem : (d r, phase C r) ∈ unusedPrimePhases L seen := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hsmall, hp⟩, Finset.mem_univ _⟩, hf.2.2⟩
        have hlong : 10 < r - s ∧ NoProperFactor (d r) := ⟨hf.1, hf.2.1⟩
        have hsum : nextSum + d r ≤ nowSum := by
          simpa only [nextSum, recordLongPrimePhase, if_pos hlong, nowSum]
            using unused_prime_phases_sum_cons_add hmem
        have hpay' : W * (2 * nextSum) + W * (2 * d r) ≤ W * (2 * nowSum) := by
          rw [← Nat.mul_add, ← Nat.mul_add]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum)
        have hgap := Nat.mul_le_mul_left W (moving_horizon_step_gap_le_twice_increment hstep)
        omega
      · have hlarge : W * (r - s) ≤ K * (C' - C) :=
          moving_horizon_large_increment_gap hstep (by omega) (by omega : C ≤ U)
        omega
    · simp only [firstLongPrimePhaseGap, if_neg hf, Nat.zero_add] at htotal
      rw [htotal, hgrowth]
      omega

theorem moving_horizon_first_prime_phase_travel_bound {slots s C sf Cf q first L U : Nat}
    {separators : Int} {phase : Nat → Nat → Fin slots}
    (hcost : HasMovingHorizonPhaseBalances210 phase s C sf Cf [] q first separators)
    (hU : Cf ≤ U) (hL : 0 < L) :
    first ≤ 2 * (slots * ∑ p ∈ Nat.primesLE L, p) + 2 * (U + 1) * (Cf - C) / (L * (L + 1)) := by
  obtain ⟨_, hbound⟩ := moving_horizon_prime_phase_weighted_bound (L := L) hcost hU
  have hs : (∑ a ∈ unusedPrimePhases (slots := slots) L [], a.1) = slots * ∑ p ∈ Nat.primesLE L, p := by
    simp [unusedPrimePhases, Finset.sum_product, Finset.mul_sum]
  rw [hs] at hbound
  let W := L * (L + 1)
  let low := 2 * (slots * ∑ p ∈ Nat.primesLE L, p)
  let growth := 2 * (U + 1) * (Cf - C)
  change W * first ≤ W * low + growth at hbound
  change first ≤ low + growth / W
  have hd : (first - low) * W ≤ growth := by
    rw [Nat.sub_mul, Nat.mul_comm first W, Nat.mul_comm low W]
    omega
  have h := (Nat.le_div_iff_mul_le (Nat.mul_pos hL (by omega))).2 hd
  change first - low ≤ growth / W at h
  omega

/-- The number of phase labels is fixed, but the labels may depend on
both coordinates. Charging the first long occurrence of each prime
in each phase still has uniformly sublinear cost. -/
theorem canonical_first_prime_phase_travel_sublinear (slots k : Nat) (hk : 0 < k) :
    ∃ threshold : Nat, ∀ {M sf Cf q first : Nat} {separators : Int} {phase : Nat → Nat → Fin slots},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonPhaseBalances210 phase (M + 2) (2 * M - 2) sf Cf [] q first separators →
      2 * (sf - (M + 2)) ≤ M → k * first ≤ M := by
  let b := max 1 slots
  have hb : 0 < b := Nat.lt_of_lt_of_le (by decide : 0 < 1) (le_max_left 1 slots)
  obtain ⟨threshold, hbudget⟩ := canonical_prime_gap_budget_sublinear (k * b) (Nat.mul_pos hk hb)
  refine ⟨threshold, ?_⟩
  intro M sf Cf q first separators phase hM hcanon hcost hshort
  have hpath := moving_horizon_phase_balances210_path hcost
  have hC := canonical_horizon_bound_of_short_travel hpath hshort
  have hstart := moving_horizon_path_index_le hpath
  have hce := D_mod_two_eq_zero_of_two_le (by omega : 2 ≤ sf)
  rw [(moving_horizon_path_endpoint hpath).2.1] at hce
  have hMpos := hcanon ▸ one_le_d_of_two_le (by omega : 2 ≤ M + 2)
  have hodd := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
  obtain ⟨L, hL, hbound⟩ := hbudget hM hC
  have hfinite := moving_horizon_first_prime_phase_travel_bound hcost (by omega : Cf ≤ 3 * M + 3) hL
  rw [show 3 * M + 3 + 1 = 3 * M + 4 by omega] at hfinite
  let low := ∑ p ∈ Nat.primesLE L, p
  let large := 2 * (3 * M + 4) * (Cf - (2 * M - 2)) / (L * (L + 1))
  change first ≤ 2 * (slots * low) + large at hfinite
  change (k * b) * (2 * low + large) ≤ M at hbound
  have hle : first ≤ b * (2 * low + large) := by
    rw [Nat.mul_add]
    have hlo : 2 * (slots * low) ≤ b * (2 * low) := by
      rw [Nat.mul_left_comm 2 slots low]
      exact Nat.mul_le_mul_right _ (le_max_right _ _)
    have hhi : large ≤ b * large := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right large (Nat.succ_le_of_lt hb)
    omega
  exact (Nat.mul_le_mul_left k hle).trans (by simpa only [Nat.mul_assoc] using hbound)

theorem canonical_first_crossing_requires_phase_balances210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ (s C r C' p first : Nat) (separators : Int),
      HasMovingHorizonPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first separators ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      (M : Int) < ((24 * (first + (r - s)) + 1315 : Nat) : Int) + separators := by
  obtain ⟨s, C, r, C', p, _, _, _, hledger, _, hfirst, hstep, hr, hp, hshort, hcross, hG, hg, _⟩ :=
    canonical_first_travel_crossing_excess hcanon hpath hlong
  obtain ⟨first, separators, hphase, hcost⟩ :=
    moving_horizon_phase_balances210 phase [] (moving_horizon_first_use_travel_path hfirst)
  have hV := (supported_excess_and_potential210_bounds (M + 2) (2 * M - 2) (by omega)).2
  have hsf := (moving_horizon_travel_excess_bounds hledger).1
  have hsr := hstep.2.1
  exact ⟨s, C, r, C', p, first, separators, hphase, hstep, hr, hp, hshort, hcross, hg, by omega⟩

theorem canonical_travel_bound_of_prime_phase_budget210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hbudget : ∀ {s C p first : Nat} {separators : Int},
      HasMovingHorizonPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first separators →
      2 * (s - (M + 2)) ≤ M →
      ((24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 1315 : Nat) : Int) + separators ≤ M) :
    2 * (sf - (M + 2)) ≤ M := by
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, separators, hphase, _, _, _, hs, _, hgap, hcross⟩ :=
      canonical_first_crossing_requires_phase_balances210 phase hcanon hpath (by omega)
    have hle := hbudget hphase hs
    omega

end A166944Research
