import A166944.ResidualPhaseCredits210

/-! # Explicit startup bounds for the residual balance -/

open Finset

namespace A166944Research

private theorem residual_small_factor {e : Nat} (he : ¬ NoProperFactor e) :
    ∃ f : Nat, 1 < f ∧ f ∣ e ∧ f * f ≤ e := by
  by_cases h : ∃ f : Nat, 1 < f ∧ f ∣ e ∧ f * f ≤ e
  · exact h
  · exfalso
    apply he (no_proper_factor_of_no_small_factor (root := Nat.sqrt e) ?_ (Nat.lt_succ_sqrt e))
    intro f hf hdiv
    have hroot : f.val ≤ Nat.sqrt e := Nat.le_of_lt_succ f.isLt
    exact h ⟨f.val, hf, hdiv, (Nat.mul_le_mul hroot hroot).trans (Nat.sqrt_le e)⟩

/-- A startup event has no earlier long prime in its phase. This
includes a first positive short event following an earlier negative one. -/
theorem residual_phase_startup_bounds210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C')
    (hnotreuse : ¬ (10 < r - s ∧ NoProperFactor (d r) ∧ (d r, phase C r) ∈ seen))
    (hpositive : 0 < residualPhaseSeparatorBalance210 phase seen s C r C') :
    d r ≤ 169 ∧ (residualPhaseSeparatorBalance210 phase seen s C r C').toNat ≤ 1478 := by
  classical
  have hr3 : 3 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
  have heodd := d_mod_two_eq_one_of_three_le hr3
  have hepos := hstep.2.2.2.1
  have he3 : 3 ≤ d r := by omega
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  have hdiv : ¬ d r ∣ 210 := by
    intro hd
    simp only [residualPhaseSeparatorBalance210, if_pos hd] at hpositive
    omega
  have hraw := hpositive
  simp only [residualPhaseSeparatorBalance210, if_neg hdiv] at hraw
  by_cases hshort : r - s ≤ 10
  · have hrest : 24 * ((r - s) - firstLongPrimePhaseGap phase seen s C r) ≤ 240 := by omega
    have hcap : (residualPhaseSeparatorBalance210 phase seen s C r C').toNat ≤ 1478 := by
      simp only [residualPhaseSeparatorBalance210, if_neg hdiv]
      omega
    exact ⟨by omega, hcap⟩
  · have hlong : 10 < r - s := by omega
    by_cases hp : NoProperFactor (d r)
    · have hnew : (d r, phase C r) ∉ seen := fun hm => hnotreuse ⟨hlong, hp, hm⟩
      have hf : IsFirstLongPrimePhase phase seen s C r := ⟨hlong, hp, hnew⟩
      have hfirst : firstLongPrimePhaseGap phase seen s C r = r - s := by
        simp only [firstLongPrimePhaseGap, if_pos hf]
      rw [hfirst, Nat.sub_self, Nat.mul_zero, Int.natCast_zero] at hraw
      constructor
      · omega
      · simp only [residualPhaseSeparatorBalance210, if_neg hdiv, hfirst, Nat.sub_self,
          Nat.mul_zero, Int.natCast_zero]
        omega
    · have hf : ¬ IsFirstLongPrimePhase phase seen s C r := fun h => hp h.2.1
      have hfirst : firstLongPrimePhaseGap phase seen s C r = 0 := by
        simp only [firstLongPrimePhaseGap, if_neg hf]
      rw [hfirst, Nat.sub_zero] at hraw
      obtain ⟨f, hf, hfd, hsq⟩ := residual_small_factor hp
      have hg := moving_horizon_step_gap_le_twice_increment_factor hstep hf hfd
      have hfo : f % 2 = 1 := by
        obtain ⟨k, hk⟩ := hfd
        rw [hk, Nat.mul_mod] at heodd
        by_cases hz : f % 2 = 0
        · simp [hz] at heodd
        · omega
      have hf7 : 7 ≤ f := by omega
      have hsmallf : f ≤ 13 := by
        by_contra h
        have hs := Nat.mul_le_mul_left 11 hsq
        have hl := Nat.mul_le_mul_left 11 (Nat.mul_le_mul_right f (by omega : 14 ≤ f))
        have hg24 := Nat.mul_le_mul_left 24 hg
        omega
      have he172 : d r ≤ 172 := by
        have hg24 := Nat.mul_le_mul_left 24 hg
        omega
      have he169 : d r ≤ 169 := by
        by_contra h
        have he171 : d r = 171 := by omega
        have hd3 : 3 ∣ d r := by rw [he171]; decide
        have hg3 := moving_horizon_step_gap_le_twice_increment_factor hstep (by decide : 1 < 3) hd3
        omega
      have hseven := moving_horizon_long_composite_seven_growth hstep hlong hp
      have hup := moving_horizon_step_update hstep
      refine ⟨he169, ?_⟩
      simp only [residualPhaseSeparatorBalance210, if_neg hdiv, hfirst, Nat.sub_zero]
      omega

@[irreducible] def residualStartupIncrements210 : Finset Nat :=
  (Finset.range 170).filter (fun e => 1 < e ∧ e % 2 = 1 ∧ ¬ e ∣ 210)

@[irreducible] def residualStartupCodes210 : Finset Nat :=
  ((residualStartupIncrements210 ×ˢ Finset.range 105) ×ˢ Finset.range 2).image
    (fun x => 420 * x.1.1 + 4 * x.1.2 + x.2)

set_option maxRecDepth 4096

private theorem residual_startup_increment_count210 : residualStartupIncrements210.card = 77 := by
  unfold residualStartupIncrements210
  decide +kernel

theorem residual_startup_code_count210 : residualStartupCodes210.card = 16170 := by
  let args : Finset ((Nat × Nat) × Nat) :=
    (residualStartupIncrements210 ×ˢ Finset.range 105) ×ˢ Finset.range 2
  have hinj : Set.InjOn (fun x : (Nat × Nat) × Nat => 420 * x.1.1 + 4 * x.1.2 + x.2)
      (args : Set _) := by
    rintro ⟨⟨e, h⟩, b⟩ hx ⟨⟨e', h'⟩, b'⟩ hy heq
    simp only [args, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx hy
    have hh : h < 105 := hx.1.2
    have hb : b < 2 := hx.2
    have hh' : h' < 105 := hy.1.2
    have hb' : b' < 2 := hy.2
    dsimp only at heq
    have he : e = e' := by omega
    have hH : h = h' := by omega
    have hB : b = b' := by omega
    exact Prod.ext (Prod.ext he hH) hB
  unfold residualStartupCodes210
  change (args.image (fun x => 420 * x.1.1 + 4 * x.1.2 + x.2)).card = 16170
  rw [Finset.card_image_of_injOn hinj]
  dsimp only [args]
  rw [Finset.card_product, Finset.card_product,
    Finset.card_range, Finset.card_range, residual_startup_increment_count210]

theorem residual_phase_startup_key_mem210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C')
    (hnotreuse : ¬ (10 < r - s ∧ NoProperFactor (d r) ∧ (d r, phase C r) ∈ seen))
    (hpositive : 0 < residualPhaseSeparatorBalance210 phase seen s C r C') :
    420 * d r + 2 * (C % 210) + r % 2 ∈ residualStartupCodes210 := by
  obtain ⟨he, _⟩ := residual_phase_startup_bounds210 hstep hnotreuse hpositive
  have hr : 3 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
  have hodd := d_mod_two_eq_one_of_three_le hr
  have hepos := hstep.2.2.2.1
  have hdiv : ¬ d r ∣ 210 := by
    intro hd
    simp only [residualPhaseSeparatorBalance210, if_pos hd] at hpositive
    omega
  have hce : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hmod := Nat.mod_lt C (by decide : 0 < 210)
  have hh : (C % 210) / 2 < 105 := by omega
  have hb : r % 2 < 2 := Nat.mod_lt _ (by decide)
  have heMem : d r ∈ residualStartupIncrements210 := by
    unfold residualStartupIncrements210
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hepos, hodd, hdiv⟩
  unfold residualStartupCodes210
  apply Finset.mem_image.mpr
  refine ⟨((d r, (C % 210) / 2), r % 2), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨heMem, Finset.mem_range.mpr hh⟩, Finset.mem_range.mpr hb⟩
  · dsimp only
    omega

def residualPhaseStartupBound210 : Nat := 16170 * 1478

/-- Distinct reachable startup keys have a much smaller total charge
than the old all-increments/all-phase-codes bound. -/
theorem residual_startup_sum_bound210 {n : Nat} {cost : Fin n → Int}
    (startup : Finset (Fin n)) (key : Fin n → Nat)
    (unique : Set.InjOn key (startup : Set (Fin n)))
    (allowed : ∀ i ∈ startup, key i ∈ residualStartupCodes210)
    (cap : ∀ i ∈ startup, (cost i).toNat ≤ 1478) :
    (∑ i ∈ startup, (cost i).toNat) ≤ residualPhaseStartupBound210 := by
  have hcard := Finset.card_le_card_of_injOn key (t := residualStartupCodes210) allowed unique
  rw [residual_startup_code_count210] at hcard
  calc
    (∑ i ∈ startup, (cost i).toNat) ≤ ∑ _i ∈ startup, 1478 := Finset.sum_le_sum cap
    _ = startup.card * 1478 := by simp
    _ ≤ 16170 * 1478 := Nat.mul_le_mul_right _ hcard

end A166944Research
