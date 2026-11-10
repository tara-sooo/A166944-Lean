import A166944.RecordReplay
import A166944.TravelResidues

/-!
# Charging first-hit travel to increments and their factors

Long gaps ending in a composite increment can be paid for by horizon
growth. A divisor of an increment also needs a definite amount of
intervening growth before it can divide another increment.
-/

namespace A166944Research

private theorem exists_small_factor_of_composite {e : Nat} (he : ¬ NoProperFactor e) :
    ∃ f : Nat, 1 < f ∧ f ∣ e ∧ f * f ≤ e := by
  by_cases h : ∃ f : Nat, 1 < f ∧ f ∣ e ∧ f * f ≤ e
  · exact h
  · exfalso
    apply he (no_proper_factor_of_no_small_factor (root := Nat.sqrt e) ?_ (Nat.lt_succ_sqrt e))
    intro f hf hdiv
    have hroot : f.val ≤ Nat.sqrt e := Nat.le_of_lt_succ f.isLt
    exact h ⟨f.val, hf, hdiv, Nat.le_trans (Nat.mul_le_mul hroot hroot) (Nat.sqrt_le e)⟩

/-- A gap greater than ten ending at a composite increment costs at
most one third of the growth caused by that increment. -/
theorem moving_horizon_long_composite_gap_le_growth {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hgap : 10 < r - s)
    (hcomposite : ¬ NoProperFactor (d r)) : 3 * (r - s) ≤ C' - C := by
  obtain ⟨f, hf, hdiv, hsq⟩ := exists_small_factor_of_composite hcomposite
  have hbound := moving_horizon_step_gap_le_twice_increment_factor hstep hf hdiv
  have hodd : f % 2 = 1 := by
    have hr : 3 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
    have hdo := d_mod_two_eq_one_of_three_le hr
    obtain ⟨k, hk⟩ := hdiv
    rw [hk, Nat.mul_mod] at hdo
    by_cases hz : f % 2 = 0
    · simp [hz] at hdo
    · omega
  have hf7 : 7 ≤ f := by omega
  have h7 := Nat.mul_le_mul_right f hf7
  have hup := moving_horizon_step_update hstep
  omega

private theorem add_mod_of_dvd {f n k : Nat} (hdiv : f ∣ n) (hk : k < f) :
    (n + k) % f = k := by
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hk]

/-- After an event using a divisor `f ≥ 5`, another event using the same
divisor needs at least `f-1` growth between the first end and the second start. -/
theorem moving_horizon_factor_reuse_growth {s C r C' t H u H' f : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hlater : IsMovingHorizonStep t H u H')
    (horder : r ≤ t) (hf : 5 ≤ f) (hdiv : f ∣ d r) (hdivLater : f ∣ d u) :
    f - 1 ≤ H - C' := by
  have hC : 0 < C := Nat.zero_lt_of_lt hstep.1.2.2
  have hH : 0 < H := Nat.zero_lt_of_lt hlater.1.2.2
  have hpos := hstep.2.2.2.1
  have hup := moving_horizon_step_update hstep
  have hafter : (C' + 2) % f = 0 ∨ (C' + 2) % f = 2 := by
    rcases moving_horizon_step_event_package hstep with ⟨_, hterm, _, _⟩ | ⟨_, hterm, _, _⟩
    · have hd : f ∣ C' := by
        rw [show C' = C - 1 + d r by omega]
        exact Nat.dvd_add (Nat.dvd_trans hdiv hterm) hdiv
      exact Or.inr (add_mod_of_dvd hd (by omega))
    · have hd : f ∣ C' + 2 := by
        rw [show C' + 2 = C + 1 + d r by omega]
        exact Nat.dvd_add (Nat.dvd_trans hdiv hterm) hdiv
      exact Or.inl (Nat.mod_eq_zero_of_dvd hd)
  have hbefore : (H + 2) % f = 1 ∨ (H + 2) % f = 3 := by
    rcases moving_horizon_step_event_package hlater with ⟨_, hterm, _, _⟩ | ⟨_, hterm, _, _⟩
    · right
      rw [show H + 2 = (H - 1) + 3 by omega]
      exact add_mod_of_dvd (Nat.dvd_trans hdivLater hterm) (by omega)
    · left
      exact add_mod_of_dvd (k := 1) (Nat.dvd_trans hdivLater hterm) (by omega)
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hCe : C' % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hHe : H % 2 = 0 := hlater.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hlater.1.1
  have hmono := D_le_of_le horder
  rw [hstate.2.1, hlater.1.2.1] at hmono
  by_cases h : f - 1 ≤ H - C'
  · exact h
  · let growth := H - C'
    have hEven : growth % 2 = 0 := by omega
    have hsmall : growth < f := by omega
    rw [show H + 2 = C' + 2 + growth by omega, Nat.add_mod, Nat.mod_eq_of_lt hsmall] at hbefore
    rcases hafter with hz | ht
    · rw [hz, Nat.zero_add, Nat.mod_eq_of_lt hsmall] at hbefore
      omega
    · rw [ht] at hbefore
      by_cases hlt : 2 + growth < f
      · rw [Nat.mod_eq_of_lt hlt] at hbefore
        omega
      · rw [show 2 + growth = f by omega, Nat.mod_self] at hbefore
        omega

/-- The next gap using the same divisor is bounded by the horizon
growth between the two starts, up to an additive two. -/
theorem moving_horizon_factor_reuse_gap {s C r C' t H u H' f : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hlater : IsMovingHorizonStep t H u H')
    (horder : r ≤ t) (hf : 5 ≤ f) (hdiv : f ∣ d r) (hdivLater : f ∣ d u) :
    u - t ≤ H - C + 2 := by
  have hreuse := moving_horizon_factor_reuse_growth hstep hlater horder hf hdiv hdivLater
  have hgap := moving_horizon_step_gap_le_twice_increment_factor hlater (by omega) hdivLater
  have hsize := Nat.le_of_dvd (by have := hstep.2.2.2.1; omega) hdiv
  have hup := moving_horizon_step_update hstep
  omega

private def residualGap (gap increment : Nat) : Nat :=
  if 10 < gap ∧ ¬ NoProperFactor increment then 0 else gap

/-- The total distance from the short gaps and the long gaps ending in
a prime increment on an actual first-hit path. -/
def HasMovingHorizonResidualTravel (s C sf Cf : Nat) : Nat → Nat → Prop
  | 0, total => HasMovingHorizonPathTo s C sf Cf 0 ∧ total = 0
  | q + 1, total =>
      ∃ r C' rest, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonResidualTravel r C' sf Cf q rest ∧
        total = residualGap (r - s) (d r) + rest

theorem moving_horizon_path_residual_travel_exists {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ total, HasMovingHorizonResidualTravel s C sf Cf q total := by
  induction q generalizing s C with
  | zero => exact ⟨0, hpath, rfl⟩
  | succ q ih =>
    obtain ⟨_, r, C', hstep, htail⟩ := hpath
    obtain ⟨rest, hrest⟩ := ih htail
    exact ⟨_, r, C', rest, hstep, hrest, rfl⟩

theorem moving_horizon_residual_travel_bound {s C sf Cf q total : Nat}
    (hcost : HasMovingHorizonResidualTravel s C sf Cf q total) :
    s ≤ sf ∧ C ≤ Cf ∧ 3 * (sf - s) ≤ 3 * total + (Cf - C) := by
  induction q generalizing s C total with
  | zero =>
    obtain ⟨⟨rfl, rfl, _⟩, rfl⟩ := hcost
    omega
  | succ q ih =>
    obtain ⟨r, C', rest, hstep, hrest, hsum⟩ := hcost
    obtain ⟨hr, hC', htail⟩ := ih hrest
    have hsr := hstep.2.1
    have hup := moving_horizon_step_update hstep
    by_cases h : 10 < r - s ∧ ¬ NoProperFactor (d r)
    · have hgap := moving_horizon_long_composite_gap_le_growth hstep h.1 h.2
      simp only [residualGap, if_pos h, Nat.zero_add] at hsum
      omega
    · simp only [residualGap, if_neg h] at hsum
      omega

/-- None of the preceding nonunit increments was divisible by `f`. -/
abbrev IsNewIncrementFactor (seen : List Nat) (f : Nat) : Prop :=
  ∀ e ∈ seen, ¬ f ∣ e

def firstUseTravelGap (seen : List Nat) (gap e : Nat) : Nat :=
  if 10 < gap ∧ NoProperFactor e ∧ IsNewIncrementFactor seen e then gap else 0

/-- The distance from long gaps ending in primes which have not divided
an earlier increment. `seen` contains the increments before the start
of this part of the path. Start a new replay with an empty list. -/
def HasMovingHorizonFirstUseTravel (s C sf Cf : Nat) (seen : List Nat) : Nat → Nat → Prop
  | 0, total => HasMovingHorizonPathTo s C sf Cf 0 ∧ total = 0
  | q + 1, total =>
      ∃ r C' rest, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonFirstUseTravel r C' sf Cf (d r :: seen) q rest ∧
        total = firstUseTravelGap seen (r - s) (d r) + rest

theorem moving_horizon_first_use_travel_path {s C sf Cf q total : Nat} {seen : List Nat}
    (hcost : HasMovingHorizonFirstUseTravel s C sf Cf seen q total) :
    HasMovingHorizonPathTo s C sf Cf q := by
  induction q generalizing s C seen total with
  | zero => exact hcost.1
  | succ q ih =>
    obtain ⟨r, C', _, hstep, hrest, _⟩ := hcost
    exact ⟨hstep.1, r, C', hstep, ih hrest⟩

theorem moving_horizon_residual_travel_first_use {s C sf Cf q total : Nat}
    (hcost : HasMovingHorizonResidualTravel s C sf Cf q total) (seen : List Nat) :
    ∃ first, HasMovingHorizonFirstUseTravel s C sf Cf seen q first ∧ first ≤ total := by
  induction q generalizing s C seen total with
  | zero => exact ⟨0, ⟨hcost.1, rfl⟩, Nat.zero_le _⟩
  | succ q ih =>
    obtain ⟨r, C', rest, hstep, hrest, hsum⟩ := hcost
    obtain ⟨first, hfirst, hle⟩ := ih hrest (d r :: seen)
    have hgap : firstUseTravelGap seen (r - s) (d r) ≤ residualGap (r - s) (d r) := by
      by_cases h : 10 < r - s ∧ NoProperFactor (d r) ∧ IsNewIncrementFactor seen (d r)
      · have hnot : ¬ (10 < r - s ∧ ¬ NoProperFactor (d r)) := fun hn => hn.2 h.2.1
        simp only [firstUseTravelGap, residualGap, if_pos h, if_neg hnot, Nat.le_refl]
      · rw [firstUseTravelGap, if_neg h]
        exact Nat.zero_le _
    refine ⟨_, ⟨r, C', first, hstep, hfirst, rfl⟩, ?_⟩
    rw [hsum]
    exact Nat.add_le_add hgap hle

/-- Before the first step across the short-travel cutoff, the horizon
has at most `M+5` growth. Consequently the residual travel before that
step and the bound for the crossing gap have a combined lower bound. -/
theorem canonical_first_travel_crossing_residual {M sf Cf q : Nat}
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ s C r C' p total : Nat,
      HasMovingHorizonResidualTravel (M + 2) (2 * M - 2) s C p total ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      3 * M < 6 * (total + (r - s)) + 2 * (C - (2 * M - 2)) ∧
      M < 6 * (total + Nat.sqrt (4 * (3 * M + 4))) + 10 := by
  let cutoff := M + 2 + M / 2
  obtain ⟨s, C, r, C', p, hpre, hstep, hs, hr, hp, hrf⟩ :=
    moving_horizon_path_first_index_crossing hpath (by omega : M + 2 ≤ cutoff) (by omega)
  have hshort : 2 * (s - (M + 2)) ≤ M := by omega
  have hcross : M < 2 * (r - (M + 2)) := by omega
  have hC := canonical_horizon_bound_of_short_travel hpre hshort
  have hCe : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hMpos : 0 < M := by
    have hpos := one_le_d_of_two_le (by omega : 2 ≤ M + 2)
    omega
  have hMo : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
  have hband : C ≤ 3 * M + 3 := by omega
  have hgap := moving_horizon_step_gap_le_sqrt hstep hband
  rw [show 3 * M + 3 + 1 = 3 * M + 4 by omega] at hgap
  obtain ⟨total, hcost⟩ := moving_horizon_path_residual_travel_exists hpre
  obtain ⟨hstart, _, hbound⟩ := moving_horizon_residual_travel_bound hcost
  have hsr := hstep.2.1
  refine ⟨s, C, r, C', p, total, hcost, hstep, hrf, hp, hshort, hcross, ?_, ?_⟩ <;> omega

end A166944Research
