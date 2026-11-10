import A166944.TravelFactors

/-!
# Travel not paid for by horizon growth

Keep short gaps and long gaps ending at reused primes in one budget.
Each step contributes the part of 24 times its remaining gap that
exceeds its own horizon growth.
-/

namespace A166944Research

def shortOrReusedTravelGap (seen : List Nat) (gap e : Nat) : Nat :=
  if gap ≤ 10 ∨ (NoProperFactor e ∧ ¬ IsNewIncrementFactor seen e) then gap else 0

private theorem residual_travel_gap_split (seen : List Nat) (gap e : Nat) :
    residualTravelGap gap e = firstUseTravelGap seen gap e + shortOrReusedTravelGap seen gap e := by
  unfold residualTravelGap firstUseTravelGap shortOrReusedTravelGap
  by_cases hg : gap ≤ 10
  · have hres : ¬ (10 < gap ∧ ¬ NoProperFactor e) := by intro h; have := h.1; omega
    have hfirst : ¬ (10 < gap ∧ NoProperFactor e ∧ IsNewIncrementFactor seen e) := by
      intro h
      have := h.1
      omega
    rw [if_neg hres, if_neg hfirst, if_pos (Or.inl hg), Nat.zero_add]
  · have hlong : 10 < gap := by omega
    by_cases hp : NoProperFactor e
    · have hres : ¬ (10 < gap ∧ ¬ NoProperFactor e) := fun h => h.2 hp
      by_cases hnew : IsNewIncrementFactor seen e
      · have hremaining : ¬ (gap ≤ 10 ∨ (NoProperFactor e ∧ ¬ IsNewIncrementFactor seen e)) :=
          fun h => h.elim hg (fun h => h.2 hnew)
        rw [if_neg hres, if_pos ⟨hlong, hp, hnew⟩, if_neg hremaining, Nat.add_zero]
      · have hfirst : ¬ (10 < gap ∧ NoProperFactor e ∧ IsNewIncrementFactor seen e) :=
          fun h => hnew h.2.2
        rw [if_neg hres, if_neg hfirst, if_pos (Or.inr ⟨hp, hnew⟩), Nat.zero_add]
    · have hfirst : ¬ (10 < gap ∧ NoProperFactor e ∧ IsNewIncrementFactor seen e) := fun h => hp h.2.1
      have hremaining : ¬ (gap ≤ 10 ∨ (NoProperFactor e ∧ ¬ IsNewIncrementFactor seen e)) :=
        fun h => h.elim hg (fun h => hp h.1)
      rw [if_pos ⟨hlong, hp⟩, if_neg hfirst, if_neg hremaining]

/-- Natural subtraction clips the excess at zero. -/
def shortOrReusedTravelExcess (seen : List Nat) (gap e : Nat) : Nat :=
  24 * shortOrReusedTravelGap seen gap e - (e - 1)

theorem short_or_reused_excess_zero_of_short_large {seen : List Nat} {gap e : Nat}
    (hgap : gap ≤ 10) (he : 241 ≤ e) : shortOrReusedTravelExcess seen gap e = 0 := by
  rw [shortOrReusedTravelExcess, shortOrReusedTravelGap, if_pos (Or.inl hgap)]
  omega

private theorem short_or_reused_travel_gap_le (seen : List Nat) (gap e : Nat) :
    shortOrReusedTravelGap seen gap e ≤ gap := by
  unfold shortOrReusedTravelGap
  split <;> omega

theorem moving_horizon_excess_zero_of_large_increment {s C r C' U : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (hU : C ≤ U)
    (he : 48 * (U + 1) ≤ d r * (d r - 1)) : shortOrReusedTravelExcess seen (r - s) (d r) = 0 := by
  have hprod := moving_horizon_step_gap_mul_increment_le_twice_horizon hstep
  have hmul : (24 * (r - s)) * d r ≤ (d r - 1) * d r := by
    calc
      (24 * (r - s)) * d r = 24 * ((r - s) * d r) := Nat.mul_assoc _ _ _
      _ ≤ 24 * (2 * (C + 1)) := Nat.mul_le_mul_left _ hprod
      _ ≤ 48 * (U + 1) := by omega
      _ ≤ d r * (d r - 1) := he
      _ = (d r - 1) * d r := Nat.mul_comm _ _
  have hpos : 0 < d r := Nat.lt_trans (by decide) hstep.2.2.2.1
  have hgap := Nat.le_of_mul_le_mul_right hmul hpos
  have hrest := Nat.mul_le_mul_left 24 (short_or_reused_travel_gap_le seen (r - s) (d r))
  unfold shortOrReusedTravelExcess
  omega

theorem moving_horizon_positive_excess_cases {s C r C' U : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (hU : C ≤ U)
    (hpos : 0 < shortOrReusedTravelExcess seen (r - s) (d r)) :
    (r - s ≤ 10 ∧ d r ≤ 240) ∨
      (10 < r - s ∧ NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor seen (d r) ∧
        d r * (d r - 1) < 48 * (U + 1)) := by
  by_cases hshort : r - s ≤ 10
  · left
    refine ⟨hshort, ?_⟩
    by_cases he : d r ≤ 240
    · exact he
    · have hzero := short_or_reused_excess_zero_of_short_large (seen := seen) (e := d r) hshort (by omega)
      omega
  · right
    have hused : NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor seen (d r) := by
      by_cases h : NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor seen (d r)
      · exact h
      · have hnone : ¬ (r - s ≤ 10 ∨ (NoProperFactor (d r) ∧ ¬ IsNewIncrementFactor seen (d r))) :=
          fun hc => hc.elim hshort h
        rw [shortOrReusedTravelExcess, shortOrReusedTravelGap, if_neg hnone] at hpos
        omega
    refine ⟨by omega, hused.1, hused.2, ?_⟩
    by_cases he : d r * (d r - 1) < 48 * (U + 1)
    · exact he
    · have hzero := moving_horizon_excess_zero_of_large_increment (seen := seen) hstep hU (by omega)
      omega

/-- Exact remaining travel and excess on one genuine first-hit path. -/
def HasMovingHorizonTravelExcess (s C sf Cf : Nat) (seen : List Nat) : Nat → Nat → Nat → Prop
  | 0, remaining, excess => HasMovingHorizonPathTo s C sf Cf 0 ∧ remaining = 0 ∧ excess = 0
  | q + 1, remaining, excess =>
      ∃ r C' rest tailExcess, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonTravelExcess r C' sf Cf (d r :: seen) q rest tailExcess ∧
        remaining = shortOrReusedTravelGap seen (r - s) (d r) + rest ∧
        excess = shortOrReusedTravelExcess seen (r - s) (d r) + tailExcess

theorem moving_horizon_residual_first_use_travel_excess {s C sf Cf q total first : Nat}
    {seen : List Nat} (hres : HasMovingHorizonResidualTravel s C sf Cf q total)
    (hfirst : HasMovingHorizonFirstUseTravel s C sf Cf seen q first) :
    ∃ excess, HasMovingHorizonTravelExcess s C sf Cf seen q (total - first) excess ∧ first ≤ total := by
  induction q generalizing s C seen total first with
  | zero =>
    obtain ⟨hpath, rfl⟩ := hres
    obtain ⟨_, rfl⟩ := hfirst
    exact ⟨0, ⟨hpath, rfl, rfl⟩, Nat.le_refl _⟩
  | succ q ih =>
    obtain ⟨r, C', rest, hstep, hrest, htotal⟩ := hres
    obtain ⟨u, H', firstRest, hstep', hfirstRest, hfirst⟩ := hfirst
    obtain ⟨hr, hC⟩ := moving_horizon_step_unique hstep hstep'
    subst u
    subst H'
    obtain ⟨excess, hExcess, hle⟩ := ih hrest hfirstRest
    have hsplit := residual_travel_gap_split seen (r - s) (d r)
    exact ⟨_, ⟨r, C', rest - firstRest, excess, hstep, hExcess, by omega, rfl⟩, by omega⟩

theorem moving_horizon_travel_excess_bounds {s C sf Cf q remaining excess : Nat} {seen : List Nat}
    (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess) :
    s ≤ sf ∧ C ≤ Cf ∧ 24 * remaining ≤ Cf - C + excess ∧ excess ≤ 24 * (sf - s) := by
  induction q generalizing s C seen remaining excess with
  | zero =>
    obtain ⟨⟨rfl, rfl, _⟩, rfl, rfl⟩ := hledger
    omega
  | succ q ih =>
    obtain ⟨r, C', rest, tailExcess, hstep, htail, hremaining, hexcess⟩ := hledger
    obtain ⟨hr, hC', hpay, htailExcess⟩ := ih htail
    have hsr := hstep.2.1
    have hup := moving_horizon_step_update hstep
    have hgap := short_or_reused_travel_gap_le seen (r - s) (d r)
    have hlocal := show shortOrReusedTravelExcess seen (r - s) (d r) =
        24 * shortOrReusedTravelGap seen (r - s) (d r) - (d r - 1) from rfl
    omega

theorem moving_horizon_travel_excess_of_common_multiple {s C sf Cf q remaining excess P : Nat}
    {seen : List Nat} (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess)
    (hpath : HasMovingHorizonPathTo s C sf Cf q) (hP : 0 < P) (hPeven : P % 2 = 0)
    (hdiv : ∀ j : Nat, s < j → j ≤ sf → d j ∣ P) : excess ≤ 72 * (P - 1) := by
  have htravel := moving_horizon_path_travel_of_common_multiple hpath hP hPeven hdiv
  have hcost := (moving_horizon_travel_excess_bounds hledger).2.2.2
  omega

/-- The last `f-1` units of horizon growth before a use of `f`. -/
def InReuseWindow (x C f : Nat) : Prop := C - (f - 1) ≤ x ∧ x < C

theorem moving_horizon_reuse_window_after_previous {s C r C' t H u H' f x : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hlater : IsMovingHorizonStep t H u H')
    (horder : r ≤ t) (hf : 5 ≤ f) (hdiv : f ∣ d r) (hdivLater : f ∣ d u)
    (hwindow : InReuseWindow x H f) : C' ≤ x := by
  have h := moving_horizon_factor_reuse_growth hstep hlater horder hf hdiv hdivLater
  have hx := hwindow.1
  omega

/-- If the first and third backward windows contain the same point,
the third width exceeds the sum of the first two event widths. -/
theorem moving_horizon_third_reuse_window_width {s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' s₃ C₃ r₃ C₃' x : Nat}
    (h₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁') (h₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (h₃ : IsMovingHorizonStep s₃ C₃ r₃ C₃') (h₁₂ : r₁ ≤ s₂) (h₂₃ : r₂ ≤ s₃)
    (hx₁ : InReuseWindow x C₁ (d r₁)) (hx₃ : InReuseWindow x C₃ (d r₃)) :
    (d r₁ - 1) + (d r₂ - 1) < d r₃ - 1 := by
  have hD₁₂ := D_le_of_le h₁₂
  have hD₂₃ := D_le_of_le h₂₃
  rw [← h₁.2.2.2.2.2.2.1, h₂.1.2.1] at hD₁₂
  rw [← h₂.2.2.2.2.2.2.1, h₃.1.2.1] at hD₂₃
  have hC₁ := moving_horizon_step_update h₁
  have hC₂ := moving_horizon_step_update h₂
  have hleft := hx₁.2
  have hright := hx₃.1
  omega

/-- Within any band `[B, 2*B)`, three ordered reuse windows cannot
contain a common point. In fact the first and third are disjoint. -/
theorem moving_horizon_reuse_windows_no_three_in_band
    {s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' s₃ C₃ r₃ C₃' x B : Nat}
    (h₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁') (h₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (h₃ : IsMovingHorizonStep s₃ C₃ r₃ C₃') (h₁₂ : r₁ ≤ s₂) (h₂₃ : r₂ ≤ s₃)
    (hB₁ : B ≤ d r₁ - 1) (hB₂ : B ≤ d r₂ - 1) (hB₃ : d r₃ - 1 < 2 * B) :
    ¬ (InReuseWindow x C₁ (d r₁) ∧ InReuseWindow x C₃ (d r₃)) := by
  intro ⟨hx₁, hx₃⟩
  have h := moving_horizon_third_reuse_window_width h₁ h₂ h₃ h₁₂ h₂₃ hx₁ hx₃
  omega

/-- A finite first-crossing bound using exact growth, first-use travel,
and the crossing gap. It needs no asymptotic estimate. -/
theorem canonical_first_travel_crossing_excess {M sf Cf q : Nat}
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ s C r C' p total first excess : Nat,
      HasMovingHorizonTravelExcess (M + 2) (2 * M - 2) s C [] p (total - first) excess ∧
      HasMovingHorizonResidualTravel (M + 2) (2 * M - 2) s C p total ∧
      HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) s C [] p first ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      C - (2 * M - 2) ≤ M + 5 ∧ r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      12 * M < 24 * (first + (r - s)) + 9 * (C - (2 * M - 2)) + excess := by
  obtain ⟨s, C, r, C', p, total, hres, hstep, hr, hp, hshort, hcross, hdist, _⟩ :=
    canonical_first_travel_crossing_residual hcanon hpath hlong
  obtain ⟨first, hfirst, hle⟩ := moving_horizon_residual_travel_first_use hres []
  obtain ⟨excess, hledger, _⟩ := moving_horizon_residual_first_use_travel_excess hres hfirst
  have hpay := (moving_horizon_travel_excess_bounds hledger).2.2.1
  have hC := canonical_horizon_bound_of_short_travel (moving_horizon_first_use_travel_path hfirst) hshort
  have hCe : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hMpos : 0 < M := by
    have h := one_le_d_of_two_le (by omega : 2 ≤ M + 2)
    omega
  have hMo : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
  have hgap := moving_horizon_step_gap_le_sqrt hstep (by omega : C ≤ 3 * M + 3)
  rw [show 3 * M + 3 + 1 = 3 * M + 4 by omega] at hgap
  refine ⟨s, C, r, C', p, total, first, excess, hledger, hres, hfirst, hstep, hr, hp,
    hshort, hcross, by omega, hgap, ?_⟩
  omega

end A166944Research
