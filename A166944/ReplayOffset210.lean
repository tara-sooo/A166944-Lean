import A166944.RebalancedBoundary210

/-! # The index offset after a first hit

The offset `2*s-C` equals `3*s-a(s)` at a replay state. Its residue
after a hit is determined by the increment and the parity of the
hit. Returns to offset at most six allow the subsequent offset to be
bounded using only the suffix of the path.
-/

open Finset

namespace A166944Research

def replayIndexOffset (s C : Nat) : Nat := 2 * s - C

private theorem twice_dvd_of_odd_dvd_of_even {e x : Nat}
    (odd : e % 2 = 1) (even : x % 2 = 0) (div : e ∣ x) : 2 * e ∣ x := by
  obtain ⟨k, hk⟩ := div
  have he : k % 2 = 0 := by rw [quotient_mod_two_of_left_odd odd, ← hk, even]
  refine ⟨k / 2, ?_⟩
  calc
    x = e * k := hk
    _ = e * (2 * (k / 2)) := congrArg (e * ·) (by omega)
    _ = (2 * e) * (k / 2) := by ac_rfl

theorem moving_horizon_step_index_offset_update {s C r C' : Nat} (step : IsMovingHorizonStep s C r C') :
    replayIndexOffset r C' + (d r - 1) = replayIndexOffset s C + 2 * (r - s) := by
  have post : IsMovingHorizonState r C' := step.2.2.2.2.2.2.2.2
  have hC := moving_horizon_state_horizon_le_twice_index step.1
  have hC' := moving_horizon_state_horizon_le_twice_index post
  have hup := moving_horizon_step_update step
  have hsr := step.2.1
  unfold replayIndexOffset
  omega

theorem moving_horizon_step_index_offset_residue {s C r C' : Nat} (step : IsMovingHorizonStep s C r C')
    (large : 5 ≤ d r) :
    ∃ k : Nat, replayIndexOffset r C' = (2 * d r) * k + (if r % 2 = 0 then 0 else 6) := by
  have post : IsMovingHorizonState r C' := step.2.2.2.2.2.2.2.2
  have hC' := moving_horizon_state_horizon_le_twice_index post
  have hCe := post.2.1 ▸ D_mod_two_eq_zero_of_two_le post.1
  have hr3 : 3 ≤ r := by have := step.1.1; have := step.2.1; omega
  have he := d_mod_two_eq_one_of_three_le hr3
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · obtain ⟨u, v, hu, _, _, _, _, hv⟩ := moving_horizon_even_factor_pair step rfl h
    have hrd : d r ∣ r := ⟨u, hu⟩
    have hCd : d r ∣ C' := ⟨v + 1, hv⟩
    have hdiv := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hrd 2) hCd
    obtain ⟨k, hk⟩ := twice_dvd_of_odd_dvd_of_even he (by omega) hdiv
    exact ⟨k, by simpa only [replayIndexOffset, h, if_pos, Nat.add_zero] using hk⟩
  · obtain ⟨u, v, hu, _, _, _, _, hv⟩ := moving_horizon_odd_factor_pair step rfl h
    have hrd : d r ∣ r - 2 := ⟨u, hu⟩
    have hCd : d r ∣ C' + 2 := ⟨v + 1, hv⟩
    have hrd' := Nat.dvd_mul_left_of_dvd hrd 2
    have hpos : C' + 2 ≤ 2 * (r - 2) := by
      by_cases hle : C' + 2 ≤ 2 * (r - 2)
      · exact hle
      · have hdiv := twice_dvd_of_odd_dvd_of_even he (by omega) (Nat.dvd_sub hCd hrd')
        have hsize := Nat.le_of_dvd (by omega : 0 < C' + 2 - 2 * (r - 2)) hdiv
        omega
    obtain ⟨k, hk⟩ := twice_dvd_of_odd_dvd_of_even he (by omega) (Nat.dvd_sub hrd' hCd)
    refine ⟨k, ?_⟩
    simp only [replayIndexOffset, h, Nat.one_ne_zero, if_false]
    omega

/-- An increment above the cofactor threshold returns the offset to
zero at an even hit and six at an odd hit. -/
theorem moving_horizon_step_index_offset_reset {s C r C' : Nat} (step : IsMovingHorizonStep s C r C')
    (large : 5 ≤ d r) (size : d r * (replayIndexOffset s C + 1) + 4 * (C + 1) < 3 * d r * d r) :
    replayIndexOffset r C' = if r % 2 = 0 then 0 else 6 := by
  obtain ⟨k, hk⟩ := moving_horizon_step_index_offset_residue step large
  by_cases hzero : k = 0
  · simpa [hzero] using hk
  · have hlo := Nat.mul_le_mul_left (2 * d r) (show 1 ≤ k by omega)
    have hupdate := moving_horizon_step_index_offset_update step
    have hgap := moving_horizon_step_gap_mul_increment_le_twice_horizon step
    have hbound : 3 * d r ≤ replayIndexOffset s C + 1 + 2 * (r - s) := by
      rw [Nat.mul_one] at hlo
      omega
    have hproduct : 3 * d r * d r ≤ d r * (replayIndexOffset s C + 1) + 4 * (C + 1) := calc
      _ ≤ (replayIndexOffset s C + 1 + 2 * (r - s)) * d r := Nat.mul_le_mul_right _ hbound
      _ = d r * (replayIndexOffset s C + 1) + 2 * ((r - s) * d r) := by rw [Nat.add_mul, Nat.mul_assoc]; ac_rfl
      _ ≤ _ := by omega
    omega

/-- A small offset permits a quadratic horizon bound when excluding
an inside new record. -/
theorem moving_horizon_no_new_record_of_half_offset_quadratic_horizon {M s C r C' : Nat}
    (hM : 5 < M) (step : IsMovingHorizonStep s C r C')
    (offset : 2 * replayIndexOffset s C ≤ M) (horizon : 8 * (C + 1) ≤ M * M) : d r ≤ M := by
  by_cases hold : d r ≤ M
  · exact hold
  · have hpos := moving_horizon_index_offset_of_large_increment step (by omega)
    have hC := moving_horizon_state_horizon_le_twice_index step.1
    have hsr := step.2.1
    have hgap := moving_horizon_step_gap_mul_increment_le_twice_horizon step
    have h4 : M ≤ 4 * (r - s) := by unfold replayIndexOffset at offset; omega
    have hlo := Nat.mul_lt_mul_of_pos_left (show M < d r by omega) (by omega : 0 < M)
    have hhi := Nat.mul_le_mul_right (d r) h4
    rw [Nat.mul_assoc] at hhi
    omega

private theorem quiet_return_no_proper_factors_of_low_index_offset {s C : Nat}
    (state : IsMovingHorizonState s C) (hC : 64 ≤ C)
    (offset : 4 * replayIndexOffset s C ≤ C + 2)
    (quiet : ∀ j : Nat, s < j → j ≤ C → d j = 1) : NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  let q := Nat.sqrt (C + 1)
  have hq : q * q ≤ C + 1 := Nat.sqrt_le _
  have hsmall : 6 * q ≤ C := by
    apply Nat.mul_self_le_mul_self_iff.mp
    calc
      (6 * q) * (6 * q) = 36 * (q * q) := by ac_rfl
      _ ≤ 37 * C := by omega
      _ ≤ C * C := Nat.mul_le_mul_right _ (by omega)
  have hlong : 2 * Nat.sqrt (C + 1) < C - s := by
    have htwice := moving_horizon_state_horizon_le_twice_index state
    have hsc := state.2.2
    change 2 * q < C - s
    unfold replayIndexOffset at offset
    omega
  exact quiet_return_no_proper_factors state quiet hlong

/-- These two endpoint bounds give the next canonical record and its
twin-primality certificate on the capped replay. -/
theorem canonical_next_record_factors_of_index_offset_bounds {M : Nat}
    (hM : 33 ≤ M) (canonical : d (M + 2) = M) (cap : IsAttainedPreviousMaximum M (M + 2))
    (bounds : ∀ {s C n : Nat}, HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C n →
      IsAttainedPreviousMaximum M s → 2 * replayIndexOffset s C ≤ M ∧ 8 * (C + 1) ≤ M * M) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have hD := (canonical_increment_coordinates (by omega) canonical).2.1
  have start : IsMovingHorizonState (M + 2) (2 * M - 2) := ⟨by omega, hD, by omega⟩
  obtain ⟨s, C, n, path, hcapped, exit⟩ := capped_moving_horizon_eventual_exit start cap
  have ⟨hoffset, hhorizon⟩ := bounds path hcapped
  have hstate := moving_horizon_path_endpoint path
  have hlo := (moving_horizon_path_gap_le_three_growth path).2.1
  rcases exit with ⟨_, quiet⟩ | ⟨r, C', step, newRecord⟩
  · obtain ⟨hnew, hpre, hd, _⟩ := canonical_quiet_return_next_record (by omega) hlo hstate hcapped quiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors_of_low_index_offset hstate (by omega) (by omega) quiet
    exact ⟨C, hnew, hpre, hd, hminus, hplus⟩
  · exact False.elim (not_lt_of_ge
      (moving_horizon_no_new_record_of_half_offset_quadratic_horizon (by omega) step hoffset hhorizon) newRecord)

theorem replay_index_offset_le_of_large_gap_growth210 {s C sf Cf n first : Nat} {balance : Int}
    (path : HasMovingHorizonPathTo s C sf Cf n)
    (trace : ResidualPhaseTrace210 s sf [] n first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    3 * replayIndexOffset sf Cf + (Cf - C) ≤ 3 * replayIndexOffset s C + 13 * trace.growthAtLargeGaps + 6 := by
  have start : IsMovingHorizonState s C := by
    cases n with
    | zero => exact path.2.2
    | succ _ => exact path.1
  have finish := moving_horizon_path_endpoint path
  have hC := moving_horizon_state_horizon_le_twice_index start
  have hCf := moving_horizon_state_horizon_le_twice_index finish
  have ⟨hindex, hhorizon, _⟩ := moving_horizon_path_gap_le_three_growth path
  have h := trace.travel_le_growth_and_large_gaps path delta
  unfold replayIndexOffset
  omega

theorem replay_index_offset_le_four_large_gap_growth_of_low_offset210 {s C sf Cf n first : Nat} {balance : Int}
    (path : HasMovingHorizonPathTo s C sf Cf n) (low : replayIndexOffset s C ≤ 6)
    (trace : ResidualPhaseTrace210 s sf [] n first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    replayIndexOffset sf Cf ≤ 4 * trace.growthAtLargeGaps + 8 := by
  have start : D s = C := by
    cases n with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have finish := (moving_horizon_path_endpoint path).2.1
  have h := replay_index_offset_le_of_large_gap_growth210 path trace delta
  have hH := trace.growth_at_large_gaps_le delta
  rw [start, finish] at hH
  omega

/-- Keep the current horizon and the final gap in the crossing
condition. Only the large-gap growth since the low-offset state is
needed for the offset part of the condition. -/
theorem rebalanced_boundary_crossing_requires_suffix_growth210
    {M t H s C r C' n first : Nat} {balance : Int}
    (path : HasMovingHorizonPathTo t H s C n) (low : replayIndexOffset t H ≤ 6)
    (step : IsMovingHorizonStep s C r C')
    (cross : rebalancedBoundaryLimit210 M < rebalancedBoundaryValue210 r C')
    (trace : ResidualPhaseTrace210 t s [] n first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f t) :
    219 * M < C + 864 * trace.growthAtLargeGaps + 325 * (r - s) + 41639 := by
  have hX := replay_index_offset_le_four_large_gap_growth_of_low_offset210 path low trace delta
  have hC := moving_horizon_state_horizon_le_twice_index step.1
  have hCe := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have hV := rebalanced_potential210_le s C hCe
  have hstep := rebalanced_boundary_step_increase_le210 step
  unfold replayIndexOffset at hX
  unfold rebalancedBoundaryValue210 at cross hstep
  unfold rebalancedBoundaryLimit210 at cross
  omega

theorem rebalanced_boundary_crossing_requires_large_suffix_below_eight210
    {M t H s C r C' n first : Nat} {balance : Int}
    (hM : 11751795061 ≤ M) (hC : C ≤ 8 * M)
    (path : HasMovingHorizonPathTo t H s C n) (low : replayIndexOffset t H ≤ 6)
    (step : IsMovingHorizonStep s C r C')
    (below : rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M)
    (cross : rebalancedBoundaryLimit210 M < rebalancedBoundaryValue210 r C')
    (trace : ResidualPhaseTrace210 t s [] n first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f t) :
    6 * M < 25 * trace.growthAtLargeGaps := by
  have hg := rebalanced_boundary_crossing_gap210 hM step below
  have h := rebalanced_boundary_crossing_requires_suffix_growth210 path low step cross trace delta
  omega

/-! ## The supported continuation from a small offset -/

private def supportedOffsetCheck210 (s C X used fuel : Nat) : Bool :=
  (Nat.ble X 76 && Nat.ble used 32) &&
    match firstClippedHit210 s C with
    | none => true
    | some (gap, e) =>
      if X + 2 * gap < e - 1 then true
      else match fuel with
        | 0 => false
        | k + 1 => supportedOffsetCheck210 ((s + gap) % 210) ((C + e - 1) % 210)
            (X + 2 * gap - (e - 1)) (used + (e - 1)) k
termination_by structural fuel

private def lowOffsetResiduesChecked210 (half : Nat) : Prop :=
  ∀ i : Fin 210, supportedOffsetCheck210 i.val ((2 * i.val + 210 - 2 * half) % 210) (2 * half) 0 9 = true

section

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem lowOffset0Checked210 : lowOffsetResiduesChecked210 0 := by
  unfold lowOffsetResiduesChecked210
  decide +kernel

private theorem lowOffset2Checked210 : lowOffsetResiduesChecked210 1 := by
  unfold lowOffsetResiduesChecked210
  decide +kernel

private theorem lowOffset4Checked210 : lowOffsetResiduesChecked210 2 := by
  unfold lowOffsetResiduesChecked210
  decide +kernel

private theorem lowOffset6Checked210 : lowOffsetResiduesChecked210 3 := by
  unfold lowOffsetResiduesChecked210
  decide +kernel

end

private theorem supported_offset_check_sound210 {s C sf Cf p fuel used : Nat}
    (path : HasMovingHorizonPathTo s C sf Cf p)
    (supported : ∀ j : Nat, s < j → j ≤ sf → d j ∣ 210)
    (checked : supportedOffsetCheck210 (s % 210) (C % 210) (replayIndexOffset s C) used fuel = true) :
    p ≤ fuel ∧ replayIndexOffset sf Cf ≤ 76 ∧ used + (Cf - C) ≤ 32 := by
  induction p generalizing s C fuel used with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := path
    rw [supportedOffsetCheck210] at checked
    simp only [Bool.and_eq_true, Nat.ble_eq] at checked
    exact ⟨Nat.zero_le _, checked.1.1, by simpa using checked.1.2⟩
  | succ p ih =>
    obtain ⟨_, r, Cr, step, tail⟩ := path
    have hsr := step.2.1
    have hr := moving_horizon_path_index_le tail
    have he := supported r hsr hr
    have hhit := first_clipped_hit210_of_supported step he
    have hX := moving_horizon_step_index_offset_update step
    have hC := moving_horizon_step_update step
    have hfinal := (moving_horizon_path_gap_le_three_growth tail).2.1
    have hd := step.2.2.2.1
    have hs : (s % 210 + (r - s)) % 210 = r % 210 := by omega
    have hc : (C % 210 + d r - 1) % 210 = Cr % 210 := by omega
    have hx : replayIndexOffset s C + 2 * (r - s) - (d r - 1) = replayIndexOffset r Cr := by omega
    rw [supportedOffsetCheck210, hhit] at checked
    have hn : ¬ replayIndexOffset s C + 2 * (r - s) < d r - 1 := by omega
    simp only [if_neg hn, Bool.and_eq_true] at checked
    cases fuel with
    | zero => simp at checked
    | succ k =>
      have htail := checked.2
      rw [hs, hc, hx] at htail
      obtain ⟨hp, hx', hu⟩ := ih tail (fun j hj hjs => supported j (by omega) hjs) htail
      exact ⟨by omega, hx', by omega⟩

/-- The supported part of an excursion from offset at most six has at
most nine events and at most 32 horizon growth. -/
theorem moving_horizon_supported_path_of_low_offset210 {s C sf Cf p : Nat}
    (path : HasMovingHorizonPathTo s C sf Cf p)
    (supported : ∀ j : Nat, s < j → j ≤ sf → d j ∣ 210)
    (low : replayIndexOffset s C ≤ 6) :
    p ≤ 9 ∧ replayIndexOffset sf Cf ≤ 76 ∧ Cf - C ≤ 32 := by
  have start : IsMovingHorizonState s C := by
    cases p with
    | zero => exact path.2.2
    | succ _ => exact path.1
  have hc := moving_horizon_state_horizon_le_twice_index start
  have hCe := start.2.1 ▸ D_mod_two_eq_zero_of_two_le start.1
  let X := replayIndexOffset s C
  have hX : X = 2 * s - C := rfl
  have hres : (2 * (s % 210) + 210 - X) % 210 = C % 210 := by omega
  let i : Fin 210 := ⟨s % 210, Nat.mod_lt _ (by decide)⟩
  have hsmall : X = 0 ∨ X = 2 ∨ X = 4 ∨ X = 6 := by omega
  have from_residue (k : Nat) (hk : X = 2 * k) (cert : lowOffsetResiduesChecked210 k) :
      supportedOffsetCheck210 (s % 210) (C % 210) X 0 9 = true := by
    have h := cert i
    change supportedOffsetCheck210 (s % 210) ((2 * (s % 210) + 210 - 2 * k) % 210) (2 * k) 0 9 = true at h
    rwa [← hk, hres] at h
  have checked : supportedOffsetCheck210 (s % 210) (C % 210) X 0 9 = true := by
    rcases hsmall with h | h | h | h
    · exact from_residue 0 h lowOffset0Checked210
    · exact from_residue 1 h lowOffset2Checked210
    · exact from_residue 2 h lowOffset4Checked210
    · exact from_residue 3 h lowOffset6Checked210
  simpa only [Nat.zero_add] using supported_offset_check_sound210 path supported checked

end A166944Research
