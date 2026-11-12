import A166944.ReplayOffset210

/-! # Inside records and departures from a small index offset

The gap and cofactor bounds give a joint condition on the offset and
horizon. A small divisor on either side can instead bound the gap directly.
Near a return, the horizon modulo four determines whether a large
increment increases the offset or returns it to zero or six.
-/

namespace A166944Research

theorem moving_horizon_no_new_record_of_joint_bound {M s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C')
    (bound : M * replayIndexOffset s C + 4 * (C + 1) ≤ M * M) : d r ≤ M := by
  apply Nat.le_of_not_gt
  intro hnew
  have hupdate := moving_horizon_step_index_offset_update step
  have hproduct := moving_horizon_step_gap_mul_increment_le_twice_horizon step
  have hgap : 0 < r - s := Nat.sub_pos_of_lt step.2.1
  have hle : M ≤ replayIndexOffset s C + 2 * (r - s) := by omega
  have hstrict := Nat.mul_lt_mul_of_pos_left hnew hgap
  have hmul := Nat.mul_le_mul_left M hle
  rw [Nat.mul_add, show M * (2 * (r - s)) = 2 * ((r - s) * M) by ac_rfl] at hmul
  omega

/-- A capped step that raises the joint expression either maintains the
offset or loses just two, with an increment above half the cap. -/
theorem moving_horizon_step_joint_bound_increase {M s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (cap : d r ≤ M)
    (increase : M * replayIndexOffset s C + 4 * (C + 1) < M * replayIndexOffset r C' + 4 * (C' + 1)) :
    replayIndexOffset s C ≤ replayIndexOffset r C' ∨
      (replayIndexOffset s C = replayIndexOffset r C' + 2 ∧ M < 2 * (d r - 1)) := by
  by_cases h : replayIndexOffset s C ≤ replayIndexOffset r C'
  · exact Or.inl h
  · have hpost := step.2.2.2.2.2.2.2.2
    have hC : C % 2 = 0 := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
    have hC' : C' % 2 = 0 := hpost.2.1 ▸ D_mod_two_eq_zero_of_two_le hpost.1
    have hdiff : replayIndexOffset r C' + 2 ≤ replayIndexOffset s C := by unfold replayIndexOffset at *; omega
    have hmul := Nat.mul_le_mul_left M hdiff
    rw [Nat.mul_add, Nat.mul_comm M 2] at hmul
    have hupdate := moving_horizon_step_update step
    have he := step.2.2.2.1
    right
    refine ⟨?_, by omega⟩
    by_cases hexact : replayIndexOffset s C = replayIndexOffset r C' + 2
    · exact hexact
    · have hmore : replayIndexOffset r C' + 4 ≤ replayIndexOffset s C := by
        unfold replayIndexOffset at *
        omega
      have hmul' := Nat.mul_le_mul_left M hmore
      rw [Nat.mul_add, Nat.mul_comm M 4] at hmul'
      omega

theorem moving_horizon_no_new_record_of_small_factor {M s C r C' v : Nat}
    (step : IsMovingHorizonStep s C r C') (odd : M % 2 = 1)
    (hv : 1 < v) (div : v ∣ C - 1 ∨ v ∣ C + 1)
    (bound : replayIndexOffset s C + 4 * v ≤ M) : d r ≤ M := by
  have hgap : r - s ≤ 2 * v := div.elim
    (moving_horizon_gap_le_twice_even_factor step hv) (moving_horizon_gap_le_twice_odd_factor step hv)
  have hupdate := moving_horizon_step_index_offset_update step
  have hr : 3 ≤ r := by have := step.1.1; have := step.2.1; omega
  have he := d_mod_two_eq_one_of_three_le hr
  omega

/-- An inside record excludes all sufficiently small divisors on both sides. -/
theorem moving_horizon_new_record_excludes_small_factors {M s C r C' B : Nat}
    (step : IsMovingHorizonStep s C r C') (odd : M % 2 = 1) (record : M < d r)
    (room : replayIndexOffset s C + 4 * B ≤ M) :
    NoSmallFactor (C - 1) B ∧ NoSmallFactor (C + 1) B := by
  have excludes (v : Fin (B + 1)) (hv : 2 ≤ v.val) : ¬ (v.val ∣ C - 1 ∨ v.val ∣ C + 1) := by
    intro hdiv
    have hsize := v.isLt
    have hold := moving_horizon_no_new_record_of_small_factor step odd (by omega) hdiv (by omega)
    exact Nat.not_lt_of_ge hold record
  exact ⟨fun v hv hd => excludes v hv (Or.inl hd), fun v hv hd => excludes v hv (Or.inr hd)⟩

private theorem long_quiet_gap_of_index_offset_le_record {M s C : Nat}
    (hM : 43 ≤ M) (hC : 2 * M - 2 ≤ C) (state : IsMovingHorizonState s C)
    (offset : replayIndexOffset s C ≤ M) : 2 * Nat.sqrt (C + 1) < C - s := by
  let q := Nat.sqrt (C + 1)
  have hq : q * q ≤ C + 1 := Nat.sqrt_le _
  have hsmall : 9 * q ≤ C := by
    apply Nat.mul_self_le_mul_self_iff.mp
    calc
      (9 * q) * (9 * q) = 81 * (q * q) := by ac_rfl
      _ ≤ 82 * C := by omega
      _ ≤ C * C := Nat.mul_le_mul_right _ (by omega)
  have htwice := moving_horizon_state_horizon_le_twice_index state
  have hsc := state.2.2
  unfold replayIndexOffset at offset
  change 2 * q < C - s
  omega

/-- At a capped endpoint the offset controls the quiet exit. An inside
exit is excluded by either the joint bound or a small divisor. -/
theorem canonical_next_record_factors_of_joint_bound_or_small_factor {M : Nat}
    (hM : 43 ≤ M) (canonical : d (M + 2) = M) (cap : IsAttainedPreviousMaximum M (M + 2))
    (bounds : ∀ {s C n : Nat}, HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C n →
      IsAttainedPreviousMaximum M s → replayIndexOffset s C ≤ M ∧
        (∀ {r C' : Nat}, IsMovingHorizonStep s C r C' →
          M * replayIndexOffset s C + 4 * (C + 1) ≤ M * M ∨
          ∃ v : Nat, 1 < v ∧ (v ∣ C - 1 ∨ v ∣ C + 1) ∧ replayIndexOffset s C + 4 * v ≤ M)) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have odd : M % 2 = 1 := canonical ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
  have hD := (canonical_increment_coordinates (by omega) canonical).2.1
  have start : IsMovingHorizonState (M + 2) (2 * M - 2) := ⟨by omega, hD, by omega⟩
  obtain ⟨s, C, n, path, hcapped, exit⟩ := capped_moving_horizon_eventual_exit start cap
  obtain ⟨hoffset, hbound⟩ := bounds path hcapped
  have hstate := moving_horizon_path_endpoint path
  have hlo := (moving_horizon_path_gap_le_three_growth path).2.1
  rcases exit with ⟨_, quiet⟩ | ⟨r, C', step, newRecord⟩
  · obtain ⟨hnew, hpre, hd, _⟩ := canonical_quiet_return_next_record (by omega) hlo hstate hcapped quiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate quiet
      (long_quiet_gap_of_index_offset_le_record hM hlo hstate hoffset)
    exact ⟨C, hnew, hpre, hd, hminus, hplus⟩
  · have hold : d r ≤ M := by
      rcases hbound step with h | ⟨v, hv, hdiv, h⟩
      · exact moving_horizon_no_new_record_of_joint_bound step h
      · exact moving_horizon_no_new_record_of_small_factor step odd hv hdiv h
    exact False.elim (Nat.not_lt_of_ge hold newRecord)

/-- When the increment exceeds the incoming offset plus one, the offset
quotient is either zero or one, as determined by the outgoing horizon. -/
theorem moving_horizon_step_index_offset_mod_four {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (large : 5 ≤ d r)
    (offset : replayIndexOffset s C + 1 < d r) :
    replayIndexOffset r C' =
      (if C' % 4 = 0 then 0 else 2 * d r) + (if r % 2 = 0 then 0 else 6) := by
  obtain ⟨k, hk⟩ := moving_horizon_step_index_offset_residue step large
  have hupdate := moving_horizon_step_index_offset_update step
  have hgap := moving_horizon_step_gap_le_twice_increment step
  have hsmall : replayIndexOffset r C' < 4 * d r := by omega
  have hk' : k = 0 ∨ k = 1 := by
    by_cases h : k ≤ 1
    · omega
    have hlo := Nat.mul_le_mul_left (2 * d r) (show 2 ≤ k by omega)
    rw [Nat.mul_comm (2 * d r) 2, ← Nat.mul_assoc] at hlo
    split at hk <;> omega
  have hC' := moving_horizon_state_horizon_le_twice_index step.2.2.2.2.2.2.2.2
  have hsum : replayIndexOffset r C' + C' = 2 * r := by unfold replayIndexOffset; omega
  have hr : 3 ≤ r := by have := step.1.1; have := step.2.1; omega
  have he := d_mod_two_eq_one_of_three_le hr
  rcases hk' with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add] at hk
    have hmod : C' % 4 = 0 := by split at hk <;> omega
    simpa only [hmod, if_pos, Nat.zero_add] using hk
  · simp only [Nat.mul_one] at hk
    have hmod : C' % 4 ≠ 0 := by split at hk <;> omega
    rwa [if_neg hmod]

theorem moving_horizon_step_index_offset_of_low_offset {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (large : 9 ≤ d r)
    (offset : replayIndexOffset s C ≤ 6) (phase : C % 4 = 0) :
    replayIndexOffset r C' =
      (if d r % 4 = 1 then 0 else 2 * d r) + (if r % 2 = 0 then 0 else 6) := by
  have h := moving_horizon_step_index_offset_mod_four step (by omega) (by omega)
  have hup := moving_horizon_step_update step
  by_cases he : d r % 4 = 1
  · have hphase : C' % 4 = 0 := by omega
    rw [if_pos hphase] at h
    rwa [if_pos he]
  · have hphase : C' % 4 ≠ 0 := by omega
    rw [if_neg hphase] at h
    rwa [if_neg he]

/-- A departure from a small offset has a cofactor at least as large as
its increment. The two hit parities give stronger bounds in different
classes modulo four. -/
theorem moving_horizon_step_low_offset_departure_cofactor {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (large : 9 ≤ d r)
    (offset : replayIndexOffset s C ≤ 6) (depart : 6 < replayIndexOffset r C') :
    (r % 2 = 0 ∧ 3 * (d r * d r) ≤ (if d r % 4 = 3 then 1 else 3) * (C - 1)) ∨
      (r % 2 = 1 ∧ 3 * (d r * d r) ≤ (if d r % 4 = 3 then 3 else 1) * (C + 1)) := by
  have hpost := moving_horizon_step_index_offset_mod_four step (by omega) (by omega)
  have hphase : C' % 4 ≠ 0 := by
    intro h
    rw [if_pos h, Nat.zero_add] at hpost
    split at hpost <;> omega
  rw [if_neg hphase] at hpost
  have hupdate := moving_horizon_step_index_offset_update step
  have hhorizon := moving_horizon_step_update step
  have hstate := moving_horizon_state_horizon_le_twice_index step.1
  have hstate' := moving_horizon_state_horizon_le_twice_index step.2.2.2.2.2.2.2.2
  have hsr := step.2.1
  have hr3 : 3 ≤ r := by have := step.1.1; omega
  have heodd := d_mod_two_eq_one_of_three_le hr3
  have hephase : d r % 4 = 1 ∨ d r % 4 = 3 := by omega
  have hx : replayIndexOffset s C + C = 2 * s := by unfold replayIndexOffset; omega
  have hx' : replayIndexOffset r C' + C' = 2 * r := by unfold replayIndexOffset; omega
  have hunit (j : Nat) (hsj : s < j) (hjr : j < r) :
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧ (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    rcases moving_horizon_first_hit_map step with h | h <;> exact h.2.2.2 j hsj hjr
  rcases moving_horizon_step_event_package step with ⟨hr, hdiv, _, hsize⟩ | ⟨hr, hdiv, _, hsize⟩
  · left
    refine ⟨hr, ?_⟩
    simp only [hr, if_pos, Nat.add_zero] at hpost
    obtain ⟨v, hv⟩ := hdiv
    have hv3 : 3 ≤ v := by
      apply Nat.le_of_not_gt
      intro h
      have hle := Nat.mul_le_mul_left (d r) (show v ≤ 2 by omega)
      omega
    have hvdiv : v ∣ C - 1 := ⟨d r, hv.trans (Nat.mul_comm _ _)⟩
    let k := if d r % 4 = 3 then 1 else 3
    have hkpar : (d r + k) % 4 = 0 := by
      rcases hephase with he | he <;> simp [k, he, Nat.add_mod]
    have hnear : replayIndexOffset s C + 1 < k * v := by
      by_cases he : d r % 4 = 3
      · have hCpos := step.1.2.2
        have hminus : (C - 1) % 4 = 3 := by omega
        rw [hv, Nat.mul_mod, he] at hminus
        have hvphase : v % 4 = 1 := by omega
        have hgap := moving_horizon_gap_le_twice_even_factor step (by omega) hvdiv
        rw [show k = 1 from if_pos he, Nat.one_mul]
        omega
      · rw [show k = 3 from if_neg he]
        omega
    let j := v * ((d r + k) / 2)
    have hj : 2 * j = C - 1 + k * v := calc
      _ = v * (2 * ((d r + k) / 2)) := by dsimp [j]; ac_rfl
      _ = v * (d r + k) := congrArg (v * ·) (by omega)
      _ = _ := by rw [Nat.mul_add, Nat.mul_comm v (d r), ← hv, Nat.mul_comm v k]
    have hjpar : j % 2 = 0 := by
      dsimp [j]
      rw [Nat.mul_mod, show ((d r + k) / 2) % 2 = 0 by omega]
      simp
    have hcofactor : 3 * d r ≤ k * v := by
      apply Nat.le_of_not_gt
      intro hvsmall
      have hsj : s < j := by have := step.1.2.2; omega
      have hjr : j < r := by have := step.1.2.2; omega
      have hjdiv : v ∣ j := ⟨_, rfl⟩
      have := Nat.gcd_eq_one_iff.mp ((hunit j hsj hjr).1 hjpar) v hjdiv hvdiv
      omega
    change 3 * (d r * d r) ≤ k * (C - 1)
    calc
      _ = (3 * d r) * d r := by rw [Nat.mul_assoc]
      _ ≤ (k * v) * d r := Nat.mul_le_mul_right _ hcofactor
      _ = _ := by rw [hv]; ac_rfl
  · right
    refine ⟨hr, ?_⟩
    simp only [hr, Nat.one_ne_zero, if_false] at hpost
    obtain ⟨v, hv⟩ := hdiv
    have hv3 : 3 ≤ v := by
      apply Nat.le_of_not_gt
      intro h
      have hle := Nat.mul_le_mul_left (d r) (show v ≤ 2 by omega)
      omega
    have hvdiv : v ∣ C + 1 := ⟨d r, hv.trans (Nat.mul_comm _ _)⟩
    have hvodd : v % 2 = 1 := by
      have hC : C % 2 = 0 := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
      have hodd : (C + 1) % 2 = 1 := by omega
      rw [hv, Nat.mul_mod, heodd, Nat.one_mul, Nat.mod_mod] at hodd
      exact hodd
    let k := if d r % 4 = 3 then 3 else 1
    have hkpar : (d r + k) % 4 = 2 := by
      rcases hephase with he | he <;> simp [k, he, Nat.add_mod]
    have hnear : 3 ≤ k * v := by
      by_cases he : d r % 4 = 3
      · rw [show k = 3 from if_pos he]
        omega
      · rwa [show k = 1 from if_neg he, Nat.one_mul]
    let j := v * ((d r + k) / 2) + 2
    have hj : 2 * j = C + k * v + 5 := calc
      _ = v * (2 * ((d r + k) / 2)) + 4 := by
        dsimp [j]
        rw [Nat.mul_add, show 2 * 2 = 4 by decide]
        ac_rfl
      _ = v * (d r + k) + 4 := congrArg (fun a => v * a + 4) (by omega)
      _ = _ := by rw [Nat.mul_add, Nat.mul_comm v (d r), ← hv, Nat.mul_comm v k]; omega
    have hjpar : j % 2 = 1 := by
      dsimp [j]
      simp [Nat.mul_mod, hvodd, show ((d r + k) / 2) % 2 = 1 by omega]
    have hcofactor : 3 * d r ≤ k * v := by
      apply Nat.le_of_not_gt
      intro hvsmall
      have hsj : s < j := by omega
      have hjr : j < r := by omega
      have hjdiv : v ∣ j - 2 := ⟨(d r + k) / 2, by simp [j]⟩
      have := Nat.gcd_eq_one_iff.mp ((hunit j hsj hjr).2 hjpar) v hjdiv hvdiv
      omega
    change 3 * (d r * d r) ≤ k * (C + 1)
    calc
      _ = (3 * d r) * d r := by rw [Nat.mul_assoc]
      _ ≤ (k * v) * d r := Nat.mul_le_mul_right _ hcofactor
      _ = _ := by rw [hv]; ac_rfl

/-- A step out of the small-offset region starts at square-root scale. -/
theorem moving_horizon_step_low_offset_departure_bound {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (offset : replayIndexOffset s C ≤ 6) :
    replayIndexOffset r C' ≤ max 28 (2 * Nat.sqrt (C + 1) + 6) := by
  by_cases large : 9 ≤ d r
  · have hpost := moving_horizon_step_index_offset_mod_four step (by omega) (by omega)
    by_cases depart : 6 < replayIndexOffset r C'
    · have hsquare : d r * d r ≤ C + 1 := by
        rcases moving_horizon_step_low_offset_departure_cofactor step large offset depart with ⟨_, h⟩ | ⟨_, h⟩
        all_goals split at h <;> omega
      have hroot := Nat.le_of_lt_succ
        (Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt hsquare (Nat.lt_succ_sqrt _)))
      have hmax := Nat.le_max_right 28 (2 * Nat.sqrt (C + 1) + 6)
      split at hpost <;> split at hpost <;> omega
    · have hmax := Nat.le_max_left 28 (2 * Nat.sqrt (C + 1) + 6)
      omega
  · have hupdate := moving_horizon_step_index_offset_update step
    have hgap := moving_horizon_step_gap_le_twice_increment step
    have hr : 3 ≤ r := by have := step.1.1; have := step.2.1; omega
    have he := d_mod_two_eq_one_of_three_le hr
    have hmax := Nat.le_max_left 28 (2 * Nat.sqrt (C + 1) + 6)
    omega

end A166944Research
