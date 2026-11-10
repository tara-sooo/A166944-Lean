import A166944.CanonicalRecord

/-!
# Checking finite record replays

Only nonunit indices need to be supplied. The checker tests the gcd
at each supplied index and checks for earlier hits. At the terminal
horizon, small-divisor checks justify the whole quiet interval at once.
-/

namespace A166944Research

private def replayGcd (j C : Nat) : Nat :=
  if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1)

private theorem replay_unit_interval {s C t : Nat} (hs : 2 ≤ s) (hD : D s = C)
    (hquiet : ∀ j : Nat, s < j → j ≤ t → replayGcd j C = 1) :
    ∀ j : Nat, s < j → j ≤ t → d j = 1 := by
  rcases first_later_nontrivial_dichotomy (C := t) hs with h | ⟨r, hsr, hrt, hdr, hfirst⟩
  · exact h
  · have hprev := first_later_event_D_eq hs hD hsr hfirst
    have hmap : d r = replayGcd r C := constant_D_event_map (by omega) hprev
    rw [hmap, hquiet r hsr hrt] at hdr
    omega

private theorem checked_replay_step {s C r : Nat} (hstate : IsMovingHorizonState s C)
    (hsr : s < r) (hrC : r ≤ C) (he : 1 < replayGcd r C)
    (hquiet : ∀ j : Nat, s < j → j < r → replayGcd j C = 1) :
    IsMovingHorizonStep s C r (C + replayGcd r C - 1) ∧ d r = replayGcd r C := by
  have hgcd (j : Nat) (hsj : s < j) (hjr : j ≤ r - 1) : replayGcd j C = 1 := by
    exact hquiet j hsj (by omega)
  have hunit := replay_unit_interval hstate.1 hstate.2.1 hgcd
  have hfirst (j : Nat) (hsj : s < j) (hjr : j < r) : d j = 1 :=
    hunit j hsj (by omega)
  have hDprev := first_later_event_D_eq hstate.1 hstate.2.1 hsr hfirst
  have hr3 : 3 ≤ r := by have := hstate.1; omega
  have hd : d r = replayGcd r C := constant_D_event_map (by omega) hDprev
  have hDstep := D_succ_add_one_eq_add_d (r - 1)
  rw [show r - 1 + 1 = r by omega, hDprev, hd] at hDstep
  have hD : D r = C + replayGcd r C - 1 := by omega
  have hodd := d_mod_two_eq_one_of_three_le hr3
  have hgrowth : C + 2 ≤ C + replayGcd r C - 1 := by omega
  exact ⟨⟨hstate, hsr, hrC, by omega, hfirst, hDprev, hD.symm, hgrowth,
    ⟨by omega, hD, by omega⟩⟩, hd⟩

private def replayQuietCheck (s C r : Nat) : Bool :=
  (List.range (r - s - 1)).all (fun i => replayGcd (s + i + 1) C == 1)

private theorem replayQuietCheck_sound {s C r : Nat} (h : replayQuietCheck s C r = true) :
    ∀ j : Nat, s < j → j < r → replayGcd j C = 1 := by
  intro j hsj hjr
  have hi : j - s - 1 ∈ List.range (r - s - 1) := List.mem_range.2 (by omega)
  have htest := (List.all_eq_true.mp h) (j - s - 1) hi
  change (replayGcd (s + (j - s - 1) + 1) C == 1) = true at htest
  simpa only [show s + (j - s - 1) + 1 = j by omega, beq_iff_eq] using htest

/-- Check that the supplied hits give an old-event path ending at the
supplied horizon. The indices in the open gaps are checked separately. -/
def recordReplayCheck (M s C : Nat) (hits : List Nat) (finish : Nat) : Bool :=
  match hits with
  | [] => C == finish
  | r :: rest =>
      let e := replayGcd r C
      (decide (s < r ∧ r ≤ C ∧ 1 < e ∧ e ≤ M) && replayQuietCheck s C r) &&
      recordReplayCheck M r (C + e - 1) rest finish

theorem recordReplayCheck_sound {M s C finish : Nat} (hits : List Nat)
    (hstate : IsMovingHorizonState s C) (hmax : IsAttainedPreviousMaximum M s)
    (hcheck : recordReplayCheck M s C hits finish = true) :
    ∃ sf : Nat, HasMovingHorizonPathTo s C sf finish hits.length ∧
      IsAttainedPreviousMaximum M sf := by
  induction hits generalizing s C with
  | nil =>
      have hfinish : C = finish := by simpa [recordReplayCheck] using hcheck
      subst finish
      exact ⟨s, ⟨rfl, rfl, hstate⟩, hmax⟩
  | cons r rest ih =>
      simp only [recordReplayCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      obtain ⟨⟨⟨hsr, hrC, he, hcap⟩, hquiet⟩, hrest⟩ := hcheck
      obtain ⟨hstep, hd⟩ := checked_replay_step hstate hsr hrC he (replayQuietCheck_sound hquiet)
      have hmax' : IsAttainedPreviousMaximum M r := by
        rcases moving_horizon_max_transfer hmax hsr hstep.2.2.2.1 hstep.2.2.2.2.1 with h | h
        · exact h.2
        · have := h.1
          omega
      obtain ⟨sf, hpath, hfmax⟩ := ih hstep.2.2.2.2.2.2.2.2 hmax' hrest
      exact ⟨sf, ⟨hstate, r, C + replayGcd r C - 1, hstep, hpath⟩, hfmax⟩

private abbrev NoSmallFactor (N root : Nat) : Prop :=
  ∀ f : Fin (root + 1), 2 ≤ f.val → ¬ f.val ∣ N

private def noSmallFactorCheck (N root : Nat) : Bool :=
  (List.range (root - 1)).all (fun i => N % (i + 2) != 0)

private theorem noSmallFactorCheck_sound {N root : Nat} (h : noSmallFactorCheck N root = true) :
    NoSmallFactor N root := by
  intro f hf hdiv
  have hfle := f.isLt
  have hi : f.val - 2 ∈ List.range (root - 1) := List.mem_range.2 (by omega)
  have htest := (List.all_eq_true.mp h) (f.val - 2) hi
  change (N % (f.val - 2 + 2) != 0) = true at htest
  simp [show f.val - 2 + 2 = f.val by omega, Nat.mod_eq_zero_of_dvd hdiv] at htest

private theorem gcd_eq_one_of_no_small_factor {N j root : Nat}
    (hj : 0 < j) (hlt : j < N) (hcheck : NoSmallFactor N root)
    (hroot : N < (root + 1) * (root + 1)) : Nat.gcd j N = 1 := by
  let g := Nat.gcd j N
  have hdivj : g ∣ j := Nat.gcd_dvd_left _ _
  have hdivN : g ∣ N := Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hj
  have hgle := Nat.le_of_dvd hj hdivj
  by_cases h : g = 1
  · exact h
  · have hg2 : 2 ≤ g := by omega
    by_cases hsmall : g ≤ root
    · exact False.elim ((hcheck ⟨g, by omega⟩ hg2) hdivN)
    · obtain ⟨q, hq⟩ := hdivN
      have hq2 : 2 ≤ q := by
        by_cases hq' : 2 ≤ q
        · exact hq'
        · have hm := Nat.mul_le_mul_left g (show q ≤ 1 by omega)
          rw [← hq, Nat.mul_one] at hm
          omega
      by_cases hsmall' : q ≤ root
      · have hdivq : q ∣ N := ⟨g, by simpa [Nat.mul_comm] using hq⟩
        exact False.elim ((hcheck ⟨q, by omega⟩ hq2) hdivq)
      · have hm := Nat.mul_le_mul (show root + 1 ≤ g by omega) (show root + 1 ≤ q by omega)
        omega

/-- Check the two horizon terms using only divisors up to their square
roots. This avoids iterating over the long final quiet tail. -/
def recordReturnCheck (C root : Nat) : Bool :=
  (decide (C + 1 < (root + 1) * (root + 1)) && noSmallFactorCheck (C - 1) root) &&
    noSmallFactorCheck (C + 1) root

private theorem recordReturnCheck_conditions {C root : Nat} (h : recordReturnCheck C root = true) :
    C + 1 < (root + 1) * (root + 1) ∧ NoSmallFactor (C - 1) root ∧ NoSmallFactor (C + 1) root := by
  simp only [recordReturnCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, noSmallFactorCheck_sound h.1.2, noSmallFactorCheck_sound h.2⟩

private theorem recordReturnCheck_sound {s C root : Nat} (hstate : IsMovingHorizonState s C)
    (hcheck : recordReturnCheck C root = true) :
    ∀ j : Nat, s < j → j ≤ C → d j = 1 := by
  have hterms := recordReturnCheck_conditions hcheck
  have hCe : C % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hs2 := hstate.1
  apply replay_unit_interval hs2 hstate.2.1
  intro j hsj hjC
  unfold replayGcd
  by_cases hj : j % 2 = 0
  · rw [if_pos hj]
    by_cases heq : j = C
    · subst j
      have hg := Nat.dvd_sub (Nat.gcd_dvd_left C (C - 1)) (Nat.gcd_dvd_right C (C - 1))
      rw [show C - (C - 1) = 1 by omega] at hg
      exact Nat.eq_one_of_dvd_one hg
    · exact gcd_eq_one_of_no_small_factor (by omega) (by omega) hterms.2.1 (by omega)
  · rw [if_neg hj]
    exact gcd_eq_one_of_no_small_factor (by omega) (by omega) hterms.2.2 hterms.1

/-- An accepted replay and return check determine the next strict
record and bound every preceding increment by the old record. -/
theorem canonical_replay_next_record {M finish root : Nat} (hits : List Nat)
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hcheck : recordReplayCheck M (M + 2) (2 * M - 2) hits finish = true)
    (hreturn : recordReturnCheck finish root = true) :
    M < finish + 1 ∧ IsAttainedPreviousMaximum M (finish + 2) ∧
      d (finish + 3) = finish + 1 ∧ D (finish + 2) = finish := by
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM hcanon).2.1, by omega⟩
  obtain ⟨sf, hpath, hfmax⟩ := recordReplayCheck_sound hits hstart hmax hcheck
  have hstate := moving_horizon_path_endpoint hpath
  have hsf := hstate.2.2
  have hF := D_le_of_le (moving_horizon_path_index_le hpath)
  rw [hstart.2.1, hstate.2.1] at hF
  have hquiet := recordReturnCheck_sound hstate hreturn
  have hD := (moving_horizon_no_event_telescope hstate hquiet).1
  have hB := B_add_index_eq_D_add_two (by omega : 2 ≤ finish)
  have hfund : B finish = 2 := by omega
  obtain ⟨hd1, hd2, hd3⟩ := fundamental_reset_at_three (by omega) hfund
  have hD1 := (D_succ_eq_self_iff_d_succ_eq_one finish).2 hd1
  have hD2 := (D_succ_eq_self_iff_d_succ_eq_one (finish + 1)).2 hd2
  obtain ⟨i, hi2, his, hdi⟩ := hfmax.2
  refine ⟨by omega, ⟨?_, ⟨i, hi2, by omega, hdi⟩⟩, hd3, hD2.trans (hD1.trans hD)⟩
  intro j hj2 hj
  by_cases hs : j ≤ sf
  · exact hfmax.1 j hj2 hs
  · by_cases hle : j ≤ finish
    · rw [hquiet j (by omega) hle]
      omega
    · have hcases : j = finish + 1 ∨ j = finish + 2 := by omega
      rcases hcases with heq | heq
      · rw [heq, hd1]
        omega
      · rw [heq, hd2]
        omega

/-- For a number at least two, this is the proper-divisor condition for
primality. It keeps the replay checker on the recurrence-side imports. -/
abbrev NoProperFactor (N : Nat) : Prop :=
  ∀ f : Fin N, 2 ≤ f.val → ¬ f.val ∣ N

private theorem no_proper_factor_of_no_small_factor {N root : Nat}
    (hcheck : NoSmallFactor N root) (hroot : N < (root + 1) * (root + 1)) : NoProperFactor N := by
  intro f hf hdiv
  have h := gcd_eq_one_of_no_small_factor (by omega : 0 < f.val) f.isLt hcheck hroot
  have hdvd := Nat.dvd_gcd (Nat.dvd_refl f.val) hdiv
  rw [h] at hdvd
  have := Nat.eq_one_of_dvd_one hdvd
  omega

theorem recordReturnCheck_factor_free {C root : Nat} (hcheck : recordReturnCheck C root = true) :
    NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have h := recordReturnCheck_conditions hcheck
  exact ⟨no_proper_factor_of_no_small_factor h.2.1 (by omega),
    no_proper_factor_of_no_small_factor h.2.2 h.1⟩

/-- Every strict record greater than five through the given index has
its canonical position and both twin candidates have no proper factors. -/
def RecordsVerifiedThrough (N : Nat) : Prop :=
  ∀ {R n : Nat}, 5 < R → 2 ≤ n → n ≤ N → d n = R →
    (∀ j : Nat, 2 ≤ j → j < n → d j < R) →
    n = R + 2 ∧ NoProperFactor (R - 2) ∧ NoProperFactor R

/-- Each certificate segment supplies a terminal horizon and the indices
of its nonunit increments. The terminal horizon fixes the next record. -/
def recordPrefixCheck (M final : Nat) (segments : List (Nat × Nat × List Nat)) : Bool :=
  match segments with
  | [] => M == final
  | (finish, root, hits) :: rest =>
      (recordReplayCheck M (M + 2) (2 * M - 2) hits finish && recordReturnCheck finish root) &&
      recordPrefixCheck (finish + 1) final rest

private theorem replay_new_maximum {M finish : Nat} (hnew : M < finish + 1)
    (hpre : IsAttainedPreviousMaximum M (finish + 2)) (hcanon : d (finish + 3) = finish + 1) :
    IsAttainedPreviousMaximum (finish + 1) (finish + 3) := by
  have hnew' : M < d (finish + 2 + 1) := by rwa [show finish + 2 + 1 = finish + 3 by omega, hcanon]
  have h := attained_previous_maximum_extend (by omega) hpre hnew'
  simpa only [show finish + 2 + 1 = finish + 3 by omega, hcanon] using h

theorem recordPrefixCheck_sound {M final : Nat} (segments : List (Nat × Nat × List Nat))
    (hM : 5 < M) (hcanon : d (M + 2) = M) (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hprefix : RecordsVerifiedThrough (M + 2))
    (hcheck : recordPrefixCheck M final segments = true) :
    d (final + 2) = final ∧ IsAttainedPreviousMaximum final (final + 2) ∧
      RecordsVerifiedThrough (final + 2) := by
  induction segments generalizing M with
  | nil =>
      have h : M = final := by simpa [recordPrefixCheck] using hcheck
      subst final
      exact ⟨hcanon, hmax, hprefix⟩
  | cons segment rest ih =>
      obtain ⟨finish, root, hits⟩ := segment
      simp only [recordPrefixCheck, Bool.and_eq_true] at hcheck
      obtain ⟨⟨hreplay, hreturn⟩, hrest⟩ := hcheck
      obtain ⟨hnew, hpre, hcanon', _⟩ := canonical_replay_next_record
        hits hM hcanon hmax hreplay hreturn
      have hmax' := replay_new_maximum hnew hpre hcanon'
      have hprefix' : RecordsVerifiedThrough (finish + 3) := by
        intro R n hR hn hnf hdn hprior
        by_cases h : n ≤ M + 2
        · exact hprefix hR hn h hdn hprior
        · by_cases heq : n = finish + 3
          · have hR' : R = finish + 1 := by rw [heq, hcanon'] at hdn; omega
            obtain ⟨hlo, hhi⟩ := recordReturnCheck_factor_free hreturn
            rw [hR', show finish + 1 - 2 = finish - 1 by omega]
            exact ⟨by omega, hlo, hhi⟩
          · have hcap := hpre.1 n hn (by omega)
            have hbig := hprior (M + 2) (by omega) (by omega)
            omega
      exact ih (by omega) hcanon' hmax' hprefix' hrest

private theorem seven_record_verified :
    ∀ n : Fin 10, 5 < d n.val → n.val = d n.val + 2 ∧
      NoProperFactor (d n.val - 2) ∧ NoProperFactor (d n.val) := by decide

theorem recordPrefixCheck_sound_from_seven {final : Nat} (segments : List (Nat × Nat × List Nat))
    (hcheck : recordPrefixCheck 7 final segments = true) :
    d (final + 2) = final ∧ IsAttainedPreviousMaximum final (final + 2) ∧
      RecordsVerifiedThrough (final + 2) := by
  have hcanon : d 9 = 7 := by decide
  have hcap : ∀ j : Fin 10, 2 ≤ j.val → d j.val ≤ 7 := by decide
  have hmax : IsAttainedPreviousMaximum 7 9 :=
    ⟨fun j hj hj9 => hcap ⟨j, by omega⟩ hj, ⟨9, by decide, by decide, hcanon⟩⟩
  have hprefix : RecordsVerifiedThrough 9 := by
    intro R n hR _ hn hdn _
    have h := seven_record_verified ⟨n, by omega⟩ (by simpa only [hdn] using hR)
    simpa only [hdn] using h
  exact recordPrefixCheck_sound segments (by decide) hcanon hmax hprefix hcheck

/-- Check the horizon bound on each supplied terminal horizon. The
existing initial record proof handles previous values below 968. -/
def recordPrefixHorizonsFit (M : Nat) (segments : List (Nat × Nat × List Nat)) : Bool :=
  match segments with
  | [] => true
  | (finish, _, _) :: rest =>
      decide (M < 968 ∨ finish ≤ 3 * M + 4) && recordPrefixHorizonsFit (finish + 1) rest

/-- For covered previous records, the checked terminal horizon bounds
every actual capped state, including those between the listed hits. -/
theorem recordPrefixCheck_horizon_bound {start final : Nat} (segments : List (Nat × Nat × List Nat))
    (hstart : 5 < start) (hcanon : d (start + 2) = start)
    (hmax : IsAttainedPreviousMaximum start (start + 2))
    (hcheck : recordPrefixCheck start final segments = true)
    (hfit : recordPrefixHorizonsFit start segments = true) :
    ∀ {M s : Nat}, start ≤ M → M < final → 968 ≤ M → d (M + 2) = M →
      IsAttainedPreviousMaximum M s → D s ≤ 3 * M + 4 := by
  induction segments generalizing start with
  | nil =>
      have h : start = final := by simpa [recordPrefixCheck] using hcheck
      intro M s hlo hhi
      omega
  | cons segment rest ih =>
      obtain ⟨finish, root, hits⟩ := segment
      simp only [recordPrefixCheck, Bool.and_eq_true] at hcheck
      simp only [recordPrefixHorizonsFit, Bool.and_eq_true, decide_eq_true_eq] at hfit
      obtain ⟨⟨hreplay, hreturn⟩, hrest⟩ := hcheck
      obtain ⟨hnew, hpre, hcanon', hD⟩ := canonical_replay_next_record
        hits hstart hcanon hmax hreplay hreturn
      intro M s hlo hhi h968 hMcanon hP
      by_cases heq : M = start
      · subst M
        have hs : s ≤ finish + 2 := by
          by_cases h : s ≤ finish + 2
          · exact h
          · have hcap := hP.1 (finish + 3) (by omega) (by omega)
            omega
        have hbound := D_le_of_le hs
        rw [hD] at hbound
        have := hfit.1
        omega
      · have hlo' : finish + 1 ≤ M := by
          by_cases h : finish + 1 ≤ M
          · exact h
          · have hcap := hpre.1 (M + 2) (by omega) (by omega)
            omega
        exact ih (by omega) hcanon' (replay_new_maximum hnew hpre hcanon') hrest hfit.2
          hlo' hhi h968 hMcanon hP

end A166944Research
