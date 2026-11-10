import A166944.RecordBarrier

/-!
# A direct reduction of the record-index question to fundamental returns

The upper bound on the original recurrence identifies the coordinates of
an already canonical increment. The next record after such an increment
is canonical exactly when the intervening history contains a fundamental
point. This reduction uses neither a global history envelope nor the
post-critical quotient cases.
-/

namespace A166944Research

theorem a_le_three_mul (n : Nat) : a n ≤ 3 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      by_cases hn : 2 ≤ n
      · have hprev : n + 1 - 1 = n := by omega
        have hmap := d_eq_if_gcd_of_two_le (show 2 ≤ n + 1 by omega)
        rw [hprev] at hmap
        have hstep := a_add_d_succ (k := n)
        by_cases hpar : (n + 1) % 2 = 0
        · rw [if_pos hpar] at hmap
          have hnDiv : d (n + 1) ∣ n + 1 := hmap.symm ▸ Nat.gcd_dvd_left _ _
          have haDiv : d (n + 1) ∣ a n := hmap.symm ▸ Nat.gcd_dvd_right _ _
          have hdiv := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hnDiv 3) haDiv
          have hbound := Nat.le_of_dvd (by omega : 0 < 3 * (n + 1) - a n) hdiv
          omega
        · rw [if_neg hpar, show n + 1 - 2 = n - 1 by omega] at hmap
          have hnDiv : d (n + 1) ∣ n - 1 := hmap.symm ▸ Nat.gcd_dvd_left _ _
          have haDiv : d (n + 1) ∣ a n := hmap.symm ▸ Nat.gcd_dvd_right _ _
          have hthree := Nat.dvd_mul_left_of_dvd hnDiv 3
          have hparity := a_mod_two_of_two_le hn
          have hneq : a n ≠ 3 * (n - 1) := by omega
          by_cases hlt : a n < 3 * (n - 1)
          · have hbound := Nat.le_of_dvd (by omega : 0 < 3 * (n - 1) - a n)
              (Nat.dvd_sub hthree haDiv)
            omega
          · have hbound := Nat.le_of_dvd (by omega : 0 < a n - 3 * (n - 1))
              (Nat.dvd_sub haDiv hthree)
            omega
      · have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with rfl | rfl <;> decide

private theorem fundamental_last_event_gap {m rho : Nat} (hm : 14 ≤ m)
    (hfund : B m = 2) (hLast : IsLastNontrivialBefore rho m) :
    5 ≤ m - rho := by
  obtain ⟨hρ2, hρm, hEvent, hunit⟩ := hLast
  have hDm := D_eq_self_of_fundamental (by omega : 2 ≤ m) hfund
  have hmeven : m % 2 = 0 := hDm ▸ D_mod_two_eq_zero_of_two_le (by omega)
  have htail := first_later_event_D_eq (r := m + 1) hρ2 (rfl : D rho = D rho)
    (by omega) (fun j hj hjm => hunit j hj (by omega))
  have hDρ : D rho = m := by simpa [hDm] using htail.symm
  have hρ3 : 3 ≤ rho := by
    by_cases h : rho = 2
    · rw [h, show D 2 = 2 by decide] at hDρ
      omega
    · omega
  have hDprev : 2 ≤ D (rho - 1) :=
    Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le (by omega))
  have heodd := d_mod_two_eq_one_of_three_le hρ3
  have he3 : 3 ≤ d rho := by omega
  have hupdate := D_succ_add_one_eq_add_d (rho - 1)
  rw [show rho - 1 + 1 = rho by omega, hDρ] at hupdate
  have hmap := constant_D_event_map (by omega : 2 ≤ rho) (rfl : D (rho - 1) = D (rho - 1))
  by_cases hgap : 5 ≤ m - rho
  · exact hgap
  by_cases hpar : rho % 2 = 0
  · rw [if_pos hpar] at hmap
    have hrDiv : d rho ∣ rho := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hprevDiv : d rho ∣ D (rho - 1) - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hmDiv : d rho ∣ m := by
      rw [show m = (D (rho - 1) - 1) + d rho by omega]
      exact Nat.dvd_add hprevDiv (Nat.dvd_refl _)
    obtain ⟨q, hq⟩ := Nat.dvd_sub hmDiv hrDiv
    have hqeven : q % 2 = 0 := by
      rw [quotient_mod_two_of_left_odd heodd, ← hq]
      omega
    have hqpos : q ≠ 0 := by
      intro hzero
      rw [hzero, Nat.mul_zero] at hq
      omega
    have hmul := Nat.mul_le_mul he3 (by omega : 2 ≤ q)
    omega
  · rw [if_neg hpar] at hmap
    have hrDiv : d rho ∣ rho - 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hprevDiv : d rho ∣ D (rho - 1) + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hmDiv : d rho ∣ m + 2 := by
      rw [show m + 2 = (D (rho - 1) + 1) + d rho by omega]
      exact Nat.dvd_add hprevDiv (Nat.dvd_refl _)
    obtain ⟨q, hq⟩ := Nat.dvd_sub hmDiv hrDiv
    rw [show m + 2 - (rho - 2) = m - rho + 4 by omega] at hq
    have hqodd : q % 2 = 1 := by
      rw [quotient_mod_two_of_left_odd heodd, ← hq]
      omega
    have hqone : q = 1 := by
      by_cases h : q = 1
      · exact h
      have hmul := Nat.mul_le_mul he3 (by omega : 3 ≤ q)
      omega
    rw [hqone, Nat.mul_one] at hq
    have hprev : D (rho - 1) = rho - 3 := by omega
    rw [hprev, show rho - 3 + 1 = rho - 2 by omega, Nat.gcd_self] at hmap
    omega

private theorem early_fundamental_mod_six :
    ∀ m : Fin 14, 6 ≤ m.val → B m.val = 2 → m.val % 6 = 0 := by
  decide

/-- Every fundamental point of the actual recurrence from 6 onward is
divisible by 6. -/
theorem fundamental_point_mod_six {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
    m % 6 = 0 := by
  by_cases hsmall : m < 14
  · exact early_fundamental_mod_six ⟨m, hsmall⟩ hm hfund
  have hDm := D_eq_self_of_fundamental (by omega : 2 ≤ m) hfund
  have hmeven : m % 2 = 0 := hDm ▸ D_mod_two_eq_zero_of_two_le (by omega)
  by_cases hdm : d m = 1
  · obtain ⟨rho, hLast⟩ := exists_last_nontrivial_before hdm
      ⟨2, by decide, by omega, by decide⟩
    have hgap := fundamental_last_event_gap (by omega) hfund hLast
    obtain ⟨hρ2, hρm, _, hunit⟩ := hLast
    have htail := first_later_event_D_eq (r := m + 1) hρ2 (rfl : D rho = D rho)
      (by omega) (fun j hj hjm => hunit j hj (by omega))
    have hDρ : D rho = m := by simpa [hDm] using htail.symm
    have hnotOne : m % 3 ≠ 1 := by
      intro hmod
      have hD := first_later_event_D_eq (r := m - 4) hρ2 hDρ
        (by omega) (fun j hj hjm => hunit j hj (by omega))
      have hmap := constant_D_event_map (by omega : 2 ≤ m - 4) hD
      rw [if_pos (by omega), hunit (m - 4) (by omega) (by omega)] at hmap
      have hdiv := Nat.gcd_eq_one_iff.mp hmap.symm 3
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    have hnotTwo : m % 3 ≠ 2 := by
      intro hmod
      have hD := first_later_event_D_eq (r := m - 3) hρ2 hDρ
        (by omega) (fun j hj hjm => hunit j hj (by omega))
      have hmap := constant_D_event_map (by omega : 2 ≤ m - 3) hD
      rw [if_neg (by omega), hunit (m - 3) (by omega) (by omega)] at hmap
      have hdiv := Nat.gcd_eq_one_iff.mp hmap.symm 3
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    omega
  · have hstep := excess_succ_add_two (k := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, hfund] at hstep
    have hdodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ m)
    have hdthree : d m = 3 := by omega
    have hmap := d_eq_if_gcd_of_two_le (by omega : 2 ≤ m)
    rw [if_pos hmeven, hdthree] at hmap
    have hdiv : 3 ∣ m := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

/-- A large fundamental point always resets after three indices. -/
theorem fundamental_reset_at_three {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
    d (m + 1) = 1 ∧ d (m + 2) = 1 ∧ d (m + 3) = m + 1 := by
  rcases fundamental_reset (by omega : 2 ≤ m) hfund with h | h
  · exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  · have hmod := fundamental_point_mod_six hm hfund
    have hmap := d_eq_if_gcd_of_two_le (by omega : 2 ≤ m + 2)
    rw [if_pos (by omega), h.2.1] at hmap
    have hdiv : 3 ∣ m + 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hbad := Nat.mod_eq_zero_of_dvd hdiv
    omega

/-- The canonical index alone forces the usual coordinates and a preceding
fundamental point. -/
theorem canonical_increment_coordinates {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) :
    a (R + 1) = 2 * R ∧ D (R + 2) = 2 * R - 2 ∧ B (R - 1) = 2 := by
  have hodd : R % 2 = 1 := hd ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ R + 2)
  have hmap := d_add_two_of_odd R (by omega : (R + 2) % 2 ≠ 0)
  have hdiv : R ∣ a (R + 1) := by
    have hg := Nat.gcd_dvd_right R (a (R + 1))
    rwa [← hmap, hd] at hg
  obtain ⟨u, hu⟩ := hdiv
  have hapar := a_mod_two_of_two_le (by omega : 2 ≤ R + 1)
  have hupar : u % 2 = 0 := by
    rw [quotient_mod_two_of_left_odd hodd, ← hu, hapar]
    omega
  have halo := two_mul_le_a_add_two (by omega : 2 ≤ R + 1)
  have hahi := a_le_three_mul (R + 1)
  have huhi : u < 4 := by
    by_cases h : u < 4
    · exact h
    have hmul := Nat.mul_le_mul_left R (by omega : 4 ≤ u)
    omega
  have hupos : u ≠ 0 := by
    intro hzero
    rw [hzero, Nat.mul_zero] at hu
    omega
  have ha : a (R + 1) = 2 * R := by
    rw [hu, show u = 2 by omega, Nat.mul_comm]
  have haRecord : a (R + 2) = 3 * R := by
    have hstep : a (R + 1) + d (R + 2) = a (R + 2) := a_add_d_succ
    omega
  have hD : D (R + 2) = 2 * R - 2 := by simp [D, haRecord]; omega
  have hB : B (R + 2) + 2 = R := by simp [B, haRecord]; omega
  exact ⟨ha, hD, (canonical_record_fundamental_predecessor hR hodd ha hd hB).1⟩

theorem canonical_increment_mod_six {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) : R % 6 = 1 := by
  have hodd : R % 2 = 1 := hd ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ R + 2)
  have hfund := (canonical_increment_coordinates hR hd).2.2
  have hmod := fundamental_point_mod_six (by omega : 6 ≤ R - 1) hfund
  omega

/-- A large increment occurs at its canonical index exactly when the
preceding horizon is strictly below the increment's index. -/
theorem large_increment_index_iff_beyond_horizon {n : Nat} (hn : 3 ≤ n)
    (hd : 5 < d n) : n = d n + 2 ↔ D (n - 1) < n := by
  constructor
  · intro hidx
    have hcanon : d (d n + 2) = d n := congrArg d hidx.symm
    have ha := (canonical_increment_coordinates hd hcanon).1
    have hpred : n - 1 = d n + 1 := by omega
    rw [hpred, D, ha]
    omega
  · intro hC
    have hbefore : 2 ≤ n - 1 := by omega
    have hBrel := B_add_index_eq_D_add_two hbefore
    have hBsmall : B (n - 1) ≤ 3 := by omega
    have hnsucc : n - 1 + 1 = n := by omega
    have hBpar := B_mod_two_of_two_le hbefore
    rcases Nat.mod_two_eq_zero_or_one n with hEven | hOdd
    · have hpredOdd : (n - 1) % 2 = 1 := by omega
      have hmap := d_succ_eq_gcd_small_residual hbefore hpredOdd (by omega)
      rw [hnsucc] at hmap
      have hsize : d n ≤ 4 - B (n - 1) := hmap ▸
        Nat.gcd_le_right n (by omega)
      omega
    · have hpredEven : (n - 1) % 2 = 0 := by omega
      rcases (show B (n - 1) = 0 ∨ B (n - 1) = 2 by omega) with hzero | htwo
      · have hstep := B_zero_transition hbefore hzero
        rw [hnsucc] at hstep
        omega
      · have hstep := B_two_transition hbefore htwo
        rw [hnsucc] at hstep
        omega

/-- From a canonical previous record, the next strict record is canonical
exactly when a fundamental point occurs between the two records. -/
theorem next_record_index_iff_fundamental {M k : Nat} (hM : 5 < M)
    (hcanonical : d (M + 2) = M)
    (hP : IsAttainedPreviousMaximum M k) (hnew : M < d (k + 1)) :
    k + 1 = d (k + 1) + 2 ↔
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2 := by
  have ⟨haM, hDM, _⟩ := canonical_increment_coordinates hM hcanonical
  constructor
  · intro hidx
    have hR : 5 < d (k + 1) := by omega
    have hcanon : d (d (k + 1) + 2) = d (k + 1) := congrArg d hidx.symm
    have hB := (canonical_increment_coordinates hR hcanon).2.2
    have hModd : M % 2 = 1 := hcanonical ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
    have hRodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ k + 1)
    have hRgap : M + 2 ≤ d (k + 1) := by omega
    have hneq : d (k + 1) ≠ M + 2 := by
      intro heq
      rw [heq, show M + 2 - 1 = M + 1 by omega] at hB
      have ha := (B_eq_two_iff_a_eq_two_mul (by omega : 2 ≤ M + 1)).1 hB
      omega
    exact ⟨d (k + 1) - 1, by omega, by omega, hB⟩
  · rintro ⟨m, hm, hmk, hfund⟩
    have hm2 : 2 ≤ m := by omega
    have hD := D_le_of_le hm
    rw [hDM, D_eq_self_of_fundamental hm2 hfund] at hD
    obtain ⟨hd1, hd2, hd3⟩ := fundamental_reset_at_three (by omega) hfund
    have hlater : k + 1 ≤ m + 3 := by
      by_cases h : k + 1 ≤ m + 3
      · exact h
      have hcap := hP.1 (m + 3) (by omega) (by omega)
      omega
    have heq : k + 1 = m + 3 := by
      by_cases h : k + 1 = m + 3
      · exact h
      rcases (show k + 1 = m + 1 ∨ k + 1 = m + 2 by omega) with h | h
      · rw [h, hd1] at hnew; omega
      · rw [h, hd2] at hnew; omega
    rw [heq, hd3]

theorem attained_previous_maximum_exists (k : Nat) (hk : 2 ≤ k) :
    ∃ M : Nat, IsAttainedPreviousMaximum M k := by
  obtain ⟨j, rfl⟩ := Nat.le.dest hk
  clear hk
  induction j with
  | zero =>
      refine ⟨d 2, ?_, ⟨2, by decide, by decide, rfl⟩⟩
      intro i hi2 hi
      have heq : i = 2 := by omega
      simp [heq]
  | succ j ih =>
      obtain ⟨M, hM⟩ := ih
      have hindex : 2 + (j + 1) - 1 = 2 + j := by omega
      by_cases hnew : M < d (2 + (j + 1))
      · exact ⟨_, attained_previous_maximum_extend (by omega)
          (by simpa only [hindex] using hM) hnew⟩
      · obtain ⟨r, hr, hrj, hdr⟩ := hM.2
        refine ⟨M, ?_, ⟨r, hr, by omega, hdr⟩⟩
        intro i hi2 hi
        by_cases h : i ≤ 2 + j
        · exact hM.1 i hi2 h
        · have heq : i = 2 + (j + 1) := by omega
          rw [heq]
          omega

private theorem early_large_increment_index :
    ∀ n : Fin 10, 5 < d n.val → n.val = d n.val + 2 := by
  decide

/-- The full record-index theorem is equivalent to proving a fundamental
return between a canonical record and its next strict record. -/
theorem record_index_iff_canonical_returns :
    (∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) ↔
    (∀ {M k : Nat}, 5 < M → M + 2 ≤ k → d (M + 2) = M →
      IsAttainedPreviousMaximum M k → M < d (k + 1) →
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2) := by
  constructor
  · intro hIndex M k hM hk hcanon hP hnew
    have hnext := hIndex (by omega : 5 < d (k + 1)) (by omega : 2 ≤ k + 1) rfl
      (critical_actual_next_difference_record_prior hP hnew)
    exact (next_record_index_iff_fundamental hM hcanon hP hnew).1 hnext
  · intro hReturn R n
    induction n using Nat.strongRecOn generalizing R with
    | ind n ih =>
        intro hR hn hd hprior
        by_cases hsmall : n ≤ 9
        · have h := early_large_increment_index ⟨n, by omega⟩ (by change 5 < d n; omega)
          change n = d n + 2 at h
          omega
        · let k := n - 1
          have hk : 9 ≤ k := by omega
          have hkn : k + 1 = n := by omega
          obtain ⟨M, hP⟩ := attained_previous_maximum_exists k (by omega)
          have hM : 5 < M := by
            have h := hP.1 9 (by decide) hk
            rw [show d 9 = 7 by decide] at h
            omega
          obtain ⟨p, hp, hpk, hdp, hpPrior⟩ := attained_previous_maximum_first_occurrence hP
          have hpEq := ih p (by omega) hM hp hdp hpPrior
          have hMcanon : d (M + 2) = M := by rwa [← hpEq]
          have hnew : M < d (k + 1) := by
            rw [hkn, hd, ← hdp]
            exact hprior p hp (by omega)
          have hfund := hReturn hM (by omega : M + 2 ≤ k) hMcanon hP hnew
          have hEq := (next_record_index_iff_fundamental hM hMcanon hP hnew).2 hfund
          simpa only [hkn, hd] using hEq

/-- A single reachability exclusion suffices for the full index theorem.
On any capped replay from a canonical record, a first hit inside the
horizon must still be old. -/
theorem record_index_iff_no_canonical_escape :
    (∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) ↔
    (∀ {M sf Cf p r C' : Nat}, 5 < M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → IsMovingHorizonStep sf Cf r C' → d r ≤ M) := by
  constructor
  · intro hIndex M sf Cf p r C' hM _ _ hP hstep
    by_cases h : d r ≤ M
    · exact h
    have hnew : M < d r := by omega
    obtain ⟨hs, hsr, hrC, _, hunit, hD, _, _, _⟩ := hstep
    have hr3 : 3 ≤ r := by have := hs.1; omega
    have hprior : ∀ j : Nat, 2 ≤ j → j < r → d j < d r := by
      intro j hj hjr
      by_cases hle : j ≤ sf
      · exact Nat.lt_of_le_of_lt (hP.1 j hj hle) hnew
      · rw [hunit j (by omega) hjr]
        omega
    have hR : 5 < d r := by omega
    have hidx := hIndex hR (by omega) rfl hprior
    have hbelow := (large_increment_index_iff_beyond_horizon hr3 hR).1 hidx
    omega
  · intro hNoEscape
    apply record_index_iff_canonical_returns.2
    intro M k hM hk hcanon hP hnew
    have hD := (canonical_increment_coordinates hM hcanon).2.1
    have hstate : IsMovingHorizonState (M + 2) (2 * M - 2) :=
      ⟨by omega, hD, by omega⟩
    have hPstart : IsAttainedPreviousMaximum M (M + 2) :=
      ⟨fun j hj hle => hP.1 j hj (Nat.le_trans hle hk),
        ⟨M + 2, by omega, Nat.le_refl _, hcanon⟩⟩
    obtain ⟨sf, Cf, p, hpath, hPsf, hexit⟩ :=
      capped_moving_horizon_eventual_exit hstate hPstart
    rcases hexit with ⟨hfund, hunit⟩ | ⟨r, C', hstep, hlarge⟩
    · have hsf := moving_horizon_path_index_le hpath
      have hCf := (moving_horizon_path_endpoint hpath).2.2
      have hnext : sf < k + 1 := by
        by_cases h : sf < k + 1
        · exact h
        have hcap := hPsf.1 (k + 1) (by omega) (by omega)
        omega
      have hCnext : Cf < k + 1 := by
        by_cases h : Cf < k + 1
        · exact h
        rw [hunit (k + 1) hnext (by omega)] at hnew
        omega
      exact ⟨Cf, by omega, hCnext, hfund⟩
    · exact False.elim (Nat.not_lt_of_ge (hNoEscape hM hcanon hpath hPsf hstep) hlarge)

/-- An escape inside the horizon can only happen once the horizon
exceeds three times the previous maximum by at least five. -/
theorem moving_horizon_new_record_horizon_lower_bound {M s C r C' : Nat}
    (hM : 5 < M) (hP : IsAttainedPreviousMaximum M s)
    (hstep : IsMovingHorizonStep s C r C') (hnew : M < d r) :
    3 * M + 5 ≤ C := by
  obtain ⟨hs, hsr, hrC, hdr, _, hD, _, _, _⟩ := hstep
  have hr3 : 3 ≤ r := by have := hs.1; omega
  have hModd := attained_previous_maximum_value_mod_two_eq_one hP hM
  have hdodd := d_mod_two_eq_one_of_three_le hr3
  by_cases hpar : r % 2 = 0
  · have hsize := constant_D_event_even_size_bound_of_le hr3 hD hpar hrC hdr
    omega
  · have hsize := constant_D_event_odd_size_bound_of_le hr3 hD hpar hrC
    omega

/-- An explicit small residue barrier certifies that a capped canonical
prefix cannot produce a new record inside the horizon. -/
theorem canonical_path_no_escape_of_low_residue_barrier {M sf Cf p r C' H : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hP : IsAttainedPreviousMaximum M sf) (hstep : IsMovingHorizonStep sf Cf r C')
    (hstart : 2 * M - 2 ≤ H) (hsmall : H ≤ 3 * M + 4)
    (hres : ∀ j : Nat, M + 2 < j → j ≤ sf → 1 < d j → H % (2 * d j) < d j - 1) :
    d r ≤ M := by
  have hDstart := (canonical_increment_coordinates hM hcanon).2.1
  have hD := D_le_low_residue_barrier_of_interval (by omega : 2 ≤ M + 2)
    (moving_horizon_path_index_le hpath) (by rwa [hDstart]) hres
  rw [hstep.1.2.1] at hD
  by_cases hnew : M < d r
  · have hhigh := moving_horizon_new_record_horizon_lower_bound hM hP hstep hnew
    omega
  · omega

/-- The canonical-index theorem would now also force arbitrarily late
fundamental points, since the difference records are unbounded. -/
theorem fundamental_points_unbounded_of_record_index
    (hIndex : ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) (N : Nat) :
    ∃ m : Nat, N < m ∧ a m = 2 * m := by
  obtain ⟨R, hlarge, n, hn, hd, hprior⟩ := difference_records_unbounded (N + 6)
  have hR : 5 < R := by omega
  have hidx := hIndex hR hn hd hprior
  have hcanon : d (R + 2) = R := by rwa [← hidx]
  have hB := (canonical_increment_coordinates hR hcanon).2.2
  exact ⟨R - 1, by omega, (B_eq_two_iff_a_eq_two_mul (by omega : 2 ≤ R - 1)).1 hB⟩

end A166944Research
