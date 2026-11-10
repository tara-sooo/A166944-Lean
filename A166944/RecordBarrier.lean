import Init.Data.Nat.Lcm
import A166944.Lemmas

/-!
# Even common-multiple bounds for capped increments

An increment cannot take the even coordinate `D` past an even multiple
of its size. This gives a finite horizon bound for a capped prefix and
forces arbitrarily large difference records.
-/

namespace A166944Research

private theorem add_le_next_multiple {e x H : Nat}
    (hlt : x < H) (hx : e ∣ x) (hH : e ∣ H) :
    x + e ≤ H := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hH
  have huv := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hlt)
  simpa [Nat.mul_add] using Nat.mul_le_mul_left e huv

/-- A single increment cannot cross an even multiple of its value. -/
theorem D_succ_le_even_multiple {n H : Nat} (hn : 2 ≤ n)
    (hHeven : H % 2 = 0) (hbound : D n ≤ H) (hdiv : d (n + 1) ∣ H) :
    D (n + 1) ≤ H := by
  have hupdate := D_succ_add_one_eq_add_d n
  have hepos := one_le_d_succ n
  by_cases he : d (n + 1) = 1
  · omega
  have hmap := constant_D_event_map_succ (show 1 ≤ n by omega) (rfl : D n = D n)
  by_cases hpar : (n + 1) % 2 = 0
  · rw [if_pos hpar] at hmap
    have hfactor : d (n + 1) ∣ D n - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hDtwo : 2 ≤ D n := Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le hn)
    have hnext := add_le_next_multiple (by omega : D n - 1 < H) hfactor hdiv
    omega
  · rw [if_neg hpar] at hmap
    have hfactor : d (n + 1) ∣ D n + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hstrict : D n < H := by
      by_cases hEq : D n = H
      · have hone := Nat.dvd_sub hfactor (hEq.symm ▸ hdiv)
        have hunit : d (n + 1) ∣ 1 := by simpa using hone
        exact False.elim (he (Nat.eq_one_of_dvd_one hunit))
      · omega
    have hDeven := D_mod_two_eq_zero_of_two_le hn
    have hnext := add_le_next_multiple (by omega : D n + 1 < H) hfactor hdiv
    omega

/-- A common even multiple of the increments on an interval bounds the
horizon throughout that interval once it bounds the initial horizon. -/
theorem D_le_even_multiple_of_interval {s n H : Nat} (hs : 2 ≤ s) (hsn : s ≤ n)
    (hHeven : H % 2 = 0) (hstart : D s ≤ H)
    (hdiv : ∀ j : Nat, s < j → j ≤ n → d j ∣ H) :
    D n ≤ H := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hsn
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hk := ih (by omega : s ≤ s + k) (fun j hsj hj => hdiv j hsj (by omega))
      have hnext := D_succ_le_even_multiple (n := s + k) (by omega) hHeven hk
        (hdiv (s + k + 1) (by omega) (by omega))
      simpa [Nat.add_assoc] using hnext

/-- If the interval increments divide a positive even number, the total
horizon growth on that interval is strictly less than that number. -/
theorem D_growth_lt_of_common_even_multiple {s n P : Nat}
    (hs : 2 ≤ s) (hsn : s ≤ n) (hP : 0 < P) (hPeven : P % 2 = 0)
    (hdiv : ∀ j : Nat, s < j → j ≤ n → d j ∣ P) :
    D n < D s + P := by
  by_cases hzero : D s % P = 0
  · have hPs : P ∣ D s := Nat.dvd_of_mod_eq_zero hzero
    have hcap := D_le_even_multiple_of_interval hs hsn
      (D_mod_two_eq_zero_of_two_le hs) (Nat.le_refl _)
      (fun j hsj hj => Nat.dvd_trans (hdiv j hsj hj) hPs)
    omega
  · let H := P * (D s / P + 1)
    have heq : H = P * (D s / P) + P := by simp [H, Nat.mul_add]
    have hsum := Nat.div_add_mod (D s) P
    have hrem := Nat.mod_lt (D s) hP
    have hH : D s ≤ H := by omega
    have hHlt : H < D s + P := by omega
    have hPeH : P ∣ H := ⟨D s / P + 1, rfl⟩
    have hHeven : H % 2 = 0 := by simp [H, Nat.mul_mod, hPeven]
    have hcap := D_le_even_multiple_of_interval hs hsn hHeven hH
      (fun j hsj hj => Nat.dvd_trans (hdiv j hsj hj) hPeH)
    exact Nat.lt_of_le_of_lt hcap hHlt

private theorem odd_multiple_block {e x : Nat} (he : e % 2 = 1)
    (hx : x % 2 = 1) (hdiv : e ∣ x) :
    ∃ q : Nat, x = (2 * e) * q + e := by
  obtain ⟨v, hv⟩ := hdiv
  have hvodd : v % 2 = 1 := by rw [quotient_mod_two_of_left_odd he, ← hv, hx]
  have hsum := Nat.div_add_mod v 2
  have hvEq : v = 2 * (v / 2) + 1 := by omega
  refine ⟨v / 2, ?_⟩
  calc
    x = e * v := hv
    _ = e * (2 * (v / 2) + 1) := congrArg (fun z => e * z) hvEq
    _ = e * (2 * (v / 2)) + e := by simp [Nat.mul_add]
    _ = (2 * e) * (v / 2) + e := by ac_rfl

private theorem horizon_crossing_residue_of_block {C H e q b : Nat}
    (hC : C = (2 * e) * q + b) (hb : b ≤ e + 1)
    (hstart : C ≤ H) (hfinish : H + 1 < C + e) :
    b ≤ H % (2 * e) := by
  let x := H - (2 * e) * q
  have hx : b ≤ x := by omega
  have hxlt : x < 2 * e := by omega
  have hform : H = x + (2 * e) * q := by omega
  calc
    b ≤ x := hx
    _ = H % (2 * e) := by
      calc
        x = (x + (2 * e) * q) % (2 * e) := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt hxlt]
        _ = H % (2 * e) := congrArg (fun z => z % (2 * e)) hform.symm

/-- Crossing any horizon bound requires the upper residue range for the
increment that crosses it. This can certify bounds much smaller than a
common multiple. -/
theorem D_succ_crossing_requires_upper_residue {n H : Nat} (hn : 2 ≤ n)
    (hstart : D n ≤ H) (hfinish : H < D (n + 1)) :
    d (n + 1) - 1 ≤ H % (2 * d (n + 1)) := by
  let e := d (n + 1)
  have heodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le (by omega)
  have hupdate : D (n + 1) + 1 = D n + e := D_succ_add_one_eq_add_d n
  have hCeven := D_mod_two_eq_zero_of_two_le hn
  have hmap := constant_D_event_map_succ (show 1 ≤ n by omega) (rfl : D n = D n)
  by_cases heven : (n + 1) % 2 = 0
  · rw [if_pos heven] at hmap
    have hDtwo : 2 ≤ D n := Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le hn)
    have hfactor : e ∣ D n - 1 := by
      change d (n + 1) ∣ D n - 1
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨q, hq⟩ := odd_multiple_block heodd (by omega) hfactor
    have hC : D n = (2 * e) * q + (e + 1) := by omega
    have hbound := horizon_crossing_residue_of_block hC (Nat.le_refl _)
      hstart (by omega)
    change e - 1 ≤ H % (2 * e)
    omega
  · rw [if_neg heven] at hmap
    have hfactor : e ∣ D n + 1 := by
      change d (n + 1) ∣ D n + 1
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨q, hq⟩ := odd_multiple_block heodd (by omega) hfactor
    have hC : D n = (2 * e) * q + (e - 1) := by omega
    exact horizon_crossing_residue_of_block hC (by omega) hstart (by omega)

/-- A bound in the lower residue range for all nonunit increments on an
interval cannot be crossed anywhere in that interval. -/
theorem D_le_low_residue_barrier_of_interval {s n H : Nat} (hs : 2 ≤ s) (hsn : s ≤ n)
    (hstart : D s ≤ H)
    (hres : ∀ j : Nat, s < j → j ≤ n → 1 < d j → H % (2 * d j) < d j - 1) :
    D n ≤ H := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hsn
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hprev := ih (by omega : s ≤ s + k) (fun j hsj hj => hres j hsj (by omega))
      by_cases h : D (s + (k + 1)) ≤ H
      · exact h
      have hcross : H < D (s + k + 1) := by
        simpa [Nat.add_assoc] using Nat.lt_of_not_ge h
      have hupdate := D_succ_add_one_eq_add_d (s + k)
      have hbig : 1 < d (s + k + 1) := by omega
      have hupper := D_succ_crossing_requires_upper_residue (by omega) hprev hcross
      have hlower := hres (s + k + 1) (by omega) (by omega) hbig
      omega

/-- The least common multiple of 2 and the positive odd integers at most
the increment cap. Increments from index 3 onward are all odd. -/
def recordHorizonBound : Nat → Nat
  | 0 => 2
  | m + 1 =>
      if (m + 1) % 2 = 1 then Nat.lcm (m + 1) (recordHorizonBound m)
      else recordHorizonBound m

private theorem recordHorizonBound_dvd_succ (M : Nat) :
    recordHorizonBound M ∣ recordHorizonBound (M + 1) := by
  by_cases h : (M + 1) % 2 = 1
  · simpa [recordHorizonBound, h] using Nat.dvd_lcm_right (M + 1) (recordHorizonBound M)
  · simp [recordHorizonBound, h]

theorem recordHorizonBound_pos_even (M : Nat) :
    0 < recordHorizonBound M ∧ 2 ∣ recordHorizonBound M := by
  induction M with
  | zero => decide
  | succ M ih =>
      refine ⟨?_, Nat.dvd_trans ih.2 (recordHorizonBound_dvd_succ M)⟩
      by_cases h : (M + 1) % 2 = 1
      · simpa [recordHorizonBound, h] using
          Nat.lcm_pos (Nat.zero_lt_succ M) ih.1
      · simpa [recordHorizonBound, h] using ih.1

theorem odd_dvd_recordHorizonBound {e M : Nat} (he : e % 2 = 1) (hcap : e ≤ M) :
    e ∣ recordHorizonBound M := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h : e = M + 1
      · subst e
        simpa [recordHorizonBound, he] using Nat.dvd_lcm_left (M + 1) (recordHorizonBound M)
      · exact Nat.dvd_trans (ih (by omega)) (recordHorizonBound_dvd_succ M)

theorem D_le_recordHorizonBound_of_cap {M n : Nat} (hn : 2 ≤ n)
    (hcap : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ M) :
    D n ≤ recordHorizonBound M := by
  have hH := recordHorizonBound_pos_even M
  have hstart : D 2 ≤ recordHorizonBound M := by
    have htwo := Nat.le_of_dvd hH.1 hH.2
    exact Nat.le_trans (by decide : D 2 ≤ 2) htwo
  exact D_le_even_multiple_of_interval (by decide : 2 ≤ 2) hn
    (Nat.mod_eq_zero_of_dvd hH.2) hstart
    (fun j hj hle =>
      odd_dvd_recordHorizonBound (d_mod_two_eq_one_of_three_le (by omega))
        (hcap j (by omega) hle))

/-- A prefix with increments at most `M` cannot extend past this index. -/
theorem capped_prefix_index_le_recordHorizonBound_add_two {M n : Nat} (hn : 2 ≤ n)
    (hcap : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ M) :
    n ≤ recordHorizonBound M + 2 := by
  have hD := D_le_recordHorizonBound_of_cap hn hcap
  have ha := two_mul_le_a_add_two hn
  have heq : D n + n = a n := Nat.sub_add_cancel (index_le_a n)
  omega

private theorem record_at_or_before_of_large_increment {M n : Nat}
    (hn : 2 ≤ n) (hnew : M < d n) :
    ∃ j : Nat, 2 ≤ j ∧ j ≤ n ∧ M < d j ∧
      ∀ i : Nat, 2 ≤ i → i < j → d i < d j := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : ∃ j : Nat, 2 ≤ j ∧ j < n ∧ M < d j
      · obtain ⟨j, hj, hjn, hlarge⟩ := h
        obtain ⟨i, hi, hij, hilarge, hiprior⟩ := ih j hjn hj hlarge
        exact ⟨i, hi, Nat.le_trans hij (Nat.le_of_lt hjn), hilarge, hiprior⟩
      · refine ⟨n, hn, Nat.le_refl n, hnew, ?_⟩
        intro j hj hjn
        have hle : d j ≤ M := by
          by_cases hlarge : M < d j
          · exact False.elim (h ⟨j, hj, hjn, hlarge⟩)
          · omega
        exact Nat.lt_of_le_of_lt hle hnew

/-- For every threshold there is a larger difference record by an explicit
finite index in the original recurrence. -/
theorem exists_difference_record_above_by_bound (M : Nat) :
    ∃ n : Nat, 2 ≤ n ∧ n ≤ recordHorizonBound M + 3 ∧ M < d n ∧
      ∀ j : Nat, 2 ≤ j → j < n → d j < d n := by
  by_cases h : ∃ n : Nat, 2 ≤ n ∧ n ≤ recordHorizonBound M + 3 ∧ M < d n
  · obtain ⟨n, hn, hbound, hnew⟩ := h
    obtain ⟨j, hj, hjn, hjlarge, hjprior⟩ :=
      record_at_or_before_of_large_increment hn hnew
    exact ⟨j, hj, Nat.le_trans hjn hbound, hjlarge, hjprior⟩
  · have hcap : ∀ j : Nat, 2 ≤ j → j ≤ recordHorizonBound M + 3 → d j ≤ M := by
      intro j hj hle
      by_cases hlarge : M < d j
      · exact False.elim (h ⟨j, hj, hle, hlarge⟩)
      · omega
    have hindex := capped_prefix_index_le_recordHorizonBound_add_two
      (by omega : 2 ≤ recordHorizonBound M + 3) hcap
    omega

theorem difference_records_unbounded (M : Nat) :
    ∃ R : Nat, M < R ∧ IsDifferenceRecord R := by
  obtain ⟨n, hn, _, hlarge, hprior⟩ := exists_difference_record_above_by_bound M
  exact ⟨d n, hlarge, n, hn, rfl, hprior⟩

/-- A moving-horizon prefix with a fixed previous maximum has a bound on
both its horizon and the number of its nonunit steps. -/
theorem capped_moving_horizon_path_bound {M s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p)
    (hP : IsAttainedPreviousMaximum M sf) :
    C + 2 * p ≤ Cf ∧ Cf ≤ recordHorizonBound M := by
  have hstate := moving_horizon_path_endpoint hpath
  have hcap := D_le_recordHorizonBound_of_cap hstate.1 hP.1
  rw [hstate.2.1] at hcap
  obtain ⟨E, _, hE, _, hcount, _, _⟩ :=
    moving_horizon_path_count_bounds (k := sf) hpath (by omega)
      (fun j hj hle => hP.1 j hj (by omega))
  exact ⟨by omega, hcap⟩

/-- An actual moving horizon with an attained maximum follows a finite
sequence of old events. Its exit is a fundamental point at the horizon or
a new record inside the horizon. -/
theorem capped_moving_horizon_eventual_exit {M s C : Nat}
    (hstate : IsMovingHorizonState s C) (hP : IsAttainedPreviousMaximum M s) :
    ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
      IsAttainedPreviousMaximum M sf ∧
      ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
        ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
  let H := recordHorizonBound M
  have aux (budget : Nat) : ∀ s C : Nat, H - C = budget →
      IsMovingHorizonState s C → IsAttainedPreviousMaximum M s →
      ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
        IsAttainedPreviousMaximum M sf ∧
        ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
          ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
        intro s C hbudget hs hPs
        rcases moving_horizon_dichotomy hs with hno | ⟨r, C', hstep⟩
        · have hDc := (moving_horizon_no_event_telescope hs hno).1
          have hBc := B_add_index_eq_D_add_two (by have := hs.1; have := hs.2.2; omega : 2 ≤ C)
          exact ⟨s, C, 0, ⟨rfl, rfl, hs⟩, hPs, Or.inl ⟨by omega, hno⟩⟩
        · rcases hstep with ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩
          rcases moving_horizon_max_transfer hPs hsr hdr hunit with hOld | hNew
          · have hbound := D_le_recordHorizonBound_of_cap hr.1 hOld.2.1
            have hCbound : C' ≤ H := by rw [hC']; exact hbound
            have hlt : H - C' < budget := by omega
            obtain ⟨sf, Cf, p, hpath, hPsf, hexit⟩ :=
              ih (H - C') hlt r C' rfl hr hOld.2
            exact ⟨sf, Cf, p + 1,
              ⟨hs, r, C', ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩, hpath⟩,
              hPsf, hexit⟩
          · exact ⟨s, C, 0, ⟨rfl, rfl, hs⟩, hPs,
              Or.inr ⟨r, C', ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩, hNew.1⟩⟩
  exact aux (H - C) s C rfl hstate hP

end A166944Research
