import A166944.Lemmas

/-!
# First-hit bounds for the critical record-index branches

A factor of either horizon term can force an earlier event. In the two
post-record branches this applies to the cofactor of the proposed increment
as well as to the increment itself.
-/

namespace A166944Research

private theorem next_multiple_with_parity {s v parity : Nat}
    (hv : 0 < v) (hvodd : v % 2 = 1) (hparity : parity < 2) :
    ∃ j : Nat, s < j ∧ j ≤ s + 2 * v ∧ v ∣ j ∧ j % 2 = parity := by
  let k := s / v + 1
  have hquot := Nat.div_add_mod s v
  have hrem := Nat.mod_lt s hv
  have hk : v * k = v * (s / v) + v := by simp [k, Nat.mul_add]
  by_cases hp : k % 2 = parity
  · refine ⟨v * k, by omega, by omega, ⟨k, rfl⟩, ?_⟩
    simp [Nat.mul_mod, hvodd, hp, Nat.mod_eq_of_lt hparity]
  · have hp' : (k + 1) % 2 = parity := by omega
    have hnext : v * (k + 1) = v * k + v := by simp [Nat.mul_add]
    refine ⟨v * (k + 1), by omega, by omega, ⟨k + 1, rfl⟩, ?_⟩
    simp [Nat.mul_mod, hvodd, hp', Nat.mod_eq_of_lt hparity]

private theorem odd_factor {v w : Nat} (hodd : w % 2 = 1) (hv : v ∣ w) :
    v % 2 = 1 := by
  obtain ⟨k, rfl⟩ := hv
  rw [Nat.mul_mod] at hodd
  by_cases hzero : v % 2 = 0
  · simp [hzero] at hodd
  · omega

private theorem moving_horizon_unit_gcd {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r) :
    (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
  rcases moving_horizon_first_hit_map hstep with h | h
  · exact h.2.2.2 j hsj hjr
  · exact h.2.2.2 j hsj hjr

/-- Any nonunit divisor of the even-event horizon term bounds the first gap. -/
theorem moving_horizon_gap_le_twice_even_factor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C - 1) :
    r - s ≤ 2 * v := by
  have hC : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hCpos : 0 < C := Nat.zero_lt_of_lt hstep.1.2.2
  have hvodd := odd_factor (by omega : (C - 1) % 2 = 1) hdiv
  obtain ⟨j, hsj, hj, hvj, hpar⟩ :=
    next_multiple_with_parity (s := s) (parity := 0) (by omega : 0 < v) hvodd (by decide)
  by_cases h : r - s ≤ 2 * v
  · exact h
  · have hunit := (moving_horizon_unit_gcd hstep hsj (by omega)).1 hpar
    have hvone := Nat.gcd_eq_one_iff.mp hunit v hvj hdiv
    omega

/-- Any nonunit divisor of the odd-event horizon term bounds the first gap. -/
theorem moving_horizon_gap_le_twice_odd_factor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C + 1) :
    r - s ≤ 2 * v := by
  have hC : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hvodd := odd_factor (by omega : (C + 1) % 2 = 1) hdiv
  obtain ⟨j, hsj, hj, hvj, hpar⟩ :=
    next_multiple_with_parity (s := s - 2) (parity := 1) (by omega : 0 < v) hvodd (by decide)
  have hs : 2 ≤ s := hstep.1.1
  by_cases h : r - s ≤ 2 * v
  · exact h
  · have hunit := (moving_horizon_unit_gcd hstep (j := j + 2) (by omega) (by omega)).2
      (by omega)
    have hvone := Nat.gcd_eq_one_iff.mp hunit v (by simpa using hvj) hdiv
    omega

private theorem cofactor_lt_twice_width {e delta w v : Nat}
    (hw : 2 ≤ w) (hdelta : delta + 1 ≤ 2 * e) (hprod : e * v ≤ delta * w + 1) :
    v < 2 * w := by
  have hwidth := Nat.mul_le_mul_right w hdelta
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hwidth
  have hright : e * (2 * w) = 2 * (e * w) := by ac_rfl
  apply Nat.lt_of_mul_lt_mul_left (a := e)
  rw [hright]
  omega

/-- The even branch bounds the increment by its record quotient and gap. -/
theorem critical_postrecord_q_three_increment_bound {M delta c r C' e : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hstep : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 0) (hclose : r - delta * c ≤ e + 2) :
    2 * e + 2 ≤ (c + 2) * (r - delta * c + 1) ∧ e < 2 * ((c + 2) * (c + 2)) := by
  let w := c + 2
  let t := r - delta * c
  obtain ⟨_, _, v, _, _, _, hv, _, _⟩ :=
    critical_postrecord_even_q_three_factor_package hdeltaodd hbound hMe hEd hstep
      he hrpar hclose
  have hscalar : 2 * delta = t + 1 + 3 * e :=
    critical_postrecord_even_q_three_scalar hdeltaodd hbound hMe hEd hstep
      he hrpar hclose
  have hw : 4 ≤ w := by omega
  have hv_eq : e * v + 1 = delta * w := hv
  have hvhi := cofactor_lt_twice_width (by omega : 2 ≤ w)
    (by omega : delta + 1 ≤ 2 * e) (show e * v ≤ delta * w + 1 by omega)
  have hbalance : e * (2 * v) + 2 = e * (3 * w) + w * (t + 1) := by
    calc
      e * (2 * v) + 2 = 2 * (e * v + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; ac_rfl
      _ = (2 * delta) * w := by rw [hv_eq, Nat.mul_assoc]
      _ = e * (3 * w) + w * (t + 1) := by
        rw [hscalar, Nat.add_mul, Nat.mul_assoc (n := 3)]
        ac_rfl
  have hterm : 2 < w * (t + 1) := by
    have hprod := Nat.mul_le_mul_left w (show 1 ≤ t + 1 by omega)
    simpa using (show 2 < w * (t + 1) by omega)
  have hvlo : 3 * w < 2 * v := by
    by_cases h : 3 * w < 2 * v
    · exact h
    have hmul := Nat.mul_le_mul_left e (show 2 * v ≤ 3 * w by omega)
    omega
  have hvlow : 3 * w + 2 ≤ 2 * v := by omega
  have hmul := Nat.mul_le_mul_left e hvlow
  rw [Nat.mul_add] at hmul
  have hgap_bound : 2 * e + 2 ≤ w * (t + 1) := by omega
  have hdiv : v ∣ delta * (c + 2) - 1 := ⟨e, by rw [Nat.mul_comm v]; omega⟩
  have ht := moving_horizon_gap_le_twice_even_factor hstep (by omega : 1 < v) hdiv
  have htwidth : t + 1 ≤ 4 * w := by omega
  have hprod := Nat.mul_le_mul_left w htwidth
  have hquad : w * (4 * w) = 4 * (w * w) := by ac_rfl
  rw [hquad] at hprod
  exact ⟨hgap_bound, by change e < 2 * (w * w); omega⟩

/-- The odd branch gives a companion bound on the increment. -/
theorem critical_postrecord_q_two_increment_bound {M delta c r C' e : Nat}
    (hcmin : 2 ≤ c) (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hstep : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 1) :
    2 * e + 3 * (c + 2) ≤ (c + 2) * (r - delta * c) + 2 ∧
      e < 2 * ((c + 2) * (c + 2)) := by
  let w := c + 2
  let t := r - delta * c
  obtain ⟨_, _, v, _, _, _, hv, _, _⟩ :=
    critical_postrecord_odd_q_two_factor_package hbound hMe hstep he hrpar
  have hscalar : 2 * delta + 3 = t + 2 * e :=
    critical_postrecord_odd_q_two_scalar hbound hMe hstep he hrpar
  have hw : 4 ≤ w := by omega
  have hv_eq : e * v = delta * w + 1 := hv
  have hvhi := cofactor_lt_twice_width (by omega : 2 ≤ w)
    (by omega : delta + 1 ≤ 2 * e) (show e * v ≤ delta * w + 1 by omega)
  have hbalance : 2 * (e * v) + 3 * w = 2 * (e * w) + w * t + 2 := by
    calc
      2 * (e * v) + 3 * w = (2 * delta + 3) * w + 2 := by
        rw [hv_eq, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_assoc]
        omega
      _ = 2 * (e * w) + w * t + 2 := by
        rw [hscalar, Nat.add_mul, Nat.mul_assoc (n := 2)]
        ac_rfl
  have hvlo : w < v := by
    by_cases h : w < v
    · exact h
    have hmul := Nat.mul_le_mul_left e (show v ≤ w by omega)
    have hsize := Nat.mul_le_mul_right w (show e ≤ delta by omega)
    omega
  have hmul := Nat.mul_le_mul_left e (show w + 1 ≤ v by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hgap_bound : 2 * e + 3 * w ≤ w * t + 2 := by omega
  have hdiv : v ∣ delta * (c + 2) + 1 := ⟨e, by rw [Nat.mul_comm v, hv]⟩
  have ht := moving_horizon_gap_le_twice_odd_factor hstep (by omega : 1 < v) hdiv
  have htwidth : t ≤ 4 * w := by omega
  have hprod := Nat.mul_le_mul_left w htwidth
  have hquad : w * (4 * w) = 4 * (w * w) := by ac_rfl
  rw [hquad] at hprod
  exact ⟨hgap_bound, by change e < 2 * (w * w); omega⟩

/-- The two smallest critical record quotients cannot precede the even q=3 branch. -/
theorem critical_postrecord_q_three_c_ge_six {M delta c r C' e : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hstep : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 0) (hclose : r - delta * c ≤ e + 2) :
    6 ≤ c := by
  obtain ⟨_, _, v, _, _, _, hv, _, _⟩ :=
    critical_postrecord_even_q_three_factor_package hdeltaodd hbound hMe hEd hstep
      he hrpar hclose
  have hscalar := critical_postrecord_even_q_three_scalar hdeltaodd hbound hMe hEd hstep
    he hrpar hclose
  have hsr := hstep.2.1
  have hC : (delta * (c + 2)) % 2 = 0 := by simp [Nat.mul_mod, show (c + 2) % 2 = 0 by omega]
  have hdiv : v ∣ delta * (c + 2) - 1 := ⟨e, by rw [Nat.mul_comm v]; omega⟩
  have hvodd := odd_factor (by omega : (delta * (c + 2) - 1) % 2 = 1) hdiv
  by_cases hgoal : 6 ≤ c
  · exact hgoal
  have hsmall : c = 2 ∨ c = 4 := by omega
  rcases hsmall with rfl | rfl
  · have hvlo : 6 ≤ v := by
      by_cases h : 6 ≤ v
      · exact h
      have hmul := Nat.mul_le_mul_left e (show v ≤ 5 by omega)
      omega
    have hvhi : v < 8 := by
      by_cases h : v < 8
      · exact h
      have hmul := Nat.mul_le_mul_left e (show 8 ≤ v by omega)
      omega
    have hv7 : v = 7 := by omega
    subst v
    have hgap := moving_horizon_gap_le_twice_even_factor hstep (by decide : 1 < 7) hdiv
    omega
  · have hvlo : 10 ≤ v := by
      by_cases h : 10 ≤ v
      · exact h
      have hmul := Nat.mul_le_mul_left e (show v ≤ 9 by omega)
      omega
    have hvhi : v < 12 := by
      by_cases h : v < 12
      · exact h
      have hmul := Nat.mul_le_mul_left e (show 12 ≤ v by omega)
      omega
    have hv11 : v = 11 := by omega
    subst v
    have hgap := moving_horizon_gap_le_twice_even_factor hstep (by decide : 1 < 11) hdiv
    omega

/-- The two smallest critical record quotients cannot precede the odd q=2 branch. -/
theorem critical_postrecord_q_two_c_ge_six {M delta c r C' e : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hstep : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 1) :
    6 ≤ c := by
  obtain ⟨_, _, v, _, _, _, hv, _, _⟩ :=
    critical_postrecord_odd_q_two_factor_package hbound hMe hstep he hrpar
  have hscalar := critical_postrecord_odd_q_two_scalar hbound hMe hstep he hrpar
  have hsr := hstep.2.1
  have heodd : e % 2 = 1 := by
    rw [← he]
    exact d_mod_two_eq_one_of_three_le (by have := hstep.1.1; omega)
  have htmin : 7 ≤ r - delta * c := by omega
  have hC : (delta * (c + 2)) % 2 = 0 := by simp [Nat.mul_mod, show (c + 2) % 2 = 0 by omega]
  have hdiv : v ∣ delta * (c + 2) + 1 := ⟨e, by rw [Nat.mul_comm v, hv]⟩
  have hvodd := odd_factor (by omega : (delta * (c + 2) + 1) % 2 = 1) hdiv
  by_cases hgoal : 6 ≤ c
  · exact hgoal
  have hsmall : c = 2 ∨ c = 4 := by omega
  rcases hsmall with rfl | rfl
  · have hvlo : 5 ≤ v := by
      by_cases h : 5 ≤ v
      · exact h
      have hmul := Nat.mul_le_mul_left e (show v ≤ 4 by omega)
      omega
    have hvhi : v < 8 := by
      by_cases h : v < 8
      · exact h
      have hmul := Nat.mul_le_mul_left e (show 8 ≤ v by omega)
      omega
    have hcases : v = 5 ∨ v = 7 := by omega
    rcases hcases with rfl | rfl
    · have hgap := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 5) hdiv
      omega
    · have hgap := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 7) hdiv
      omega
  · have hvlo : 7 ≤ v := by
      by_cases h : 7 ≤ v
      · exact h
      have hmul := Nat.mul_le_mul_left e (show v ≤ 6 by omega)
      omega
    have hvhi : v < 12 := by
      by_cases h : v < 12
      · exact h
      have hmul := Nat.mul_le_mul_left e (show 12 ≤ v by omega)
      omega
    have hcases : v = 7 ∨ v = 9 ∨ v = 11 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hgap := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 7) hdiv
      have hes : e = 13 ∨ e = 25 := by omega
      rcases hes with rfl | rfl
      · have hd : delta = 15 := by omega
        subst delta
        have hu := (moving_horizon_unit_gcd hstep (j := 65) (by decide) (by omega)).2
          (by decide)
        exact False.elim ((by decide : Nat.gcd (65 - 2) (15 * (4 + 2) + 1) ≠ 1) hu)
      · have hfive : 5 ∣ delta * (4 + 2) + 1 := by rw [← hv]; decide
        have hgap' := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 5) hfive
        omega
    · have hthree : 3 ∣ delta * (4 + 2) + 1 := Nat.dvd_trans (by decide : 3 ∣ 9) hdiv
      have hgap := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 3) hthree
      omega
    · have hgap := moving_horizon_gap_le_twice_odd_factor hstep (by decide : 1 < 11) hdiv
      omega

/-- A mod-3 obstruction involving both first-hit windows at a critical record. -/
theorem critical_straddling_mod_three_gap {s n delta r C' : Nat}
    (hn : n % 2 = 0) (hdelta : delta % 3 = 2)
    (hpre : IsMovingHorizonStep s (n + delta + 1) n (n + 2 * delta))
    (hpost : IsMovingHorizonStep n (n + 2 * delta) r C') :
    n - s ≤ 3 ∨ r - n ≤ 6 := by
  by_cases ht : n - s ≤ 3
  · exact Or.inl ht
  by_cases hu : r - n ≤ 6
  · exact Or.inr hu
  have hs : 2 ≤ s := hpre.1.1
  have hpreOdd := (moving_horizon_unit_gcd hpre (j := n - 3) (by omega) (by omega)).2
    (by omega)
  have hpostOdd := (moving_horizon_unit_gcd hpost (j := n + 1) (by omega) (by omega)).2
    (by omega)
  have hpostEven := (moving_horizon_unit_gcd hpost (j := n + 6) (by omega) (by omega)).1
    (by omega)
  have h2 : n % 3 ≠ 2 := by
    intro h
    exact (by decide : 3 ≠ 1) (Nat.gcd_eq_one_iff.mp hpreOdd 3
      (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
  have h1 : n % 3 ≠ 1 := by
    intro h
    exact (by decide : 3 ≠ 1) (Nat.gcd_eq_one_iff.mp hpostOdd 3
      (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
  have h0 : n % 3 ≠ 0 := by
    intro h
    exact (by decide : 3 ≠ 1) (Nat.gcd_eq_one_iff.mp hpostEven 3
      (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
  omega

/-- In the odd branch, a critical increment congruent to 2 mod 3 forces
the previous event to be at most three indices before the record. -/
theorem critical_postrecord_q_two_pre_gap_le_three {M s delta c r C' e : Nat}
    (hc : c % 2 = 0) (hdeltaodd : delta % 2 = 1) (hdelta : delta % 3 = 2)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hpre : IsMovingHorizonStep s (delta * c + delta + 1) (delta * c)
      (delta * (c + 2)))
    (hpost : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 1) :
    delta * c - s ≤ 3 := by
  have heodd : e % 2 = 1 := by
    rw [← he]
    exact d_mod_two_eq_one_of_three_le (by have := hpost.1.1; have := hpost.2.1; omega)
  have hscalar := critical_postrecord_odd_q_two_scalar hbound hMe hpost he hrpar
  have hn : (delta * c) % 2 = 0 := by simp [Nat.mul_mod, hc]
  have hsum : delta * (c + 2) = delta * c + 2 * delta := by
    simp [Nat.mul_add, Nat.mul_comm delta 2]
  have h := critical_straddling_mod_three_gap hn hdelta
    (by simpa only [hsum] using hpre) (by simpa only [hsum] using hpost)
  omega

/-- The two-index even branch has an exact integer parameter, so its critical
index is at least quadratic in the following increment. -/
theorem critical_postrecord_q_three_gap_two_parameters {M delta c r C' e : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hstep : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 0) (hgap : r - delta * c = 2) :
    ∃ h : Nat, 1 ≤ h ∧ 2 * delta = 3 * (e + 1) ∧ 3 * c + 4 = 2 * (e * h) ∧
      delta * c = (e + 1) * (e * h - 2) := by
  have hclose : r - delta * c ≤ e + 2 := by omega
  have hscalar := critical_postrecord_even_q_three_scalar hdeltaodd hbound hMe hEd
    hstep he hrpar hclose
  have hde : 2 * delta = 3 * (e + 1) := by omega
  have hr : r = delta * c + 2 := by have := hstep.2.1; omega
  have hlin : 2 * r = 3 * (e * c) + (3 * c + 4) := by
    calc
      2 * r = (2 * delta) * c + 4 := by simp [hr, Nat.mul_add, Nat.mul_assoc]
      _ = 3 * (e * c) + (3 * c + 4) := by
        rw [hde, Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.add_assoc]
  have hdiv := (moving_horizon_event_divisibility_even hstep he hrpar).1
  have htotal := Nat.dvd_mul_left_of_dvd hdiv 2
  rw [hlin] at htotal
  have hfirst : e ∣ 3 * (e * c) :=
    Nat.dvd_mul_left_of_dvd (show e ∣ e * c from ⟨c, rfl⟩) 3
  have hrem : e ∣ 3 * c + 4 := by simpa using Nat.dvd_sub htotal hfirst
  obtain ⟨q, hq⟩ := hrem
  have heodd : e % 2 = 1 := by
    rw [← he]
    exact d_mod_two_eq_one_of_three_le (by have := hstep.1.1; have := hstep.2.1; omega)
  have hqeven : q % 2 = 0 := by
    have hm := congrArg (fun x : Nat => x % 2) hq
    simpa [Nat.mul_mod, heodd, show (3 * c + 4) % 2 = 0 by omega] using hm.symm
  let h := q / 2
  have hh : 2 * h = q := by have := Nat.div_add_mod q 2; omega
  have hpos : 1 ≤ h := by
    by_cases hhpos : 1 ≤ h
    · exact hhpos
    have hqzero : q = 0 := by omega
    rw [hqzero, Nat.mul_zero] at hq
    omega
  have hmul : 3 * c + 4 = 2 * (e * h) := by rw [hq, ← hh]; ac_rfl
  have hlin' : 3 * c = 2 * (e * h - 2) := by omega
  have hdouble : 2 * (delta * c) = 2 * ((e + 1) * (e * h - 2)) := by
    calc
      2 * (delta * c) = (2 * delta) * c := by ac_rfl
      _ = (e + 1) * (3 * c) := by rw [hde]; ac_rfl
      _ = 2 * ((e + 1) * (e * h - 2)) := by rw [hlin']; ac_rfl
  exact ⟨h, hpos, hde, hmul, by omega⟩

/-- With one index before the critical record and two after it, the last
old event is a divisor of a small expression in the gap-two parameter. -/
theorem critical_q_three_short_straddle_last_factor
    {M delta c e s C C' f : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hold : IsMovingHorizonStep s C (delta * c - 1) (delta * c + delta + 1))
    (hf : d (delta * c - 1) = f)
    (hpost : IsMovingHorizonStep (delta * c) (delta * (c + 2)) (delta * c + 2) C')
    (he : d (delta * c + 2) = e) :
    ∃ h : Nat, 1 ≤ h ∧ 3 * c + 4 = 2 * (e * h) ∧
      delta * c = (e + 1) * (e * h - 2) ∧ f ∣ 15 * (4 * h + 1) := by
  have hn : (delta * c) % 2 = 0 := by simp [Nat.mul_mod, hc]
  have hnmin : 3 ≤ delta * c := by have := hold.1.1; have := hold.2.1; omega
  obtain ⟨h, hpos, hde, hmul, hindex⟩ :=
    critical_postrecord_q_three_gap_two_parameters hc hcmin hdeltaodd hbound hMe hEd
      hpost he (by omega) (by omega)
  rcases moving_horizon_step_endpoint_anchor hold hf with hEven | ⟨_, hfn, hfC⟩
  · omega
  have hleft : f ∣ delta * c - 3 := by
    simpa only [show (delta * c - 1) - 2 = delta * c - 3 by omega] using hfn
  have hfd : f ∣ delta + 6 := by
    have hdiff : (delta * c + delta + 1 + 2) - (delta * c - 3) = delta + 6 := by omega
    simpa only [hdiff] using Nat.dvd_sub hfC hleft
  have hA : f ∣ 6 * c + 3 := by
    have hdiff : (delta + 6) * c - (delta * c - 3) = 6 * c + 3 := by
      rw [Nat.add_mul]
      omega
    simpa only [hdiff] using Nat.dvd_sub (Nat.dvd_mul_right_of_dvd hfd c) hleft
  have hB : f ∣ 3 * (e + 5) := by
    rw [show 3 * (e + 5) = (delta + 6) * 2 by omega]
    exact Nat.dvd_mul_right_of_dvd hfd 2
  have hdiff : (4 * h) * (3 * (e + 5)) = 3 * (6 * c + 3) + 15 * (4 * h + 1) := by
    calc
      (4 * h) * (3 * (e + 5)) = 12 * (e * h) + 60 * h := by
        rw [Nat.mul_add 3 e 5, Nat.mul_add]
        have h₁ : (4 * h) * (3 * e) = (4 * 3) * (e * h) := by ac_rfl
        have h₂ : (4 * h) * (3 * 5) = (4 * (3 * 5)) * h := by ac_rfl
        rw [h₁, h₂]
      _ = 3 * (6 * c + 3) + 15 * (4 * h + 1) := by omega
  have hfinal := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hB (4 * h))
    (Nat.dvd_mul_left_of_dvd hA 3)
  exact ⟨h, hpos, hmul, hindex, by simpa [hdiff] using hfinal⟩

/-- The gap-two branch would require more than `e*h` old events in
the canonical prefix, where `h` is the exact gap-two parameter. -/
theorem critical_q_three_gap_two_old_count_bound
    {M delta c sf Cf p r C' e : Nat}
    (hc : c % 2 = 0) (hcmin : 2 ≤ c) (hdeltaodd : delta % 2 = 1)
    (hbound : delta + 6 ≤ 2 * M) (hMe : M < e) (hEd : e < delta)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hcap : ∀ j : Nat, 2 ≤ j → j < delta * c → d j ≤ M)
    (hpre : IsMovingHorizonStep sf Cf (delta * c) (delta * (c + 2)))
    (hcrit : d (delta * c) = delta)
    (hpost : IsMovingHorizonStep (delta * c) (delta * (c + 2)) r C')
    (he : d r = e) (hrpar : r % 2 = 0) (hgap : r - delta * c = 2) :
    ∃ h : Nat, 1 ≤ h ∧ 3 * c + 4 = 2 * (e * h) ∧ e * h < p := by
  obtain ⟨h, hpos, _, hparam, hindex⟩ :=
    critical_postrecord_q_three_gap_two_parameters hc hcmin hdeltaodd hbound hMe hEd
      hpost he hrpar hgap
  let y := e * h
  have hy : e ≤ y := by simpa [y] using Nat.mul_le_mul_left e hpos
  have hCf : Cf = delta * c + delta + 1 := by
    have hf := moving_horizon_critical_predecessor_factorization hpre
      ⟨hcrit, rfl, hc, hcmin, rfl⟩
    have h := hf.2.1
    omega
  have hidx : (delta * c - 1) + 1 = delta * c := by have := hpre.2.1; omega
  obtain ⟨E, _, hE, _, _, hEM, _⟩ := moving_horizon_path_count_bounds
    (k := delta * c - 1) hpath (by rw [hidx]; exact hpre.2.1)
    (fun j hj hle => hcap j hj (by simpa only [hidx] using hle))
  refine ⟨h, hpos, hparam, ?_⟩
  by_cases hlt : y < p
  · exact hlt
  have hgrowth := Nat.mul_le_mul_left (M - 1) (show p ≤ y by omega)
  have hMp : M * p = (M - 1) * p + p := by
    calc
      M * p = ((M - 1) + 1) * p := congrArg (fun z => z * p) (by omega)
      _ = (M - 1) * p + p := by simp [Nat.add_mul]
  rw [hMp] at hEM
  have hindex' : delta * c = (e + 1) * (y - 2) := hindex
  have hmon := Nat.mul_le_mul_right (y - 2) (show M + 2 ≤ e + 1 by omega)
  rw [← hindex'] at hmon
  have hmul : (M + 2) * (y - 2) + 2 * (M + 2) = (M - 1) * y + 3 * y := by
    rw [Nat.mul_comm 2 (M + 2), ← Nat.mul_add, Nat.sub_add_cancel (by omega : 2 ≤ y)]
    calc
      (M + 2) * y = ((M - 1) + 3) * y := congrArg (fun z => z * y) (by omega)
      _ = (M - 1) * y + 3 * y := Nat.add_mul _ _ _
  omega

private def smallRecordNext (M : Nat) : Nat :=
  match M with
  | 7 => 15
  | 13 => 45
  | 43 => 141
  | 139 => 315
  | 313 => 663
  | _ => 1323

set_option maxRecDepth 5000 in
set_option maxHeartbeats 12000000 in
/-- Check each small candidate against the original recurrence, including
every increment before its first subsequent record. -/
private theorem small_canonical_next_record :
    ∀ M : Fin 968, 5 < M.val → d (M.val + 2) = M.val →
      let n := smallRecordNext M.val
      2 ≤ n ∧ n % 2 = 1 ∧ M.val < d n ∧ ∀ j : Fin n, d j.val ≤ M.val := by
  decide

/-- A first critical failure already forces the previous record to be large,
independently of the post-record event. -/
theorem critical_previous_max_ge_968 {k M : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (henv : HasHistoryEnvelopeBefore (k + 1)) :
    968 ≤ M := by
  by_cases hlarge : 968 ≤ M
  · exact hlarge
  obtain ⟨p, c, _, _, hp, _, hM5, hidx, _, _, _, _, hcrit, hceven, _⟩ :=
    critical_previous_maximum_canonical hk hP hIH hnew hfail henv
  rw [hidx] at hp
  obtain ⟨hn, hnodd, hrecord, hprior⟩ :=
    small_canonical_next_record ⟨M, by omega⟩ hM5 hp
  have hcrit_even : (k + 1) % 2 = 0 := by
    rw [hcrit]
    simp [Nat.mul_mod, hceven]
  rcases Nat.lt_trichotomy (k + 1) (smallRecordNext M) with h | h | h
  · have hbefore := hprior ⟨k + 1, h⟩
    change d (k + 1) ≤ M at hbefore
    omega
  · have hodd : (k + 1) % 2 = 1 := by rw [h]; exact hnodd
    omega
  · have hbefore := hP.1 (smallRecordNext M) hn (by omega)
    exact False.elim (Nat.not_lt_of_ge hbefore hrecord)

/-- Actual first failures followed by either intermediate branch require
a large record quotient and a correspondingly distant pre-record horizon. -/
theorem critical_intermediate_postrecord_replay_bounds {k M r C' e : Nat}
    (hk : 2 ≤ k) (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (henv : HasHistoryEnvelopeBefore (k + 1))
    (hstep : IsMovingHorizonStep (k + 1) (D (k + 1)) r C')
    (he : d r = e) (hMe : M < e) (hEd : e < d (k + 1))
    (hbranch : r % 2 = 1 ∨ (r % 2 = 0 ∧ r - (k + 1) ≤ e + 2)) :
    ∃ c : Nat, k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 22 ≤ c ∧
      23 * (M + 1) + 1 ≤ D k := by
  have hM := critical_previous_max_ge_968 hk hP hIH hnew hfail henv
  have hbound : d (k + 1) + 6 ≤ 2 * M :=
    (new_max_failure_reduction hk hIH hnew hfail).2.2.2.2
  have hdeltaodd := d_mod_two_eq_one_of_three_le (n := k + 1) (by omega)
  obtain ⟨c, hidx, hceven, hcmin, _, hD, _, _⟩ :=
    critical_even_quotient_normal_form hk hIH hnew hfail
  have hstep' : IsMovingHorizonStep (d (k + 1) * c) (d (k + 1) * (c + 2)) r C' := by
    simpa only [← hidx, ← hD] using hstep
  have hsize : e < 2 * ((c + 2) * (c + 2)) := by
    rcases hbranch with hodd | ⟨heven, hclose⟩
    · exact (critical_postrecord_q_two_increment_bound hcmin hbound hMe hEd
        hstep' he hodd).2
    · have hclose' : r - d (k + 1) * c ≤ e + 2 := by rw [← hidx]; exact hclose
      exact (critical_postrecord_q_three_increment_bound hceven hcmin hdeltaodd
        hbound hMe hEd hstep' he heven hclose').2
  have hc : 22 ≤ c := by
    by_cases h : 22 ≤ c
    · exact h
    have hwidth : c + 2 ≤ 22 := by omega
    have hsquare := Nat.mul_le_mul hwidth hwidth
    omega
  have hDpre := critical_previous_D_coordinate hD (rfl : d (k + 1) = d (k + 1))
  have hprod := Nat.mul_le_mul (show M + 1 ≤ d (k + 1) by omega)
    (show 23 ≤ c + 1 by omega)
  refine ⟨c, hidx, hceven, hc, ?_⟩
  rw [hDpre, Nat.mul_comm 23 (M + 1)]
  omega

end A166944Research
