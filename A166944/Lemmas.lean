import A166944.ResearchDefs

/-!
# Verified A166944 lemmas

Only Lean-verified reusable lemmas belong here.

Rules:
- no `sorry` / `admit` / new axioms;
- experimental or conjectural statements belong in `Attempt.lean` or the Issue;
- keep this file lightweight: do not import Formal Conjectures.
-/

namespace A166944Research

theorem d_add_two (n : Nat) :
    d (n + 2) = if (n + 2) % 2 = 0 then
      Nat.gcd (n + 2) (a (n + 1))
    else Nat.gcd n (a (n + 1)) := by
  simp only [d, a]
  split <;> simp_all

theorem d_add_two_of_even (n : Nat) (h : (n + 2) % 2 = 0) :
    d (n + 2) = Nat.gcd (n + 2) (a (n + 1)) := by
  simpa [h] using d_add_two n

theorem d_add_two_of_odd (n : Nat) (h : (n + 2) % 2 ≠ 0) :
    d (n + 2) = Nat.gcd n (a (n + 1)) := by
  have h' : n % 2 ≠ 0 := by simpa using h
  simpa [h'] using d_add_two n

theorem a_pos : ∀ n : Nat, 0 < n → 0 < a n := by
  intro n
  induction n with
  | zero =>
      intro h
      cases h
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          intro _
          simp only [a]
          split <;> exact Nat.add_pos_left (ih (Nat.zero_lt_succ n)) _

theorem d_add_two_pos (n : Nat) : 0 < d (n + 2) := by
  rw [d_add_two]
  split <;> exact Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n))

theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

theorem a_le_of_le {m n : Nat} (hmn : m ≤ n) : a m ≤ a n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using a_le_succ (m + k))

theorem gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one {m n : Nat}
    (h : m % 2 = 1 ∨ n % 2 = 1) : Nat.gcd m n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (Nat.gcd m n) with hg | hg
  · exfalso
    have h2g : 2 ∣ Nat.gcd m n := Nat.dvd_of_mod_eq_zero hg
    rcases h with hm | hn
    · have h2m : 2 ∣ m := Nat.dvd_trans h2g (Nat.gcd_dvd_left m n)
      have hm0 : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2m
      have : (0 : Nat) = 1 := hm0.symm.trans hm
      cases this
    · have h2n : 2 ∣ n := Nat.dvd_trans h2g (Nat.gcd_dvd_right m n)
      have hn0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2n
      have : (0 : Nat) = 1 := hn0.symm.trans hn
      cases this
  · exact hg

theorem a_add_two_mod_two (n : Nat) :
    a (n + 2) % 2 = (n + 2) % 2 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
      change a (n + 3) % 2 = (n + 3) % 2
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hidx : (n + 3) % 2 ≠ 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 0 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 0 := by simp [hn]
        have hg : Nat.gcd (n + 1) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inl (by simp [Nat.add_mod, hn]))
        rw [a]
        rw [if_neg hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]
      · have hidx : (n + 3) % 2 = 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 1 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 1 := by simp [hn]
        have hg : Nat.gcd (n + 3) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inr hprev)
        rw [a]
        rw [if_pos hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]

theorem a_mod_two_of_two_le {n : Nat} (hn : 2 ≤ n) :
    a n % 2 = n % 2 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using a_add_two_mod_two k

theorem d_add_two_mod_two_eq_one {n : Nat} (hn : 1 ≤ n) :
    d (n + 2) % 2 = 1 := by
  rw [d_add_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · have hprev : a (n + 1) % 2 = 1 := by
      calc
        a (n + 1) % 2 = (n + 1) % 2 :=
          a_mod_two_of_two_le (Nat.succ_le_succ hn)
        _ = 1 := by simp [Nat.add_mod, hn0]
    have hg : Nat.gcd (n + 2) (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inr hprev)
    simp [hn0, hg]
  · have hg : Nat.gcd n (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inl hn1)
    simp [hn1, hg]

theorem d_mod_two_eq_one_of_three_le {n : Nat} (hn : 3 ≤ n) :
    d n % 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    d_add_two_mod_two_eq_one hk

theorem d_eq_if_gcd_of_two_le {n : Nat} (hn : 2 ≤ n) :
    d n = if n % 2 = 0 then
      Nat.gcd n (a (n - 1))
    else Nat.gcd (n - 2) (a (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two k

theorem record_value_mod_two_eq_one {R : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) : R % 2 = 1 := by
  rcases hrec with ⟨w, hw2, hwd, _⟩
  have hw3 : 3 ≤ w := by
    obtain ⟨k, rfl⟩ := Nat.le.dest hw2
    cases k with
    | zero =>
        exfalso
        rw [← hwd] at hR
        simpa [d, a] using hR
    | succ k =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.le_add_right 3 k)
  rw [← hwd]
  exact d_mod_two_eq_one_of_three_le hw3

theorem one_or_three_le_of_mod_two_eq_one {c : Nat} (hc : c % 2 = 1) :
    c = 1 ∨ 3 ≤ c := by
  cases c with
  | zero => simp at hc
  | succ c =>
      cases c with
      | zero => exact Or.inl rfl
      | succ c =>
          cases c with
          | zero => simp at hc
          | succ c =>
              right
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Nat.le_add_right 3 c)

theorem two_le_of_pos_of_mod_two_eq_zero {c : Nat} (hcpos : 0 < c)
    (hc : c % 2 = 0) : 2 ≤ c := by
  cases c with
  | zero => simp at hcpos
  | succ c =>
      cases c with
      | zero => simp at hc
      | succ c =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.le_add_right 2 c)

theorem record_even_occurrence_structure {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (heven : n % 2 = 0) :
    ∃ c : Nat, n = R * c ∧ c % 2 = 0 ∧ 2 ≤ c := by
  have hdiv : R ∣ n := by
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_pos heven]
    exact Nat.gcd_dvd_left _ _
  rcases hdiv with ⟨c, hc⟩
  have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
  have hcmod : c % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
    · exact hc0
    · exfalso
      have hnodd : n % 2 = 1 := by
        rw [hc]
        simp [Nat.mul_mod, hRodd, hc1]
      have : (1 : Nat) = 0 := hnodd.symm.trans heven
      cases this
  have hcpos : 0 < c := by
    cases c with
    | zero =>
        have hn0 : n = 0 := by simpa using hc
        rw [hn0] at hn
        simp at hn
    | succ c => exact Nat.zero_lt_succ c
  exact ⟨c, hc, hcmod, two_le_of_pos_of_mod_two_eq_zero hcpos hcmod⟩

theorem record_odd_occurrence_structure {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (hodd : n % 2 = 1) :
    ∃ c : Nat, n - 2 = R * c ∧ c % 2 = 1 ∧ 1 ≤ c ∧
      (c = 1 ∨ 3 ≤ c) := by
  have hne : n % 2 ≠ 0 := by simp [hodd]
  have hdiv : R ∣ n - 2 := by
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_neg hne]
    exact Nat.gcd_dvd_left _ _
  rcases hdiv with ⟨c, hc⟩
  have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
  have hn_eq : R * c + 2 = n := by
    calc
      R * c + 2 = (n - 2) + 2 := by rw [hc]
      _ = n := Nat.sub_add_cancel hn
  have hcmod : c % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
    · exfalso
      have hn0 : n % 2 = 0 := by
        rw [← hn_eq]
        simp [Nat.add_mod, Nat.mul_mod, hRodd, hc0]
      have : (0 : Nat) = 1 := hn0.symm.trans hodd
      cases this
    · exact hc1
  have hcpos : 1 ≤ c := by
    cases c with
    | zero => simp at hcmod
    | succ c => exact Nat.succ_le_succ (Nat.zero_le c)
  exact ⟨c, hc, hcmod, hcpos, one_or_three_le_of_mod_two_eq_one hcmod⟩

theorem record_index_structure {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R) :
    n = R + 2 ∨ (n % 2 = 0 ∧ 2 * R ≤ n) ∨
      (n % 2 = 1 ∧ 3 * R + 2 ≤ n) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · right
    left
    refine ⟨hn0, ?_⟩
    rcases record_even_occurrence_structure hR hrec hn hd hn0 with
      ⟨c, hc, _, hc2⟩
    rw [hc]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left R hc2
  · rcases record_odd_occurrence_structure hR hrec hn hd hn1 with
      ⟨c, hc, _, _, hc_cases⟩
    rcases hc_cases with rfl | hc3
    · left
      calc
        n = (n - 2) + 2 := (Nat.sub_add_cancel hn).symm
        _ = R * 1 + 2 := by rw [hc]
        _ = R + 2 := by simp
    · right
      right
      refine ⟨hn1, ?_⟩
      calc
        3 * R + 2 = R * 3 + 2 := by simp [Nat.mul_comm]
        _ ≤ R * c + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left R hc3) 2
        _ = (n - 2) + 2 := by rw [hc]
        _ = n := Nat.sub_add_cancel hn

theorem attained_previous_maximum_first_occurrence {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      ∀ j : Nat, 2 ≤ j → j < r → d j < P := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      rcases hP.2 with ⟨r, hr2, hrk, hdr⟩
      by_cases hprev : ∃ j : Nat, 2 ≤ j ∧ j < k ∧ d j = P
      · rcases hprev with ⟨j, hj2, hjk, hdj⟩
        have hPj : IsAttainedPreviousMaximum P j := by
          refine ⟨?_, ⟨j, hj2, Nat.le_refl j, hdj⟩⟩
          intro i hi2 hij
          have hjk' : j ≤ k := Nat.le_of_lt hjk
          exact hP.1 i hi2 (Nat.le_trans hij hjk')
        rcases ih j hjk hPj with ⟨s, hs2, hsj, hsd, hsprior⟩
        exact ⟨s, hs2, Nat.le_trans hsj (Nat.le_of_lt hjk), hsd, hsprior⟩
      · have hr_eq : r = k := by
          apply Nat.le_antisymm hrk
          exact Nat.le_of_not_gt (fun hkr => hprev ⟨r, hr2, hkr, hdr⟩)
        refine ⟨k, ?_, Nat.le_refl k, ?_, ?_⟩
        · simpa [hr_eq] using hr2
        · simpa [hr_eq] using hdr
        · intro j hj2 hjk
          have hjle := hP.1 j hj2 (Nat.le_of_lt hjk)
          have hneq : d j ≠ P := by
            intro hdj
            exact hprev ⟨j, hj2, hjk, hdj⟩
          exact Nat.lt_of_le_of_ne hjle hneq

theorem attained_previous_maximum_record {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧ IsDifferenceRecord P := by
  rcases attained_previous_maximum_first_occurrence hP with
    ⟨r, hr2, hrk, hdr, hprior⟩
  exact ⟨r, hr2, hrk, hdr, ⟨r, hr2, hdr, hprior⟩⟩

theorem attained_previous_maximum_value_mod_two_eq_one {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) (hP5 : 5 < P) :
    P % 2 = 1 := by
  rcases attained_previous_maximum_record hP with
    ⟨r, hr2, _, hdr, hrec⟩
  exact record_value_mod_two_eq_one hP5 hrec

theorem attained_previous_maximum_index_structure {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) (hP5 : 5 < P) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      (r = P + 2 ∨ (r % 2 = 0 ∧ 2 * P ≤ r) ∨
        (r % 2 = 1 ∧ 3 * P + 2 ≤ r)) := by
  rcases attained_previous_maximum_record hP with
    ⟨r, hr2, hrk, hdr, hrec⟩
  exact ⟨r, hr2, hrk, hdr, record_index_structure hP5 hrec hr2 hdr⟩

theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

theorem index_le_a : ∀ n : Nat, n ≤ a n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          rw [a]
          split
          · have hg : 1 ≤ Nat.gcd (n + 2) (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)
          · have hg : 1 ≤ Nat.gcd n (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)

theorem D_succ_add_one_eq_add_d (n : Nat) :
    D (n + 1) + 1 = D n + d (n + 1) := by
  simp only [D, d]
  have hindex : n ≤ a n := index_le_a n
  have hnext : n + 1 ≤ a (n + 1) := index_le_a (n + 1)
  have hstep : a n ≤ a (n + 1) := a_le_succ n
  calc
    a (n + 1) - (n + 1) + 1 =
        a (n + 1) - (n + 1) + ((n + 1) - n) := by simp
    _ = a (n + 1) - n :=
      Nat.sub_add_sub_cancel hnext (Nat.le_add_right n 1)
    _ = (a n - n) + (a (n + 1) - a n) := by
      calc
        a (n + 1) - n = (a (n + 1) - a n) + (a n - n) :=
          (Nat.sub_add_sub_cancel hstep hindex).symm
        _ = (a n - n) + (a (n + 1) - a n) := Nat.add_comm _ _

theorem D_succ_eq_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + d (n + 1) - 1 := by
  simpa using congrArg (fun x : Nat => x - 1) (D_succ_add_one_eq_add_d n)

theorem one_le_d_succ (n : Nat) : 1 ≤ d (n + 1) := by
  cases n with
  | zero => simp [d, a]
  | succ n => exact Nat.succ_le_of_lt (d_add_two_pos n)

theorem D_succ_eq_D_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + (d (n + 1) - 1) := by
  rw [D_succ_eq_add_d_sub_one n]
  exact Nat.add_sub_assoc (one_le_d_succ n) (D n)

theorem D_add_two_le_succ_of_two_le {n : Nat} (hn : 2 ≤ n)
    (h : 1 < d (n + 1)) : D n + 2 ≤ D (n + 1) := by
  have hn3 : 3 ≤ n + 1 := by
    exact Nat.succ_le_succ hn
  have hdodd : d (n + 1) % 2 = 1 := by
    simpa [Nat.add_assoc] using d_mod_two_eq_one_of_three_le hn3
  have hd3 : 3 ≤ d (n + 1) := by
    rcases one_or_three_le_of_mod_two_eq_one hdodd with hd1 | hd3
    · have : (1 : Nat) < 1 := by simpa [hd1] using h
      exact False.elim (Nat.lt_irrefl 1 this)
    · exact hd3
  have hdsub : 2 ≤ d (n + 1) - 1 := by
    apply Nat.le_sub_of_add_le
    simpa using hd3
  rw [D_succ_eq_D_add_d_sub_one]
  exact Nat.add_le_add_left hdsub (D n)

theorem D_le_succ (n : Nat) : D n ≤ D (n + 1) := by
  have hle : D n + 1 ≤ D n + d (n + 1) :=
    Nat.add_le_add_left (one_le_d_succ n) (D n)
  have hle' : D n + 1 ≤ D (n + 1) + 1 :=
    Nat.le_trans hle (Nat.le_of_eq (D_succ_add_one_eq_add_d n).symm)
  exact Nat.le_of_succ_le_succ hle'

theorem D_le_of_le {m n : Nat} (hmn : m ≤ n) : D m ≤ D n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using D_le_succ (m + k))

theorem D_mod_two_eq_zero_of_two_le {n : Nat} (hn : 2 ≤ n) :
    D n % 2 = 0 := by
  have hsum : D n + n = a n :=
    Nat.sub_add_cancel (index_le_a n)
  rcases Nat.mod_two_eq_zero_or_one (D n) with hzero | hone
  · exact hzero
  · have hsum_mod : (D n + n) % 2 = n % 2 := by
      rw [hsum]
      exact a_mod_two_of_two_le hn
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · simp [Nat.add_mod, hone, hn0] at hsum_mod
    · simp [Nat.add_mod, hone, hn1] at hsum_mod

theorem quotient_mod_two_of_left_odd {R q : Nat} (hR : R % 2 = 1) :
    q % 2 = (R * q) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · simp [Nat.mul_mod, hR, hq0]
  · simp [Nat.mul_mod, hR, hq1]

theorem constant_D_event_map {r C : Nat} (hr : 2 ≤ r)
    (hD : D (r - 1) = C) :
    d r = if r % 2 = 0 then Nat.gcd r (C - 1)
      else Nat.gcd (r - 2) (C + 1) := by
  have hr1 : 1 ≤ r := Nat.le_trans (by simp) hr
  have hs : 1 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hrs : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have ha : a (r - 1) = C + (r - 1) := by
    calc
      a (r - 1) = D (r - 1) + (r - 1) :=
        (Nat.sub_add_cancel (index_le_a (r - 1))).symm
      _ = C + (r - 1) := by rw [hD]
  have hC : 1 ≤ C := by
    rw [← hD]
    calc
      1 = D 1 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  by_cases heven : r % 2 = 0
  · rw [if_pos heven, d_eq_if_gcd_of_two_le hr, if_pos heven, ha]
    have hsum : C + (r - 1) = (C - 1) + r := by
      calc
        C + (r - 1) = ((C - 1) + 1) + (r - 1) := by
          rw [Nat.sub_add_cancel hC]
        _ = (C - 1) + ((r - 1) + 1) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (C - 1) + r := by rw [hrs]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right r (C - 1) 1)
  · rw [if_neg heven, d_eq_if_gcd_of_two_le hr, if_neg heven, ha]
    have hpred : r - 1 = (r - 2) + 1 := by
      apply (Nat.sub_eq_iff_eq_add hr1).2
      calc
        r = (r - 2) + 2 := (Nat.sub_add_cancel hr).symm
        _ = ((r - 2) + 1) + 1 := by simp [Nat.add_assoc]
    have hsum : C + (r - 1) = (C + 1) + (r - 2) := by
      rw [hpred]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right (r - 2) (C + 1) 1)

theorem constant_D_event_map_succ {s C : Nat} (hs : 1 ≤ s)
    (hD : D s = C) :
    d (s + 1) = if (s + 1) % 2 = 0 then Nat.gcd (s + 1) (C - 1)
      else Nat.gcd (s - 1) (C + 1) := by
  have hr : 2 ≤ s + 1 := Nat.succ_le_succ hs
  have hpred : s + 1 - 1 = s := Nat.add_sub_cancel s 1
  have hpred2 : s + 1 - 2 = s - 1 := by
    cases s with
    | zero => simp at hs
    | succ s => simp [Nat.add_assoc]
  simpa [hpred, hpred2] using constant_D_event_map hr (by simpa [hpred] using hD)

theorem constant_D_event_even_proper_iff {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0) :
    d r < C - 1 ↔ ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hqpos : 0 < C - 1 := by
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right r hqpos)
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

theorem constant_D_event_odd_proper_iff {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0) :
    d r < C + 1 ↔ ¬ (C + 1) ∣ r - 2 := by
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right (r - 2) (by simp))
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

theorem three_mul_le_of_odd_dvd_odd_of_proper {x q : Nat}
    (hxodd : x % 2 = 1) (hqodd : q % 2 = 1)
    (hdiv : x ∣ q) (hproper : x < q) :
    3 * x ≤ q := by
  rcases hdiv with ⟨t, ht⟩
  have htodd : t % 2 = 1 := by
    calc
      t % 2 = (x * t) % 2 := quotient_mod_two_of_left_odd hxodd
      _ = q % 2 := by rw [ht]
      _ = 1 := hqodd
  rcases one_or_three_le_of_mod_two_eq_one htodd with ht1 | ht3
  · have heq : q = x := by
      calc
        q = x * t := ht
        _ = x := by rw [ht1]; simp
    have : x < x := by simpa [heq] using hproper
    exact False.elim (Nat.lt_irrefl x this)
  · calc
      3 * x = x * 3 := by simp [Nat.mul_comm]
      _ ≤ x * t := Nat.mul_le_mul_left x ht3
      _ = q := ht.symm

theorem constant_D_event_even_size_bound {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hproper : d r < C - 1) :
    3 * d r ≤ C - 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hCstep : C - 1 + 1 = C :=
    Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
  have hqmod : (C - 1) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdiv : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  exact three_mul_le_of_odd_dvd_odd_of_proper hdmod hqmod hdiv hproper

theorem constant_D_event_odd_size_bound {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0)
    (hproper : d r < C + 1) :
    3 * d r ≤ C + 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hqmod : (C + 1) % 2 = 1 := by simp [Nat.add_mod, hCmod]
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  have hdiv : d r ∣ C + 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  exact three_mul_le_of_odd_dvd_odd_of_proper hdmod hqmod hdiv hproper

theorem constant_D_event_even_not_dvd_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hle : r ≤ C) (hnontriv : 1 < d r) :
    ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hCpos : 0 < C - 1 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdvd : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hdle : d r ≤ C - 1 := Nat.le_of_dvd hCpos hdvd
  have hd2 : 2 ≤ d r := Nat.succ_le_of_lt hnontriv
  have hq2 : 2 ≤ C - 1 := Nat.le_trans hd2 hdle
  have hqodd : (C - 1) % 2 = 1 := by
    have hCstep : C - 1 + 1 = C :=
      Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  intro hdiv
  have hqle : C - 1 ≤ r :=
    Nat.le_of_dvd (Nat.lt_of_lt_of_le (by simp) hr) hdiv
  have hupper : r ≤ (C - 1) + 1 := by
    calc
      r ≤ C := hle
      _ = (C - 1) + 1 :=
        (Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)).symm
  rcases Nat.lt_or_eq_of_le hqle with hlt | heq
  · have hreq : r = (C - 1) + 1 :=
      Nat.le_antisymm hupper (Nat.succ_le_of_lt hlt)
    have hone : C - 1 ∣ 1 := by
      have hsub := Nat.dvd_sub hdiv (Nat.dvd_refl (C - 1))
      rw [hreq] at hsub
      simpa [Nat.add_sub_cancel_left] using hsub
    have hqone : C - 1 = 1 := Nat.eq_one_of_dvd_one hone
    have : (2 : Nat) ≤ 1 := by simpa [hqone] using hq2
    simp at this
  · have hbad : (1 : Nat) = 0 := by
      calc
        1 = (C - 1) % 2 := hqodd.symm
        _ = r % 2 := by rw [heq]
        _ = 0 := heven
    cases hbad

theorem constant_D_event_odd_not_dvd_of_le {r C : Nat} (hr : 3 ≤ r)
    (hle : r ≤ C) :
    ¬ (C + 1) ∣ r - 2 := by
  intro hdiv
  have hr2 : 0 < r - 2 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hr)
  have hqle : C + 1 ≤ r - 2 := Nat.le_of_dvd hr2 hdiv
  have hbad : C + 1 ≤ C :=
    Nat.le_trans hqle (Nat.le_trans (Nat.sub_le r 2) hle)
  exact (Nat.not_succ_le_self C) hbad

theorem constant_D_event_even_size_bound_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hle : r ≤ C) (hnontriv : 1 < d r) :
    3 * d r ≤ C - 1 := by
  apply constant_D_event_even_size_bound hr hD heven
  exact (constant_D_event_even_proper_iff hr hD heven).2
    (constant_D_event_even_not_dvd_of_le hr hD heven hle hnontriv)

theorem constant_D_event_odd_size_bound_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0)
    (hle : r ≤ C) :
    3 * d r ≤ C + 1 := by
  apply constant_D_event_odd_size_bound hr hD hodd
  exact (constant_D_event_odd_proper_iff hr hD hodd).2
    (constant_D_event_odd_not_dvd_of_le hr hle)

theorem constant_D_event_coprime_of_critical_form {delta c r : Nat}
    (hr : 3 ≤ r)
    (hD : D (r - 1) = delta * (c + 2)) :
    Nat.gcd delta (d r) = 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hC2 : 2 ≤ delta * (c + 2) := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hCpos : 1 ≤ delta * (c + 2) := Nat.le_trans (by simp) hC2
  by_cases heven : r % 2 = 0
  · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
    rw [if_pos heven] at hmap
    have hdvd : d r ∣ delta * (c + 2) - 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    let g := Nat.gcd delta (d r)
    have hgdelta : g ∣ delta := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d r := Nat.gcd_dvd_right _ _
    have hgq : g ∣ delta * (c + 2) - 1 := Nat.dvd_trans hgd hdvd
    have hgC : g ∣ delta * (c + 2) :=
      Nat.dvd_mul_right_of_dvd hgdelta (c + 2)
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hgC hgq
      have hdiff : delta * (c + 2) -
          (delta * (c + 2) - 1) = 1 :=
        Nat.sub_sub_self hCpos
      rw [hdiff] at hsub
      exact hsub
    exact Nat.eq_one_of_dvd_one hg1
  · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
    rw [if_neg heven] at hmap
    have hdvd : d r ∣ delta * (c + 2) + 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    let g := Nat.gcd delta (d r)
    have hgdelta : g ∣ delta := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d r := Nat.gcd_dvd_right _ _
    have hgq : g ∣ delta * (c + 2) + 1 := Nat.dvd_trans hgd hdvd
    have hgC : g ∣ delta * (c + 2) :=
      Nat.dvd_mul_right_of_dvd hgdelta (c + 2)
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hgq hgC
      simpa using hsub
    exact Nat.eq_one_of_dvd_one hg1

theorem D_growth_of_nontrivial_chain {start finish s : Nat}
    (hstart : 2 ≤ start) (hchain : HasNontrivialChain start finish s) :
    D start + 2 * s ≤ D finish := by
  induction s generalizing start finish with
  | zero => exact D_le_of_le hchain
  | succ s ih =>
      rcases hchain with ⟨r, hsr, hrf, hdr, htail⟩
      have hstart_r : start ≤ r - 1 :=
        Nat.le_sub_of_add_le (Nat.succ_le_of_lt hsr)
      have hpred : 2 ≤ r - 1 := by
        apply Nat.le_sub_of_add_le
        exact Nat.le_trans (Nat.add_le_add_right hstart 1)
          (Nat.succ_le_of_lt hsr)
      have hr1 : 1 ≤ r :=
        Nat.le_trans (Nat.le_trans (by simp) hpred) (Nat.sub_le r 1)
      have hidx : r - 1 + 1 = r := Nat.sub_add_cancel hr1
      have hdr' : 1 < d ((r - 1) + 1) := by
        rw [hidx]
        exact hdr
      have hstep : D (r - 1) + 2 ≤ D r := by
        simpa [hidx] using D_add_two_le_succ_of_two_le hpred hdr'
      have hstart_step : D start + 2 ≤ D r :=
        Nat.le_trans (Nat.add_le_add_right (D_le_of_le hstart_r) 2) hstep
      have htail_growth : D r + 2 * s ≤ D finish :=
        ih (Nat.le_trans hstart (Nat.le_of_lt hsr)) htail
      calc
        D start + 2 * Nat.succ s = (D start + 2) + 2 * s := by
          simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
        _ ≤ D r + 2 * s := Nat.add_le_add_right hstart_step _
        _ ≤ D finish := htail_growth

theorem D_growth_after_D_step {r C finish s : Nat} (hr : 2 ≤ r)
    (hstep : D r = C + (d r - 1))
    (hchain : HasNontrivialChain r finish s) :
    C + (d r - 1) + 2 * s ≤ D finish := by
  have h := D_growth_of_nontrivial_chain hr hchain
  rw [hstep] at h
  exact h

theorem D_succ_eq_self_iff_d_succ_eq_one (n : Nat) :
    D (n + 1) = D n ↔ d (n + 1) = 1 := by
  constructor
  · intro h
    have h' := D_succ_add_one_eq_add_d n
    rw [h] at h'
    exact (Nat.add_left_cancel h').symm
  · intro h
    have h' := D_succ_add_one_eq_add_d n
    rw [h] at h'
    exact Nat.succ.inj h'

theorem D_lt_succ_of_one_lt_d {n : Nat} (h : 1 < d (n + 1)) :
    D n < D (n + 1) := by
  have hlt : D n + 1 < D n + d (n + 1) := Nat.add_lt_add_left h (D n)
  have hlt' : D n + 1 < D (n + 1) + 1 := by
    calc
      D n + 1 < D n + d (n + 1) := hlt
      _ = D (n + 1) + 1 := (D_succ_add_one_eq_add_d n).symm
  exact Nat.lt_of_succ_lt_succ hlt'

theorem gcd_quotients_eq_one {R c q : Nat} (hRpos : 0 < R)
    (h : Nat.gcd (R * c) (R * q) = R) : Nat.gcd c q = 1 := by
  apply Nat.mul_left_cancel hRpos
  calc
    R * Nat.gcd c q = Nat.gcd (R * c) (R * q) :=
      (Nat.gcd_mul_left R c q).symm
    _ = R := h
    _ = R * 1 := (Nat.mul_one R).symm

theorem occurrence_index_three_le {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R) : 3 ≤ n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  cases k with
  | zero =>
      exfalso
      rw [← hd] at hR
      simpa [d, a] using hR
  | succ k =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.le_add_right 3 k)

theorem pred_mod_two_eq_one_of_even {n : Nat} (hn : 3 ≤ n)
    (heven : n % 2 = 0) : (n - 1) % 2 = 1 := by
  cases n with
  | zero => simp at hn
  | succ n =>
      change n % 2 = 1
      change (n + 1) % 2 = 0 at heven
      rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
      · simp [Nat.add_mod, hn0] at heven
      · exact hn1

theorem pred_mod_two_eq_zero_of_odd {n : Nat} (hn : 3 ≤ n)
    (hodd : n % 2 = 1) : (n - 1) % 2 = 0 := by
  cases n with
  | zero => simp at hn
  | succ n =>
      change n % 2 = 0
      change (n + 1) % 2 = 1 at hodd
      rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
      · exact hn0
      · simp [Nat.add_mod, hn1] at hodd

theorem record_even_occurrence_quotients {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (heven : n % 2 = 0) :
    ∃ c q : Nat, n = R * c ∧ a (n - 1) = R * q ∧ c % 2 = 0 ∧
      q % 2 = 1 ∧ Nat.gcd c q = 1 ∧ 2 ≤ c := by
  rcases record_even_occurrence_structure hR hrec hn hd heven with
    ⟨c, hc, hc0, hc2⟩
  have hdiv : R ∣ a (n - 1) := by
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_pos heven]
    exact Nat.gcd_dvd_right _ _
  rcases hdiv with ⟨q, hq⟩
  have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hnprev : 2 ≤ n - 1 :=
    Nat.le_sub_of_add_le (by simpa using hn3)
  have hprev : (n - 1) % 2 = 1 :=
    pred_mod_two_eq_one_of_even hn3 heven
  have ha_mod : a (n - 1) % 2 = 1 :=
    (a_mod_two_of_two_le hnprev).trans hprev
  have hq1 : q % 2 = 1 := by
    calc
      q % 2 = (R * q) % 2 := quotient_mod_two_of_left_odd hRodd
      _ = a (n - 1) % 2 := by rw [← hq]
      _ = 1 := ha_mod
  have hgd : Nat.gcd (R * c) (R * q) = R := by
    calc
      Nat.gcd (R * c) (R * q) = Nat.gcd n (a (n - 1)) := by
        rw [← hc, ← hq]
      _ = d n := by
        rw [d_eq_if_gcd_of_two_le hn, if_pos heven]
      _ = R := hd
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  exact ⟨c, q, hc, hq, hc0, hq1, gcd_quotients_eq_one hRpos hgd, hc2⟩

theorem record_odd_occurrence_quotients {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (hodd : n % 2 = 1) :
    ∃ c q : Nat, n - 2 = R * c ∧ a (n - 1) = R * q ∧ c % 2 = 1 ∧
      q % 2 = 0 ∧ Nat.gcd c q = 1 ∧ 1 ≤ c ∧ (c = 1 ∨ 3 ≤ c) := by
  rcases record_odd_occurrence_structure hR hrec hn hd hodd with
    ⟨c, hc, hc1, hcpos, hc_cases⟩
  have hne : n % 2 ≠ 0 := by simp [hodd]
  have hdiv : R ∣ a (n - 1) := by
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_neg hne]
    exact Nat.gcd_dvd_right _ _
  rcases hdiv with ⟨q, hq⟩
  have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hnprev : 2 ≤ n - 1 :=
    Nat.le_sub_of_add_le (by simpa using hn3)
  have hprev : (n - 1) % 2 = 0 :=
    pred_mod_two_eq_zero_of_odd hn3 hodd
  have ha_mod : a (n - 1) % 2 = 0 :=
    (a_mod_two_of_two_le hnprev).trans hprev
  have hq0 : q % 2 = 0 := by
    calc
      q % 2 = (R * q) % 2 := quotient_mod_two_of_left_odd hRodd
      _ = a (n - 1) % 2 := by rw [← hq]
      _ = 0 := ha_mod
  have hgd : Nat.gcd (R * c) (R * q) = R := by
    calc
      Nat.gcd (R * c) (R * q) = Nat.gcd (n - 2) (a (n - 1)) := by
        rw [← hc, ← hq]
      _ = d n := by
        rw [d_eq_if_gcd_of_two_le hn, if_neg hne]
      _ = R := hd
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  exact ⟨c, q, hc, hq, hc1, hq0, gcd_quotients_eq_one hRpos hgd, hcpos,
    hc_cases⟩

theorem attained_previous_maximum_quotient_structure {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) (hP5 : 5 < P) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      ((r % 2 = 0 ∧
          ∃ c q : Nat, r = P * c ∧ a (r - 1) = P * q ∧
            c % 2 = 0 ∧ q % 2 = 1 ∧ Nat.gcd c q = 1 ∧ 2 ≤ c) ∨
        (r % 2 = 1 ∧
          ∃ c q : Nat, r - 2 = P * c ∧ a (r - 1) = P * q ∧
            c % 2 = 1 ∧ q % 2 = 0 ∧ Nat.gcd c q = 1 ∧
            1 ≤ c ∧ (c = 1 ∨ 3 ≤ c))) := by
  rcases attained_previous_maximum_record hP with
    ⟨r, hr2, hrk, hdr, hrec⟩
  rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
  · rcases record_even_occurrence_quotients hP5 hrec hr2 hdr hr0 with
      ⟨c, q, hc, hq, hc0, hq1, hcop, hc2⟩
    exact ⟨r, hr2, hrk, hdr, Or.inl ⟨hr0, c, q, hc, hq, hc0, hq1, hcop, hc2⟩⟩
  · rcases record_odd_occurrence_quotients hP5 hrec hr2 hdr hr1 with
      ⟨c, q, hc, hq, hc1, hq0, hcop, hcpos, hcases⟩
    exact ⟨r, hr2, hrk, hdr,
      Or.inr ⟨hr1, c, q, hc, hq, hc1, hq0, hcop, hcpos, hcases⟩⟩

theorem record_late_branch_gcd_reduction {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R)
    (hlate : (n % 2 = 0 ∧ 2 * R ≤ n) ∨
      (n % 2 = 1 ∧ 3 * R + 2 ≤ n)) :
    R + 2 < n ∧ d (R + 2) < R ∧
      d (R + 2) = Nat.gcd R (a (R + 1)) ∧
      Nat.gcd R (a (R + 1)) < R ∧ ¬ R ∣ a (R + 1) := by
  have h2 : 2 < R := Nat.lt_trans (by simp) hR
  have hR2 : R + 2 < 2 * R := by
    simpa [Nat.two_mul] using Nat.add_lt_add_left h2 R
  have hnlate : R + 2 < n := by
    rcases hlate with ⟨_, hbound⟩ | ⟨_, hbound⟩
    · exact Nat.lt_of_lt_of_le hR2 hbound
    · have h23 : 2 * R ≤ 3 * R + 2 := by
        calc
          2 * R ≤ 3 * R := Nat.mul_le_mul_right R (by simp)
          _ ≤ 3 * R + 2 := Nat.le_add_right _ _
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hR2 h23) hbound
  have hk : 2 ≤ R + 2 := by
    simpa [Nat.add_comm] using (Nat.le_add_right 2 R)
  have hlt : d (R + 2) < R := hprior (R + 2) hk hnlate
  have hrec : IsDifferenceRecord R := ⟨n, hn, hd, hprior⟩
  have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
  have hne : (R + 2) % 2 ≠ 0 := by simp [Nat.add_mod, hRodd]
  have hgd : d (R + 2) = Nat.gcd R (a (R + 1)) :=
    d_add_two_of_odd R hne
  have hGlt : Nat.gcd R (a (R + 1)) < R := by
    rw [← hgd]
    exact hlt
  have hnot : ¬ R ∣ a (R + 1) := by
    intro hdiv
    rw [Nat.gcd_eq_left hdiv] at hGlt
    exact Nat.lt_irrefl R hGlt
  exact ⟨hnlate, hlt, hgd, hGlt, hnot⟩

theorem record_index_or_late_gcd_reduction {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R) :
    n = R + 2 ∨
      (R + 2 < n ∧ d (R + 2) < R ∧
        d (R + 2) = Nat.gcd R (a (R + 1)) ∧
        Nat.gcd R (a (R + 1)) < R ∧ ¬ R ∣ a (R + 1)) := by
  have hrec : IsDifferenceRecord R := ⟨n, hn, hd, hprior⟩
  rcases record_index_structure hR hrec hn hd with hmain | hlate
  · exact Or.inl hmain
  · exact Or.inr (record_late_branch_gcd_reduction hR hn hd hprior hlate)

theorem record_index_eq_of_dvd_a_succ {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R)
    (hbridge : R ∣ a (R + 1)) : n = R + 2 := by
  rcases record_index_or_late_gcd_reduction hR hn hd hprior with hmain | hlate
  · exact hmain
  · exact (hlate.2.2.2.2 hbridge).elim

theorem record_index_eq_iff_dvd_a_succ {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R) :
    n = R + 2 ↔ R ∣ a (R + 1) := by
  constructor
  · intro hindex
    have hrec : IsDifferenceRecord R := ⟨n, hn, hd, hprior⟩
    have hRodd : R % 2 = 1 := record_value_mod_two_eq_one hR hrec
    have hne : (R + 2) % 2 ≠ 0 := by simp [Nat.add_mod, hRodd]
    have hgd : d (R + 2) = Nat.gcd R (a (R + 1)) :=
      d_add_two_of_odd R hne
    have hd' : d (R + 2) = R := by simpa [hindex] using hd
    have hg : Nat.gcd R (a (R + 1)) = R := by
      rw [← hgd]
      exact hd'
    simpa only [hg] using (Nat.gcd_dvd_right R (a (R + 1)))
  · exact record_index_eq_of_dvd_a_succ hR hn hd hprior

theorem a_add_d_succ {k : Nat} :
    a k + d (k + 1) = a (k + 1) := by
  have hsub : d (k + 1) = a (k + 1) - a k := by simp [d]
  rw [hsub]
  simpa [Nat.add_comm] using Nat.sub_add_cancel (a_le_succ k)

theorem a_succ_ge_add_one {k : Nat} :
    a k + 1 ≤ a (k + 1) := by
  calc
    a k + 1 ≤ a k + d (k + 1) :=
      Nat.add_le_add_left (one_le_d_succ k) _
    _ = a (k + 1) := a_add_d_succ

theorem a_lower_step {k : Nat} (hk : 2 ≤ k)
    (hbound : 2 * k ≤ a k + 2) :
    2 * (k + 1) ≤ a (k + 1) + 2 := by
  rcases Nat.eq_or_lt_of_le hbound with heq | hlt
  · have hk2 : 2 ≤ 2 * k := by
      exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
    have ha : a k = 2 * k - 2 := by
      exact (Nat.sub_eq_iff_eq_add hk2).2 heq |>.symm
    have ha2 : a k = 2 * (k - 1) := by
      calc
        a k = 2 * k - 2 := ha
        _ = 2 * (k - 1) := by
          rw [Nat.mul_sub_left_distrib]
    have hak0 : a k % 2 = 0 := by
      have hmod := congrArg (fun x : Nat => x % 2) heq
      simpa [Nat.mul_mod, Nat.add_mod] using hmod.symm
    have hk0 : k % 2 = 0 := by
      calc
        k % 2 = a k % 2 := (a_mod_two_of_two_le hk).symm
        _ = 0 := hak0
    have hk3 : 3 ≤ k := by
      have hne2 : ¬ k = 2 := by
        intro hk2eq
        subst k
        simp [a] at heq
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk (by
        intro h
        exact hne2 h.symm))
    have hkminus : 2 ≤ k - 1 :=
      Nat.le_sub_of_add_le (by simpa using hk3)
    have hidx : (k - 1) + 2 = k + 1 := by
      calc
        (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
        _ = k + 1 := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
    have hne : (k + 1) % 2 ≠ 0 := by simp [Nat.add_mod, hk0]
    have hne' : ((k - 1) + 2) % 2 ≠ 0 := by simpa [hidx] using hne
    have hdk : d (k + 1) = k - 1 := by
      calc
        d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
        _ = Nat.gcd (k - 1) (a ((k - 1) + 1)) :=
          d_add_two_of_odd (k - 1) hne'
        _ = Nat.gcd (k - 1) (a k) := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
        _ = k - 1 := by
          rw [ha2]
          simpa using (Nat.gcd_mul_right 1 (k - 1) 2)
    have hd2 : 2 ≤ d (k + 1) := by simpa [hdk] using hkminus
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (a k + 2) + 2 := by rw [heq]
      _ ≤ (a k + d (k + 1)) + 2 := by
        exact Nat.add_le_add_right (Nat.add_le_add_left hd2 (a k)) 2
      _ = a (k + 1) + 2 := by rw [a_add_d_succ]
  · have hnext : 2 * k + 1 ≤ a k + 2 := Nat.succ_le_of_lt hlt
    have hstep : a k + 1 ≤ a (k + 1) := a_succ_ge_add_one
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (2 * k + 1) + 1 := by simp [Nat.add_assoc]
      _ ≤ (a k + 2) + 1 := Nat.add_le_add_right hnext 1
      _ = (a k + 1) + 2 := by simp [Nat.add_assoc, Nat.add_left_comm]
      _ ≤ a (k + 1) + 2 := Nat.add_le_add_right hstep 2

theorem two_mul_le_a_add_two {k : Nat} (hk : 2 ≤ k) :
    2 * k ≤ a k + 2 := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hk
  clear hk
  induction t with
  | zero => simp [a]
  | succ t ih =>
      have ht : 2 ≤ 2 + t := Nat.le_add_right 2 t
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (a_lower_step ht ih)

theorem two_mul_sub_two_le_a {k : Nat} (hk : 2 ≤ k) :
    2 * k - 2 ≤ a k := by
  exact (Nat.sub_le_iff_le_add).2 (two_mul_le_a_add_two hk)

theorem B_add_index_eq_D_add_two {n : Nat} (hn : 2 ≤ n) :
    B n + n = D n + 2 := by
  have hbase : 2 * n - 2 ≤ a n := two_mul_sub_two_le_a hn
  have hBsum : B n + (2 * n - 2) = a n := Nat.sub_add_cancel hbase
  have hDsum : D n + n = a n := Nat.sub_add_cancel (index_le_a n)
  have hsplit : 2 * n - 2 = n + (n - 2) := by
    have hnn : 2 ≤ n + n := Nat.le_trans hn (Nat.le_add_right n n)
    have hnn' : 2 ≤ 2 * n := by simpa only [Nat.two_mul] using hnn
    apply (Nat.sub_eq_iff_eq_add hnn').2
    calc
      2 * n = n + n := by simp [Nat.succ_mul, Nat.add_comm]
      _ = n + ((n - 2) + 2) := by rw [Nat.sub_add_cancel hn]
      _ = n + (n - 2) + 2 := by simp [Nat.add_assoc]
  have hleft : B n + n + (n - 2) = D n + n := by
    calc
      B n + n + (n - 2) = B n + (2 * n - 2) := by
        rw [hsplit]
        simp [Nat.add_assoc]
      _ = a n := hBsum
      _ = D n + n := hDsum.symm
  have hright : D n + n = (D n + 2) + (n - 2) := by
    calc
      D n + n = D n + ((n - 2) + 2) := by rw [Nat.sub_add_cancel hn]
      _ = (D n + 2) + (n - 2) := by simp [Nat.add_assoc, Nat.add_comm]
  apply Nat.add_right_cancel
  calc
    (B n + n) + (n - 2) = D n + n := hleft
    _ = (D n + 2) + (n - 2) := hright

theorem D_eq_self_of_fundamental {m : Nat} (hm : 2 ≤ m)
    (hfund : B m = 2) : D m = m := by
  have h := B_add_index_eq_D_add_two hm
  rw [hfund] at h
  have hcancel : 2 + m = 2 + D m := by
    calc
      2 + m = D m + 2 := h
      _ = 2 + D m := by simp [Nat.add_comm]
  exact (Nat.add_left_cancel hcancel).symm

theorem excess_succ_add_two {k : Nat} (hk : 2 ≤ k) :
    B (k + 1) + 2 = B k + d (k + 1) := by
  simp only [B]
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hnext : 2 * (k + 1) - 2 ≤ a (k + 1) :=
    (Nat.sub_le_iff_le_add).2
      (two_mul_le_a_add_two (Nat.le_trans hk (Nat.le_succ k)))
  have hnext0 : 2 * k ≤ a (k + 1) := by
    simpa [Nat.mul_add] using hnext
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hshift : a (k + 1) - 2 * k + 2 =
      a (k + 1) - (2 * k - 2) := by
    have h := Nat.sub_add_sub_cancel hnext0
      (Nat.sub_le (2 * k) 2)
    simpa [Nat.sub_sub_self hk2] using h
  have hsum : (a k - (2 * k - 2)) + d (k + 1) =
      a (k + 1) - (2 * k - 2) := by
    have h := Nat.sub_add_sub_cancel (a_le_succ k) hbase
    calc
      (a k - (2 * k - 2)) + d (k + 1) =
          d (k + 1) + (a k - (2 * k - 2)) := Nat.add_comm _ _
      _ = (a (k + 1) - a k) + (a k - (2 * k - 2)) := by
        rw [d]
        simp
      _ = a (k + 1) - (2 * k - 2) := h
  calc
    a (k + 1) - (2 * (k + 1) - 2) + 2 =
        a (k + 1) - 2 * k + 2 := by simp [Nat.mul_add]
    _ = a (k + 1) - (2 * k - 2) := hshift
    _ = (a k - (2 * k - 2)) + d (k + 1) := hsum.symm

theorem lower_shift {n : Nat} (hn : 3 ≤ n) :
    2 * (n - 2) ≤ a (n - 1) := by
  have hnprev : 2 ≤ n - 1 :=
    Nat.le_sub_of_add_le (by simpa using hn)
  have h := two_mul_sub_two_le_a hnprev
  simpa [Nat.mul_sub_left_distrib, Nat.sub_sub] using h

theorem B_sub_eq_mul_sub {R n c q : Nat} (hc : n - 2 = R * c)
    (hq : a (n - 1) = R * q) :
    B (n - 1) = R * (q - 2 * c) := by
  have hbase : 2 * (n - 1) - 2 = 2 * (n - 2) := by
    simp [Nat.mul_sub_left_distrib, Nat.sub_sub]
  calc
    B (n - 1) = R * q - 2 * (R * c) := by
      simp only [B, hbase, hq, hc]
    _ = R * q - R * (2 * c) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = R * (q - 2 * c) := (Nat.mul_sub_left_distrib R q (2 * c)).symm

theorem record_odd_occurrence_excess {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (hodd : n % 2 = 1) :
    ∃ c q : Nat, n - 2 = R * c ∧ a (n - 1) = R * q ∧ c % 2 = 1 ∧
      q % 2 = 0 ∧ Nat.gcd c q = 1 ∧ 1 ≤ c ∧ (c = 1 ∨ 3 ≤ c) ∧
      2 * c ≤ q ∧
      (q = 2 * c → c = 1 ∧ n = R + 2) ∧
      (3 ≤ c → 2 * R ≤ B (n - 1)) := by
  rcases record_odd_occurrence_quotients hR hrec hn hd hodd with
    ⟨c, q, hc, hq, hc1, hq0, hgcd, hcpos, hc_cases⟩
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hlow : 2 * (n - 2) ≤ a (n - 1) := lower_shift hn3
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  have hmul : R * (2 * c) ≤ R * q := by
    calc
      R * (2 * c) = 2 * (R * c) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 2 * (n - 2) := by rw [hc]
      _ ≤ a (n - 1) := hlow
      _ = R * q := hq
  have hqbound : 2 * c ≤ q := Nat.le_of_mul_le_mul_left hmul hRpos
  have hgc : Nat.gcd c (2 * c) = c := by
    simpa using (Nat.gcd_mul_right 1 c 2)
  have hqeq : q = 2 * c → c = 1 ∧ n = R + 2 := by
    intro hqe
    have hcop : Nat.gcd c (2 * c) = 1 := by simpa [hqe] using hgcd
    have hc_one : c = 1 := hgc.symm.trans hcop
    refine ⟨hc_one, ?_⟩
    calc
      n = (n - 2) + 2 := (Nat.sub_add_cancel hn).symm
      _ = R * 1 + 2 := by rw [hc, hc_one]
      _ = R + 2 := by simp
  have hclate : 3 ≤ c → 2 * R ≤ B (n - 1) := by
    intro hc3
    have hqneq : ¬ q = 2 * c := by
      intro hqe
      have hcop : Nat.gcd c (2 * c) = 1 := by simpa [hqe] using hgcd
      have hc_one : c = 1 := hgc.symm.trans hcop
      have hc3' : 3 ≤ 1 := by simpa [hc_one] using hc3
      simpa using hc3'
    have hlt : 2 * c < q :=
      Nat.lt_of_le_of_ne hqbound (by
        intro h
        exact hqneq h.symm)
    have hdiff_pos : 0 < q - 2 * c := Nat.sub_pos_of_lt hlt
    have hsubadd : q - 2 * c + 2 * c = q := Nat.sub_add_cancel hqbound
    have hdiff0 : (q - 2 * c) % 2 = 0 := by
      have hmod := congrArg (fun x : Nat => x % 2) hsubadd
      simpa [Nat.add_mod, Nat.mul_mod, hq0] using hmod
    have hdiff2 : 2 ≤ q - 2 * c :=
      two_le_of_pos_of_mod_two_eq_zero hdiff_pos hdiff0
    calc
      2 * R = R * 2 := by simp [Nat.mul_comm]
      _ ≤ R * (q - 2 * c) := Nat.mul_le_mul_left R hdiff2
      _ = B (n - 1) := (B_sub_eq_mul_sub hc hq).symm
  exact ⟨c, q, hc, hq, hc1, hq0, hgcd, hcpos, hc_cases, hqbound, hqeq,
    hclate⟩

theorem record_even_occurrence_excess {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (heven : n % 2 = 0) :
    ∃ c q : Nat, n = R * c ∧ a (n - 1) = R * q ∧ c % 2 = 0 ∧
      q % 2 = 1 ∧ Nat.gcd c q = 1 ∧ 2 ≤ c ∧ 2 * c ≤ q ∧
      B (n - 1) = R * (q - 2 * c) + 4 ∧
      R + 4 ≤ B (n - 1) := by
  rcases record_even_occurrence_quotients hR hrec hn hd heven with
    ⟨c, q, hc, hq, hc0, hq1, hgcd, hc2⟩
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hlow : 2 * (n - 2) ≤ a (n - 1) := lower_shift hn3
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  have hqbound : 2 * c ≤ q := by
    by_cases hbound : 2 * c ≤ q
    · exact hbound
    · have hq_lt : q < 2 * c := Nat.lt_of_not_ge hbound
      have hq_succ : q + 1 ≤ 2 * c := Nat.succ_le_of_lt hq_lt
      have hmul : R * (q + 1) ≤ R * (2 * c) :=
        Nat.mul_le_mul_left R hq_succ
      have hmul' : R * q + R ≤ R * (2 * c) := by
        simpa [Nat.mul_add] using hmul
      have hlow' : R * (2 * c) - 4 ≤ R * q := by
        calc
          R * (2 * c) - 4 = 2 * (n - 2) := by
            rw [hc]
            simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm]
          _ ≤ a (n - 1) := hlow
          _ = R * q := hq
      have hupper : R * (2 * c) ≤ R * q + 4 :=
        (Nat.sub_le_iff_le_add).1 hlow'
      have hRle : R ≤ 4 := by
        apply Nat.le_of_add_le_add_left
        exact Nat.le_trans hmul' hupper
      have hRgt : 4 < R := Nat.lt_trans (by simp) hR
      exact False.elim ((Nat.not_lt_of_ge hRle) hRgt)
  have hq_lt : 2 * c < q := by
    exact Nat.lt_of_le_of_ne hqbound (by
      intro h
      have : (2 * c) % 2 = 1 := by simpa [h] using hq1
      simp [Nat.mul_mod] at this)
  have hq_succ : 2 * c + 1 ≤ q := Nat.succ_le_of_lt hq_lt
  have hmul : R * (2 * c + 1) ≤ R * q :=
    Nat.mul_le_mul_left R hq_succ
  have hbase : 2 * (n - 1) - 2 ≤ a (n - 1) := by
    exact two_mul_sub_two_le_a (Nat.le_sub_of_add_le (by simpa using hn3))
  have hR2 : 2 ≤ R := Nat.le_trans (by simp) (Nat.le_of_lt hR)
  have hc1 : 1 ≤ c := Nat.le_trans (by simp) hc2
  have hRc : R ≤ R * c := by
    calc
      R = R * 1 := (Nat.mul_one R).symm
      _ ≤ R * c := Nat.mul_le_mul_left R hc1
  have hfour : 4 ≤ 2 * (R * c) := by
    calc
      4 = 2 * 2 := by simp
      _ ≤ 2 * R := Nat.mul_le_mul_left 2 hR2
      _ ≤ 2 * (R * c) := Nat.mul_le_mul_left 2 hRc
  have hbase_eq : 2 * (n - 1) - 2 = 2 * (R * c) - 4 := by
    calc
      2 * (n - 1) - 2 = 2 * (n - 2) := by
        simp [Nat.mul_sub_left_distrib, Nat.sub_sub]
      _ = 2 * (R * c - 2) := by rw [hc]
      _ = 2 * (R * c) - 4 := by
        simp [Nat.mul_sub_left_distrib, Nat.mul_comm]
  have hformula : B (n - 1) = R * (q - 2 * c) + 4 := by
    have hdiff : R * q - 2 * (R * c) = R * (q - 2 * c) := by
      calc
        R * q - 2 * (R * c) = R * q - R * (2 * c) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = R * (q - 2 * c) :=
          (Nat.mul_sub_left_distrib R q (2 * c)).symm
    have hqmul : 2 * (R * c) ≤ R * q := by
      calc
        2 * (R * c) = R * (2 * c) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ R * q := Nat.mul_le_mul_left R hqbound
    have hshift : R * q - (2 * (R * c) - 4) =
        (R * q - 2 * (R * c)) + 4 := by
      apply Nat.sub_eq_of_eq_add
      calc
        R * q = (R * q - 2 * (R * c)) + 2 * (R * c) :=
          (Nat.sub_add_cancel hqmul).symm
        _ = (R * q - 2 * (R * c)) + (4 + (2 * (R * c) - 4)) := by
          rw [Nat.add_sub_cancel' hfour]
        _ = ((R * q - 2 * (R * c)) + 4) +
            (2 * (R * c) - 4) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    calc
      B (n - 1) = R * q - (2 * (R * c) - 4) := by
        simp only [B]
        rw [hq, hbase_eq]
      _ = (R * q - 2 * (R * c)) + 4 := hshift
      _ = R * (q - 2 * c) + 4 := by rw [hdiff]
  have hB : R + 4 ≤ B (n - 1) := by
    rw [hformula]
    have hdiffge : 1 ≤ q - 2 * c := by
      exact Nat.le_sub_of_add_le (by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hq_succ)
    have hRdiff : R ≤ R * (q - 2 * c) :=
      by simpa using Nat.mul_le_mul_left R hdiffge
    exact Nat.add_le_add_right hRdiff 4
  exact ⟨c, q, hc, hq, hc0, hq1, hgcd, hc2, hqbound, hformula, hB⟩

theorem excess_le_of_envelope {k M : Nat} (hk : 2 ≤ k)
    (henv : a k + 4 ≤ 2 * k + 2 * M) : B k + 2 ≤ 2 * M := by
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := by
    exact Nat.sub_add_cancel hbase
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hbase4 : (2 * k - 2) + 4 = 2 * k + 2 := by
    calc
      (2 * k - 2) + 4 = (2 * k - 2) + 2 + 2 := by simp [Nat.add_assoc]
      _ = 2 * k + 2 := by rw [Nat.sub_add_cancel hk2]
  have hchain : 2 * k + (B k + 2) ≤ 2 * k + 2 * M := by
    calc
      2 * k + (B k + 2) = B k + (2 * k + 2) := by ac_rfl
      _ = B k + ((2 * k - 2) + 4) := by rw [hbase4]
      _ = (B k + (2 * k - 2)) + 4 := by simp [Nat.add_assoc]
      _ = a k + 4 := by rw [hsum]
      _ ≤ 2 * k + 2 * M := henv
  exact Nat.le_of_add_le_add_left hchain

theorem odd_late_contradicts_envelope {R n M : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (hlate : 3 * R + 2 ≤ n) (hodd : n % 2 = 1) (hM : M < R)
    (henv : a (n - 1) + 4 ≤ 2 * (n - 1) + 2 * M) : False := by
  rcases record_odd_occurrence_excess hR hrec hn hd hodd with
    ⟨c, q, hc, hq, hc1, hq0, hgcd, hcpos, hc_cases, hqbound, hqeq,
      hclate⟩
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  have hlate' : 3 * R ≤ n - 2 := Nat.le_sub_of_add_le hlate
  have hmul : R * 3 ≤ R * c := by
    rw [← hc]
    simpa [Nat.mul_comm] using hlate'
  have hc3 : 3 ≤ c := Nat.le_of_mul_le_mul_left hmul hRpos
  have hB : 2 * R ≤ B (n - 1) := hclate hc3
  have hnprev : 2 ≤ n - 1 :=
    Nat.le_sub_of_add_le (by simpa using hn3)
  have hupper : B (n - 1) + 2 ≤ 2 * M :=
    excess_le_of_envelope hnprev henv
  have hRM : 2 * M ≤ 2 * R :=
    Nat.mul_le_mul_left 2 (Nat.le_of_lt hM)
  have hbad : 2 * R + 2 ≤ 2 * R := by
    calc
      2 * R + 2 ≤ B (n - 1) + 2 := Nat.add_le_add_right hB 2
      _ ≤ 2 * M := hupper
      _ ≤ 2 * R := hRM
  exact False.elim ((Nat.not_lt_of_ge hbad) (by simp))

theorem odd_late_impossible_of_history_envelope {R n : Nat}
    (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R)
    (hlate : 3 * R + 2 ≤ n) (hodd : n % 2 = 1)
    (henv : ∀ k M : Nat,
      (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ M) →
        a k + 4 ≤ 2 * k + 2 * M) : False := by
  have hhist : ∀ j : Nat, 2 ≤ j → j ≤ n - 1 → d j ≤ R - 1 := by
    intro j hj hjlast
    have hn1 : 1 ≤ n := Nat.le_trans (by simp) hn
    have hjlt : j < n := by
      have hjlt' := Nat.lt_succ_of_le hjlast
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hn1] at hjlt'
      exact hjlt'
    have hstep : d j + 1 ≤ R := Nat.succ_le_of_lt (hprior j hj hjlt)
    exact Nat.le_sub_of_add_le hstep
  have hRpos : 0 < R := Nat.lt_trans (Nat.zero_lt_succ 4) hR
  have hM : R - 1 < R := Nat.sub_one_lt (Nat.ne_of_gt hRpos)
  exact odd_late_contradicts_envelope hR ⟨n, hn, hd, hprior⟩ hn hd hlate hodd hM
    (henv (n - 1) (R - 1) hhist)

theorem even_occurrence_contradicts_envelope {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (heven : n % 2 = 0)
    (henv : a n + 4 ≤ 2 * n + 2 * R) : False := by
  rcases record_even_occurrence_excess hR hrec hn hd heven with
    ⟨c, q, hc, hq, hc0, hq1, hgcd, hc2, hqbound, hformula, hB⟩
  have hn3 : 3 ≤ n := occurrence_index_three_le hR hn hd
  have hnprev : 2 ≤ n - 1 :=
    Nat.le_sub_of_add_le (by simpa using hn3)
  have hstep : B n + 2 = B (n - 1) + R := by
    have hstep0 := excess_succ_add_two hnprev
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hn), hd] at hstep0
    exact hstep0
  have hupper : B n + 2 ≤ 2 * R := excess_le_of_envelope hn henv
  have hlow : 2 * R + 4 ≤ B n + 2 := by
    calc
      2 * R + 4 = (R + 4) + R := by
        simp [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ B (n - 1) + R := Nat.add_le_add_right hB R
      _ = B n + 2 := hstep.symm
  have hbad : 2 * R + 4 ≤ 2 * R := Nat.le_trans hlow hupper
  exact False.elim ((Nat.not_lt_of_ge hbad) (by simp))

theorem even_occurrence_impossible_of_history_envelope {R n : Nat}
    (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R)
    (heven : n % 2 = 0)
    (henv : ∀ k M : Nat,
      (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ M) →
        a k + 4 ≤ 2 * k + 2 * M) : False := by
  have hhist : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ R := by
    intro j hj hjn
    rcases Nat.eq_or_lt_of_le hjn with hjeq | hjlt
    · simpa [hjeq, hd]
    · exact Nat.le_of_lt (hprior j hj hjlt)
  exact even_occurrence_contradicts_envelope hR ⟨n, hn, hd, hprior⟩ hn hd heven
    (henv n R hhist)

theorem record_index_eq_of_history_envelope {R n : Nat} (hR : 5 < R)
    (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ k : Nat, 2 ≤ k → k < n → d k < R)
    (henv : ∀ k M : Nat,
      (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ M) →
        a k + 4 ≤ 2 * k + 2 * M) : n = R + 2 := by
  have hrec : IsDifferenceRecord R := ⟨n, hn, hd, hprior⟩
  rcases record_index_structure hR hrec hn hd with hmain | hlate
  · exact hmain
  · rcases hlate with hlate | hlate
    · exact False.elim (even_occurrence_impossible_of_history_envelope hR hn hd
        hprior hlate.1 henv)
    · exact False.elim (odd_late_impossible_of_history_envelope hR hn hd hprior
        hlate.2 hlate.1 henv)

theorem base_eq_two_mul_pred (k : Nat) :
    2 * k - 2 = 2 * (k - 1) := by
  rw [Nat.mul_sub_left_distrib]

theorem B_mod_two_of_two_le {k : Nat} (hk : 2 ≤ k) :
    B k % 2 = k % 2 := by
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := Nat.sub_add_cancel hbase
  have hbase_mod : (2 * k - 2) % 2 = 0 := by
    rw [base_eq_two_mul_pred k]
    simp [Nat.mul_mod]
  calc
    B k % 2 = (B k + (2 * k - 2)) % 2 := by
      rw [Nat.add_mod, hbase_mod]
      simp
    _ = a k % 2 := by rw [hsum]
    _ = k % 2 := a_mod_two_of_two_le hk

theorem d_succ_eq_gcd_even_residual {k : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) :
    d (k + 1) = Nat.gcd (k - 1) (B k) := by
  have hidx : (k - 1) + 2 = k + 1 := by
    calc
      (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
      _ = k + 1 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hprev : (k - 1) + 1 = k := by
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hne : (k + 1) % 2 ≠ 0 := by
    simp [Nat.add_mod, hk0]
  have hne' : ((k - 1) + 2) % 2 ≠ 0 := by
    simpa [hidx] using hne
  have hsum : B k + (2 * k - 2) = a k :=
    Nat.sub_add_cancel (two_mul_sub_two_le_a hk)
  have ha : a k = B k + 2 * (k - 1) := by
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = B k + 2 * (k - 1) := by rw [base_eq_two_mul_pred k]
  calc
    d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
    _ = Nat.gcd (k - 1) (a ((k - 1) + 1)) :=
      d_add_two_of_odd (k - 1) hne'
    _ = Nat.gcd (k - 1) (a k) := by rw [hprev]
    _ = Nat.gcd (k - 1) (B k + 2 * (k - 1)) := by rw [ha]
    _ = Nat.gcd (k - 1) (B k) := by
      simpa using (Nat.gcd_add_mul_right_right (k - 1) (B k) 2)

theorem d_succ_eq_gcd_odd_residual {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : 4 ≤ B k) :
    d (k + 1) = Nat.gcd (k + 1) (B k - 4) := by
  have hidx : (k - 1) + 2 = k + 1 := by
    calc
      (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
      _ = k + 1 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hprev : (k - 1) + 1 = k := by
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have heven : (k + 1) % 2 = 0 := by
    simp [Nat.add_mod, hk1]
  have heven' : ((k - 1) + 2) % 2 = 0 := by
    simpa [hidx] using heven
  have hsum : B k + (2 * k - 2) = a k :=
    Nat.sub_add_cancel (two_mul_sub_two_le_a hk)
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hbase4 : (2 * k - 2) + 4 = 2 * k + 2 := by
    calc
      (2 * k - 2) + 4 = (2 * k - 2) + 2 + 2 := by simp [Nat.add_assoc]
      _ = 2 * k + 2 := by rw [Nat.sub_add_cancel hk2]
  have ha : a k = (B k - 4) + 2 * (k + 1) := by
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = ((B k - 4) + 4) + (2 * k - 2) := by
        rw [Nat.sub_add_cancel hB]
      _ = (B k - 4) + ((2 * k - 2) + 4) := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (B k - 4) + (2 * k + 2) := by rw [hbase4]
      _ = (B k - 4) + 2 * (k + 1) := by simp [Nat.mul_add]
  calc
    d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
    _ = Nat.gcd ((k - 1) + 2) (a ((k - 1) + 1)) :=
      d_add_two_of_even (k - 1) heven'
    _ = Nat.gcd (k + 1) (a k) := by rw [hidx, hprev]
    _ = Nat.gcd (k + 1) ((B k - 4) + 2 * (k + 1)) := by rw [ha]
    _ = Nat.gcd (k + 1) (B k - 4) := by
      simpa using (Nat.gcd_add_mul_right_right (k + 1) (B k - 4) 2)

theorem even_residual_structure {k : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) :
    ∃ t : Nat, B k = d (k + 1) * t ∧ t % 2 = 0 ∧
      (B k = 0 ∨ 2 * d (k + 1) ≤ B k) := by
  have hidentity := d_succ_eq_gcd_even_residual hk hk0
  have hdvd : d (k + 1) ∣ B k := by
    rw [hidentity]
    exact Nat.gcd_dvd_right _ _
  rcases hdvd with ⟨t, ht⟩
  have hk3 : 3 ≤ k + 1 := by
    simpa using Nat.add_le_add_right hk 1
  have hdodd : d (k + 1) % 2 = 1 :=
    d_mod_two_eq_one_of_three_le hk3
  have htmod : t % 2 = 0 := by
    calc
      t % 2 = (d (k + 1) * t) % 2 :=
        quotient_mod_two_of_left_odd hdodd
      _ = B k % 2 := by rw [ht]
      _ = k % 2 := B_mod_two_of_two_le hk
      _ = 0 := hk0
  by_cases hzero : B k = 0
  · exact ⟨t, ht, htmod, Or.inl hzero⟩
  · refine ⟨t, ht, htmod, Or.inr ?_⟩
    have htne : t ≠ 0 := by
      intro ht0
      apply hzero
      simpa [ht0] using ht
    have htpos : 0 < t := Nat.pos_of_ne_zero htne
    have ht2 : 2 ≤ t := two_le_of_pos_of_mod_two_eq_zero htpos htmod
    calc
      2 * d (k + 1) = d (k + 1) * 2 := by simp [Nat.mul_comm]
      _ ≤ d (k + 1) * t := Nat.mul_le_mul_left _ ht2
      _ = B k := ht.symm

theorem odd_residual_structure {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : 4 ≤ B k) :
    ∃ t : Nat, B k - 4 = d (k + 1) * t ∧ t % 2 = 1 ∧
      d (k + 1) + 4 ≤ B k := by
  have hidentity := d_succ_eq_gcd_odd_residual hk hk1 hB
  have hdvd : d (k + 1) ∣ B k - 4 := by
    rw [hidentity]
    exact Nat.gcd_dvd_right _ _
  rcases hdvd with ⟨t, ht⟩
  have hresmod : (B k - 4) % 2 = 1 := by
    calc
      (B k - 4) % 2 = ((B k - 4) + 4) % 2 := by
        rw [Nat.add_mod]
        simp
      _ = B k % 2 := by rw [Nat.sub_add_cancel hB]
      _ = k % 2 := B_mod_two_of_two_le hk
      _ = 1 := hk1
  have hk3 : 3 ≤ k + 1 := by
    simpa using Nat.add_le_add_right hk 1
  have hdodd : d (k + 1) % 2 = 1 :=
    d_mod_two_eq_one_of_three_le hk3
  have htmod : t % 2 = 1 := by
    calc
      t % 2 = (d (k + 1) * t) % 2 :=
        quotient_mod_two_of_left_odd hdodd
      _ = (B k - 4) % 2 := by rw [ht]
      _ = 1 := hresmod
  have htpos : 0 < t := by
    cases t with
    | zero => simp at htmod
    | succ t => exact Nat.zero_lt_succ t
  have ht1 : 1 ≤ t := htpos
  refine ⟨t, ht, htmod, ?_⟩
  calc
    d (k + 1) + 4 ≤ d (k + 1) * t + 4 := by
      have hmul : d (k + 1) * 1 ≤ d (k + 1) * t :=
        Nat.mul_le_mul_left _ ht1
      simpa using Nat.add_le_add_right hmul 4
    _ = (B k - 4) + 4 := by rw [ht]
    _ = B k := Nat.sub_add_cancel hB

theorem d_succ_eq_gcd_small_residual {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : B k ≤ 4) :
    d (k + 1) = Nat.gcd (k + 1) (4 - B k) := by
  have hidx : (k - 1) + 2 = k + 1 := by
    calc
      (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
      _ = k + 1 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hprev : (k - 1) + 1 = k := by
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have heven : (k + 1) % 2 = 0 := by
    simp [Nat.add_mod, hk1]
  have heven' : ((k - 1) + 2) % 2 = 0 := by
    simpa [hidx] using heven
  have hsum : B k + (2 * k - 2) = a k :=
    Nat.sub_add_cancel (two_mul_sub_two_le_a hk)
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hbase4 : (2 * k - 2) + 4 = 2 * k + 2 := by
    calc
      (2 * k - 2) + 4 = (2 * k - 2) + 2 + 2 := by simp [Nat.add_assoc]
      _ = 2 * k + 2 := by rw [Nat.sub_add_cancel hk2]
  have hBsum : B k + (4 - B k) = 4 := Nat.add_sub_cancel' hB
  have ha : a k + (4 - B k) = 2 * (k + 1) := by
    calc
      a k + (4 - B k) = (B k + (2 * k - 2)) + (4 - B k) := by
        rw [hsum]
      _ = (2 * k - 2) + (B k + (4 - B k)) := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (2 * k - 2) + 4 := by rw [hBsum]
      _ = 2 * k + 2 := hbase4
      _ = 2 * (k + 1) := by simp [Nat.mul_add]
  have hkplus : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hfour : 4 ≤ 2 * (k + 1) := by
    calc
      4 = 2 * 2 := by simp
      _ ≤ 2 * (k + 1) := Nat.mul_le_mul_left 2 hkplus
  have hrespos : 4 - B k ≤ 2 * (k + 1) :=
    Nat.le_trans (Nat.sub_le _ _) hfour
  have hasub : a k = 2 * (k + 1) - (4 - B k) := by
    exact (Nat.sub_eq_iff_eq_add hrespos).2 ha.symm |>.symm
  calc
    d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
    _ = Nat.gcd ((k - 1) + 2) (a ((k - 1) + 1)) :=
      d_add_two_of_even (k - 1) heven'
    _ = Nat.gcd (k + 1) (a k) := by rw [hidx, hprev]
    _ = Nat.gcd (k + 1) (2 * (k + 1) - (4 - B k)) := by rw [hasub]
    _ = Nat.gcd (k + 1) (4 - B k) := by
      have hmul : 4 - B k ≤ (k + 1) * 2 := by
        simpa [Nat.mul_comm] using hrespos
      simpa [Nat.mul_comm] using (Nat.gcd_mul_left_sub_right (m := k + 1)
        (n := 4 - B k) (k := 2) hmul)

theorem odd_small_residual_classification {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : B k < 4) :
    (B k = 1 ∧ (d (k + 1) = 1 ∨ d (k + 1) = 3)) ∨
      (B k = 3 ∧ d (k + 1) = 1) := by
  have hBmod : B k % 2 = 1 := by
    calc
      B k % 2 = k % 2 := B_mod_two_of_two_le hk
      _ = 1 := hk1
  rcases one_or_three_le_of_mod_two_eq_one hBmod with hB1 | hB3
  · left
    refine ⟨hB1, ?_⟩
    have hd : d (k + 1) = Nat.gcd (k + 1) 3 := by
      calc
        d (k + 1) = Nat.gcd (k + 1) (4 - B k) :=
          d_succ_eq_gcd_small_residual hk hk1 (Nat.le_of_lt hB)
        _ = Nat.gcd (k + 1) 3 := by rw [hB1]
    have hdiv : d (k + 1) ∣ 3 := by
      rw [hd]
      exact Nat.gcd_dvd_right _ _
    have hle : d (k + 1) ≤ 3 := Nat.le_of_dvd (by simp) hdiv
    rcases one_or_three_le_of_mod_two_eq_one
      (d_mod_two_eq_one_of_three_le (Nat.succ_le_succ hk)) with
      hd1 | hd3
    · exact Or.inl hd1
    · exact Or.inr (Nat.le_antisymm hle hd3)
  · right
    refine ⟨?_, ?_⟩
    · exact Nat.le_antisymm (Nat.le_of_lt_succ hB) hB3
    calc
      d (k + 1) = Nat.gcd (k + 1) (4 - B k) :=
        d_succ_eq_gcd_small_residual hk hk1 (Nat.le_of_lt hB)
      _ = 1 := by
        rw [Nat.le_antisymm (Nat.le_of_lt_succ hB) hB3]
        simp

theorem odd_small_high_state {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : B k < 4) (hhigh : 2 < d (k + 1)) :
    B k = 1 ∧ d (k + 1) = 3 := by
  rcases odd_small_residual_classification hk hk1 hB with
    ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
  · simp [hd1] at hhigh
  · exact ⟨hB1, hd3⟩
  · simp [hd1] at hhigh

theorem B_eq_two_iff_a_eq_two_mul {k : Nat} (hk : 2 ≤ k) :
    B k = 2 ↔ a k = 2 * k := by
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := Nat.sub_add_cancel hbase
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  constructor
  · intro hB
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = 2 + (2 * k - 2) := by rw [hB]
      _ = (2 * k - 2) + 2 := by simp [Nat.add_comm]
      _ = 2 * k := Nat.sub_add_cancel hk2
  · intro ha
    change a k - (2 * k - 2) = 2
    rw [ha]
    have hbase' : 2 * k - 2 ≤ 2 * k := Nat.sub_le _ _
    apply (Nat.sub_eq_iff_eq_add hbase').2
    calc
      2 * k = (2 * k - 2) + 2 := (Nat.sub_add_cancel hk2).symm
      _ = 2 + (2 * k - 2) := by simp [Nat.add_comm]

theorem envelope_failure_to_excess {k M : Nat} (hk : 2 ≤ k)
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * M) :
    2 * M < B k + d (k + 1) := by
  have h := Nat.lt_of_not_ge hfail
  rw [excess_succ_add_two hk] at h
  exact h

theorem existing_max_even_failure {k M : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) (hIH : B k + 2 ≤ 2 * M)
    (hmax : d (k + 1) ≤ M)
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * M) :
    ∃ t : Nat, B k = d (k + 1) * t ∧ t % 2 = 0 ∧ 2 ≤ t ∧
      B k + 2 ≤ 2 * M ∧ 2 * M < B k + d (k + 1) := by
  have hfail' := envelope_failure_to_excess hk hfail
  rcases even_residual_structure hk hk0 with
    ⟨t, ht, htmod, hzero | hbound⟩
  · have hstep : B k + d (k + 1) ≤ 2 * M := by
      calc
        B k + d (k + 1) = d (k + 1) := by rw [hzero]; simp
        _ ≤ M := hmax
        _ ≤ 2 * M := by simpa [Nat.two_mul] using Nat.le_add_right M M
    exact False.elim ((Nat.not_lt_of_ge hstep) hfail')
  · have hBzero : B k ≠ 0 := by
      intro hzero
      have hstep : B k + d (k + 1) ≤ 2 * M := by
        calc
          B k + d (k + 1) = d (k + 1) := by rw [hzero]; simp
          _ ≤ M := hmax
          _ ≤ 2 * M := by simpa [Nat.two_mul] using Nat.le_add_right M M
      exact (Nat.not_lt_of_ge hstep) hfail'
    have htne : t ≠ 0 := by
      intro ht0
      apply hBzero
      rw [ht, ht0]
      simp
    have htpos : 0 < t := Nat.pos_of_ne_zero htne
    have ht2 : 2 ≤ t := two_le_of_pos_of_mod_two_eq_zero htpos htmod
    exact ⟨t, ht, htmod, ht2, hIH, hfail'⟩

theorem existing_max_odd_failure {k M : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hIH : B k + 2 ≤ 2 * M)
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * M) :
    ∃ t : Nat, B k - 4 = d (k + 1) * t ∧ t % 2 = 1 ∧
      B k + 2 ≤ 2 * M ∧ 2 * M < B k + d (k + 1) := by
  have hfail' := envelope_failure_to_excess hk hfail
  by_cases hB4 : 4 ≤ B k
  · rcases odd_residual_structure hk hk1 hB4 with
      ⟨t, ht, htmod, hlower⟩
    exact ⟨t, ht, htmod, hIH, hfail'⟩
  · have hBsmall : B k < 4 := Nat.lt_of_not_ge hB4
    rcases odd_small_residual_classification hk hk1 hBsmall with
      ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
    · have hstep : B k + d (k + 1) ≤ 2 * M := by
        calc
          B k + d (k + 1) = 2 := by simp [hB1, hd1]
          _ ≤ B k + 2 := by simp [hB1]
          _ ≤ 2 * M := hIH
      exact False.elim ((Nat.not_lt_of_ge hstep) hfail')
    · have hM2 : 2 ≤ M := by
        have hIH' : 3 ≤ 2 * M := by simpa [hB1] using hIH
        cases M with
        | zero => simp at hIH'
        | succ M =>
          cases M with
          | zero => simp at hIH'
          | succ M => simp
      have hstep : B k + d (k + 1) ≤ 2 * M := by
        calc
          B k + d (k + 1) = 4 := by simp [hB1, hd3]
          _ = 2 * 2 := by simp
          _ ≤ 2 * M := Nat.mul_le_mul_left 2 hM2
      exact False.elim ((Nat.not_lt_of_ge hstep) hfail')
    · have hstep : B k + d (k + 1) ≤ 2 * M := by
        calc
          B k + d (k + 1) = 4 := by simp [hB3, hd1]
          _ ≤ B k + 2 := by simp [hB3]
          _ ≤ 2 * M := hIH
      exact False.elim ((Nat.not_lt_of_ge hstep) hfail')

theorem existing_max_failure_reduction {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hmax : d (k + 1) ≤ M)
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * M) :
    (k % 2 = 0 ∧
      ∃ t : Nat, B k = d (k + 1) * t ∧ t % 2 = 0 ∧ 2 ≤ t ∧
        B k + 2 ≤ 2 * M ∧ 2 * M < B k + d (k + 1)) ∨
    (k % 2 = 1 ∧
      ∃ t : Nat, B k - 4 = d (k + 1) * t ∧ t % 2 = 1 ∧
        B k + 2 ≤ 2 * M ∧ 2 * M < B k + d (k + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · exact Or.inl ⟨hk0,
      existing_max_even_failure hk hk0 hIH hmax hfail⟩
  · exact Or.inr ⟨hk1,
      existing_max_odd_failure hk hk1 hIH hfail⟩

theorem new_max_even_step {k M : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) (hIH : B k + 2 ≤ 2 * M)
    (hnew : M < d (k + 1)) :
    B (k + 1) + 2 ≤ 2 * d (k + 1) := by
  rcases even_residual_structure hk hk0 with
    ⟨t, ht, htmod, hzero | hbound⟩
  · have hstep := excess_succ_add_two hk
    calc
      B (k + 1) + 2 = B k + d (k + 1) := hstep
      _ = d (k + 1) := by rw [hzero]; simp
      _ ≤ 2 * d (k + 1) := by
        simpa [Nat.two_mul] using Nat.le_add_right (d (k + 1)) (d (k + 1))
  · have hchain : 2 * d (k + 1) + 2 ≤ 2 * M := by
      calc
        2 * d (k + 1) + 2 ≤ B k + 2 := Nat.add_le_add_right hbound 2
        _ ≤ 2 * M := hIH
    have hbad : 2 * d (k + 1) ≤ 2 * M :=
      Nat.le_trans (Nat.le_add_right _ _) hchain
    have hlt : 2 * M < 2 * d (k + 1) :=
      (Nat.mul_lt_mul_left (by simp : 0 < 2)).2 hnew
    exact False.elim ((Nat.not_lt_of_ge hbad) hlt)

theorem new_max_odd_failure_reduction {k M : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hIH : B k + 2 ≤ 2 * M)
    (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    4 ≤ B k ∧ B k = d (k + 1) + 4 ∧
      B (k + 1) + 2 = 2 * d (k + 1) + 4 ∧
      d (k + 1) + 6 ≤ 2 * M := by
  have hfail' : 2 * d (k + 1) < B k + d (k + 1) := by
    have h := Nat.lt_of_not_ge hfail
    rw [excess_succ_add_two hk] at h
    exact h
  by_cases hB4 : 4 ≤ B k
  · rcases odd_residual_structure hk hk1 hB4 with
      ⟨t, ht, htmod, hlower⟩
    rcases one_or_three_le_of_mod_two_eq_one htmod with ht1 | ht3
    · have hBeq : B k = d (k + 1) + 4 := by
        calc
          B k = (B k - 4) + 4 := (Nat.sub_add_cancel hB4).symm
          _ = d (k + 1) * t + 4 := by rw [ht]
          _ = d (k + 1) + 4 := by rw [ht1]; simp
      have hnext : B (k + 1) + 2 = 2 * d (k + 1) + 4 := by
        calc
          B (k + 1) + 2 = B k + d (k + 1) := excess_succ_add_two hk
          _ = 2 * d (k + 1) + 4 := by
            rw [hBeq]
            simp [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hIH' : d (k + 1) + 6 ≤ 2 * M := by
        calc
          d (k + 1) + 6 = B k + 2 := by rw [hBeq]
          _ ≤ 2 * M := hIH
      exact ⟨hB4, hBeq, hnext, hIH'⟩
    · have hmul : 3 * d (k + 1) ≤ d (k + 1) * t :=
        by simpa [Nat.mul_comm] using
          (Nat.mul_le_mul_left (d (k + 1)) ht3)
      have hBplus : B k + 2 = (B k - 4) + 6 := by
        rw [← Nat.sub_add_cancel hB4]
        simp [Nat.add_assoc]
      have hbig : 3 * d (k + 1) + 6 ≤ B k + 2 := by
        calc
          3 * d (k + 1) + 6 ≤ d (k + 1) * t + 6 :=
            Nat.add_le_add_right hmul 6
          _ = (B k - 4) + 6 := by rw [ht]
          _ = B k + 2 := hBplus.symm
      have hchain : 3 * d (k + 1) ≤ 2 * M := by
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hbig hIH)
      have hlt : 2 * M < 2 * d (k + 1) :=
        (Nat.mul_lt_mul_left (by simp : 0 < 2)).2 hnew
      have hge : 2 * d (k + 1) ≤ 3 * d (k + 1) := by
        simpa [Nat.mul_comm] using
          (Nat.mul_le_mul_right (d (k + 1)) (by simp : 2 ≤ 3))
      exact False.elim ((Nat.not_lt_of_ge hge)
        (Nat.lt_of_le_of_lt hchain hlt))
  · have hBsmall : B k < 4 := Nat.lt_of_not_ge hB4
    rcases odd_small_residual_classification hk hk1 hBsmall with
      ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
    · have hM0 : M = 0 := by
        have : M < 1 := by simpa [hd1] using hnew
        simpa using this
      simp [hB1, hd1, hM0] at hIH
    · simp [hB1, hd3] at hfail'
    · have hM0 : M = 0 := by
        have : M < 1 := by simpa [hd1] using hnew
        simpa using this
      simp [hB3, hd1, hM0] at hIH

theorem new_max_failure_reduction {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    k % 2 = 1 ∧ 4 ≤ B k ∧ B k = d (k + 1) + 4 ∧
      B (k + 1) + 2 = 2 * d (k + 1) + 4 ∧
      d (k + 1) + 6 ≤ 2 * M := by
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · exact False.elim (hfail (new_max_even_step hk hk0 hIH hnew))
  · exact ⟨hk1, new_max_odd_failure_reduction hk hk1 hIH hnew hfail⟩

theorem new_max_failure_next_B_eq {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    B (k + 1) = 2 * d (k + 1) + 2 := by
  have hstate := new_max_failure_reduction hk hIH hnew hfail
  have hnext : B (k + 1) + 2 = 2 * d (k + 1) + 4 := hstate.2.2.2.1
  have hcancel : B (k + 1) + 2 = (2 * d (k + 1) + 2) + 2 := by
    calc
      B (k + 1) + 2 = 2 * d (k + 1) + 4 := hnext
      _ = (2 * d (k + 1) + 2) + 2 := by simp [Nat.add_assoc]
  exact Nat.add_right_cancel hcancel

theorem critical_new_increment_lower_bound {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    9 ≤ d (k + 1) := by
  have hstate := new_max_failure_reduction hk hIH hnew hfail
  have hbound : d (k + 1) + 6 ≤ 2 * M := hstate.2.2.2.2
  have hM : M + 1 ≤ d (k + 1) := Nat.succ_le_of_lt hnew
  have h2M : 2 * M + 2 ≤ 2 * d (k + 1) := by
    calc
      2 * M + 2 = 2 * (M + 1) := by simp [Nat.mul_succ]
      _ ≤ 2 * d (k + 1) := Nat.mul_le_mul_left 2 hM
  have h8 : 8 ≤ d (k + 1) := by
    have h : d (k + 1) + 8 ≤ 2 * d (k + 1) := by
      calc
        d (k + 1) + 8 = d (k + 1) + 6 + 2 := by simp [Nat.add_assoc]
        _ ≤ 2 * M + 2 := Nat.add_le_add_right hbound 2
        _ ≤ 2 * d (k + 1) := h2M
    have h' : d (k + 1) + 8 ≤ d (k + 1) + d (k + 1) := by
      simpa [Nat.two_mul] using h
    exact Nat.le_of_add_le_add_left h'
  have hdodd : d (k + 1) % 2 = 1 :=
    d_mod_two_eq_one_of_three_le (Nat.succ_le_succ hk)
  have hne : ¬ d (k + 1) = 8 := by
    intro heq
    rw [heq] at hdodd
    simp at hdodd
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h8 (fun h => hne h.symm))

theorem critical_even_quotient_normal_form {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∃ c : Nat, k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      a k = d (k + 1) * (2 * c + 1) ∧
      D (k + 1) = d (k + 1) * (c + 2) ∧
      (2 * c + 1) % 2 = 1 ∧ Nat.gcd c (2 * c + 1) = 1 := by
  have hstate := new_max_failure_reduction hk hIH hnew hfail
  have hk1 : k % 2 = 1 := hstate.1
  have hB4 : 4 ≤ B k := hstate.2.1
  have hB : B k = d (k + 1) + 4 := hstate.2.2.1
  have hn2 : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have heven : (k + 1) % 2 = 0 := by
    simp [Nat.add_mod, hk1]
  have hdiv : d (k + 1) ∣ k + 1 := by
    rw [d_succ_eq_gcd_odd_residual hk hk1 hB4, hB]
    simp only [Nat.add_sub_cancel]
    exact Nat.gcd_dvd_left _ _
  rcases hdiv with ⟨c, hc⟩
  have hdeltaodd : d (k + 1) % 2 = 1 :=
    d_mod_two_eq_one_of_three_le (Nat.succ_le_succ hk)
  have hcmod : c % 2 = 0 := by
    calc
      c % 2 = (d (k + 1) * c) % 2 :=
        quotient_mod_two_of_left_odd hdeltaodd
      _ = (k + 1) % 2 := (congrArg (fun x : Nat => x % 2) hc).symm
      _ = 0 := heven
  have hcpos : 0 < c := by
    cases c with
    | zero =>
        have hbad := hn2
        rw [hc] at hbad
        simp at hbad
    | succ c => exact Nat.zero_lt_succ c
  have hc2 : 2 ≤ c := two_le_of_pos_of_mod_two_eq_zero hcpos hcmod
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := Nat.sub_add_cancel hbase
  have hbase4 : (2 * k - 2) + 4 = 2 * (k + 1) := by
    calc
      (2 * k - 2) + 4 = (2 * k - 2) + 2 + 2 := by simp [Nat.add_assoc]
      _ = 2 * k + 2 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk))]
      _ = 2 * (k + 1) := by simp [Nat.mul_add]
  have ha : a k = d (k + 1) * (2 * c + 1) := by
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = (d (k + 1) + 4) + (2 * k - 2) := by rw [hB]
      _ = d (k + 1) + ((2 * k - 2) + 4) := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = d (k + 1) + 2 * (k + 1) := by rw [hbase4]
      _ = d (k + 1) + 2 * (d (k + 1) * c) := by
        exact congrArg (fun x : Nat => d (k + 1) + 2 * x) hc
      _ = d (k + 1) * (2 * c + 1) := by
        calc
          d (k + 1) + 2 * (d (k + 1) * c) =
              d (k + 1) + d (k + 1) * (2 * c) := by
            congr 1
            calc
              2 * (d (k + 1) * c) = (2 * d (k + 1)) * c :=
                (Nat.mul_assoc 2 (d (k + 1)) c).symm
              _ = (d (k + 1) * 2) * c := by rw [Nat.mul_comm 2]
              _ = d (k + 1) * (2 * c) := Nat.mul_assoc _ _ _
          _ = d (k + 1) * 1 + d (k + 1) * (2 * c) := by simp
          _ = d (k + 1) * (1 + 2 * c) := by rw [Nat.mul_add]
          _ = d (k + 1) * (2 * c + 1) :=
            congrArg (fun x : Nat => d (k + 1) * x) (Nat.add_comm 1 (2 * c))
  have hBnext := new_max_failure_next_B_eq hk hIH hnew hfail
  have hrel := B_add_index_eq_D_add_two hn2
  have hD : D (k + 1) = d (k + 1) * (c + 2) := by
    have hcancel : D (k + 1) + 2 = d (k + 1) * (c + 2) + 2 := by
      calc
        D (k + 1) + 2 = B (k + 1) + (k + 1) := hrel.symm
        _ = (2 * d (k + 1) + 2) + (k + 1) := by rw [hBnext]
        _ = (2 * d (k + 1) + 2) + d (k + 1) * c := by
          exact congrArg (fun x : Nat => (2 * d (k + 1) + 2) + x) hc
        _ = d (k + 1) * (c + 2) + 2 := by
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
    exact Nat.add_right_cancel hcancel
  have hdn : d (k + 1) = Nat.gcd (k + 1) (a k) := by
    rw [d_eq_if_gcd_of_two_le hn2, if_pos heven]
    simp
  have hgd : Nat.gcd (d (k + 1) * c) (d (k + 1) * (2 * c + 1)) = d (k + 1) := by
    calc
      Nat.gcd (d (k + 1) * c) (d (k + 1) * (2 * c + 1)) =
          Nat.gcd (k + 1) (a k) := by rw [← hc, ← ha]
      _ = d (k + 1) := hdn.symm
  have hcop : Nat.gcd c (2 * c + 1) = 1 :=
    gcd_quotients_eq_one (d_pos_of_two_le hn2) hgd
  exact ⟨c, hc, hcmod, hc2, ha, hD, by simp [Nat.add_mod], hcop⟩

theorem critical_initial_slack {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    k + 1 + 2 * d (k + 1) = D (k + 1) := by
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, _, _, _, hD, _, _⟩
  have hkc : k + 1 + 2 * d (k + 1) =
      d (k + 1) * c + 2 * d (k + 1) :=
    congrArg (fun x : Nat => x + 2 * d (k + 1)) hc
  calc
    k + 1 + 2 * d (k + 1) = d (k + 1) * c + 2 * d (k + 1) := hkc
    _ = d (k + 1) * (c + 2) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_assoc]
    _ = D (k + 1) := hD.symm

theorem critical_failure_impossible_of_separation {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hsep : 2 * P ≤ d (k + 1) + 1) : False := by
  have hstate := new_max_failure_reduction hk hIH hnew hfail
  have hlow : d (k + 1) + 6 ≤ 2 * P := hstate.2.2.2.2
  have hbad : d (k + 1) + 2 ≤ d (k + 1) + 1 := by
    exact Nat.le_trans (by simp [Nat.add_assoc]) (Nat.le_trans hlow hsep)
  exact (Nat.not_succ_le_self (d (k + 1) + 1)) hbad

theorem critical_failure_impossible_of_small_previous_max {k P : Nat}
    (hk : 2 ≤ k) (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hPsmall : P ≤ 5) : False := by
  have hdelta9 := critical_new_increment_lower_bound hk hIH hnew hfail
  have hsep : 2 * P ≤ d (k + 1) + 1 := by
    calc
      2 * P ≤ 2 * 5 := Nat.mul_le_mul_left 2 hPsmall
      _ = 10 := by decide
      _ ≤ d (k + 1) + 1 := Nat.succ_le_succ hdelta9
  exact critical_failure_impossible_of_separation hk hIH hnew hfail hsep

theorem critical_previous_maximum_prefix {k M : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∃ p c u v : Nat,
      2 ≤ p ∧ p ≤ k ∧ d p = M ∧
      (∀ j : Nat, 2 ≤ j → j < p → d j < M) ∧
      5 < M ∧
      (p = M + 2 ∨
        (M + 2 < p ∧ d (M + 2) < M ∧
          d (M + 2) = Nat.gcd M (a (M + 1)) ∧
          Nat.gcd M (a (M + 1)) < M ∧ ¬ M ∣ a (M + 1))) ∧
      ((p % 2 = 0 ∧ p = M * u ∧ a (p - 1) = M * v ∧
          u % 2 = 0 ∧ v % 2 = 1 ∧ Nat.gcd u v = 1 ∧ 2 ≤ u) ∨
        (p % 2 = 1 ∧ p - 2 = M * u ∧ a (p - 1) = M * v ∧
          u % 2 = 1 ∧ v % 2 = 0 ∧ Nat.gcd u v = 1 ∧
          1 ≤ u ∧ (u = 1 ∨ 3 ≤ u))) ∧
      k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      a k = d (k + 1) * (2 * c + 1) ∧
      D (k + 1) = d (k + 1) * (c + 2) := by
  have hM5 : 5 < M := by
    by_cases hM5 : 5 < M
    · exact hM5
    · exact False.elim (critical_failure_impossible_of_small_previous_max hk hIH
        hnew hfail (Nat.le_of_not_gt hM5))
  rcases attained_previous_maximum_first_occurrence hP with
    ⟨p, hp2, hpk, hdp, hprior⟩
  have hrec : IsDifferenceRecord M := ⟨p, hp2, hdp, hprior⟩
  have hsplit := record_index_or_late_gcd_reduction hM5 hp2 hdp hprior
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, hcmod, hc2, hak, hD, _, _⟩
  rcases Nat.mod_two_eq_zero_or_one p with hp0 | hp1
  · rcases record_even_occurrence_quotients hM5 hrec hp2 hdp hp0 with
      ⟨u, v, hpu, hpv, hu0, hv1, huv, hu2⟩
    exact ⟨p, c, u, v, hp2, hpk, hdp, hprior, hM5, hsplit,
      Or.inl ⟨hp0, hpu, hpv, hu0, hv1, huv, hu2⟩,
      hc, hcmod, hc2, hak, hD⟩
  · rcases record_odd_occurrence_quotients hM5 hrec hp2 hdp hp1 with
      ⟨u, v, hpu, hpv, hu1, hv0, huv, hupos, hucases⟩
    exact ⟨p, c, u, v, hp2, hpk, hdp, hprior, hM5, hsplit,
      Or.inr ⟨hp1, hpu, hpv, hu1, hv0, huv, hupos, hucases⟩,
      hc, hcmod, hc2, hak, hD⟩

theorem critical_endpoint_lower_bound {k M m s : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hbelow : k + 1 < m) (hfund : B m = 2)
    (hchain : HasNontrivialChain (k + 1) m s) :
    k + 1 + 2 * d (k + 1) + 2 * s ≤ m := by
  have hkplus : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hBnext := new_max_failure_next_B_eq hk hIH hnew hfail
  have hrel := B_add_index_eq_D_add_two hkplus
  rw [hBnext] at hrel
  have hDstart : D (k + 1) = k + 1 + 2 * d (k + 1) := by
    have hcancel : 2 + D (k + 1) = 2 + (k + 1 + 2 * d (k + 1)) := by
      calc
        2 + D (k + 1) = D (k + 1) + 2 := by simp [Nat.add_comm]
        _ = (2 * d (k + 1) + 2) + (k + 1) := hrel.symm
        _ = 2 + (k + 1 + 2 * d (k + 1)) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    exact Nat.add_left_cancel hcancel
  have hm2 : 2 ≤ m := Nat.le_trans hkplus (Nat.le_of_lt hbelow)
  have hDm : D m = m := D_eq_self_of_fundamental hm2 hfund
  have hgrowth := D_growth_of_nontrivial_chain hkplus hchain
  calc
    k + 1 + 2 * d (k + 1) + 2 * s = D (k + 1) + 2 * s := by rw [hDstart]
    _ ≤ D m := hgrowth
    _ = m := hDm

theorem fundamental_point_iff {m : Nat} (hm : 2 ≤ m) :
    B m = 2 ↔ a m = 2 * m :=
  B_eq_two_iff_a_eq_two_mul hm

theorem one_interval_const_D_B {l t : Nat} (hl : 2 ≤ l)
    (hone : ∀ j : Nat, l < j → j ≤ l + t → d j = 1) :
    D (l + t) = D l ∧ B (l + t) + t = B l := by
  induction t with
  | zero => simp
  | succ t iht =>
      have hlt : l < l + t + 1 :=
        Nat.lt_succ_of_le (Nat.le_add_right l t)
      have hle : l + t + 1 ≤ l + Nat.succ t := by simp [Nat.add_assoc]
      have hd : d (l + t + 1) = 1 := hone _ hlt hle
      have hone' : ∀ j : Nat, l < j → j ≤ l + t → d j = 1 := by
        intro j hj hjt
        exact hone j hj (Nat.le_trans hjt (Nat.le_add_right (l + t) 1))
      have ih := iht hone'
      have hltwo : 2 ≤ l + t :=
        Nat.le_trans hl (Nat.le_add_right l t)
      have hstep := excess_succ_add_two hltwo
      have hBstep : B (l + t + 1) + 1 = B (l + t) := by
        have hcancel : B (l + t + 1) + 1 + 1 = B (l + t) + 1 := by
          calc
            B (l + t + 1) + 1 + 1 = B (l + t + 1) + 2 := by
              simp [Nat.add_assoc]
            _ = B (l + t) + d (l + t + 1) := hstep
            _ = B (l + t) + 1 := by rw [hd]
        exact Nat.add_right_cancel hcancel
      have hDstep : D (l + t + 1) = D (l + t) :=
        (D_succ_eq_self_iff_d_succ_eq_one (l + t)).2 hd
      constructor
      · calc
          D (l + Nat.succ t) = D (l + t + 1) := by simp [Nat.add_assoc]
          _ = D (l + t) := hDstep
          _ = D l := ih.1
      · calc
          B (l + Nat.succ t) + Nat.succ t =
              B (l + t + 1) + (t + 1) := by simp [Nat.add_assoc]
          _ = (B (l + t + 1) + 1) + t := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = B (l + t) + t := by rw [hBstep]
          _ = B l := ih.2

theorem first_later_nontrivial_of_exists {n C : Nat} (hn : 2 ≤ n)
    (hex : ∃ j : Nat, n < j ∧ j ≤ C ∧ 1 < d j) :
    ∃ r : Nat, n < r ∧ r ≤ C ∧ 1 < d r ∧
      ∀ j : Nat, n < j → j < r → d j = 1 := by
  induction C using Nat.strongRecOn with
  | ind C ih =>
      rcases hex with ⟨r, hnr, hrC, hdr⟩
      by_cases hprev : ∃ j : Nat, n < j ∧ j < C ∧ 1 < d j
      · rcases hprev with ⟨j, hnj, hjC, hdj⟩
        have hexj : ∃ q : Nat, n < q ∧ q ≤ j ∧ 1 < d q :=
          ⟨j, hnj, Nat.le_refl j, hdj⟩
        rcases ih j hjC hexj with ⟨s, hns, hsj, hds, hprior⟩
        exact ⟨s, hns, Nat.le_trans hsj (Nat.le_of_lt hjC), hds, hprior⟩
      · have hr_eq : r = C := by
          apply Nat.le_antisymm hrC
          exact Nat.le_of_not_gt (fun hrc => hprev ⟨r, hnr, hrc, hdr⟩)
        refine ⟨C, ?_, Nat.le_refl C, ?_, ?_⟩
        · simpa [hr_eq] using hnr
        · simpa [hr_eq] using hdr
        · intro j hnj hjC
          by_cases heq : d j = 1
          · exact heq
          · have hj2 : 2 ≤ j := Nat.le_trans hn (Nat.le_of_lt hnj)
            have hdpos : 1 ≤ d j := one_le_d_of_two_le hj2
            have hdgt : 1 < d j :=
              Nat.lt_of_le_of_ne hdpos (fun h => heq h.symm)
            exact False.elim (hprev ⟨j, hnj, hjC, hdgt⟩)

theorem first_later_nontrivial_dichotomy {n C : Nat} (hn : 2 ≤ n) :
    (∀ j : Nat, n < j → j ≤ C → d j = 1) ∨
      ∃ r : Nat, n < r ∧ r ≤ C ∧ 1 < d r ∧
        ∀ j : Nat, n < j → j < r → d j = 1 := by
  by_cases hex : ∃ j : Nat, n < j ∧ j ≤ C ∧ 1 < d j
  · exact Or.inr (first_later_nontrivial_of_exists hn hex)
  · left
    intro j hnj hjC
    by_cases heq : d j = 1
    · exact heq
    · have hj2 : 2 ≤ j := Nat.le_trans hn (Nat.le_of_lt hnj)
      have hdpos : 1 ≤ d j := one_le_d_of_two_le hj2
      have hdgt : 1 < d j :=
        Nat.lt_of_le_of_ne hdpos (fun h => heq h.symm)
      exact False.elim (hex ⟨j, hnj, hjC, hdgt⟩)

theorem first_later_event_D_eq {n C r : Nat} (hn : 2 ≤ n)
    (hC : D n = C) (hnr : n < r)
    (hfirst : ∀ j : Nat, n < j → j < r → d j = 1) :
    D (r - 1) = C := by
  have hle : n ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using Nat.succ_le_of_lt hnr
  obtain ⟨t, ht⟩ := Nat.le.dest hle
  have hr1 : 1 ≤ r := by
    have hn1 : 1 ≤ n := Nat.le_trans (by simp) hn
    exact Nat.le_trans hn1 (Nat.le_of_lt hnr)
  have hone : ∀ j : Nat, n < j → j ≤ n + t → d j = 1 := by
    intro j hnj hjt
    apply hfirst j hnj
    have hjpred : j ≤ r - 1 := by
      exact Nat.le_trans hjt (Nat.le_of_eq ht)
    apply Nat.lt_of_succ_le
    calc
      j + 1 ≤ (r - 1) + 1 := Nat.add_le_add_right hjpred 1
      _ = r := Nat.sub_add_cancel hr1
  have htail := one_interval_const_D_B hn hone
  rw [ht] at htail
  exact htail.1.trans hC

theorem moving_horizon_no_event_telescope {s C : Nat}
    (hs : IsMovingHorizonState s C)
    (hno : ∀ j : Nat, s < j → j ≤ C → d j = 1) :
    D C = C ∧ B C + (C - s) = B s := by
  rcases hs with ⟨hs2, hDs, hsc⟩
  have hsle : s ≤ C := Nat.le_of_lt hsc
  have hsum : s + (C - s) = C := by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hsle
  have hone : ∀ j : Nat, s < j → j ≤ s + (C - s) → d j = 1 := by
    intro j hsj hj
    apply hno j hsj
    rw [hsum] at hj
    exact hj
  have htail := one_interval_const_D_B hs2 hone
  constructor
  · calc
      D C = D (s + (C - s)) := congrArg D hsum.symm
      _ = D s := htail.1
      _ = C := hDs
  · calc
      B C + (C - s) = B (s + (C - s)) + (C - s) := by rw [hsum]
      _ = B s := htail.2

theorem moving_horizon_slack_coordinate {s C : Nat}
    (hs : IsMovingHorizonState s C) :
    B s = (C - s) + 2 := by
  rcases hs with ⟨hs2, hDs, hsc⟩
  have hsle : s ≤ C := Nat.le_of_lt hsc
  have hsum : (C - s) + s = C := Nat.sub_add_cancel hsle
  have hrel := B_add_index_eq_D_add_two hs2
  apply Nat.add_right_cancel
  calc
    B s + s = D s + 2 := hrel
    _ = C + 2 := by rw [hDs]
    _ = ((C - s) + 2) + s := by
      rw [Nat.add_assoc, Nat.add_comm 2 s, ← Nat.add_assoc, hsum]

theorem moving_horizon_step_of_exists {s C : Nat}
    (hs : IsMovingHorizonState s C)
    (hex : ∃ j : Nat, s < j ∧ j ≤ C ∧ 1 < d j) :
    ∃ r C', IsMovingHorizonStep s C r C' := by
  rcases first_later_nontrivial_of_exists hs.1 hex with
    ⟨r, hsr, hrC, hdr, hfirst⟩
  have hDrpred : D (r - 1) = C :=
    first_later_event_D_eq hs.1 hs.2.1 hsr hfirst
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hrpred : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr3
  have hrsucc : r - 1 + 1 = r :=
    Nat.sub_add_cancel (Nat.le_trans (by simp) hr3)
  have hdr' : 1 < d (r - 1 + 1) := by
    rw [hrsucc]
    exact hdr
  have hgrowth : C + 2 ≤ D r := by
    have h := D_add_two_le_succ_of_two_le hrpred hdr'
    rw [hrsucc, hDrpred] at h
    exact h
  have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
  have hrC' : r < D r := by
    calc
      r ≤ C := hrC
      _ < C + 2 := by simp
      _ ≤ D r := hgrowth
  refine ⟨r, D r, ?_⟩
  exact ⟨hs, hsr, hrC, hdr, hfirst, hDrpred, rfl, hgrowth,
    ⟨hr2, rfl, hrC'⟩⟩

theorem moving_horizon_slack_transition {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) = (C - s) + (d r - 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr1 : 1 ≤ r :=
    Nat.le_trans (by simp) (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hrsucc : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hDstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    rw [hrsucc, hDr] at h
    exact h
  have hsle : s ≤ r := Nat.le_of_lt hsr
  calc
    (C' - r) + (r - s) = (C + (d r - 1) - r) + (r - s) := by
      rw [hC', hDstep]
    _ = ((C - r) + (d r - 1)) + (r - s) := by
      rw [Nat.sub_add_comm hrC]
    _ = (C - r + (r - s)) + (d r - 1) := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = (C - s) + (d r - 1) := by
      rw [Nat.sub_add_sub_cancel hrC hsle]

theorem moving_horizon_step_size_le_slack {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    d r ≤ C - s := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, _, _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hC2 : 2 ≤ C := by
    rw [← hs.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hs.1
  have hCmod : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hsc : s ≤ C := Nat.le_of_lt hs.2.2
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  by_cases hle : d r ≤ C - s
  · exact hle
  · have hslack : C - s < d r := Nat.lt_of_not_ge hle
    by_cases heven : r % 2 = 0
    · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
      rw [if_pos heven] at hmap
      have hdivr : d r ∣ r := by
        rw [hmap]
        exact Nat.gcd_dvd_left _ _
      have hdivC : d r ∣ C - 1 := by
        rw [hmap]
        exact Nat.gcd_dvd_right _ _
      have hrne : r ≠ C := by
        intro hreq
        have hdvdC : d r ∣ C := by simpa [hreq] using hdivr
        have hdvd1 : d r ∣ 1 := by
          have hsub := Nat.dvd_sub hdvdC hdivC
          rw [Nat.sub_sub_self (Nat.le_trans (by simp) hC2)] at hsub
          exact hsub
        have hdone : d r = 1 := Nat.eq_one_of_dvd_one hdvd1
        have : (1 : Nat) < 1 := by simpa [hdone] using hdr
        exact Nat.lt_irrefl 1 this
      have hrl : r ≤ C - 1 := by
        apply Nat.le_sub_of_add_le
        exact Nat.succ_le_of_lt
          (Nat.lt_of_le_of_ne hrC (fun h => hrne h))
      have hqdiv : d r ∣ C - 1 - r := Nat.dvd_sub hdivC hdivr
      have hq_lt : C - 1 - r < d r := by
        calc
          C - 1 - r ≤ C - r := by
            rw [Nat.sub_sub]
            exact Nat.sub_le_sub_left (by simp) C
          _ < C - s := Nat.sub_lt_sub_left hs.2.2 hsr
          _ < d r := hslack
      have hqzero : C - 1 - r = 0 :=
        Nat.eq_zero_of_dvd_of_lt hqdiv hq_lt
      have hreq : r = C - 1 := by
        apply Nat.le_antisymm hrl
        exact (Nat.sub_eq_zero_iff_le).1 hqzero
      have hCstep : C - 1 + 1 = C := Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
      have hqmod : (C - 1) % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
        · have hbad : C % 2 = 1 := by
            calc
              C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
              _ = 1 := by simp [Nat.add_mod, hq0]
          simp [hCmod] at hbad
        · exact hq1
      have hbad : (1 : Nat) = 0 := by
        calc
          1 = (C - 1) % 2 := hqmod.symm
          _ = r % 2 := by rw [hreq]
          _ = 0 := heven
      cases hbad
    · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
      rw [if_neg heven] at hmap
      have hdivC : d r ∣ C + 1 := by
        rw [hmap]
        exact Nat.gcd_dvd_right _ _
      have hdivr : d r ∣ r - 2 := by
        rw [hmap]
        exact Nat.gcd_dvd_left _ _
      have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
      have hqarg : r - 2 ≤ C + 1 :=
        Nat.le_trans (Nat.sub_le r 2) (Nat.le_trans hrC (by simp))
      have hqeq : (C + 1) - (r - 2) = C - r + 3 := by
        apply (Nat.sub_eq_iff_eq_add hqarg).2
        calc
          C + 1 = (C - r) + r + 1 := by rw [Nat.sub_add_cancel hrC]
          _ = (C - r) + (r + 1) := Nat.add_assoc _ _ _
          _ = (C - r) + (3 + (r - 2)) := by
            rw [show r + 1 = 3 + (r - 2) by
              calc
                r + 1 = (r - 2 + 2) + 1 := by
                  rw [Nat.sub_add_cancel hr2]
                _ = (r - 2) + (2 + 1) := Nat.add_assoc _ _ _
                _ = (r - 2) + 3 := by rfl
                _ = 3 + (r - 2) := Nat.add_comm _ _]
          _ = (C - r + 3) + (r - 2) := (Nat.add_assoc _ _ _).symm
      have hqdiv : d r ∣ (C + 1) - (r - 2) := Nat.dvd_sub hdivC hdivr
      have hCr_lt : C - r < C - s := Nat.sub_lt_sub_left hs.2.2 hsr
      have hdiff : C - r + 1 ≤ C - s := Nat.succ_le_of_lt hCr_lt
      have hqle : (C + 1) - (r - 2) ≤ C - s + 2 := by
        rw [hqeq]
        exact Nat.add_le_add_right hdiff 2
      have hd3 : 3 ≤ d r := by
        rcases one_or_three_le_of_mod_two_eq_one hdodd with hd1 | hd3
        · have : (1 : Nat) < 1 := by simpa [hd1] using hdr
          exact False.elim (Nat.lt_irrefl 1 this)
        · exact hd3
      have hLle : C - s ≤ d r - 1 :=
        Nat.le_sub_of_add_le (Nat.succ_le_of_lt hslack)
      have hL2 : C - s + 2 ≤ (d r - 1) + 2 :=
        Nat.add_le_add_right hLle 2
      have hdminus : d r - 1 + 2 < 2 * d r := by
        calc
          d r - 1 + 2 = (d r - 1 + 1) + 1 := by simp [Nat.add_assoc]
          _ = d r + 1 := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hdr)]
          _ < d r + d r := Nat.add_lt_add_left (Nat.lt_of_lt_of_le (by simp) hd3) _
          _ = 2 * d r := by simp [Nat.two_mul]
      have hq_lt_two : (C + 1) - (r - 2) < 2 * d r :=
        Nat.lt_of_le_of_lt (Nat.le_trans hqle hL2) hdminus
      have hqpos : 0 < (C + 1) - (r - 2) :=
        Nat.sub_pos_of_lt
          (Nat.lt_of_le_of_lt (Nat.sub_le r 2) (Nat.lt_succ_of_le hrC))
      have hqeqd : (C + 1) - (r - 2) = d r :=
        Nat.eq_of_dvd_of_lt_two_mul (Nat.ne_of_gt hqpos) hqdiv hq_lt_two
      have hqmod : ((C + 1) - (r - 2)) % 2 = 0 := by
        rw [hqeq]
        have hCrmod : (C - r) % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (C - r) with hzero | hone
          · have hbad : C % 2 = 1 := by
              have hrmod : r % 2 = 1 := by
                rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
                · exact False.elim (heven hr0)
                · exact hr1
              calc
                C % 2 = ((C - r) + r) % 2 := by rw [Nat.sub_add_cancel hrC]
                _ = 1 := by simp [Nat.add_mod, hzero, hrmod]
            simp [hCmod] at hbad
          · exact hone
        simp [Nat.add_mod, hCrmod, heven]
      have hbad : (0 : Nat) = 1 := by
        calc
          0 = ((C + 1) - (r - 2)) % 2 := hqmod.symm
          _ = (d r) % 2 := by rw [hqeqd]
          _ = 1 := hdodd
      cases hbad

theorem moving_horizon_step_size_add_le {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    d r + s ≤ C := by
  exact (Nat.le_sub_iff_add_le (Nat.le_of_lt hstep.1.2.2)).1
    (moving_horizon_step_size_le_slack hstep)

theorem moving_horizon_next_slack_upper {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    C' - r + 2 ≤ 2 * (C - s) := by
  have htransition := moving_horizon_slack_transition hstep
  have hsize := moving_horizon_step_size_le_slack hstep
  have hdist : 1 ≤ r - s := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using Nat.succ_le_of_lt hstep.2.1
  have hleft : C' - r + 1 ≤ (C - s) + (d r - 1) := by
    calc
      C' - r + 1 ≤ (C' - r) + (r - s) :=
        Nat.add_le_add_left hdist (C' - r)
      _ = (C - s) + (d r - 1) := htransition
  have hdpos : 1 ≤ d r :=
    one_le_d_of_two_le (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  calc
    C' - r + 2 = (C' - r + 1) + 1 := by simp [Nat.add_assoc]
    _ ≤ (C - s) + (d r - 1) + 1 := Nat.add_le_add_right hleft 1
    _ = (C - s) + ((d r - 1) + 1) := by simp [Nat.add_assoc]
    _ = (C - s) + d r := by rw [Nat.sub_add_cancel hdpos]
    _ ≤ (C - s) + (C - s) := Nat.add_le_add_left hsize _
    _ = 2 * (C - s) := by simp [Nat.two_mul]

theorem moving_horizon_step_event_package {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r ∣ C - 1 ∧ d r < C - 1 ∧ 3 * d r ≤ C - 1) ∨
      (r % 2 = 1 ∧ d r ∣ C + 1 ∧ d r < C + 1 ∧ 3 * d r ≤ C + 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, _, _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  by_cases heven : r % 2 = 0
  · left
    have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_pos heven] at hmap
    have hdiv : d r ∣ C - 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C - 1 :=
      (constant_D_event_even_proper_iff hr3 hDr heven).2
        (constant_D_event_even_not_dvd_of_le hr3 hDr heven hrC hdr)
    have hbound : 3 * d r ≤ C - 1 :=
      constant_D_event_even_size_bound_of_le hr3 hDr heven hrC hdr
    exact ⟨heven, hdiv, hproper, hbound⟩
  · right
    have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact False.elim (heven hzero)
      · exact hone
    have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_neg heven] at hmap
    have hdiv : d r ∣ C + 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C + 1 :=
      (constant_D_event_odd_proper_iff hr3 hDr heven).2
        (constant_D_event_odd_not_dvd_of_le hr3 hrC)
    have hbound : 3 * d r ≤ C + 1 :=
      constant_D_event_odd_size_bound_of_le hr3 hDr heven hrC
    exact ⟨hodd, hdiv, hproper, hbound⟩

theorem moving_horizon_even_quotient_normal_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    ∃ q : Nat, C - s = (r - s) + 1 + d r * q ∧ q % 2 = 1 ∧
      1 ≤ q ∧ C' - r = d r * (q + 1) := by
  have htransition := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hC2 : 2 ≤ C := by
    rw [← hs.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hs.1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  rw [if_pos heven] at hmap
  have hdivr : d r ∣ r := by
    rw [hmap]
    exact Nat.gcd_dvd_left _ _
  have hdivC : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hrne : r ≠ C := by
    intro hreq
    have hdvdC : d r ∣ C := by simpa [hreq] using hdivr
    have hdvd1 : d r ∣ 1 := by
      have hsub := Nat.dvd_sub hdvdC hdivC
      rw [Nat.sub_sub_self (Nat.le_trans (by simp) hC2)] at hsub
      exact hsub
    have hdone : d r = 1 := Nat.eq_one_of_dvd_one hdvd1
    have : (1 : Nat) < 1 := by simpa [hdone] using hdr
    exact Nat.lt_irrefl 1 this
  have hrlt : r < C := Nat.lt_of_le_of_ne hrC (fun h => hrne h)
  have hrle : r ≤ C - 1 := by
    apply Nat.le_sub_of_add_le
    exact Nat.succ_le_of_lt hrlt
  have hdivdiff : d r ∣ (C - 1) - r := Nat.dvd_sub hdivC hdivr
  rcases hdivdiff with ⟨q, hq⟩
  have hCminus : C - 1 = r + d r * q := by
    calc
      C - 1 = ((C - 1) - r) + r := (Nat.sub_add_cancel hrle).symm
      _ = d r * q + r := by rw [hq]
      _ = r + d r * q := Nat.add_comm _ _
  have hCpos : 1 ≤ C := Nat.le_trans (by simp) hC2
  have hCeq : C = r + d r * q + 1 := by
    calc
      C = (C - 1) + 1 := (Nat.sub_add_cancel hCpos).symm
      _ = (r + d r * q) + 1 := by rw [hCminus]
  have hrsum : (r - s) + s = r := Nat.sub_add_cancel (Nat.le_of_lt hsr)
  have hL : C - s = (r - s) + 1 + d r * q := by
    apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (Nat.le_of_lt hsr) hrC)).2
    calc
      C = r + d r * q + 1 := hCeq
      _ = ((r - s) + 1 + d r * q) + s := by
        calc
          r + d r * q + 1 = r + 1 + d r * q := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = (r - s) + s + 1 + d r * q := by rw [hrsum]
          _ = ((r - s) + 1 + d r * q) + s := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hCmod : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hCminusmod : (C - 1) % 2 = 1 := by
    have hCstep : C - 1 + 1 = C := Nat.sub_add_cancel hCpos
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hzero | hone
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hzero]
      simp [hCmod] at hbad
    · exact hone
  have hqmod : q % 2 = 1 := by
    calc
      q % 2 = (d r * q) % 2 := quotient_mod_two_of_left_odd hdodd
      _ = (r + d r * q) % 2 := by simp [Nat.add_mod, heven]
      _ = (C - 1) % 2 := by rw [← hCminus]
      _ = 1 := hCminusmod
  have hq1 : 1 ≤ q := by
    cases q with
    | zero => simp at hqmod
    | succ q => exact Nat.succ_le_succ (Nat.zero_le q)
  have hepos : 1 ≤ d r := one_le_d_of_two_le (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hcancel : (C' - r) + (r - s) =
      (d r * (q + 1)) + (r - s) := by
    calc
      (C' - r) + (r - s) = (C - s) + (d r - 1) := htransition
      _ = ((r - s) + 1 + d r * q) + (d r - 1) := by rw [hL]
      _ = (r - s) + ((d r - 1) + 1) + d r * q := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (r - s) + d r + d r * q := by rw [Nat.sub_add_cancel hepos]
      _ = d r * (q + 1) + (r - s) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hL' : C' - r = d r * (q + 1) := by
    apply Nat.add_right_cancel hcancel
  exact ⟨q, hL, hqmod, hq1, hL'⟩

theorem moving_horizon_odd_quotient_normal_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    ∃ q : Nat, C - s + 3 = (r - s) + d r * q ∧ q % 2 = 0 ∧
      2 ≤ q ∧ C' - r + 4 = d r * (q + 1) := by
  have htransition := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hC2 : 2 ≤ C := by
    rw [← hs.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hs.1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  have hne : r % 2 ≠ 0 := by simp [hodd]
  rw [if_neg hne] at hmap
  have hdivr : d r ∣ r - 2 := by
    rw [hmap]
    exact Nat.gcd_dvd_left _ _
  have hdivC : d r ∣ C + 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
  have hqarg : r - 2 ≤ C + 1 :=
    Nat.le_trans (Nat.sub_le r 2) (Nat.le_trans hrC (by simp))
  have hdivdiff : d r ∣ (C + 1) - (r - 2) := Nat.dvd_sub hdivC hdivr
  rcases hdivdiff with ⟨q, hq⟩
  have hCplus : C + 1 = (r - 2) + d r * q := by
    calc
      C + 1 = ((C + 1) - (r - 2)) + (r - 2) :=
        (Nat.sub_add_cancel hqarg).symm
      _ = d r * q + (r - 2) := by rw [hq]
      _ = (r - 2) + d r * q := Nat.add_comm _ _
  have hCplus3 : C + 3 = r + d r * q := by
    calc
      C + 3 = (C + 1) + 2 := by simp [Nat.add_assoc]
      _ = ((r - 2) + d r * q) + 2 := by rw [hCplus]
      _ = (r - 2) + 2 + d r * q := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = r + d r * q := by rw [Nat.sub_add_cancel hr2]
  have hrsum : (r - s) + s = r := Nat.sub_add_cancel (Nat.le_of_lt hsr)
  have hsle : s ≤ C := Nat.le_trans (Nat.le_of_lt hsr) hrC
  have hL : C - s + 3 = (r - s) + d r * q := by
    apply Nat.add_right_cancel
    calc
      (C - s + 3) + s = (C - s) + s + 3 := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = C + 3 := by rw [Nat.sub_add_cancel hsle]
      _ = r + d r * q := hCplus3
      _ = (r - s) + s + d r * q := by rw [hrsum]
      _ = ((r - s) + d r * q) + s := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hCmod : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hCplusmod : (C + 1) % 2 = 1 := by
    simp [Nat.add_mod, hCmod]
  have hrminusmod : (r - 2) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (r - 2) with hzero | hone
    · have hbad : r % 2 = 0 := by
        calc
          r % 2 = ((r - 2) + 2) % 2 := by
            rw [Nat.sub_add_cancel hr2]
          _ = 0 := by simp [Nat.add_mod, hzero]
      simp [hodd] at hbad
    · exact hone
  have hqmod : q % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
    · exact hq0
    · have hbad : (1 : Nat) = 0 := by
        calc
          1 = (C + 1) % 2 := hCplusmod.symm
          _ = ((r - 2) + d r * q) % 2 := by rw [hCplus]
          _ = 0 := by simp [Nat.add_mod, hrminusmod, Nat.mul_mod, hdodd, hq1]
      cases hbad
  have hqne : q ≠ 0 := by
    intro hq0
    have heq : C + 1 = r - 2 := by simpa [hq0] using hCplus
    have hlt : r - 2 < C + 1 :=
      Nat.lt_of_le_of_lt (Nat.sub_le r 2)
        (Nat.lt_of_le_of_lt hrC (Nat.lt_succ_self C))
    have : r - 2 < r - 2 := by simpa [heq] using hlt
    exact Nat.lt_irrefl _ this
  have hqpos : 0 < q := by
    cases q with
    | zero => exact False.elim (hqne rfl)
    | succ q => exact Nat.zero_lt_succ q
  have hq2 : 2 ≤ q := two_le_of_pos_of_mod_two_eq_zero hqpos hqmod
  have hepos : 1 ≤ d r := one_le_d_of_two_le (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hfour : d r - 1 + 4 = 3 + ((d r - 1) + 1) := by
    calc
      d r - 1 + 4 = (d r - 1 + 1) + 3 := by
        simp [Nat.add_assoc]
      _ = d r + 3 := by rw [Nat.sub_add_cancel hepos]
      _ = 3 + ((d r - 1) + 1) := by
        rw [Nat.sub_add_cancel hepos]
        simp [Nat.add_comm]
  have hcancel : (C' - r + 4) + (r - s) =
      (d r * (q + 1)) + (r - s) := by
    calc
      (C' - r + 4) + (r - s) = (C' - r) + (r - s) + 4 := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (C - s) + (d r - 1) + 4 := by rw [htransition]
      _ = (C - s) + (3 + ((d r - 1) + 1)) := by
        rw [Nat.add_assoc, hfour]
      _ = (C - s + 3) + ((d r - 1) + 1) := by
        simp [Nat.add_assoc]
      _ = ((r - s) + d r * q) + ((d r - 1) + 1) := by rw [hL]
      _ = (r - s) + d r + d r * q := by
        rw [Nat.sub_add_cancel hepos]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = d r * (q + 1) + (r - s) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hL' : C' - r + 4 = d r * (q + 1) := Nat.add_right_cancel hcancel
  exact ⟨q, hL, hqmod, hq2, hL'⟩

theorem moving_horizon_normalized_new_max_even {P s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hnew : P < d r) (hPodd : P % 2 = 1) :
    r % 2 = 0 ∧ C' - r = 2 * d r := by
  have hdist : 1 ≤ r - s := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using Nat.succ_le_of_lt hstep.2.1
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · rcases moving_horizon_even_quotient_normal_form hstep heven with
      ⟨q, hL, hqmod, hq1, hL'⟩
    have hbound : d r * q ≤ 2 * P := by
      calc
        d r * q ≤ (r - s) + 1 + d r * q := Nat.le_add_left _ _
        _ = 2 * P := by rw [← hL, hnorm]
    have hq_lt_two : q < 2 := by
      rcases Nat.lt_or_ge q 2 with hlt | hge
      · exact hlt
      · have hmul : 2 * d r ≤ d r * q := by
          calc
            2 * d r = d r * 2 := by simp [Nat.mul_comm]
            _ ≤ d r * q := Nat.mul_le_mul_left _ hge
        have htoo : 2 * P < d r * q := by
          calc
            2 * P < 2 * d r := (Nat.mul_lt_mul_left (by simp : 0 < 2)).2 hnew
            _ ≤ d r * q := hmul
        exact False.elim ((Nat.not_lt_of_ge hbound) htoo)
    have hqeq : q = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hq_lt_two) hq1
    refine ⟨heven, ?_⟩
    rw [hL', hqeq]
    simp [Nat.two_mul, Nat.mul_comm]
  · rcases moving_horizon_odd_quotient_normal_form hstep hodd with
      ⟨q, hL, hqmod, hq2, hL'⟩
    have hepos : 1 ≤ d r := one_le_d_of_two_le
      (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
    have h2e : 2 * d r ≤ d r * q := by
      calc
        2 * d r = d r * 2 := by simp [Nat.mul_comm]
        _ ≤ d r * q := Nat.mul_le_mul_left _ hq2
    have hlower : 1 + 2 * d r ≤ (r - s) + d r * q := by
      calc
        1 + 2 * d r ≤ 1 + d r * q := Nat.add_le_add_left h2e 1
        _ ≤ (r - s) + d r * q := Nat.add_le_add_right hdist _
    have hEq : 2 * P + 3 = (r - s) + d r * q := by
      calc
        2 * P + 3 = C - s + 3 := by rw [hnorm]
        _ = (r - s) + d r * q := hL
    have hbound : 2 * d r + 1 ≤ (2 * P + 2) + 1 := by
      calc
        2 * d r + 1 = 1 + 2 * d r := by simp [Nat.add_comm]
        _ ≤ (r - s) + d r * q := hlower
        _ = (2 * P + 2) + 1 := by rw [← hEq]
    have hbound2 : 2 * d r ≤ 2 * P + 2 := by
      exact Nat.le_of_succ_le_succ (by simpa [Nat.add_assoc] using hbound)
    have hbound2' : 2 * d r ≤ 2 * (P + 1) := by
      simpa [Nat.mul_succ] using hbound2
    have hedle : d r ≤ P + 1 := Nat.le_of_mul_le_mul_left hbound2' (by simp)
    have heq : d r = P + 1 :=
      Nat.le_antisymm hedle (Nat.succ_le_of_lt hnew)
    have hbad : (1 : Nat) = 0 := by
      calc
        1 = d r % 2 := hdodd.symm
        _ = (P + 1) % 2 := by rw [heq]
        _ = 0 := by simp [Nat.add_mod, hPodd]
    cases hbad

theorem moving_horizon_dichotomy {s C : Nat}
    (hs : IsMovingHorizonState s C) :
    (∀ j : Nat, s < j → j ≤ C → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep s C r C' := by
  rcases first_later_nontrivial_dichotomy hs.1 with hno | hex
  · exact Or.inl hno
  · rcases hex with ⟨r, hsr, hrC, hdr, _⟩
    exact Or.inr (moving_horizon_step_of_exists hs ⟨r, hsr, hrC, hdr⟩)

theorem attained_previous_maximum_extend {P s : Nat}
    (hs : 2 ≤ s) (hP : IsAttainedPreviousMaximum P (s - 1))
    (hnew : P < d s) : IsAttainedPreviousMaximum (d s) s := by
  refine ⟨?_, ⟨s, hs, Nat.le_refl s, rfl⟩⟩
  intro j hj2 hjs
  by_cases hpred : j ≤ s - 1
  · exact Nat.le_trans (hP.1 j hj2 hpred) (Nat.le_of_lt hnew)
  · rcases Nat.lt_or_ge j s with hlt | hge
    · exact False.elim (hpred (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)))
    · have heq : j = s := Nat.le_antisymm hjs hge
      simpa [heq]

theorem moving_horizon_max_transfer {P s r : Nat}
    (hP : IsAttainedPreviousMaximum P s) (hsr : s < r)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, s < j → j < r → d j = 1) :
    (d r ≤ P ∧ IsAttainedPreviousMaximum P r) ∨
      (P < d r ∧ IsAttainedPreviousMaximum (d r) r) := by
  by_cases hle : d r ≤ P
  · left
    refine ⟨hle, ?_⟩
    rcases hP.2 with ⟨q, hq2, hqs, hdq⟩
    refine ⟨?_, ⟨q, hq2, Nat.le_trans hqs (Nat.le_of_lt hsr), hdq⟩⟩
    intro j hj2 hjr
    by_cases hjs : j ≤ s
    · exact hP.1 j hj2 hjs
    · have hsj : s < j := Nat.lt_of_not_ge hjs
      rcases Nat.lt_or_eq_of_le hjr with hjlt | hjeq
      · rw [hfirst j hsj hjlt]
        have hPpos : 1 ≤ P := by
          rw [← hdq]
          exact one_le_d_of_two_le hq2
        exact hPpos
      · simpa [hjeq] using hle
  · right
    have hgt : P < d r := Nat.lt_of_not_ge hle
    have hr2 : 2 ≤ r := by
      rcases hP.2 with ⟨q, hq2, hqs, _⟩
      exact Nat.le_trans hq2 (Nat.le_trans hqs (Nat.le_of_lt hsr))
    refine ⟨hgt, ?_⟩
    refine ⟨?_, ⟨r, hr2, Nat.le_refl r, rfl⟩⟩
    intro j hj2 hjr
    by_cases hjs : j ≤ s
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hP.1 j hj2 hjs) hgt)
    · have hsj : s < j := Nat.lt_of_not_ge hjs
      rcases Nat.lt_or_eq_of_le hjr with hjlt | hjeq
      · rw [hfirst j hsj hjlt]
        exact Nat.le_of_lt hdr
      · simpa [hjeq]

theorem moving_horizon_record_state_regeneration
    {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hP : IsAttainedPreviousMaximum P s) (hP5 : 5 < P)
    (hnorm : C - s = 2 * P) (hnew : P < d r) :
    ∃ c : Nat, r = d r * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      IsAttainedPreviousMaximum (d r) r ∧
      C' = d r * (c + 2) ∧ D r = d r * (c + 2) := by
  have hPodd : P % 2 = 1 :=
    attained_previous_maximum_value_mod_two_eq_one hP hP5
  have hrigid := moving_horizon_normalized_new_max_even
    hstep hnorm hnew hPodd
  have hfirst : ∀ j : Nat, s < j → j < r → d j = 1 :=
    hstep.2.2.2.2.1
  have hmax := moving_horizon_max_transfer hP hstep.2.1
    hstep.2.2.2.1 hfirst
  have hnewhist : IsAttainedPreviousMaximum (d r) r := by
    rcases hmax with h | h
    · exact False.elim ((Nat.not_le_of_gt hnew) h.1)
    · exact h.2
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, hrstate⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  rw [if_pos hrigid.1] at hmap
  have hdivr : d r ∣ r := by
    rw [hmap]
    exact Nat.gcd_dvd_left _ _
  rcases hdivr with ⟨c, hc⟩
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hcmod : c % 2 = 0 := by
    calc
      c % 2 = (d r * c) % 2 := quotient_mod_two_of_left_odd hdodd
      _ = r % 2 := congrArg (fun x : Nat => x % 2) hc.symm
      _ = 0 := hrigid.1
  have hcpos : 0 < c := by
    cases c with
    | zero =>
        have hbad := hr3
        rw [hc] at hbad
        simp at hbad
    | succ c => exact Nat.zero_lt_succ c
  have hc2 : 2 ≤ c := two_le_of_pos_of_mod_two_eq_zero hcpos hcmod
  have hrleC' : r ≤ C' := Nat.le_of_lt hrstate.2.2
  have hsum : (C' - r) + r = C' := Nat.sub_add_cancel hrleC'
  have hCeq : C' = d r * (c + 2) := by
    calc
      C' = (C' - r) + r := hsum.symm
      _ = 2 * d r + r := by rw [hrigid.2]
      _ = 2 * d r + d r * c := congrArg (fun x : Nat => 2 * d r + x) hc
      _ = d r * (c + 2) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.mul_comm]
  have hDeq : D r = d r * (c + 2) := hC'.symm.trans hCeq
  exact ⟨c, hc, hcmod, hc2, hnewhist, hCeq, hDeq⟩

theorem moving_horizon_far_old_event_envelope {P s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hfar : d r + 3 ≤ r - s) :
    B r + 2 ≤ 2 * P := by
  have htransition := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, hrstate⟩
  have hepos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hfour : d r - 1 + 4 = d r + 3 := by
    calc
      d r - 1 + 4 = (d r - 1 + 1) + 3 := by simp [Nat.add_assoc]
      _ = d r + 3 := by rw [Nat.sub_add_cancel hepos]
  have hsum : (C' - r + 4) + (r - s) ≤ 2 * P + (r - s) := by
    calc
      (C' - r + 4) + (r - s) = (C' - r) + (r - s) + 4 := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (C - s) + (d r - 1) + 4 := by rw [htransition]
      _ = 2 * P + (d r + 3) := by
        rw [hnorm]
        simp [Nat.add_assoc, hfour]
      _ ≤ 2 * P + (r - s) := Nat.add_le_add_left hfar _
  have hslack : C' - r + 4 ≤ 2 * P := Nat.le_of_add_le_add_right hsum
  have hcoord := moving_horizon_slack_coordinate hrstate
  calc
    B r + 2 = (C' - r + 2) + 2 := by rw [hcoord]
    _ = C' - r + 4 := by simp [Nat.add_assoc]
    _ ≤ 2 * P := hslack

theorem moving_horizon_old_event_dichotomy {P s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hold : d r ≤ P) :
    (d r ≤ P ∧ r - s ≤ d r + 2) ∨ B r + 2 ≤ 2 * P := by
  rcases Nat.lt_or_ge (r - s) (d r + 3) with hclose | hfar
  · have hclose' : r - s ≤ d r + 2 := Nat.le_of_lt_succ (by simpa using hclose)
    exact Or.inl ⟨hold, hclose'⟩
  · exact Or.inr (moving_horizon_far_old_event_envelope hstep hnorm hfar)

theorem moving_horizon_step_update {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    C' = C + (d r - 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr1 : 1 ≤ r := Nat.le_trans (by simp) (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hrsucc : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hDstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    rw [hrsucc, hDr] at h
    exact h
  exact hC'.trans hDstep

theorem moving_horizon_successive_event_gcd_dvd_three
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') :
    Nat.gcd (d r) (d u) ∣ 3 := by
  have hupdate := moving_horizon_step_update hstep
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have hu3 : 3 ≤ u := by
    exact Nat.le_trans (Nat.succ_le_succ hnext.1.1)
      (Nat.succ_le_of_lt hnext.2.1)
  have heodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  let g := Nat.gcd (d r) (d u)
  have hge : g ∣ d r := Nat.gcd_dvd_left _ _
  have hgf : g ∣ d u := Nat.gcd_dvd_right _ _
  have hC2 : 2 ≤ C := by
    rw [← hstep.1.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hstep.1.1
  have hCpos : 1 ≤ C := Nat.le_trans (by simp) hC2
  have hepos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  rcases Nat.mod_two_eq_zero_or_one r with hre | hro
  · have hmapr := constant_D_event_map (Nat.le_trans (by simp) hr3)
      hstep.2.2.2.2.2.1
    rw [if_pos hre] at hmapr
    have heC : d r ∣ C - 1 := by
      rw [hmapr]
      exact Nat.gcd_dvd_right _ _
    rcases Nat.mod_two_eq_zero_or_one u with hue | huo
    · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
      rw [if_pos hue] at hmapu
      have hfC : d u ∣ C' - 1 := by
        rw [hmapu]
        exact Nat.gcd_dvd_right _ _
      have hgA : g ∣ C - 1 := Nat.dvd_trans hge heC
      have hgB : g ∣ C' - 1 := Nat.dvd_trans hgf hfC
      have hform : C' - 1 = (C - 1) + (d r - 1) := by
        rw [hupdate]
        have hsumpos : 1 ≤ C + (d r - 1) :=
          Nat.le_trans hCpos (Nat.le_add_right C (d r - 1))
        apply (Nat.sub_eq_iff_eq_add hsumpos).2
        rw [show C = (C - 1) + 1 by exact (Nat.sub_add_cancel hCpos).symm]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hgem1 : g ∣ d r - 1 := by
        have hsub := Nat.dvd_sub hgB hgA
        rw [hform] at hsub
        simpa using hsub
      have hg1 : g ∣ 1 := by
        have hsub := Nat.dvd_sub hge hgem1
        rw [Nat.sub_sub_self hepos] at hsub
        exact hsub
      exact Nat.dvd_trans hg1 ⟨3, by simp⟩
    · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
      rw [if_neg (by simp [huo])] at hmapu
      have hfC : d u ∣ C' + 1 := by
        rw [hmapu]
        exact Nat.gcd_dvd_right _ _
      have hgA : g ∣ C - 1 := Nat.dvd_trans hge heC
      have hgB : g ∣ C' + 1 := Nat.dvd_trans hgf hfC
      have honeplus : 1 + (d r - 1) + 1 = d r + 1 := by
        calc
          1 + (d r - 1) + 1 = (d r - 1 + 1) + 1 := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = d r + 1 := by rw [Nat.sub_add_cancel hepos]
      have hform : C' + 1 = (C - 1) + (d r + 1) := by
        rw [hupdate]
        calc
          C + (d r - 1) + 1 = (C - 1) + (1 + (d r - 1) + 1) := by
            rw [show C = (C - 1) + 1 by exact (Nat.sub_add_cancel hCpos).symm]
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = (C - 1) + (d r + 1) := by rw [honeplus]
      have hgep1 : g ∣ d r + 1 := by
        have hsub := Nat.dvd_sub hgB hgA
        rw [hform] at hsub
        simpa using hsub
      have hg1 : g ∣ 1 := by
        have hsub := Nat.dvd_sub hgep1 hge
        simpa using hsub
      exact Nat.dvd_trans hg1 ⟨3, by simp⟩
  · have hmapr := constant_D_event_map (Nat.le_trans (by simp) hr3)
      hstep.2.2.2.2.2.1
    rw [if_neg (by simp [hro])] at hmapr
    have heC : d r ∣ C + 1 := by
      rw [hmapr]
      exact Nat.gcd_dvd_right _ _
    rcases Nat.mod_two_eq_zero_or_one u with hue | huo
    · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
      rw [if_pos hue] at hmapu
      have hfC : d u ∣ C' - 1 := by
        rw [hmapu]
        exact Nat.gcd_dvd_right _ _
      have hgA : g ∣ C + 1 := Nat.dvd_trans hge heC
      have hgB : g ∣ C' - 1 := Nat.dvd_trans hgf hfC
      have hd3 : 3 ≤ d r := by
        rcases one_or_three_le_of_mod_two_eq_one heodd with h1 | h3
        · have : (1 : Nat) < 1 := by simpa [h1] using hstep.2.2.2.1
          exact False.elim (Nat.lt_irrefl 1 this)
        · exact h3
      have hminus3 : d r - 1 = (d r - 3) + 2 := by
        apply (Nat.sub_eq_iff_eq_add hepos).2
        calc
          d r = (d r - 3) + 3 := (Nat.sub_add_cancel hd3).symm
          _ = (d r - 3) + 2 + 1 := by simp [Nat.add_assoc]
      have hform : C' - 1 = (C + 1) + (d r - 3) := by
        rw [hupdate]
        have hsumpos : 1 ≤ C + (d r - 1) :=
          Nat.le_trans hCpos (Nat.le_add_right C (d r - 1))
        apply (Nat.sub_eq_iff_eq_add hsumpos).2
        calc
          C + (d r - 1) = C + ((d r - 3) + 2) := by rw [hminus3]
          _ = (C + 1) + (d r - 3) + 1 := by
            calc
              C + ((d r - 3) + 2) = (C + (d r - 3)) + 2 := by
                simp [Nat.add_assoc]
              _ = (C + (d r - 3)) + (1 + 1) := by simp
              _ = (C + 1) + (d r - 3) + 1 := by
                calc
                  (C + (d r - 3)) + (1 + 1) =
                      ((C + (d r - 3)) + 1) + 1 := by rw [Nat.add_assoc]
                  _ = ((C + 1) + (d r - 3)) + 1 := by
                    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hgem3 : g ∣ d r - 3 := by
        have hsub := Nat.dvd_sub hgB hgA
        rw [hform] at hsub
        simpa using hsub
      have hg3 : g ∣ 3 := by
        have hsub := Nat.dvd_sub hge hgem3
        rw [Nat.sub_sub_self (Nat.le_trans (by simp) hd3)] at hsub
        exact hsub
      exact hg3
    · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
      rw [if_neg (by simp [huo])] at hmapu
      have hfC : d u ∣ C' + 1 := by
        rw [hmapu]
        exact Nat.gcd_dvd_right _ _
      have hgA : g ∣ C + 1 := Nat.dvd_trans hge heC
      have hgB : g ∣ C' + 1 := Nat.dvd_trans hgf hfC
      have hform : C' + 1 = (C + 1) + (d r - 1) := by
        rw [hupdate]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hgem1 : g ∣ d r - 1 := by
        have hsub := Nat.dvd_sub hgB hgA
        rw [hform] at hsub
        simpa using hsub
      have hg1 : g ∣ 1 := by
        have hsub := Nat.dvd_sub hge hgem1
        rw [Nat.sub_sub_self hepos] at hsub
        exact hsub
      exact Nat.dvd_trans hg1 ⟨3, by simp⟩

theorem moving_horizon_excess_transition {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (B r + 2) + (r - s) + 1 = (B s + 2) + d r := by
  have htrans := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩
  have hscoord := moving_horizon_slack_coordinate hs
  have hrcoord := moving_horizon_slack_coordinate hrstate
  have hdpos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  calc
    (B r + 2) + (r - s) + 1 = ((C' - r) + 2 + 2) + (r - s) + 1 := by
      rw [hrcoord]
    _ = ((C' - r) + (r - s)) + 5 := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = ((C - s) + (d r - 1)) + 5 := by rw [htrans]
    _ = (C - s) + d r + 4 := by
      have hfive : d r - 1 + 5 = d r + 4 := by
        calc
          d r - 1 + 5 = (d r - 1 + 1) + 4 := by simp [Nat.add_assoc]
          _ = d r + 4 := by rw [Nat.sub_add_cancel hdpos]
      calc
        (C - s) + (d r - 1) + 5 = (C - s) + (d r - 1 + 5) := by
          simp [Nat.add_assoc]
        _ = (C - s) + (d r + 4) := by rw [hfive]
        _ = (C - s) + d r + 4 := by simp [Nat.add_assoc]
    _ = (B s + 2) + d r := by
      rw [hscoord]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem moving_horizon_excess_coordinates {P X s C r C' X' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hXs : B s + 2 = 2 * P + X)
    (hXr : B r + 2 = 2 * P + X') :
    X' + (r - s) + 1 = X + d r := by
  have h := moving_horizon_excess_transition hstep
  rw [hXs, hXr] at h
  have hcancel : (2 * P + X') + ((r - s) + 1) =
      (2 * P + X) + d r := by
    simpa [Nat.add_assoc] using h
  have hcancel' : 2 * P + (X' + (r - s) + 1) =
      2 * P + (X + d r) := by
    simpa [Nat.add_assoc] using hcancel
  exact Nat.add_left_cancel hcancel'

theorem moving_horizon_normalized_close_old_excess
    {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P)
    (hclose : r - s ≤ d r + 2) :
    B r + 2 = 2 * P + (d r + 3 - (r - s)) := by
  have hXs : B s + 2 = 2 * P + 4 := by
    rw [moving_horizon_slack_coordinate hstep.1, hnorm]
  have htrans := moving_horizon_excess_transition hstep
  rw [hXs] at htrans
  have htbound : r - s ≤ d r + 3 := Nat.le_trans hclose (by simp)
  have hsum : (d r + 3 - (r - s)) + (r - s) = d r + 3 :=
    Nat.sub_add_cancel htbound
  have hright : (B r + 2) + (r - s) = 2 * P + (d r + 3) := by
    have hplus : (B r + 2) + (r - s) + 1 =
        (2 * P + (d r + 3)) + 1 := by
      calc
        (B r + 2) + (r - s) + 1 = 2 * P + 4 + d r := htrans
        _ = (2 * P + (d r + 3)) + 1 := by
          calc
            2 * P + 4 + d r = 2 * P + (d r + 4) := by
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            _ = 2 * P + (d r + 3 + 1) := by
              simp [Nat.add_assoc]
            _ = (2 * P + (d r + 3)) + 1 := by
              simp [Nat.add_assoc]
    exact Nat.add_right_cancel hplus
  apply Nat.add_right_cancel (m := r - s)
  calc
    (B r + 2) + (r - s) = 2 * P + (d r + 3) := hright
    _ = (2 * P + (d r + 3 - (r - s))) + (r - s) := by
      rw [← hsum]
      simp [Nat.add_assoc]

theorem moving_horizon_regenerated_record_quotient_transition
    {P s C r C' c c' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcanon_s : s = P * c) (hcanon_C : C = P * (c + 2))
    (hnew : P < d r)
    (hregen : r = d r * c' ∧ c' % 2 = 0 ∧ 2 ≤ c' ∧
      C' = d r * (c' + 2)) :
    r - s + d r + 1 = 2 * P ∧
      d r * (c' + 1) + 1 = P * (c + 2) ∧ c' ≤ c := by
  rcases hregen with ⟨hr, hcmod, hc2, hC'⟩
  have hnorm : C - s = 2 * P := by
    rw [hcanon_C, hcanon_s]
    calc
      P * (c + 2) - P * c = P * ((c + 2) - c) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
      _ = 2 * P := by simp [Nat.mul_comm]
  have hepos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  have hr' : d r * c' = r := hr.symm
  have hCminus : C' - r = 2 * d r := by
    calc
      C' - r = d r * (c' + 2) - d r * c' := by rw [hC', hr']
      _ = d r * ((c' + 2) - c') :=
        (Nat.mul_sub_left_distrib _ _ _).symm
      _ = 2 * d r := by simp [Nat.mul_comm]
  have htrans := moving_horizon_slack_transition hstep
  rw [hCminus, hnorm] at htrans
  have htime : r - s + d r + 1 = 2 * P := by
    have hplus := congrArg (fun n : Nat => n + 1) htrans
    have hcancel : (r - s + d r + 1) + d r =
        2 * P + d r := by
      calc
        (r - s + d r + 1) + d r = (2 * d r + (r - s)) + 1 := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul]
        _ = (2 * P + (d r - 1)) + 1 := hplus
        _ = 2 * P + d r := by
          rw [Nat.add_assoc, Nat.sub_add_cancel hepos]
    exact Nat.add_right_cancel hcancel
  have hupdate := moving_horizon_step_update hstep
  rw [hC', hcanon_C] at hupdate
  have hquot : d r * (c' + 1) + 1 = P * (c + 2) := by
    have hplus := congrArg (fun n : Nat => n + 1) hupdate
    have hcancel : (d r * (c' + 1) + 1) + d r =
        P * (c + 2) + d r := by
      calc
        (d r * (c' + 1) + 1) + d r = d r * (c' + 2) + 1 := by
          calc
            (d r * (c' + 1) + 1) + d r =
                d r * (c' + 1) + (1 + d r) := by simp [Nat.add_assoc]
            _ = d r * (c' + 1) + (d r + 1) := by rw [Nat.add_comm 1]
            _ = (d r * (c' + 1) + d r * 1) + 1 := by
              simpa only [Nat.mul_one] using
                (Nat.add_assoc (d r * (c' + 1)) (d r) 1).symm
            _ = d r * ((c' + 1) + 1) + 1 := by
              exact congrArg (fun n : Nat => n + 1)
                (Nat.mul_add (d r) (c' + 1) 1).symm
            _ = d r * (c' + 2) + 1 := by simp [Nat.add_assoc]
        _ = (P * (c + 2) + (d r - 1)) + 1 := hplus
        _ = P * (c + 2) + d r := by
          rw [Nat.add_assoc, Nat.sub_add_cancel hepos]
    exact Nat.add_right_cancel hcancel
  have hcp : c' ≤ c := by
    by_cases hcp : c' ≤ c
    · exact hcp
    · have hcpgt : c + 1 ≤ c' := Nat.succ_le_of_lt (Nat.lt_of_not_ge hcp)
      have hcpplus : c + 2 ≤ c' + 1 := by
        exact Nat.add_le_add_right hcpgt 1
      have hcpos : 0 < c + 2 := by simp
      have hmul : P * (c + 2) < d r * (c' + 1) := by
        calc
          P * (c + 2) < d r * (c + 2) :=
            (Nat.mul_lt_mul_right hcpos).2 hnew
          _ ≤ d r * (c' + 1) := Nat.mul_le_mul_left _ hcpplus
      have hlt : P * (c + 2) < P * (c + 2) := by
        calc
          P * (c + 2) < d r * (c' + 1) := hmul
          _ < d r * (c' + 1) + 1 := Nat.lt_succ_self _
          _ = P * (c + 2) := hquot
      exact False.elim (Nat.lt_irrefl _ hlt)
  exact ⟨htime, hquot, hcp⟩

theorem moving_horizon_same_quotient_plateau
    {P e c : Nat} (hPpos : 1 ≤ P) (hnew : P < e)
    (hquot : e * (c + 1) + 1 = P * (c + 2)) :
    P - 1 = (e - P) * (c + 1) := by
  have heP : P ≤ e := Nat.le_of_lt hnew
  have hdiff : e = P + (e - P) := by
    calc
      e = (e - P) + P := (Nat.sub_add_cancel heP).symm
      _ = P + (e - P) := Nat.add_comm _ _
  have hEq : (P + (e - P)) * (c + 1) + 1 = P * (c + 2) := by
    rw [← hdiff, hquot]
  have hcancel : P * (c + 1) + ((e - P) * (c + 1) + 1) =
      P * (c + 1) + P := by
    calc
      P * (c + 1) + ((e - P) * (c + 1) + 1) =
          (P + (e - P)) * (c + 1) + 1 := by
            calc
              P * (c + 1) + ((e - P) * (c + 1) + 1) =
                  (P * (c + 1) + (e - P) * (c + 1)) + 1 := by
                    simp [Nat.add_assoc]
              _ = (P + (e - P)) * (c + 1) + 1 := by
                rw [Nat.add_mul]
      _ = P * (c + 2) := hEq
      _ = P * (c + 1) + P := by
        calc
          P * (c + 2) = P * ((c + 1) + 1) := by simp [Nat.add_assoc]
          _ = P * (c + 1) + P * 1 := Nat.mul_add _ _ _
          _ = P * (c + 1) + P := by simp
  have : (e - P) * (c + 1) + 1 = P := Nat.add_left_cancel hcancel
  exact (Nat.sub_eq_iff_eq_add hPpos).2 this.symm

theorem moving_horizon_successive_event_gcd_eq_one_of_prev_even
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') (hre : r % 2 = 0) :
    Nat.gcd (d r) (d u) = 1 := by
  have hupdate := moving_horizon_step_update hstep
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have hu3 : 3 ≤ u := by
    exact Nat.le_trans (Nat.succ_le_succ hnext.1.1)
      (Nat.succ_le_of_lt hnext.2.1)
  let g := Nat.gcd (d r) (d u)
  have hge : g ∣ d r := Nat.gcd_dvd_left _ _
  have hgf : g ∣ d u := Nat.gcd_dvd_right _ _
  have hC2 : 2 ≤ C := by
    rw [← hstep.1.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hstep.1.1
  have hCpos : 1 ≤ C := Nat.le_trans (by simp) hC2
  have hepos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  have hmapr := constant_D_event_map (Nat.le_trans (by simp) hr3)
      hstep.2.2.2.2.2.1
  rw [if_pos hre] at hmapr
  have heC : d r ∣ C - 1 := by
    rw [hmapr]
    exact Nat.gcd_dvd_right _ _
  rcases Nat.mod_two_eq_zero_or_one u with hue | huo
  · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
    rw [if_pos hue] at hmapu
    have hfC : d u ∣ C' - 1 := by
      rw [hmapu]
      exact Nat.gcd_dvd_right _ _
    have hgA : g ∣ C - 1 := Nat.dvd_trans hge heC
    have hgB : g ∣ C' - 1 := Nat.dvd_trans hgf hfC
    have hform : C' - 1 = (C - 1) + (d r - 1) := by
      rw [hupdate]
      have hsumpos : 1 ≤ C + (d r - 1) :=
        Nat.le_trans hCpos (Nat.le_add_right C (d r - 1))
      apply (Nat.sub_eq_iff_eq_add hsumpos).2
      rw [show C = (C - 1) + 1 by exact (Nat.sub_add_cancel hCpos).symm]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hgem1 : g ∣ d r - 1 := by
      have hsub := Nat.dvd_sub hgB hgA
      rw [hform] at hsub
      simpa using hsub
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hge hgem1
      rw [Nat.sub_sub_self hepos] at hsub
      exact hsub
    exact Nat.eq_one_of_dvd_one hg1
  · have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
        hnext.2.2.2.2.2.1
    rw [if_neg (by simp [huo])] at hmapu
    have hfC : d u ∣ C' + 1 := by
      rw [hmapu]
      exact Nat.gcd_dvd_right _ _
    have hgA : g ∣ C - 1 := Nat.dvd_trans hge heC
    have hgB : g ∣ C' + 1 := Nat.dvd_trans hgf hfC
    have honeplus : 1 + (d r - 1) + 1 = d r + 1 := by
      calc
        1 + (d r - 1) + 1 = (d r - 1 + 1) + 1 := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = d r + 1 := by rw [Nat.sub_add_cancel hepos]
    have hform : C' + 1 = (C - 1) + (d r + 1) := by
      rw [hupdate]
      calc
        C + (d r - 1) + 1 = (C - 1) + (1 + (d r - 1) + 1) := by
          rw [show C = (C - 1) + 1 by exact (Nat.sub_add_cancel hCpos).symm]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (C - 1) + (d r + 1) := by rw [honeplus]
    have hgep1 : g ∣ d r + 1 := by
      have hsub := Nat.dvd_sub hgB hgA
      rw [hform] at hsub
      simpa using hsub
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hgep1 hge
      simpa using hsub
    exact Nat.eq_one_of_dvd_one hg1

theorem moving_horizon_successive_event_gcd_eq_one_of_odd_odd
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (hro : r % 2 = 1) (huo : u % 2 = 1) :
    Nat.gcd (d r) (d u) = 1 := by
  have hupdate := moving_horizon_step_update hstep
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have hu3 : 3 ≤ u := by
    exact Nat.le_trans (Nat.succ_le_succ hnext.1.1)
      (Nat.succ_le_of_lt hnext.2.1)
  have heodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  let g := Nat.gcd (d r) (d u)
  have hge : g ∣ d r := Nat.gcd_dvd_left _ _
  have hgf : g ∣ d u := Nat.gcd_dvd_right _ _
  have hC2 : 2 ≤ C := by
    rw [← hstep.1.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hstep.1.1
  have hCpos : 1 ≤ C := Nat.le_trans (by simp) hC2
  have hepos : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  have hmapr := constant_D_event_map (Nat.le_trans (by simp) hr3)
      hstep.2.2.2.2.2.1
  rw [if_neg (by simp [hro])] at hmapr
  have heC : d r ∣ C + 1 := by
    rw [hmapr]
    exact Nat.gcd_dvd_right _ _
  have hmapu := constant_D_event_map (Nat.le_trans (by simp) hu3)
      hnext.2.2.2.2.2.1
  rw [if_neg (by simp [huo])] at hmapu
  have hfC : d u ∣ C' + 1 := by
    rw [hmapu]
    exact Nat.gcd_dvd_right _ _
  have hgA : g ∣ C + 1 := Nat.dvd_trans hge heC
  have hgB : g ∣ C' + 1 := Nat.dvd_trans hgf hfC
  have hform : C' + 1 = (C + 1) + (d r - 1) := by
    rw [hupdate]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hgem1 : g ∣ d r - 1 := by
    have hsub := Nat.dvd_sub hgB hgA
    rw [hform] at hsub
    simpa using hsub
  have hg1 : g ∣ 1 := by
    have hsub := Nat.dvd_sub hge hgem1
    rw [Nat.sub_sub_self hepos] at hsub
    exact hsub
  exact Nat.eq_one_of_dvd_one hg1

theorem moving_horizon_successive_event_gcd_eq_one_of_parity
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (h : r % 2 = 0 ∨ (r % 2 = 1 ∧ u % 2 = 1)) :
    Nat.gcd (d r) (d u) = 1 := by
  rcases h with hre | ⟨hro, huo⟩
  · exact moving_horizon_successive_event_gcd_eq_one_of_prev_even hstep hnext hre
  · exact moving_horizon_successive_event_gcd_eq_one_of_odd_odd hstep hnext hro huo

theorem moving_horizon_successive_event_gcd_dvd_three_of_odd_even
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (_hro : r % 2 = 1) (_hue : u % 2 = 0) :
    Nat.gcd (d r) (d u) ∣ 3 := by
  exact moving_horizon_successive_event_gcd_dvd_three hstep hnext

theorem moving_horizon_same_quotient_two_step_dvd
    {P e f c : Nat} (hPpos : 1 ≤ P) (hPe : P < e) (hef : e < f)
    (hquot₁ : e * (c + 1) + 1 = P * (c + 2))
    (hquot₂ : f * (c + 1) + 1 = e * (c + 2)) :
    (c + 1) ^ 2 ∣ P - 1 := by
  have hplateau₁ := moving_horizon_same_quotient_plateau hPpos hPe hquot₁
  have hplateau₂ := moving_horizon_same_quotient_plateau
    (Nat.le_trans hPpos (Nat.le_of_lt hPe)) hef hquot₂
  let k := c + 1
  have hkP : k ∣ P - 1 := by
    refine ⟨e - P, ?_⟩
    simpa [k, Nat.mul_comm] using hplateau₁
  have hke : k ∣ e - 1 := by
    refine ⟨f - e, ?_⟩
    simpa [k, Nat.mul_comm] using hplateau₂
  have hkediff : k ∣ (e - 1) - (P - 1) := Nat.dvd_sub hke hkP
  have hsum : 1 + (P - 1) = P := by
    rw [Nat.add_comm, Nat.sub_add_cancel hPpos]
  have hkediff' : k ∣ e - P := by
    simpa [Nat.sub_sub, hsum] using hkediff
  rcases hkediff' with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    P - 1 = (e - P) * k := hplateau₁
    _ = (k * q) * k := by rw [hq]
    _ = k ^ 2 * q := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem moving_horizon_equal_successive_event_is_three
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (heq : d r = d u) : d r = 3 := by
  have hdiv := moving_horizon_successive_event_gcd_dvd_three hstep hnext
  have hself : Nat.gcd (d r) (d u) = d r := by rw [heq]; exact Nat.gcd_self _
  have hdvd : d r ∣ 3 := by rw [hself] at hdiv; exact hdiv
  have hdodd := d_mod_two_eq_one_of_three_le
    (Nat.le_trans (Nat.succ_le_succ hstep.1.1) (Nat.succ_le_of_lt hstep.2.1))
  have hdpos : 1 < d r := hstep.2.2.2.1
  rcases one_or_three_le_of_mod_two_eq_one hdodd with hd1 | hd3
  · exact False.elim ((Nat.not_lt_of_ge (by simpa [hd1] using hdpos)) hdpos)
  · have hdle : d r ≤ 3 := Nat.le_of_dvd (by simp) hdvd
    exact Nat.le_antisymm hdle hd3

theorem moving_horizon_no_three_equal_successive_events
    {s C r C' u C'' v C''' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (hlast : IsMovingHorizonStep u C'' v C''')
    (heq1 : d r = d u) (heq2 : d u = d v) : False := by
  rcases Nat.mod_two_eq_zero_or_one r with hre | hro
  · have hg := moving_horizon_successive_event_gcd_eq_one_of_prev_even
      hstep hnext hre
    have hself : Nat.gcd (d r) (d u) = d r := by rw [heq1]; exact Nat.gcd_self _
    have : d r = 1 := by rw [hself] at hg; exact hg
    exact Nat.not_lt_of_ge (by simp [this]) hstep.2.2.2.1
  · rcases Nat.mod_two_eq_zero_or_one u with hue | huo
    · have hg := moving_horizon_successive_event_gcd_eq_one_of_prev_even
        hnext hlast hue
      have hself : Nat.gcd (d u) (d v) = d u := by rw [heq2]; exact Nat.gcd_self _
      have : d u = 1 := by rw [hself] at hg; exact hg
      exact Nat.not_lt_of_ge (by simp [this]) hnext.2.2.2.1
    · have hg := moving_horizon_successive_event_gcd_eq_one_of_odd_odd
        hstep hnext hro huo
      have hself : Nat.gcd (d r) (d u) = d r := by rw [heq1]; exact Nat.gcd_self _
      have : d r = 1 := by rw [hself] at hg; exact hg
      exact Nat.not_lt_of_ge (by simp [this]) hstep.2.2.2.1

theorem moving_horizon_close_chain_excess_telescope
    {P s C X E T q : Nat}
    (hchain : HasMovingHorizonCloseChain P s C X E T q) :
    ∃ sf Cf Xf, IsMovingHorizonState sf Cf ∧
      B sf + 2 = 2 * P + Xf ∧ Xf + T = X + E := by
  induction q generalizing s C X E T with
  | zero =>
      rcases hchain with ⟨hs, hXs, hE, hT⟩
      subst E
      subst T
      exact ⟨s, C, X, hs, hXs, by simp⟩
  | succ q ih =>
      rcases hchain with ⟨r, C', X', E', T', hstep, hold, hclose,
        hXs, hXr, hE, hT, htail⟩
      rcases ih htail with ⟨sf, Cf, Xf, hsf, hXf, htailEq⟩
      have hlocal := moving_horizon_excess_coordinates hstep hXs hXr
      refine ⟨sf, Cf, Xf, hsf, hXf, ?_⟩
      rw [hE, hT]
      have hlocal' : X' + (r - s + 1) = X + d r := by
        simpa [Nat.add_assoc] using hlocal
      calc
        Xf + (T' + (r - s + 1)) =
            (Xf + T') + (r - s + 1) := by simp [Nat.add_assoc]
        _ = (X' + E') + (r - s + 1) := by rw [htailEq]
        _ = X' + (r - s + 1) + E' := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (X + d r) + E' := by rw [hlocal']
        _ = X + (E' + d r) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem moving_horizon_close_chain_preserves_maximum
    {P s C X E T q : Nat}
    (hP : IsAttainedPreviousMaximum P s)
    (hchain : HasMovingHorizonCloseChain P s C X E T q) :
    ∃ sf Cf Xf, IsMovingHorizonState sf Cf ∧
      IsAttainedPreviousMaximum P sf ∧ B sf + 2 = 2 * P + Xf ∧
      Xf + T = X + E := by
  induction q generalizing s C X E T with
  | zero =>
      rcases hchain with ⟨hs, hXs, hE, hT⟩
      subst E
      subst T
      exact ⟨s, C, X, hs, hP, hXs, by simp⟩
  | succ q ih =>
      rcases hchain with ⟨r, C', X', E', T', hstep, hold, hclose,
        hXs, hXr, hE, hT, htail⟩
      rcases hstep with ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩
      have hmax := moving_horizon_max_transfer hP hsr hdr hfirst
      have hPr : IsAttainedPreviousMaximum P r := by
        rcases hmax with ⟨_, hPr⟩ | hnew
        · exact hPr
        · exact False.elim ((Nat.not_lt_of_ge hold) hnew.1)
      rcases ih hPr htail with ⟨sf, Cf, Xf, hsf, hPsf, hXf, htailEq⟩
      refine ⟨sf, Cf, Xf, hsf, hPsf, hXf, ?_⟩
      rw [hE, hT]
      have hlocal := moving_horizon_excess_coordinates
        ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩ hXs hXr
      have hlocal' : X' + (r - s + 1) = X + d r := by
        simpa [Nat.add_assoc] using hlocal
      calc
        Xf + (T' + (r - s + 1)) =
            (Xf + T') + (r - s + 1) := by simp [Nat.add_assoc]
        _ = (X' + E') + (r - s + 1) := by rw [htailEq]
        _ = X' + (r - s + 1) + E' := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (X + d r) + E' := by rw [hlocal']
        _ = X + (E' + d r) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem moving_horizon_chain_growth {s C q : Nat}
    (hchain : HasMovingHorizonChain s C q) :
    ∃ sf Cf, IsMovingHorizonState sf Cf ∧ C + 2 * q ≤ Cf := by
  induction q generalizing s C with
  | zero => exact ⟨s, C, hchain, by simp⟩
  | succ q ih =>
      rcases hchain with ⟨r, C', hstep, htail⟩
      rcases hstep with ⟨_, _, _, _, _, _, _, hgrowth, _⟩
      rcases ih htail with ⟨sf, Cf, hsf, htailgrowth⟩
      refine ⟨sf, Cf, hsf, ?_⟩
      calc
        C + 2 * Nat.succ q = (C + 2) + 2 * q := by
          simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
        _ ≤ C' + 2 * q := Nat.add_le_add_right hgrowth _
        _ ≤ Cf := htailgrowth

theorem critical_failure_moving_horizon_state {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    IsMovingHorizonState (k + 1) (D (k + 1)) := by
  have hn : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, _, _, _, hD, _, _⟩
  have hdelta : 0 < d (k + 1) := d_pos_of_two_le hn
  refine ⟨hn, rfl, ?_⟩
  calc
    k + 1 = d (k + 1) * c := hc
    _ < d (k + 1) * (c + 2) := (Nat.mul_lt_mul_left hdelta).2 (by simp)
    _ = D (k + 1) := hD.symm

theorem critical_failure_moving_horizon_dichotomy {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    (∀ j : Nat, k + 1 < j → j ≤ D (k + 1) → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep (k + 1) (D (k + 1)) r C' := by
  exact moving_horizon_dichotomy
    (critical_failure_moving_horizon_state hk hIH hnew hfail)

theorem critical_failure_current_maximum {k P : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k) (hnew : P < d (k + 1)) :
    IsAttainedPreviousMaximum (d (k + 1)) (k + 1) :=
  attained_previous_maximum_extend (Nat.le_trans hk (Nat.le_succ k)) hP hnew

theorem critical_first_event_current_or_new_max {k P r : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k) (hnew : P < d (k + 1))
    (hr : k + 1 < r) (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    (d r ≤ d (k + 1) ∧ IsAttainedPreviousMaximum (d (k + 1)) r) ∨
      (d (k + 1) < d r ∧ IsAttainedPreviousMaximum (d r) r) :=
  moving_horizon_max_transfer
    (critical_failure_current_maximum hk hP hnew) hr hdr hfirst

theorem critical_first_event_transfer {k M C r : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hC : D (k + 1) = C) (hr : k + 1 < r) (hrC : r ≤ C)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    ∃ c : Nat, k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      D (r - 1) = C ∧
      ((r % 2 = 0 ∧ d r ∣ C - 1 ∧ d r < C - 1 ∧
          3 * d r ≤ C - 1 ∧ Nat.gcd (d (k + 1)) (d r) = 1) ∨
        (r % 2 = 1 ∧ d r ∣ C + 1 ∧ d r < C + 1 ∧
          3 * d r ≤ C + 1 ∧ Nat.gcd (d (k + 1)) (d r) = 1)) ∧
      B r + 2 = B (r - 1) + d r ∧
      D r = C + (d r - 1) ∧
      C + 2 ≤ D r ∧
      B (r - 1) + (r - 1) = C + 2 ∧
      B r + r = D r + 2 := by
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, hcmod, hc2, _, hcriticalD, _, _⟩
  have hn : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hDr : D (r - 1) = C :=
    first_later_event_D_eq hn hC hr hfirst
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hk) (Nat.le_of_lt hr)
  have hrpred : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa using hr3
  have hCform : C = d (k + 1) * (c + 2) := hC.symm.trans hcriticalD
  have hDrform : D (r - 1) = d (k + 1) * (c + 2) := hDr.trans hCform
  have hcop : Nat.gcd (d (k + 1)) (d r) = 1 :=
    constant_D_event_coprime_of_critical_form hr3 hDrform
  have hBstep : B r + 2 = B (r - 1) + d r := by
    have h := excess_succ_add_two hrpred
    have hrsucc : r - 1 + 1 = r :=
      Nat.sub_add_cancel (Nat.le_trans (by simp) hr3)
    simpa [hrsucc] using h
  have hDstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    have hrsucc : r - 1 + 1 = r :=
      Nat.sub_add_cancel (Nat.le_trans (by simp) hr3)
    rw [hrsucc, hDr] at h
    exact h
  have hDgrowth : C + 2 ≤ D r := by
    have hrsucc : r - 1 + 1 = r :=
      Nat.sub_add_cancel (Nat.le_trans (by simp) hr3)
    have hdr' : 1 < d (r - 1 + 1) := by simpa [hrsucc] using hdr
    have h := D_add_two_le_succ_of_two_le hrpred hdr'
    rw [hrsucc, hDr] at h
    exact h
  have hBpred : B (r - 1) + (r - 1) = C + 2 := by
    have h := B_add_index_eq_D_add_two hrpred
    rw [hDr] at h
    exact h
  have hBcurr : B r + r = D r + 2 :=
    B_add_index_eq_D_add_two (Nat.le_trans (by simp) hr3)
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_pos heven] at hmap
    have hdiv : d r ∣ C - 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C - 1 :=
      (constant_D_event_even_proper_iff hr3 hDr heven).2
        (constant_D_event_even_not_dvd_of_le hr3 hDr heven hrC hdr)
    have hbound : 3 * d r ≤ C - 1 :=
      constant_D_event_even_size_bound_of_le hr3 hDr heven hrC hdr
    exact ⟨c, hc, hcmod, hc2, hDr,
      Or.inl ⟨heven, hdiv, hproper, hbound, hcop⟩,
      hBstep, hDstep, hDgrowth, hBpred, hBcurr⟩
  · have hoddne : r % 2 ≠ 0 := by simp [hodd]
    have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_neg hoddne] at hmap
    have hdiv : d r ∣ C + 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C + 1 :=
      (constant_D_event_odd_proper_iff hr3 hDr hoddne).2
        (constant_D_event_odd_not_dvd_of_le hr3 hrC)
    have hbound : 3 * d r ≤ C + 1 :=
      constant_D_event_odd_size_bound_of_le hr3 hDr hoddne hrC
    exact ⟨c, hc, hcmod, hc2, hDr,
      Or.inr ⟨hodd, hdiv, hproper, hbound, hcop⟩,
      hBstep, hDstep, hDgrowth, hBpred, hBcurr⟩

theorem critical_first_event_previous_or_new_max
    {k P C r : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hC : D (k + 1) = C) (hr : k + 1 < r) (hrC : r ≤ C)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    d r ≤ P ∨ (P < d r ∧ d r < d (k + 1)) ∨
      IsAttainedPreviousMaximum (d r) r := by
  have hpack := critical_first_event_transfer hk hIH hnew hfail hC hr hrC hdr hfirst
  rcases hpack with ⟨_, _, _, _, _, hparity, _, _, _, _, _⟩
  have hcop : Nat.gcd (d (k + 1)) (d r) = 1 := by
    rcases hparity with ⟨_, _, _, _, hcop⟩ | ⟨_, _, _, _, hcop⟩
    · exact hcop
    · exact hcop
  have hdelta9 : 9 ≤ d (k + 1) :=
    critical_new_increment_lower_bound hk hIH hnew hfail
  have hneq : d r ≠ d (k + 1) := by
    intro heq
    have hdelta1 : d (k + 1) = 1 := by
      rw [heq] at hcop
      simpa using hcop
    have hbad : False := by
      simpa [hdelta1] using hdelta9
    exact hbad.elim
  rcases Nat.lt_or_ge (d r) (d (k + 1)) with hlt | hge
  · rcases Nat.lt_or_ge P (d r) with hgt | hle
    · exact Or.inr (Or.inl ⟨hgt, hlt⟩)
    · exact Or.inl hle
  · have hgt : d (k + 1) < d r :=
      Nat.lt_of_le_of_ne hge (fun h => hneq h.symm)
    have hr2 : 2 ≤ r :=
      Nat.le_trans (Nat.le_trans hk (Nat.le_succ k)) (Nat.le_of_lt hr)
    have hbound : ∀ j : Nat, 2 ≤ j → j ≤ r → d j ≤ d r := by
      intro j hj2 hjr
      by_cases hjk : j ≤ k
      · have hpj := hP.1 j hj2 hjk
        exact Nat.le_trans hpj
          (Nat.le_of_lt (Nat.lt_trans hnew hgt))
      · have hkj : k < j := Nat.lt_of_not_ge hjk
        have hkn : k + 1 ≤ j := Nat.succ_le_of_lt hkj
        by_cases hjeq : j = k + 1
        · simpa [hjeq] using (Nat.le_of_lt hgt)
        · by_cases hjreq : j = r
          · simpa [hjreq]
          · have hnj : k + 1 < j :=
              Nat.lt_of_le_of_ne hkn (fun h => hjeq h.symm)
            have hjrlt : j < r := Nat.lt_of_le_of_ne hjr hjreq
            have hdj : d j = 1 := hfirst j hnj hjrlt
            rw [hdj]
            exact one_le_d_of_two_le hr2
    exact Or.inr (Or.inr ⟨hbound, ⟨r, hr2, Nat.le_refl r, rfl⟩⟩)

theorem critical_failure_no_event_to_fundamental {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hno : ∀ j : Nat, k + 1 < j → j ≤ D (k + 1) → d j = 1) :
    B (D (k + 1)) = 2 ∧ D (D (k + 1)) = D (k + 1) := by
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, _, _, _, hD, _, _⟩
  have hn : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hB := new_max_failure_next_B_eq hk hIH hnew hfail
  have hend : k + 1 + 2 * d (k + 1) = D (k + 1) := by
    calc
      k + 1 + 2 * d (k + 1) = d (k + 1) * c + 2 * d (k + 1) :=
        congrArg (fun x => x + 2 * d (k + 1)) hc
      _ = d (k + 1) * (c + 2) := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      _ = D (k + 1) := hD.symm
  have hone : ∀ j : Nat, k + 1 < j →
      j ≤ k + 1 + 2 * d (k + 1) → d j = 1 := by
    intro j hj hjend
    apply hno j hj
    rw [← hend]
    exact hjend
  have htail := one_interval_const_D_B hn hone
  have hBtail : B (D (k + 1)) + 2 * d (k + 1) = B (k + 1) := by
    calc
      B (D (k + 1)) + 2 * d (k + 1) =
          B (k + 1 + 2 * d (k + 1)) + 2 * d (k + 1) := by rw [hend]
      _ = B (k + 1) := htail.2
  have hBend : B (D (k + 1)) = 2 := by
    have hEq : B (D (k + 1)) + 2 * d (k + 1) =
        2 + 2 * d (k + 1) := by
      calc
        B (D (k + 1)) + 2 * d (k + 1) = B (k + 1) := hBtail
        _ = 2 * d (k + 1) + 2 := hB
        _ = 2 + 2 * d (k + 1) := by simp [Nat.add_comm]
    exact Nat.add_right_cancel hEq
  constructor
  · exact hBend
  · calc
      D (D (k + 1)) = D (k + 1 + 2 * d (k + 1)) := congrArg D hend.symm
      _ = D (k + 1) := htail.1

theorem critical_failure_first_event_dichotomy {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    (B (D (k + 1)) = 2 ∧ D (D (k + 1)) = D (k + 1)) ∨
      ∃ r : Nat, k + 1 < r ∧ r ≤ D (k + 1) ∧ 1 < d r ∧
        ∀ j : Nat, k + 1 < j → j < r → d j = 1 := by
  have hn : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  rcases first_later_nontrivial_dichotomy hn with hno | hevent
  · exact Or.inl (critical_failure_no_event_to_fundamental hk hIH hnew hfail hno)
  · exact Or.inr hevent

theorem last_nontrivial_telescope {rho m : Nat} (hrho : 2 ≤ rho)
    (hbelow : rho < m) (hfund : B m = 2)
    (hone : ∀ j : Nat, rho < j → j ≤ m → d j = 1) :
    ∃ t : Nat, 0 < t ∧ m = rho + t ∧ D m = D rho ∧ B rho = 2 + t := by
  obtain ⟨t, rfl⟩ := Nat.le.dest (Nat.le_of_lt hbelow)
  have htpos : 0 < t := by
    cases t with
    | zero => simp at hbelow
    | succ t => exact Nat.zero_lt_succ t
  have htail := one_interval_const_D_B hrho hone
  refine ⟨t, htpos, rfl, htail.1, ?_⟩
  calc
    B rho = B (rho + t) + t := htail.2.symm
    _ = 2 + t := by rw [hfund]

theorem B_two_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 2) :
    d (k + 1) = 1 ∧ B (k + 1) = 1 := by
  have hk0 : k % 2 = 0 := by
    calc
      k % 2 = B k % 2 := (B_mod_two_of_two_le hk).symm
      _ = 2 % 2 := by rw [hB]
      _ = 0 := by simp
  rcases even_residual_structure hk hk0 with
    ⟨t, ht, htmod, hzero | hbound⟩
  · simp [hB] at hzero
  · have hdle : d (k + 1) ≤ 1 := by
      have hbound' : 2 * d (k + 1) ≤ 2 := by simpa [hB] using hbound
      exact Nat.le_of_mul_le_mul_left hbound' (by simp : 0 < 2)
    have hdpos : 1 ≤ d (k + 1) :=
      one_le_d_of_two_le (Nat.le_trans hk (Nat.le_succ k))
    have hd : d (k + 1) = 1 := Nat.le_antisymm hdle hdpos
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 1 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 2 + 1 := by rw [hB, hd]
        _ = 1 + 2 := by simp
    exact ⟨hd, Nat.add_right_cancel hnext⟩

theorem B_one_transition {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1)
    (hB : B k = 1) :
    (d (k + 1) = 1 ∧ B (k + 1) = 0) ∨
      (d (k + 1) = 3 ∧ B (k + 1) = 2) := by
  have hsmall : B k < 4 := by simpa [hB]
  rcases odd_small_residual_classification hk hk1 hsmall with
    ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
  · left
    refine ⟨hd1, ?_⟩
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 0 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 1 + 1 := by rw [hB, hd1]
        _ = 0 + 2 := by simp
    exact Nat.add_right_cancel hnext
  · right
    refine ⟨hd3, ?_⟩
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 2 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 1 + 3 := by rw [hB, hd3]
        _ = 2 + 2 := by simp
    exact Nat.add_right_cancel hnext
  · have : (3 : Nat) = 1 := by rw [← hB3, hB]
    cases this

theorem B_three_transition {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1)
    (hB : B k = 3) : d (k + 1) = 1 ∧ B (k + 1) = 2 := by
  have hsmall : B k < 4 := by simpa [hB]
  rcases odd_small_residual_classification hk hk1 hsmall with
    ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
  · have : (1 : Nat) = 3 := by rw [← hB1, hB]
    cases this
  · have : (1 : Nat) = 3 := by rw [← hB1, hB]
    cases this
  · refine ⟨hd1, ?_⟩
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 2 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 3 + 1 := by rw [hB, hd1]
        _ = 2 + 2 := by simp
    exact Nat.add_right_cancel hnext

theorem B_zero_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 0) :
    d (k + 1) = k - 1 ∧ B (k + 1) + 2 = k - 1 := by
  have hk0 : k % 2 = 0 := by
    calc
      k % 2 = B k % 2 := (B_mod_two_of_two_le hk).symm
      _ = 0 % 2 := by rw [hB]
      _ = 0 := by simp
  have hd : d (k + 1) = k - 1 := by
    calc
      d (k + 1) = Nat.gcd (k - 1) (B k) :=
        d_succ_eq_gcd_even_residual hk hk0
      _ = Nat.gcd (k - 1) 0 := by rw [hB]
      _ = k - 1 := by simp
  have hstep := excess_succ_add_two hk
  have hnext : B (k + 1) + 2 = k - 1 := by
    calc
      B (k + 1) + 2 = B k + d (k + 1) := hstep
      _ = k - 1 := by rw [hB, hd]; simp
  exact ⟨hd, hnext⟩

theorem odd_failure_fundamental_distance {k M m : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hbelow : k + 1 < m) (hfund : B m = 2)
    (hone : ∀ j : Nat, k + 1 < j → j ≤ m → d j = 1) :
    m = k + 1 + 2 * d (k + 1) := by
  have hstate := new_max_failure_reduction hk hIH hnew hfail
  have hnext : B (k + 1) + 2 = 2 * d (k + 1) + 4 :=
    hstate.2.2.2.1
  have hBnext : B (k + 1) = 2 * d (k + 1) + 2 := by
    have hcancel : B (k + 1) + 2 = (2 * d (k + 1) + 2) + 2 := by
      calc
        B (k + 1) + 2 = 2 * d (k + 1) + 4 := hnext
        _ = (2 * d (k + 1) + 2) + 2 := by simp [Nat.add_assoc]
    exact Nat.add_right_cancel hcancel
  have hrho : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  obtain ⟨t, ht, hm, hD, hBrho⟩ :=
    last_nontrivial_telescope hrho hbelow hfund hone
  have ht_eq : t = 2 * d (k + 1) := by
    have hcancel : 2 + t = 2 + 2 * d (k + 1) := by
      calc
        2 + t = B (k + 1) := hBrho.symm
        _ = 2 * d (k + 1) + 2 := hBnext
        _ = 2 + 2 * d (k + 1) := by simp [Nat.add_comm]
    exact Nat.add_left_cancel hcancel
  simpa [ht_eq] using hm

theorem odd_failure_distance_of_last_nontrivial {k M m : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hrho : IsLastNontrivialBefore (k + 1) m) (hfund : B m = 2) :
    m = k + 1 + 2 * d (k + 1) := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  exact odd_failure_fundamental_distance hk hIH hnew hfail hbelow hfund hone

theorem critical_index_le_last_nontrivial {k m rho : Nat}
    (hcrit : 1 < d (k + 1)) (hbelow : k + 1 < m)
    (hrho : IsLastNontrivialBefore rho m) :
    k + 1 ≤ rho := by
  rcases hrho with ⟨hrho2, hlast, hnontriv, hone⟩
  rcases Nat.lt_or_ge rho (k + 1) with hlt | hge
  · have hd : d (k + 1) = 1 :=
      hone (k + 1) hlt (Nat.le_of_lt hbelow)
    have hfalse : (1 : Nat) < 1 := by simpa [hd] using hcrit
    exact False.elim (Nat.lt_irrefl 1 hfalse)
  · exact hge

theorem odd_failure_distance_or_later_nontrivial {k M m rho : Nat}
    (hk : 2 ≤ k) (hIH : B k + 2 ≤ 2 * M)
    (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hcrit : 1 < d (k + 1)) (hbelow : k + 1 < m)
    (hfund : B m = 2) (hrho : IsLastNontrivialBefore rho m) :
    m = k + 1 + 2 * d (k + 1) ∨ k + 1 < rho := by
  have hle := critical_index_le_last_nontrivial hcrit hbelow hrho
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  · left
    subst rho
    exact odd_failure_distance_of_last_nontrivial hk hIH hnew hfail hrho hfund

theorem exists_last_nontrivial_before {m : Nat} (hm : d m = 1)
    (hex : ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q) :
    ∃ rho : Nat, IsLastNontrivialBefore rho m := by
  revert hm hex
  induction m with
  | zero =>
      intro _ hex
      rcases hex with ⟨q, _, hq, _⟩
      exact False.elim (Nat.not_lt_zero q hq)
  | succ m ih =>
      intro hm hex
      by_cases hmone : d m = 1
      · by_cases hpred : ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q
        · rcases ih hmone hpred with ⟨rho, hrho⟩
          rcases hrho with ⟨hrho2, hlt, hlarge, htail⟩
          refine ⟨rho, hrho2, Nat.lt_trans hlt (Nat.lt_succ_self m), hlarge, ?_⟩
          intro j hj hjle
          rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
          · exact htail j hj (Nat.le_of_lt_succ hjlt)
          · simpa [hjeq] using hm
        · rcases hex with ⟨q, hq2, hqle, hqd⟩
          have hqle' : q ≤ m := Nat.le_of_lt_succ hqle
          have hqm : q = m := by
            rcases Nat.lt_or_eq_of_le hqle' with hqmt | hqeq
            · exact False.elim (hpred ⟨q, hq2, hqmt, hqd⟩)
            · exact hqeq
          subst q
          refine ⟨m, hq2, Nat.lt_succ_self m, hqd, ?_⟩
          intro j hj hjle
          rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
          · have hjm : j ≤ m := Nat.le_of_lt_succ hjlt
            exact False.elim ((Nat.not_lt_of_ge hjm) hj)
          · simpa [hjeq] using hm
      · rcases hex with ⟨q, hq2, hqle, _⟩
        have hqle' : q ≤ m := Nat.le_of_lt_succ hqle
        have hm2 : 2 ≤ m := Nat.le_trans hq2 hqle'
        have hdmpos : 1 ≤ d m := one_le_d_of_two_le hm2
        have hdmgt : 1 < d m :=
          Nat.lt_of_le_of_ne hdmpos (fun h => hmone h.symm)
        refine ⟨m, hm2, Nat.lt_succ_self m, hdmgt, ?_⟩
        intro j hj hjle
        rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
        · have hjm : j ≤ m := Nat.le_of_lt_succ hjlt
          exact False.elim ((Nat.not_lt_of_ge hjm) hj)
        · simpa [hjeq] using hm

theorem exists_last_nontrivial_before_iff {m : Nat} :
    (∃ rho : Nat, IsLastNontrivialBefore rho m) ↔
      (d m = 1 ∧ ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q) := by
  constructor
  · rintro ⟨rho, ⟨hrho2, hbelow, hlarge, htail⟩⟩
    refine ⟨htail m hbelow (Nat.le_refl m), ⟨rho, hrho2, hbelow, hlarge⟩⟩
  · rintro ⟨hm, hex⟩
    exact exists_last_nontrivial_before hm hex

theorem last_nontrivial_before_unique {rho sigma m : Nat}
    (hrho : IsLastNontrivialBefore rho m)
    (hsigma : IsLastNontrivialBefore sigma m) :
    rho = sigma := by
  rcases hrho with ⟨hrho2, hrl, hrlarge, hrtail⟩
  rcases hsigma with ⟨hsigma2, hsl, hslarge, hstail⟩
  rcases Nat.lt_or_ge rho sigma with hlt | hge
  · have hdsigma : d sigma = 1 :=
      hrtail sigma hlt (Nat.le_of_lt hsl)
    have : (1 : Nat) < 1 := by simpa [hdsigma] using hslarge
    exact False.elim (Nat.lt_irrefl 1 this)
  · rcases Nat.lt_or_eq_of_le hge with hlt | heq
    · have hdrho : d rho = 1 := hstail rho hlt (Nat.le_of_lt hrl)
      have : (1 : Nat) < 1 := by simpa [hdrho] using hrlarge
      exact False.elim (Nat.lt_irrefl 1 this)
    · exact heq.symm

theorem rho_bound_iff_B_bound {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    3 * rho ≤ 2 * m ↔ m + 6 ≤ 3 * B rho := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  obtain ⟨t, ht, hm, hD, hBrho⟩ :=
    last_nontrivial_telescope hrho2 hbelow hfund hone
  have hrt_iff : rho ≤ 2 * t ↔ m + 6 ≤ 3 * B rho := by
    rw [hm, hBrho]
    constructor
    · intro hrt
      have hsum : rho + t ≤ 3 * t := by
        calc
          rho + t ≤ 2 * t + t := Nat.add_le_add_right hrt t
          _ = 3 * t := by simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
      calc
        rho + t + 6 = 6 + (rho + t) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ 6 + 3 * t := Nat.add_le_add_left hsum 6
        _ = 3 * (2 + t) := by
          rw [Nat.mul_add]
    · intro hbound
      have hsum : rho + t ≤ 3 * t := by
        apply Nat.le_of_add_le_add_left
        calc
          6 + (rho + t) = rho + t + 6 := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ ≤ 3 * (2 + t) := hbound
          _ = 6 + 3 * t := by
            rw [Nat.mul_add]
      have hrt : rho ≤ 2 * t := by
        apply Nat.le_of_add_le_add_right
        calc
          rho + t ≤ 3 * t := hsum
          _ = 2 * t + t := by
            simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
      exact hrt
  constructor
  · intro hleft
    apply hrt_iff.1
    apply Nat.le_of_add_le_add_left
    calc
      2 * rho + rho = 3 * rho := by simp [Nat.succ_mul, Nat.add_assoc]
      _ ≤ 2 * m := hleft
      _ = 2 * rho + 2 * t := by rw [hm, Nat.mul_add]
  · intro hright
    have hrt : rho ≤ 2 * t := hrt_iff.2 hright
    calc
      3 * rho = 2 * rho + rho := by simp [Nat.succ_mul, Nat.add_assoc]
      _ ≤ 2 * rho + 2 * t := Nat.add_le_add_left hrt (2 * rho)
      _ = 2 * (rho + t) := by simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 * m := by rw [hm]

theorem last_nontrivial_telescope_addition {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    B rho + rho = m + 2 := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  obtain ⟨t, ht, hm, hD, hBrho⟩ :=
    last_nontrivial_telescope hrho2 hbelow hfund hone
  calc
    B rho + rho = (2 + t) + rho := by rw [hBrho]
    _ = (rho + t) + 2 := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = m + 2 := by rw [← hm]

theorem last_nontrivial_B_bounds {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    3 ≤ B rho ∧ B rho ≤ m := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  obtain ⟨t, ht, hm, hD, hBrho⟩ :=
    last_nontrivial_telescope hrho2 hbelow hfund hone
  have ht1 : 1 ≤ t := ht
  constructor
  · calc
      3 = 2 + 1 := by simp
      _ ≤ 2 + t := Nat.add_le_add_left ht1 2
      _ = B rho := hBrho.symm
  · calc
      B rho = 2 + t := hBrho
      _ ≤ rho + t := Nat.add_le_add_right hrho2 t
      _ = m := hm.symm

theorem critical_later_strict_transport {k M m rho : Nat}
    (hk : 2 ≤ k) (hIH : B k + 2 ≤ 2 * M)
    (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hlater : k + 1 < rho)
    (hrho : IsLastNontrivialBefore rho m) :
    2 * d (k + 1) + k + 3 < B rho + rho := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  have hkplus : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hpred : k + 1 ≤ rho - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using Nat.succ_le_of_lt hlater
  have hrho1 : 1 ≤ rho :=
    Nat.le_trans (by simp) (Nat.le_of_lt hlater)
  have hDle : D (k + 1) ≤ D (rho - 1) := D_le_of_le hpred
  have hDstrict : D (rho - 1) < D rho := by
    have hnontriv' : 1 < d (rho - 1 + 1) := by
      rw [Nat.sub_add_cancel hrho1]
      exact hnontriv
    have h := D_lt_succ_of_one_lt_d (n := rho - 1) hnontriv'
    rw [Nat.sub_add_cancel hrho1] at h
    exact h
  have hDlt : D (k + 1) < D rho := Nat.lt_of_le_of_lt hDle hDstrict
  have hsum : B (k + 1) + (k + 1) < B rho + rho := by
    calc
      B (k + 1) + (k + 1) = D (k + 1) + 2 :=
        B_add_index_eq_D_add_two hkplus
      _ < D rho + 2 := Nat.add_lt_add_right hDlt 2
      _ = B rho + rho := (B_add_index_eq_D_add_two hrho2).symm
  have hBnext := new_max_failure_next_B_eq hk hIH hnew hfail
  calc
    2 * d (k + 1) + k + 3 = B (k + 1) + (k + 1) := by
      rw [hBnext]
      change 2 * d (k + 1) + k + (1 + 2) =
        (2 * d (k + 1) + 2) + (k + 1)
      calc
        2 * d (k + 1) + k + (1 + 2) =
            2 * d (k + 1) + (k + (1 + 2)) := by rw [Nat.add_assoc]
        _ = 2 * d (k + 1) + ((k + 1) + 2) := by simp [Nat.add_assoc]
        _ = 2 * d (k + 1) + (2 + (k + 1)) := by
          rw [Nat.add_comm (k + 1) 2]
        _ = (2 * d (k + 1) + 2) + (k + 1) :=
          (Nat.add_assoc _ _ _).symm
    _ < B rho + rho := hsum

theorem critical_later_distance_strict {k M m rho : Nat}
    (hk : 2 ≤ k) (hIH : B k + 2 ≤ 2 * M)
    (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (_hbelow : k + 1 < m) (hfund : B m = 2)
    (hrho : IsLastNontrivialBefore rho m) (hlater : k + 1 < rho) :
    k + 1 + 2 * d (k + 1) < m := by
  have hstrict := critical_later_strict_transport hk hIH hnew hfail hlater hrho
  have htelescope := last_nontrivial_telescope_addition hrho hfund
  rw [htelescope] at hstrict
  have hadd : (k + 1 + 2 * d (k + 1)) + 2 < m + 2 := by
    calc
      (k + 1 + 2 * d (k + 1)) + 2 =
          2 * d (k + 1) + k + 3 := by
        calc
          (k + 1 + 2 * d (k + 1)) + 2 =
              2 * d (k + 1) + (k + (1 + 2)) := by
                calc
                  (k + 1 + 2 * d (k + 1)) + 2 =
                      (k + 1) + (2 * d (k + 1) + 2) :=
                    Nat.add_assoc _ _ _
                  _ = (k + 1) + (2 + 2 * d (k + 1)) := by
                    rw [Nat.add_comm (2 * d (k + 1)) 2]
                  _ = (k + 1 + 2) + 2 * d (k + 1) :=
                    (Nat.add_assoc _ _ _).symm
                  _ = 2 * d (k + 1) + (k + 1 + 2) :=
                    Nat.add_comm _ _
                  _ = 2 * d (k + 1) + (k + (1 + 2)) := by
                    rw [Nat.add_assoc]
          _ = 2 * d (k + 1) + k + 3 := by simp [Nat.add_assoc]
      _ < m + 2 := hstrict
  exact Nat.add_lt_add_iff_right.mp hadd

theorem later_nontrivial_residual_transport {k m rho : Nat}
    (hk : 2 ≤ k) (hlater : k + 1 < rho)
    (hrho : IsLastNontrivialBefore rho m) :
    3 ≤ d rho ∧ B rho + 2 = B (rho - 1) + d rho ∧
      ((rho % 2 = 0 ∧
          ((B (rho - 1) = 1 ∧ d rho = 3) ∨
            (4 ≤ B (rho - 1) ∧
              ∃ t : Nat, B (rho - 1) - 4 = d rho * t ∧
                t % 2 = 1 ∧ d rho + 4 ≤ B (rho - 1)))) ∨
        (rho % 2 = 1 ∧
          ∃ t : Nat, B (rho - 1) = d rho * t ∧
            t % 2 = 0 ∧
            (B (rho - 1) = 0 ∨ 2 * d rho ≤ B (rho - 1)))) := by
  rcases hrho with ⟨hrho2, hbelow, hnontriv, hone⟩
  have hrho4 : 4 ≤ rho := by
    have hstep : k + 2 ≤ rho := Nat.succ_le_of_lt hlater
    have hk2 : 4 ≤ k + 2 := by
      simpa [Nat.add_assoc] using Nat.add_le_add_right hk 2
    exact Nat.le_trans hk2 hstep
  have hrho3 : 3 ≤ rho := Nat.le_trans (by simp) hrho4
  have hpred : 2 ≤ rho - 1 := by
    apply Nat.le_sub_of_add_le
    simpa using hrho3
  have hpred_succ : rho - 1 + 1 = rho :=
    Nat.sub_add_cancel (Nat.le_trans (by simp) hrho3)
  have hstep : B rho + 2 = B (rho - 1) + d rho := by
    have h := excess_succ_add_two hpred
    simpa [hpred_succ] using h
  have hodd : d rho % 2 = 1 := d_mod_two_eq_one_of_three_le hrho3
  have hd3 : 3 ≤ d rho := by
    rcases one_or_three_le_of_mod_two_eq_one hodd with hd1 | hd3
    · have hfalse : (1 : Nat) < 1 := by simpa [hd1] using hnontriv
      exact False.elim (Nat.lt_irrefl 1 hfalse)
    · exact hd3
  rcases Nat.mod_two_eq_zero_or_one rho with hrho0 | hrho1
  · have hpred1 : (rho - 1) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (rho - 1) with hpred0 | hpred1
      · have hbad : (rho - 1 + 1) % 2 = 1 := by
          simp [Nat.add_mod, hpred0]
        rw [hpred_succ, hrho0] at hbad
        simp at hbad
      · exact hpred1
    by_cases hB4 : 4 ≤ B (rho - 1)
    · rcases odd_residual_structure hpred hpred1 hB4 with
        ⟨t, ht, htmod, hlower⟩
      rw [hpred_succ] at ht hlower
      exact ⟨hd3, hstep, Or.inl ⟨hrho0, Or.inr ⟨hB4, t, ht, htmod, by
        exact hlower⟩⟩⟩
    · rcases odd_small_residual_classification hpred hpred1
        (Nat.lt_of_not_ge hB4) with
        ⟨hB1, hd1 | hd3'⟩ | ⟨hB3, hd1⟩
      · have hfalse : (1 : Nat) < 1 := by
          have hd1rho : d rho = 1 := by simpa [hpred_succ] using hd1
          simpa [hd1rho] using hnontriv
        exact False.elim (Nat.lt_irrefl 1 hfalse)
      · exact ⟨hd3, hstep, Or.inl ⟨hrho0, Or.inl ⟨hB1, by
          simpa [hpred_succ] using hd3'⟩⟩⟩
      · have hfalse : (1 : Nat) < 1 := by
          have hd1rho : d rho = 1 := by simpa [hpred_succ] using hd1
          simpa [hd1rho] using hnontriv
        exact False.elim (Nat.lt_irrefl 1 hfalse)
  · have hpred0 : (rho - 1) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (rho - 1) with hpred0 | hpred1
      · exact hpred0
      · have hbad : (rho - 1 + 1) % 2 = 0 := by
          simp [Nat.add_mod, hpred1]
        rw [hpred_succ, hrho1] at hbad
        simp at hbad
    rcases even_residual_structure hpred hpred0 with
      ⟨t, ht, htmod, hbound⟩
    rw [hpred_succ] at ht hbound
    exact ⟨hd3, hstep, Or.inr ⟨hrho1, t, ht, htmod, by
      rcases hbound with hzero | hbound
      · exact Or.inl hzero
      · exact Or.inr hbound⟩⟩

theorem critical_intermediate_even_quotient_eq_three
    {delta M e t q : Nat}
    (hdeltaodd : delta % 2 = 1) (heodd : e % 2 = 1)
    (hMe : M < e) (hEd : e < delta)
    (hbound : delta + 6 ≤ 2 * M) (hclose : t ≤ e + 2)
    (hform : 2 * delta = t + 1 + e * q)
    (hqodd : q % 2 = 1) : q = 3 := by
  have hgap : e + 2 ≤ delta := by omega
  have hqle : q < 5 := by
    by_cases hq5 : 5 ≤ q
    · have hdelta2e : delta < 2 * e := by omega
      have h2delta5e : 2 * delta < 5 * e := by omega
      have h5eq : 5 * e ≤ e * q := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left e hq5
      have heqle : e * q ≤ 2 * delta := by omega
      have h5le : 5 * e ≤ 2 * delta := Nat.le_trans h5eq heqle
      exact False.elim ((Nat.not_lt_of_ge h5le) h2delta5e)
    · exact Nat.lt_of_not_ge hq5
  rcases one_or_three_le_of_mod_two_eq_one hqodd with hqone | hqthree
  · simp [hqone] at hform
    omega
  · omega

theorem critical_intermediate_odd_quotient_eq_two
    {delta M e t q : Nat}
    (hMe : M < e) (hbound : delta + 6 ≤ 2 * M)
    (hform : 2 * delta + 3 = t + e * q)
    (hqeven : q % 2 = 0) (hq2 : 2 ≤ q) : q = 2 := by
  have hqle : q < 4 := by
    by_cases hq4 : 4 ≤ q
    · have hdelta2e : delta + 6 < 2 * e := by omega
      have h4e : 4 * e ≤ e * q := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left e hq4
      have heqle : e * q ≤ 2 * delta + 3 := by omega
      have h4le : 4 * e ≤ 2 * delta + 3 := Nat.le_trans h4e heqle
      have hdelta4e : 2 * delta + 3 < 4 * e := by omega
      exact False.elim ((Nat.not_lt_of_ge h4le) hdelta4e)
    · exact Nat.lt_of_not_ge hq4
  omega

theorem moving_horizon_first_hit_map {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r = Nat.gcd r (C - 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) ∨
      (r % 2 = 1 ∧ d r = Nat.gcd (r - 2) (C + 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  have hunit : ∀ j : Nat, s < j → j < r →
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    intro j hsj hjr
    have hj2 : 2 ≤ j := Nat.le_trans hs.1 (Nat.le_of_lt hsj)
    have hfirstj : ∀ l : Nat, s < l → l < j → d l = 1 := by
      intro l hsl hlj
      exact hfirst l hsl (Nat.lt_trans hlj hjr)
    have hDj : D (j - 1) = C :=
      first_later_event_D_eq hs.1 hs.2.1 hsj hfirstj
    have hjmap := constant_D_event_map hj2 hDj
    have hdj : d j = 1 := hfirst j hsj hjr
    constructor
    · intro hevenj
      rw [if_pos hevenj] at hjmap
      rw [hjmap] at hdj
      exact hdj
    · intro hoddj
      have hjne : j % 2 ≠ 0 := by simp [hoddj]
      rw [if_neg hjne] at hjmap
      rw [hjmap] at hdj
      exact hdj
  by_cases heven : r % 2 = 0
  · left
    rw [if_pos heven] at hmap
    exact ⟨heven, hmap, hdr, hunit⟩
  · right
    have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact False.elim (heven hzero)
      · exact hone
    rw [if_neg heven] at hmap
    exact ⟨hodd, hmap, hdr, hunit⟩

theorem moving_horizon_same_parity_event_drift
    {s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' e : Nat}
    (hstep₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁')
    (hstep₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (he₁ : d r₁ = e) (he₂ : d r₂ = e)
    (hpar : r₁ % 2 = r₂ % 2) :
    e ∣ r₂ - r₁ ∧ e ∣ C₂ - C₁ := by
  rcases hstep₁ with ⟨hs₁, hs₁r, hr₁C, hdr₁, hfirst₁, hD₁, hC₁', hg₁, hstate₁⟩
  rcases hstep₂ with ⟨hs₂, hs₂r, hr₂C, hdr₂, hfirst₂, hD₂, hC₂', hg₂, hstate₂⟩
  have hr₁3 : 3 ≤ r₁ := by
    exact Nat.le_trans (Nat.succ_le_succ hs₁.1) (Nat.succ_le_of_lt hs₁r)
  have hr₂3 : 3 ≤ r₂ := by
    exact Nat.le_trans (Nat.succ_le_succ hs₂.1) (Nat.succ_le_of_lt hs₂r)
  rcases Nat.mod_two_eq_zero_or_one r₁ with h₁even | h₁odd
  · have h₂even : r₂ % 2 = 0 := by simpa [hpar] using h₁even
    have hmap₁ := constant_D_event_map (Nat.le_trans (by simp) hr₁3) hD₁
    have hmap₂ := constant_D_event_map (Nat.le_trans (by simp) hr₂3) hD₂
    rw [if_pos h₁even] at hmap₁
    rw [if_pos h₂even] at hmap₂
    have hdivr₁ : e ∣ r₁ := by
      rw [← he₁, hmap₁]
      exact Nat.gcd_dvd_left _ _
    have hdivr₂ : e ∣ r₂ := by
      rw [← he₂, hmap₂]
      exact Nat.gcd_dvd_left _ _
    have hdivC₁ : e ∣ C₁ - 1 := by
      rw [← he₁, hmap₁]
      exact Nat.gcd_dvd_right _ _
    have hdivC₂ : e ∣ C₂ - 1 := by
      rw [← he₂, hmap₂]
      exact Nat.gcd_dvd_right _ _
    have hdiffR := Nat.dvd_sub hdivr₂ hdivr₁
    have hdiffC := Nat.dvd_sub hdivC₂ hdivC₁
    have hC₁pos : 1 ≤ C₁ := by
      rw [← hs₁.2.1]
      have hD1 : 1 ≤ D 1 := by simp [D, a]
      exact Nat.le_trans hD1
        (D_le_of_le (Nat.le_trans (by simp) hs₁.1))
    have hsumC : 1 + (C₁ - 1) = C₁ := by
      rw [Nat.add_comm, Nat.sub_add_cancel hC₁pos]
    constructor
    · exact hdiffR
    · simpa [Nat.sub_sub, hsumC] using hdiffC
  · have h₂odd : r₂ % 2 = 1 := by simpa [hpar] using h₁odd
    have hmap₁ := constant_D_event_map (Nat.le_trans (by simp) hr₁3) hD₁
    have hmap₂ := constant_D_event_map (Nat.le_trans (by simp) hr₂3) hD₂
    rw [if_neg (by simp [h₁odd])] at hmap₁
    rw [if_neg (by simp [h₂odd])] at hmap₂
    have hdivr₁ : e ∣ r₁ - 2 := by
      rw [← he₁, hmap₁]
      exact Nat.gcd_dvd_left _ _
    have hdivr₂ : e ∣ r₂ - 2 := by
      rw [← he₂, hmap₂]
      exact Nat.gcd_dvd_left _ _
    have hdivC₁ : e ∣ C₁ + 1 := by
      rw [← he₁, hmap₁]
      exact Nat.gcd_dvd_right _ _
    have hdivC₂ : e ∣ C₂ + 1 := by
      rw [← he₂, hmap₂]
      exact Nat.gcd_dvd_right _ _
    have hdiffR := Nat.dvd_sub hdivr₂ hdivr₁
    have hdiffC := Nat.dvd_sub hdivC₂ hdivC₁
    have hr₁2 : 2 ≤ r₁ := Nat.le_trans hs₁.1 (Nat.le_of_lt hs₁r)
    have hdiffCeq : (C₂ + 1) - (C₁ + 1) = C₂ - C₁ := by omega
    have hshift : 2 + (r₁ - 2) = r₁ := by
      rw [Nat.add_comm, Nat.sub_add_cancel hr₁2]
    constructor
    · simpa [Nat.sub_sub, hshift] using hdiffR
    · rw [hdiffCeq] at hdiffC
      exact hdiffC

theorem moving_horizon_no_two_event_drift_cycle {e₁ e₂ : Nat}
    (he₁ : 3 ≤ e₁) (he₂ : 3 ≤ e₂)
    (h₁ : e₁ ∣ e₁ + e₂ - 2) (h₂ : e₂ ∣ e₁ + e₂ - 2) : False := by
  have hd₁ := Nat.dvd_sub h₁ (Nat.dvd_refl e₁)
  have hd₂ := Nat.dvd_sub h₂ (Nat.dvd_refl e₂)
  have hEq₁ : e₁ + e₂ - 2 - e₁ = e₂ - 2 := by omega
  have hEq₂ : e₁ + e₂ - 2 - e₂ = e₁ - 2 := by omega
  rw [hEq₁] at hd₁
  rw [hEq₂] at hd₂
  rcases Nat.le_total e₁ e₂ with hle | hle
  · have hlt : e₁ - 2 < e₂ := by omega
    have hz : e₁ - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hd₂ hlt
    omega
  · have hlt : e₂ - 2 < e₁ := by omega
    have hz : e₂ - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hd₁ hlt
    omega

theorem moving_horizon_no_repeated_two_event_block
    {s₀ C₀ r₁ C₁ r₂ C₂ r₃ C₃ r₄ C₄ e₁ e₂ : Nat}
    (hstep₁ : IsMovingHorizonStep s₀ C₀ r₁ C₁)
    (hstep₂ : IsMovingHorizonStep r₁ C₁ r₂ C₂)
    (hstep₃ : IsMovingHorizonStep r₂ C₂ r₃ C₃)
    (hstep₄ : IsMovingHorizonStep r₃ C₃ r₄ C₄)
    (he₁ : d r₁ = e₁) (he₂ : d r₂ = e₂)
    (he₃ : d r₃ = e₁) (he₄ : d r₄ = e₂)
    (hp₁ : r₁ % 2 = r₃ % 2) (hp₂ : r₂ % 2 = r₄ % 2) : False := by
  have hu₁ := moving_horizon_step_update hstep₁
  have hu₂ := moving_horizon_step_update hstep₂
  have hu₃ := moving_horizon_step_update hstep₃
  rw [he₁] at hu₁
  rw [he₂] at hu₂
  rw [he₃] at hu₃
  have hC₀₂ : C₂ - C₀ = (e₁ - 1) + (e₂ - 1) := by
    rw [hu₂, hu₁]
    omega
  have hC₁₃ : C₃ - C₁ = (e₁ - 1) + (e₂ - 1) := by
    rw [hu₃, hu₂]
    omega
  have hdr₁₃ := moving_horizon_same_parity_event_drift
    hstep₁ hstep₃ he₁ he₃ hp₁
  have hdr₂₄ := moving_horizon_same_parity_event_drift
    hstep₂ hstep₄ he₂ he₄ hp₂
  have hdiv₁ : e₁ ∣ (e₁ - 1) + (e₂ - 1) := by
    rw [← hC₀₂]
    exact hdr₁₃.2
  have hdiv₂ : e₂ ∣ (e₁ - 1) + (e₂ - 1) := by
    rw [← hC₁₃]
    exact hdr₂₄.2
  have he₁pos : 1 ≤ e₁ := by
    rw [← he₁]
    exact one_le_d_of_two_le (Nat.le_trans hstep₁.1.1 (Nat.le_of_lt hstep₁.2.1))
  have he₂pos : 1 ≤ e₂ := by
    rw [← he₂]
    exact one_le_d_of_two_le (Nat.le_trans hstep₂.1.1 (Nat.le_of_lt hstep₂.2.1))
  have hsum : (e₁ - 1) + (e₂ - 1) = e₁ + e₂ - 2 := by omega
  rw [hsum] at hdiv₁ hdiv₂
  have he₁odd : e₁ % 2 = 1 := by
    rw [← he₁]
    exact d_mod_two_eq_one_of_three_le
      (Nat.le_trans (Nat.succ_le_succ hstep₁.1.1)
        (Nat.succ_le_of_lt hstep₁.2.1))
  have he₂odd : e₂ % 2 = 1 := by
    rw [← he₂]
    exact d_mod_two_eq_one_of_three_le
      (Nat.le_trans (Nat.succ_le_succ hstep₂.1.1)
        (Nat.succ_le_of_lt hstep₂.2.1))
  have he₁min : 3 ≤ e₁ := by
    have hgt : 1 < e₁ := by simpa [he₁] using hstep₁.2.2.2.1
    rcases one_or_three_le_of_mod_two_eq_one he₁odd with h | h
    · omega
    · exact h
  have he₂min : 3 ≤ e₂ := by
    have hgt : 1 < e₂ := by simpa [he₂] using hstep₂.2.2.2.1
    rcases one_or_three_le_of_mod_two_eq_one he₂odd with h | h
    · omega
    · exact h
  exact moving_horizon_no_two_event_drift_cycle he₁min he₂min hdiv₁ hdiv₂

theorem moving_horizon_small_excess_new_max
    {P X s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hP : IsAttainedPreviousMaximum P s) (hP5 : 5 < P)
    (hXs : B s + 2 = 2 * P + X) (hX : X ≤ 5)
    (hnew : P < d r) :
    ∃ c : Nat, r = d r * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      IsAttainedPreviousMaximum (d r) r ∧
      C' = d r * (c + 2) ∧ D r = d r * (c + 2) := by
  have hPodd : P % 2 = 1 :=
    attained_previous_maximum_value_mod_two_eq_one hP hP5
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have heodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hcoord := moving_horizon_slack_coordinate hstep.1
  have hL : C - s + 4 = 2 * P + X := by
    calc
      C - s + 4 = B s + 2 := by rw [hcoord]
      _ = 2 * P + X := hXs
  rcases Nat.mod_two_eq_zero_or_one r with hreven | hrodd
  · have hqpack := moving_horizon_even_quotient_normal_form hstep hreven
    rcases hqpack with ⟨q, hqform, hqmod, _, hqnext⟩
    have hq : q = 1 := by
      rcases one_or_three_le_of_mod_two_eq_one hqmod with hqone | hqthree
      · exact hqone
      · have hmul : 3 * d r ≤ d r * q := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d r) hqthree
        exfalso
        omega
    have hnext : C' - r = 2 * d r := by
      simpa [hq, Nat.mul_comm] using hqnext
    have hfirst : ∀ j : Nat, s < j → j < r → d j = 1 :=
      hstep.2.2.2.2.1
    have hmax := moving_horizon_max_transfer hP hstep.2.1
      hstep.2.2.2.1 hfirst
    have hnewhist : IsAttainedPreviousMaximum (d r) r := by
      rcases hmax with h | h
      · exact False.elim ((Nat.not_le_of_gt hnew) h.1)
      · exact h.2
    rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, hrstate⟩
    have hdivr : d r ∣ r := by
      have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
      rw [if_pos hreven] at hmap
      rw [hmap]
      exact Nat.gcd_dvd_left _ _
    rcases hdivr with ⟨c, hc⟩
    have hcmod : c % 2 = 0 := by
      calc
        c % 2 = (d r * c) % 2 := quotient_mod_two_of_left_odd heodd
        _ = r % 2 := congrArg (fun x : Nat => x % 2) hc.symm
        _ = 0 := hreven
    have hcpos : 0 < c := by
      cases c with
      | zero =>
          have hrzero : r = 0 := by simpa using hc
          omega
      | succ c => exact Nat.zero_lt_succ c
    have hc2 : 2 ≤ c := two_le_of_pos_of_mod_two_eq_zero hcpos hcmod
    have hrleC' : r ≤ C' := Nat.le_of_lt hrstate.2.2
    have hsum : (C' - r) + r = C' := Nat.sub_add_cancel hrleC'
    have hCeq : C' = d r * (c + 2) := by
      calc
        C' = (C' - r) + r := hsum.symm
        _ = 2 * d r + r := by rw [hnext]
        _ = 2 * d r + d r * c := congrArg (fun x : Nat => 2 * d r + x) hc
        _ = d r * (c + 2) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.mul_comm]
    exact ⟨c, hc, hcmod, hc2, hnewhist, hCeq, hC'.symm.trans hCeq⟩
  · have hqpack := moving_horizon_odd_quotient_normal_form hstep hrodd
    rcases hqpack with ⟨q, hqform, hqmod, hq2, _⟩
    have hmul : 2 * d r ≤ d r * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d r) hq2
    have hPe2 : P + 2 ≤ d r := by omega
    have htpos : 1 ≤ r - s := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_comm] using Nat.succ_le_of_lt hstep.2.1
    have hEq : (r - s) + d r * q + 1 = 2 * P + X := by
      calc
        (r - s) + d r * q + 1 = (C - s + 3) + 1 := by rw [hqform]
        _ = C - s + 4 := by omega
        _ = 2 * P + X := hL
    exfalso
    omega

theorem moving_horizon_same_quotient_plateau_power
    {P c q : Nat} (hPpos : 1 ≤ P)
    (hchain : HasSameQuotientRegenerationChain P c q) :
    (c + 1) ^ q ∣ P - 1 := by
  induction q generalizing P with
  | zero => exact ⟨P - 1, by simp⟩
  | succ q ih =>
      rcases hchain with ⟨e, hPe, hquot, htail⟩
      have hepos : 1 ≤ e := Nat.le_trans hPpos (Nat.le_of_lt hPe)
      have hrel : (e - 1) * (c + 1) = (P - 1) * (c + 2) := by
        have heq : e * (c + 1) = P * (c + 2) - 1 :=
          Nat.eq_sub_of_add_eq hquot
        rw [Nat.sub_mul, Nat.sub_mul, heq]
        have hck : 1 + (c + 1) = c + 2 := by omega
        simp [Nat.sub_sub, hck]
      have hpow : (c + 1) ^ q ∣ e - 1 := ih hepos htail
      have hpowmul : (c + 1) ^ (q + 1) ∣ (e - 1) * (c + 1) := by
        rcases hpow with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        rw [Nat.pow_succ]
        calc
          (e - 1) * (c + 1) = ((c + 1) ^ q * z) * (c + 1) := by rw [hz]
          _ = (c + 1) ^ q * (c + 1) * z := by
            simp [Nat.mul_comm, Nat.mul_left_comm]
      have hcop0 : Nat.Coprime (c + 1) (c + 2) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        calc
          Nat.gcd (c + 1) (c + 2) = Nat.gcd (c + 1) 1 := by
            rw [show c + 2 = 1 + (c + 1) by omega]
            exact Nat.gcd_add_self_right _ _
          _ = 1 := Nat.gcd_one_right _
      have hcop : Nat.Coprime ((c + 1) ^ (q + 1)) (c + 2) :=
        hcop0.pow_left _
      have hdiv : (c + 1) ^ (q + 1) ∣ (P - 1) * (c + 2) := by
        rw [← hrel]
        exact hpowmul
      exact hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_comm] using hdiv)

end A166944Research
