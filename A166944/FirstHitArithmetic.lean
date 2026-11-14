import A166944.Lemmas

namespace A166944Research

/-!
# Lane F: divisor / gap arithmetic and composite-event slack

All statements below are kernel-checked against `A166944/Lemmas.lean` (Lean core only,
no Mathlib).  They are the reusable first-hit arithmetic toolkit proposed by lane F.
-/

theorem mod_two_add_two_mul_eq_self (r p : Nat) (_hp : 2 * p ≤ r) :
    ((r - 2 * p) + 2 * p) % 2 = (r - 2 * p) % 2 := by
  rw [Nat.add_mod, Nat.mul_mod]
  simp

theorem mod_two_sub_two_mul_of_even {r p : Nat} (h : r % 2 = 0) (hp : 2 * p ≤ r) :
    (r - 2 * p) % 2 = 0 := by
  have hsum : (r - 2 * p) + 2 * p = r := Nat.sub_add_cancel hp
  have hcongr : r % 2 = ((r - 2 * p) + 2 * p) % 2 :=
    congrArg (fun x => x % 2) hsum.symm
  have hfin : r % 2 = (r - 2 * p) % 2 :=
    hcongr.trans (mod_two_add_two_mul_eq_self r p hp)
  rw [h] at hfin
  exact hfin.symm

theorem mod_two_sub_two_mul_of_odd {r p : Nat} (h : r % 2 = 1) (hp : 2 * p ≤ r) :
    (r - 2 * p) % 2 = 1 := by
  have hsum : (r - 2 * p) + 2 * p = r := Nat.sub_add_cancel hp
  have hcongr : r % 2 = ((r - 2 * p) + 2 * p) % 2 :=
    congrArg (fun x => x % 2) hsum.symm
  have hfin : r % 2 = (r - 2 * p) % 2 :=
    hcongr.trans (mod_two_add_two_mul_eq_self r p hp)
  rw [h] at hfin
  exact hfin.symm

theorem moving_horizon_event_divisor_gap {s C r C' p : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hp2 : 2 ≤ p) (hpdvd : p ∣ d r) :
    r - s ≤ 2 * p := by
  have hspos : 2 ≤ s := hstep.1.1
  have hsr : s < r := hstep.2.1
  have hrC : r ≤ C := hstep.2.2.1
  rcases moving_horizon_first_hit_map hstep with h | h
  · obtain ⟨hre, hmap, hdr, hsieve⟩ := h
    by_cases hle : r - s ≤ 2 * p
    · exact hle
    · have hlt : 2 * p < r - s := Nat.lt_of_not_ge hle
      have hpr : 2 * p ≤ r := by omega
      have hps : s < r - 2 * p := by omega
      have hplt : r - 2 * p < r := by omega
      have hpeven : (r - 2 * p) % 2 = 0 := mod_two_sub_two_mul_of_even hre hpr
      have hgone : Nat.gcd (r - 2 * p) (C - 1) = 1 := (hsieve (r - 2 * p) hps hplt).1 hpeven
      have hpdivr : p ∣ r := Nat.dvd_trans hpdvd (by rw [hmap]; exact Nat.gcd_dvd_left _ _)
      have hpdivC : p ∣ C - 1 :=
        Nat.dvd_trans hpdvd (by rw [hmap]; exact Nat.gcd_dvd_right _ _)
      have hpdiv2p : p ∣ 2 * p := ⟨2, by rw [Nat.mul_comm]⟩
      have hpdivsub : p ∣ r - 2 * p := Nat.dvd_sub hpdivr hpdiv2p
      have hpdivgcd : p ∣ Nat.gcd (r - 2 * p) (C - 1) := Nat.dvd_gcd hpdivsub hpdivC
      rw [hgone] at hpdivgcd
      have hple1 : p ≤ 1 := Nat.le_of_dvd (by simp) hpdivgcd
      omega
  · obtain ⟨hro, hmap, hdr, hsieve⟩ := h
    by_cases hle : r - s ≤ 2 * p
    · exact hle
    · have hlt : 2 * p < r - s := Nat.lt_of_not_ge hle
      have hpr : 2 * p ≤ r := by omega
      have hps : s < r - 2 * p := by omega
      have hplt : r - 2 * p < r := by omega
      have hpodd : (r - 2 * p) % 2 = 1 := mod_two_sub_two_mul_of_odd hro hpr
      have hgone : Nat.gcd (r - 2 * p - 2) (C + 1) = 1 := (hsieve (r - 2 * p) hps hplt).2 hpodd
      have hpdivr2 : p ∣ r - 2 :=
        Nat.dvd_trans hpdvd (by rw [hmap]; exact Nat.gcd_dvd_left _ _)
      have hpdivC : p ∣ C + 1 :=
        Nat.dvd_trans hpdvd (by rw [hmap]; exact Nat.gcd_dvd_right _ _)
      have hpdiv2p : p ∣ 2 * p := ⟨2, by rw [Nat.mul_comm]⟩
      have hpdivsub : p ∣ r - 2 - 2 * p := Nat.dvd_sub hpdivr2 hpdiv2p
      have harg : r - 2 * p - 2 = r - 2 - 2 * p := by omega
      have hpdivgcd : p ∣ Nat.gcd (r - 2 * p - 2) (C + 1) := by
        rw [harg]
        exact Nat.dvd_gcd hpdivsub hpdivC
      rw [hgone] at hpdivgcd
      have hple1 : p ≤ 1 := Nat.le_of_dvd (by simp) hpdivgcd
      omega

theorem exists_small_divisor_of_composite {e : Nat}
    (h : ∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ e = a * b) :
    ∃ p : Nat, 2 ≤ p ∧ p ∣ e ∧ p * p ≤ e := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  rcases Nat.le_total a b with hab | hba
  · refine ⟨a, ha, ⟨b, rfl⟩, ?_⟩
    exact Nat.mul_le_mul_left a hab
  · refine ⟨b, hb, ⟨a, by rw [Nat.mul_comm]⟩, ?_⟩
    calc
      b * b ≤ b * a := Nat.mul_le_mul_left b hba
      _ = a * b := by rw [Nat.mul_comm]

theorem two_mul_two_mul_sq (p : Nat) : (2 * p) * (2 * p) = 4 * (p * p) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm p 2 p, ← Nat.mul_assoc, ← Nat.mul_assoc]

theorem moving_horizon_composite_event_gap_sq {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C') (he : d r = e)
    (hcomp : ∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ e = a * b) :
    (r - s) * (r - s) ≤ 4 * e := by
  obtain ⟨p, hp2, hpdvd, hpsq⟩ := exists_small_divisor_of_composite hcomp
  have hgap : r - s ≤ 2 * p :=
    moving_horizon_event_divisor_gap hstep hp2 (by rw [he]; exact hpdvd)
  calc
    (r - s) * (r - s) ≤ (2 * p) * (2 * p) := Nat.mul_le_mul hgap hgap
    _ = 4 * (p * p) := two_mul_two_mul_sq p
    _ ≤ 4 * e := Nat.mul_le_mul_left 4 hpsq

theorem moving_horizon_step_size_add_two_le_slack_of_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    d r + 2 ≤ C - s := by
  obtain ⟨q, hL, hqmod, hq1, hL'⟩ := moving_horizon_even_quotient_normal_form hstep heven
  have hdist : 1 ≤ r - s := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using Nat.succ_le_of_lt hstep.2.1
  have hmul : d r * 1 ≤ d r * q := Nat.mul_le_mul_left (d r) hq1
  omega

theorem moving_horizon_step_size_add_one_le_slack_of_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    d r + 1 ≤ C - s := by
  obtain ⟨q, hL, hqmod, hq2, hL'⟩ := moving_horizon_odd_quotient_normal_form hstep hodd
  have hdist : 1 ≤ r - s := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using Nat.succ_le_of_lt hstep.2.1
  have hdr3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hmul : d r * 2 ≤ d r * q := Nat.mul_le_mul_left (d r) hq2
  omega

theorem moving_horizon_step_size_lt_slack {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    d r < C - s := by
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · have h := moving_horizon_step_size_add_two_le_slack_of_even hstep heven
    omega
  · have h := moving_horizon_step_size_add_one_le_slack_of_odd hstep hodd
    omega

#print axioms moving_horizon_event_divisor_gap
#print axioms moving_horizon_composite_event_gap_sq
#print axioms moving_horizon_step_size_lt_slack

end A166944Research
