import A166944.TravelFactors

/-!
# Index and horizon residues at repeated uses of a factor

The parity of an event fixes both coordinates modulo twice any
nonunit factor of the increment. Two uses constrain the elapsed
index distance and horizon growth simultaneously.
-/

namespace A166944Research

private theorem mod_twice_factor_of_dvd {p n : Nat} (hp : p % 2 = 1) (h : p ∣ n) :
    n % (2 * p) = p * (n % 2) := by
  obtain ⟨k, rfl⟩ := h
  have hk : (p * k) % 2 = k % 2 := by
    rw [Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod]
  rw [hk, Nat.mul_comm 2 p, Nat.mul_mod_mul_left]

/-- At an even hit the residues are `(0, p+1)`. At an odd hit they
are `(p+2, p-1)`, in index and pre-event horizon order. -/
theorem moving_horizon_factor_event_residues {s C r C' p : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hp : 2 < p) (hdiv : p ∣ d r) :
    (r % 2 = 0 ∧ r % (2 * p) = 0 ∧ C % (2 * p) = p + 1) ∨
      (r % 2 = 1 ∧ r % (2 * p) = p + 2 ∧ C % (2 * p) = p - 1) := by
  have hr : 3 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
  have hCpos : 1 ≤ C := by have := hstep.1.2.2; omega
  have hCe : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hodd : p % 2 = 1 := by
    have hd := d_mod_two_eq_one_of_three_le hr
    obtain ⟨k, hk⟩ := hdiv
    rw [hk, Nat.mul_mod] at hd
    by_cases hz : p % 2 = 0
    · simp [hz] at hd
    · omega
  have h1 : 1 % (2 * p) = 1 := Nat.mod_eq_of_lt (by omega)
  rcases Nat.mod_two_eq_zero_or_one r with he | ho
  · obtain ⟨hdr, hdC⟩ := moving_horizon_event_divisibility_even hstep rfl he
    have hrmod := mod_twice_factor_of_dvd hodd (Nat.dvd_trans hdiv hdr)
    rw [he, Nat.mul_zero] at hrmod
    have hCterm := mod_twice_factor_of_dvd hodd (Nat.dvd_trans hdiv hdC)
    rw [show (C - 1) % 2 = 1 by omega, Nat.mul_one] at hCterm
    refine Or.inl ⟨he, hrmod, ?_⟩
    rw [show C = C - 1 + 1 by omega, Nat.add_mod, hCterm, h1]
    exact Nat.mod_eq_of_lt (by omega)
  · obtain ⟨hdr, hdC⟩ := moving_horizon_event_divisibility_odd hstep rfl ho
    have hrterm := mod_twice_factor_of_dvd hodd (Nat.dvd_trans hdiv hdr)
    rw [show (r - 2) % 2 = 1 by omega, Nat.mul_one] at hrterm
    have hrmod : r % (2 * p) = p + 2 := by
      rw [show r = r - 2 + 2 by omega, Nat.add_mod, hrterm, Nat.mod_eq_of_lt (by omega : 2 < 2 * p)]
      exact Nat.mod_eq_of_lt (by omega)
    have hCterm := mod_twice_factor_of_dvd hodd (Nat.dvd_trans hdiv hdC)
    rw [show (C + 1) % 2 = 1 by omega, Nat.mul_one] at hCterm
    have hsum := Nat.mod_add_mod_eq (a := C) (b := 1) (c := 2 * p)
    rw [hCterm, h1] at hsum
    have hlt := Nat.mod_lt C (by omega : 0 < 2 * p)
    refine Or.inr ⟨ho, hrmod, ?_⟩
    by_cases h : C % (2 * p) + 1 < 2 * p
    · rw [if_pos h] at hsum
      omega
    · rw [if_neg h] at hsum
      omega

private theorem mod_sub_of_residue_sum {x y m a b t : Nat}
    (hm : 0 < m) (hxy : x ≤ y) (hx : x % m = a) (hy : y % m = b)
    (ht : t < m) (hadd : (a + t) % m = b) : (y - x) % m = t := by
  let k := m - x % m
  have hxlt := Nat.mod_lt x hm
  have hzero : (x + k) % m = 0 := by
    rw [← Nat.mod_add_mod x m k, show x % m + k = m by omega, Nat.mod_self]
  have heq : (x + t) % m = y % m := by
    rw [← Nat.mod_add_mod x m t, hx, hadd, hy]
  have h := Nat.add_mod_eq_add_mod_right k heq
  have hl : (x + t + k) % m = t := by
    rw [show x + t + k = (x + k) + t by omega, ← Nat.mod_add_mod (x + k) m t,
      hzero, Nat.zero_add, Nat.mod_eq_of_lt ht]
  have hr : (y + k) % m = (y - x) % m := by
    rw [show y + k = (x + k) + (y - x) by omega, ← Nat.mod_add_mod (x + k) m (y - x),
      hzero, Nat.zero_add]
  rw [hl, hr] at h
  exact h.symm

theorem moving_horizon_factor_reuse_drift_residues {s C r C' t H u H' p : Nat}
    (hfirst : IsMovingHorizonStep s C r C') (hlater : IsMovingHorizonStep t H u H')
    (horder : r ≤ t) (hp : 2 < p) (hdiv : p ∣ d r) (hdivLater : p ∣ d u) :
    (r % 2 = u % 2 ∧ (2 * p) ∣ u - r ∧ (2 * p) ∣ H - C) ∨
      (r % 2 = 0 ∧ u % 2 = 1 ∧ (u - r) % (2 * p) = p + 2 ∧ (H - C) % (2 * p) = 2 * p - 2) ∨
      (r % 2 = 1 ∧ u % 2 = 0 ∧ (u - r) % (2 * p) = p - 2 ∧ (H - C) % (2 * p) = 2) := by
  have hru : r ≤ u := Nat.le_trans horder (Nat.le_of_lt hlater.2.1)
  have hCH := D_le_of_le (Nat.le_trans (Nat.le_of_lt hfirst.2.1) horder)
  rw [hfirst.1.2.1, hlater.1.2.1] at hCH
  have hm : 0 < 2 * p := by omega
  have same {x y : Nat} (hxy : x ≤ y) (h : x % (2 * p) = y % (2 * p)) : (2 * p) ∣ y - x := by
    apply Nat.dvd_of_mod_eq_zero
    exact mod_sub_of_residue_sum hm hxy rfl h.symm hm (by simp)
  rcases moving_horizon_factor_event_residues hfirst hp hdiv with ⟨hr, hrm, hCm⟩ | ⟨hr, hrm, hCm⟩
  · rcases moving_horizon_factor_event_residues hlater hp hdivLater with ⟨hu, hum, hHm⟩ | ⟨hu, hum, hHm⟩
    · exact Or.inl ⟨hr.trans hu.symm, same hru (hrm.trans hum.symm), same hCH (hCm.trans hHm.symm)⟩
    · refine Or.inr (Or.inl ⟨hr, hu, ?_, ?_⟩)
      · exact mod_sub_of_residue_sum hm hru hrm hum (by omega)
          (by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega))
      · apply mod_sub_of_residue_sum hm hCH hCm hHm (by omega)
        rw [show p + 1 + (2 * p - 2) = p - 1 + 2 * p by omega]
        simpa using Nat.mod_eq_of_lt (by omega : p - 1 < 2 * p)
  · rcases moving_horizon_factor_event_residues hlater hp hdivLater with ⟨hu, hum, hHm⟩ | ⟨hu, hum, hHm⟩
    · refine Or.inr (Or.inr ⟨hr, hu, ?_, ?_⟩)
      · apply mod_sub_of_residue_sum hm hru hrm hum (by omega)
        rw [show p + 2 + (p - 2) = 2 * p by omega, Nat.mod_self]
      · apply mod_sub_of_residue_sum hm hCH hCm hHm (by omega)
        rw [show p - 1 + 2 = p + 1 by omega]
        exact Nat.mod_eq_of_lt (by omega)
    · exact Or.inl ⟨hr.trans hu.symm, same hru (hrm.trans hum.symm), same hCH (hCm.trans hHm.symm)⟩

/-- If an increment `p` is followed by just one intervening event
before reuse, an intervening increment below `3*p` is determined by
the two parities. -/
theorem moving_horizon_one_step_reuse_middle_increment {s C r C' t H u H' p : Nat}
    (hfirst : IsMovingHorizonStep s C r C') (hmiddle : IsMovingHorizonStep r C' t H)
    (hlater : IsMovingHorizonStep t H u H') (hp : 5 ≤ p) (he : d r = p)
    (hdivLater : p ∣ d u) (hsmall : d t < 3 * p) :
    (r % 2 = u % 2 ∧ d t = p + 2) ∨ (r % 2 = 1 ∧ u % 2 = 0 ∧ d t = p + 4) := by
  have hdiv : p ∣ d r := he.symm ▸ Nat.dvd_refl p
  have horder := Nat.le_of_lt hmiddle.2.1
  have hG := moving_horizon_factor_reuse_growth hfirst hlater horder hp hdiv hdivLater
  have hfirstUp := moving_horizon_step_update hfirst
  have hmiddleUp := moving_horizon_step_update hmiddle
  have hneq : d t ≠ p := by
    intro h
    have hbad := moving_horizon_factor_reuse_growth hfirst hmiddle (Nat.le_refl r) hp hdiv
      (h.symm ▸ Nat.dvd_refl p)
    omega
  have hr3 : 3 ≤ r := by have := hfirst.1.1; have := hfirst.2.1; omega
  have hpOdd := he ▸ d_mod_two_eq_one_of_three_le hr3
  have htOdd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ t)
  have hband : 2 * p ≤ H - C := by omega
  have hmod : (H - C) % (2 * p) = H - C - 2 * p := by
    rw [Nat.mod_eq_sub_mod hband]
    exact Nat.mod_eq_of_lt (by omega)
  rcases moving_horizon_factor_reuse_drift_residues hfirst hlater horder (by omega) hdiv hdivLater with
    ⟨hpar, _, hHd⟩ | ⟨_, _, _, hHm⟩ | ⟨hr, hu, _, hHm⟩
  · have hzero := Nat.mod_eq_zero_of_dvd hHd
    exact Or.inl ⟨hpar, by omega⟩
  · omega
  · exact Or.inr ⟨hr, hu, by omega⟩

end A166944Research
