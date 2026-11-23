import Mathlib.Tactic

set_option autoImplicit false

namespace PrimePowerRefireCharge

/-- An odd divisor of an even horizon's neighbor cannot jump over the next
available even multiple of itself. -/
theorem even_barrier {C B e : Nat} (lo : 2 ≤ C) (leCB : C ≤ B)
    (hC : C % 2 = 0) (hB : B % 2 = 0) (he : e % 2 = 1)
    (eb : e ∣ B) (side : e ∣ C - 1 ∨ e ∣ C + 1) : C + (e - 1) ≤ B := by
  obtain ⟨k, hk⟩ := eb
  rcases side with hm | hp
  · obtain ⟨j, hj⟩ := hm
    by_contra bad
    have hjlt : e * j < e * k := by omega
    have jk : j < k := Nat.lt_of_mul_lt_mul_left hjlt
    have hz : e * (j + 1) ≤ e * k := Nat.mul_le_mul_left e (by omega)
    rw [Nat.mul_succ] at hz
    omega
  · obtain ⟨j, hj⟩ := hp
    by_contra bad
    by_cases hjk : j < k
    · have hz : e * (j + 1) ≤ e * k := Nat.mul_le_mul_left e (by omega)
      rw [Nat.mul_succ] at hz
      omega
    · by_cases heq : j = k
      · subst j
        omega
      · have hz : e * (k + 1) ≤ e * j := Nat.mul_le_mul_left e (by omega)
        rw [Nat.mul_succ] at hz
        omega

def cell (q C : Nat) : Nat := (C + 2) / (2 * q)

private theorem cell_div {q a r : Nat} (hr : r < 2 * q) :
    (2 * q * a + r) / (2 * q) = a := by
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

/-- One q-divisible event advances the q-cell counter by its exact weighted charge.
This is the local arithmetic behind the repeated-q-firing ledger. -/
theorem q_hit_cell_jump {q C e : Nat} (hq : 5 ≤ q) (hqodd : q % 2 = 1)
    (hC : C % 2 = 0) (hClo : 2 ≤ C) (he : e % 2 = 1) (hqe : q ∣ e)
    (hactive : q ∣ C - 1 ∨ q ∣ C + 1) :
    cell q (C + e - 1) = cell q C + (e / q + 1) / 2 := by
  obtain ⟨h, heq⟩ := hqe
  have hqpos : 0 < q := by omega
  have hhmod : h % 2 = 1 := by
    have hz : (q * h) % 2 = 1 := by simpa [heq] using he
    simpa [Nat.mul_mod, hqodd] using hz
  let b : Nat := h / 2
  have hhform : h = 2 * b + 1 := by dsimp [b]; omega
  have hequot : e / q = h := by
    rw [heq]
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith [hqpos]
  have hweight : (e / q + 1) / 2 = b + 1 := by
    rw [hequot, hhform]
    omega
  have hstep : C + e - 1 + 2 = C + e + 1 := by omega
  unfold cell
  rw [hstep]
  rcases hactive with hminus | hplus
  · obtain ⟨k, hk⟩ := hminus
    have hCform : C = q * k + 1 := by omega
    have hmodC : (q * k + 1) % 2 = 0 := by
      rw [← hCform]
      exact hC
    have hkmod : k % 2 = 1 := by
      have ht : (k % 2 + 1) % 2 = 0 := by
        simpa [Nat.add_mod, Nat.mul_mod, hqodd] using hmodC
      omega
    let a : Nat := k / 2
    have hkform : k = 2 * a + 1 := by dsimp [a]; omega
    have hbefore : C + 2 = 2 * q * a + (q + 3) := by
      rw [hCform, hkform]
      ring
    have hafter : C + e + 1 = 2 * q * (a + b + 1) + 2 := by
      rw [hCform, heq, hkform, hhform]
      ring
    have hc0 : (C + 2) / (2 * q) = a := by
      rw [hbefore]
      apply cell_div
      omega
    have hc1 : (C + e + 1) / (2 * q) = a + b + 1 := by
      rw [hafter]
      apply cell_div
      omega
    rw [hc0, hc1, hweight]
    omega
  · obtain ⟨k, hk⟩ := hplus
    have hplusmod : (C + 1) % 2 = 1 := by omega
    have hkmul : (q * k) % 2 = 1 := by simpa [hk] using hplusmod
    have hkmod : k % 2 = 1 := by
      simpa [Nat.mul_mod, hqodd] using hkmul
    let a : Nat := k / 2
    have hkform : k = 2 * a + 1 := by dsimp [a]; omega
    have hbefore : C + 2 = 2 * q * a + (q + 1) := by
      calc
        C + 2 = (C + 1) + 1 := by omega
        _ = q * k + 1 := by rw [hk]
        _ = 2 * q * a + (q + 1) := by rw [hkform]; ring
    have hafter : C + e + 1 = 2 * q * (a + b + 1) := by
      calc
        C + e + 1 = (C + 1) + e := by omega
        _ = q * k + q * h := by rw [hk, heq]
        _ = 2 * q * (a + b + 1) := by rw [hkform, hhform]; ring
    have hc0 : (C + 2) / (2 * q) = a := by
      rw [hbefore]
      apply cell_div
      omega
    have hc1 : (C + e + 1) / (2 * q) = a + b + 1 := by
      rw [hafter]
      simpa using (cell_div (q := q) (a := a + b + 1) (r := 0) (by omega))
    rw [hc0, hc1, hweight]
    omega

#print axioms q_hit_cell_jump
#print axioms even_barrier

end PrimePowerRefireCharge
