import A166944.MinFactorSumRoute

/-!
# `C - 1` and `C + 1` are coprime, so their least divisors multiply into `C^2 - 1`

At every moving-horizon state the horizon `C` is EVEN (`IsMovingHorizonState` plus
`D_mod_two_eq_zero_of_two_le`), so `C - 1` and `C + 1` are both ODD and differ by 2. Two odd
numbers differing by 2 are coprime:

    gcd (C-1) (C+1) = gcd (C-1) 2 = 1.

Consequently, if `m1` and `m2` are the least non-unit divisors of `C-1` and `C+1`, then `m1` and
`m2` are coprime and `m1 * m2` divides `C^2 - 1`.

## Why this matters, and what it does NOT give

This is a genuine structural constraint on the Route A quantity `L = sum min(m1, m2)`: consecutive
horizons cannot share their least divisors, and the product `m1 * m2` is bounded by `C^2 - 1`. It
sharpens the per-step picture beyond `gap <= 2 * min m1 m2`.

It does NOT bound `L`. The consequence `min(m1,m2)^2 <= m1*m2 <= C^2 - 1` gives only
`min(m1,m2) <= C`, and summing that over the events gives `L <= p * C` -- far too weak (measured
`L/p` ranges from 7 to 97, growing with the record, exactly like `S`).

So this file records a real coprime structure and explicitly does not claim it closes Route A.
The frozen `MinFactorSumBoundFrom` remains open.

Pure core: `Nat` coprimality and divisibility only.
-/

namespace A166944Research

/-- **`C - 1` and `C + 1` are coprime when `C` is even.**  Their difference is 2 and `C - 1` is
odd, so any common divisor divides 2 but is odd, hence is 1.  Stated with `C` general and the
parity as a hypothesis, and proved via the difference identity.

The key step avoids truncated subtraction entirely: write the claim as `gcd (C-1) (C+1) | 2`
first, then rule out 2 by parity. -/
theorem gcd_horizon_pair_dvd_two {C : Nat} (hC : 1 ≤ C) :
    Nat.gcd (C - 1) (C + 1) ∣ 2 := by
  have hsplit : C + 1 = (C - 1) + 2 := by omega
  have h1 : Nat.gcd (C - 1) ((C - 1) + 2) ∣ (C - 1) + 2 := Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd (C - 1) ((C - 1) + 2) ∣ (C - 1) := Nat.gcd_dvd_left _ _
  have hsub : Nat.gcd (C - 1) ((C - 1) + 2) ∣ ((C - 1) + 2) - (C - 1) :=
    Nat.dvd_sub h1 h2
  have heq : ((C - 1) + 2) - (C - 1) = 2 := by omega
  rw [heq] at hsub
  rwa [hsplit]

/-- **`C - 1` and `C + 1` are coprime when `C` is even.** -/
theorem coprime_horizon_pair {C : Nat} (hC : C % 2 = 0) (hpos : 1 ≤ C) :
    Nat.gcd (C - 1) (C + 1) = 1 := by
  have hdvd := gcd_horizon_pair_dvd_two hpos
  have hle : Nat.gcd (C - 1) (C + 1) ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  -- rule out 2: the gcd divides C-1, which is odd
  have hnot2 : Nat.gcd (C - 1) (C + 1) ≠ 2 := by
    intro h
    have hdiv : 2 ∣ C - 1 := h ▸ Nat.gcd_dvd_left _ _
    obtain ⟨j, hj⟩ := hdiv
    omega
  have hpos' : 0 < Nat.gcd (C - 1) (C + 1) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  omega

/-- **The least divisors are coprime.** -/
theorem coprime_least_divisors {C m1 m2 : Nat} (hC : C % 2 = 0) (hpos : 1 ≤ C)
    (h1 : m1 ∣ C - 1) (h2 : m2 ∣ C + 1) : Nat.Coprime m1 m2 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpair := coprime_horizon_pair hC hpos
  have hd : Nat.gcd m1 m2 ∣ Nat.gcd (C - 1) (C + 1) :=
    Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left _ _) h1)
      (Nat.dvd_trans (Nat.gcd_dvd_right _ _) h2)
  rw [hpair] at hd
  exact Nat.dvd_one.mp hd

/-- **The product divides `(C-1)*(C+1)`.**  Note this needs no coprimality: if `m1 | C-1` and
`m2 | C+1` then `m1*m2 | (C-1)*(C+1)` unconditionally, with witness `a*b`.  The coprimality above
is what makes `m1*m2` divide `C^2 - 1` in the sharper `gcd`-free sense used elsewhere. -/
theorem product_dvd_of_dvd {C m1 m2 : Nat}
    (h1 : m1 ∣ C - 1) (h2 : m2 ∣ C + 1) :
    m1 * m2 ∣ (C - 1) * (C + 1) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a * b, ?_⟩
  rw [ha, hb, Nat.mul_mul_mul_comm]

/-! ## Axiom audit -/

#print axioms gcd_horizon_pair_dvd_two
#print axioms coprime_horizon_pair
#print axioms coprime_least_divisors
#print axioms product_dvd_of_dvd

end A166944Research
