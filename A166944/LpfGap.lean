
import A166944.Lemmas
import A166944.FirstHitForm

/-!
# A factor `q` of the horizon term forces a gap of at most `2 * q`

`Mod3Gap` proves the case `q = 3`:

    (3 ∣ C - 1) => r - s <= 6        (even branch)
    (3 ∣ C + 1) => r - s <= 6        (odd branch)

This file generalizes `3` to an arbitrary `q >= 2`, giving `r - s <= 2 * q` in both branches.

The mechanism is unchanged from `Mod3Gap`: `FirstHitForm.step_is_first_gcd_hit` is the
MINIMALITY of the event index -- no `j` with `s < j < r` passes the gcd test -- so it suffices
to exhibit ONE admissible `j` with `s < j <= s + 2 * q`.

## The asymmetry between the branches, stated honestly

* **Even branch** (`q ∣ C - 1`): we need an EVEN `j` with `q ∣ j`.  The witness is
  `2 * (q * k) + 2 * q` where `s = 2 * (q * k) + R` and `R < 2 * q`: an even multiple of `q`
  lying in `(s, s + 2 * q]`.  **No parity hypothesis on `q` is needed** -- this works for every
  `q >= 2`.  (`Mod3Gap`'s "even multiple of 6" is the special case `q = 3`.)

* **Odd branch** (`q ∣ C + 1`): we need an ODD `j` with `q ∣ j - 2`, i.e. `j = q * m + 2` with
  `m` odd.  Consecutive such `j` differ by `2 * q` -- **but only when `q` is odd**: if `q` is
  even then `q * m + 2` is even for EVERY `m`, so no such `j` exists at all.  This branch
  therefore genuinely requires `q % 2 = 1`.  `Mod3Gap` never had to state this because `3` is
  odd.  `odd_branch_needs_q_odd` below records that dropping it makes the statement FALSE, and
  `q_odd_of_dvd_odd` is the one-liner that discharges it when the term is odd.

**On the orbit of this conjecture the parity hypothesis is free, and that is a theorem.**
A moving-horizon state has `C = D s` with `2 <= s`; `Lemmas.D_mod_two_eq_zero_of_two_le` gives
`D n % 2 = 0` for `2 <= n`, so `C` is even, so `C + 1` is odd, so every `q >= 2` dividing
`C + 1` is odd.  That chain is `q_odd_of_dvd_succ_of_even`; the hypothesis-free orbit forms are
`gap_le_twice_of_dvd_even_state` and `gap_le_twice_of_dvd_odd_state`.  The general lemmas still
carry the parity hypothesis explicitly, because the general statements need it.

Pure core: `omega` / `Nat.dvd_gcd` / `Nat.le_of_dvd` / `Nat.mul_add` / `Nat.div_add_mod`.
-/

namespace A166944Research

/-! ## Parity toolkit -/

/-- **An odd number has only odd divisors.** -/
theorem q_odd_of_dvd_odd {q N : Nat} (hdvd : q ∣ N) (hN : N % 2 = 1) : q % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one q with hzero | hone
  · exfalso
    obtain ⟨m, hm⟩ := hdvd
    have hz : N % 2 = 0 := by rw [hm, Nat.mul_mod, hzero, Nat.zero_mul]
    omega
  · exact hone

/-- **`C` even makes every divisor `q >= 2` of `C + 1` odd.**  This is how a caller on the
conjecture's orbit discharges the odd branch's parity hypothesis in one line. -/
theorem q_odd_of_dvd_succ_of_even {q C : Nat} (hCeven : C % 2 = 0) (hdvd : q ∣ C + 1) :
    q % 2 = 1 :=
  q_odd_of_dvd_odd hdvd (by omega)

/-! ## Multiplicative normal forms

Every nonlinear identity is isolated here as a rewrite in the cofactor shape `2 * (q * k) + ...`,
so `omega` only ever sees the product `q * k` as a single atom and the arithmetic stays linear.
-/

/-- `q * (2*k) = 2*(q*k)`. -/
theorem q_mul_two_k (q k : Nat) : q * (2 * k) = 2 * (q * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]

/-- `(2*m + n) % 2 = n % 2`: the only parity computation used, in fully general form. -/
theorem two_mul_add_mod_two (m n : Nat) : (2 * m + n) % 2 = n % 2 := by
  rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]

/-- `q * (2*k + 1) = 2*(q*k) + q`. -/
theorem q_mul_two_k_add_one' (q k : Nat) : q * (2 * k + 1) = 2 * (q * k) + q := by
  rw [Nat.mul_add, Nat.mul_one, q_mul_two_k]

/-- `q * (2*k + 2) = 2*(q*k) + 2*q`. -/
theorem q_mul_two_k_add_two' (q k : Nat) : q * (2 * k + 2) = 2 * (q * k) + 2 * q := by
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, Nat.mul_add, Nat.mul_one,
      q_mul_two_k_add_one']
  omega

/-- `q * (2*k + 3) = 2*(q*k) + q + 2*q`. -/
theorem q_mul_two_k_add_three' (q k : Nat) : q * (2 * k + 3) = 2 * (q * k) + q + 2 * q := by
  rw [show 2 * k + 3 = 2 * k + 2 + 1 by omega, Nat.mul_add, Nat.mul_one,
      q_mul_two_k_add_two']
  omega

/-! ## The two container lemmas -/

/-- **Every window of `2 * q` consecutive integers contains an even multiple of `q`.**
No parity hypothesis on `q`: the witness is `2 * (q*k) + 2*q`, an even multiple of `q`. -/
theorem exists_even_multiple_of_q {q : Nat} (hq : 2 ≤ q) (s : Nat) :
    ∃ j : Nat, s < j ∧ j ≤ s + 2 * q ∧ j % 2 = 0 ∧ q ∣ j := by
  obtain ⟨k, R, hk, hR⟩ : ∃ k R, 2 * (q * k) + R = s ∧ R < 2 * q :=
    ⟨s / (2 * q), s % (2 * q), by rw [← Nat.mul_assoc]; exact Nat.div_add_mod s (2 * q),
      Nat.mod_lt s (by omega)⟩
  refine ⟨2 * (q * k) + 2 * q, ?_, ?_, ?_, ?_⟩
  · generalize hT : 2 * (q * k) = T at *
    omega
  · generalize hT : 2 * (q * k) = T at *
    omega
  · rw [show 2 * (q * k) + 2 * q = 2 * (q * k + q) by rw [Nat.mul_add],
        Nat.mul_mod_right]
  · exact ⟨2 * k + 2, (q_mul_two_k_add_two' q k).symm⟩

/-- **Every window of `2 * q` consecutive integers contains an odd `j` with `q ∣ j - 2`,
PROVIDED `q` is odd.**  Two candidates `2 * q` apart, one of which must land in the window.
The parity hypothesis is essential: see `odd_branch_needs_q_odd`. -/
theorem exists_odd_two_less_multiple_of_q {q : Nat} (hq : 2 ≤ q) (hqodd : q % 2 = 1) (s : Nat) :
    ∃ j : Nat, s < j ∧ j ≤ s + 2 * q ∧ j % 2 = 1 ∧ q ∣ j - 2 := by
  obtain ⟨k, R, hk, hR⟩ : ∃ k R, 2 * (q * k) + R = s ∧ R < 2 * q :=
    ⟨s / (2 * q), s % (2 * q), by rw [← Nat.mul_assoc]; exact Nat.div_add_mod s (2 * q),
      Nat.mod_lt s (by omega)⟩
  have hodd1 : (2 * (q * k) + q + 2) % 2 = 1 := by
    rw [show 2 * (q * k) + q + 2 = 2 * (q * k) + (q + 2) by omega, two_mul_add_mod_two]
    omega
  have hodd2 : (2 * (q * k) + 2 * q + q + 2) % 2 = 1 := by
    rw [show 2 * (q * k) + 2 * q + q + 2 = 2 * (q * k + q) + (q + 2) by omega,
        two_mul_add_mod_two]
    omega
  by_cases hlow : R < q + 2
  · refine ⟨2 * (q * k) + q + 2, ?_, ?_, hodd1, ?_⟩
    · generalize hT : 2 * (q * k) = T at *
      omega
    · generalize hT : 2 * (q * k) = T at *
      omega
    · have hsub : 2 * (q * k) + q + 2 - 2 = 2 * (q * k) + q := by omega
      rw [hsub]
      exact ⟨2 * k + 1, (q_mul_two_k_add_one' q k).symm⟩
  · refine ⟨2 * (q * k) + 2 * q + q + 2, ?_, ?_, hodd2, ?_⟩
    · generalize hT : 2 * (q * k) = T at *
      omega
    · generalize hT : 2 * (q * k) = T at *
      omega
    · have hsub : 2 * (q * k) + 2 * q + q + 2 - 2 = 2 * (q * k) + 2 * q + q := by omega
      rw [hsub]
      have h3 : q * (2 * k + 3) = 2 * (q * k) + 2 * q + q := by
        rw [q_mul_two_k_add_three']
        omega
      exact ⟨2 * k + 3, h3.symm⟩

/-! ## `q` odd cannot be dropped from the odd branch -/

/-- **The odd branch's parity hypothesis cannot be dropped.**  With `q = 2` no odd `j` has
`2 ∣ j - 2`: an odd `j` has `j - 2` odd, and `2` divides only even numbers.  (`C = 3` makes
`2 ∣ C + 1`, so this is a genuine instance of the odd branch's hypothesis with `q` even.) -/
theorem odd_branch_needs_q_odd : ¬ ∀ j : Nat, j % 2 = 1 → 2 ∣ j - 2 := by
  intro hall
  obtain ⟨m, hm⟩ := hall 3 (by decide)
  omega

/-! ## The gap bounds -/

/-- **Even branch.**  If `q >= 2` divides `C - 1` then the gap is at most `2 * q`.  Exact
generalization of `Mod3Gap.gap_le_six_of_three_dvd_even`; no parity hypothesis on `q`. -/
theorem gap_le_twice_of_dvd_even {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 0) (hq : 2 ≤ q) (hdvd : q ∣ C - 1) : r - s ≤ 2 * q := by
  rcases Nat.lt_or_ge (r - s) (2 * q + 1) with hlt | hge
  · omega
  · exfalso
    obtain ⟨j, hsj, hjs, hje, hjq⟩ := exists_even_multiple_of_q hq s
    have hjr : j < r := by omega
    have hres := (step_is_first_gcd_hit hstep hDconst).2 j hsj hjr
    rw [if_pos (by omega : j % 2 = 0)] at hres
    have hd : q ∣ Nat.gcd j (C - 1) := Nat.dvd_gcd hjq hdvd
    have hgpos : 0 < Nat.gcd j (C - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hle : q ≤ Nat.gcd j (C - 1) := Nat.le_of_dvd hgpos hd
    omega

/-- **Odd branch.**  If `q >= 2` is ODD and divides `C + 1` then the gap is at most `2 * q`.
Exact generalization of `Mod3Gap.gap_le_six_of_three_dvd_odd`; the parity hypothesis is
genuinely needed (`odd_branch_needs_q_odd`). -/
theorem gap_le_twice_of_dvd_odd {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 1) (hq : 2 ≤ q) (hqodd : q % 2 = 1) (hdvd : q ∣ C + 1) :
    r - s ≤ 2 * q := by
  rcases Nat.lt_or_ge (r - s) (2 * q + 1) with hlt | hge
  · omega
  · exfalso
    obtain ⟨j, hsj, hjs, hje, hjq⟩ := exists_odd_two_less_multiple_of_q hq hqodd s
    have hjr : j < r := by omega
    have hres := (step_is_first_gcd_hit hstep hDconst).2 j hsj hjr
    rw [if_neg (by omega : ¬ j % 2 = 0)] at hres
    have hd : q ∣ Nat.gcd (j - 2) (C + 1) := Nat.dvd_gcd hjq hdvd
    have hgpos : 0 < Nat.gcd (j - 2) (C + 1) := Nat.gcd_pos_of_pos_right _ (by omega)
    have hle : q ≤ Nat.gcd (j - 2) (C + 1) := Nat.le_of_dvd hgpos hd
    omega

/-! ## Orbit forms: the parity hypothesis is discharged from the state -/

/-- A moving-horizon state has an even horizon. -/
theorem horizon_even_of_state {s C : Nat} (hstate : IsMovingHorizonState s C) : C % 2 = 0 := by
  rw [← hstate.2.1]
  exact D_mod_two_eq_zero_of_two_le hstate.1

/-- **Even branch, orbit form** (no parity side condition exists to discharge). -/
theorem gap_le_twice_of_dvd_even_state {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 0) (hq : 2 ≤ q) (hdvd : q ∣ C - 1) : r - s ≤ 2 * q :=
  gap_le_twice_of_dvd_even hstep hDconst hr hq hdvd

/-- **Odd branch, orbit form: NO parity hypothesis left.**  On a moving-horizon state the
horizon is even, hence `C + 1` is odd, hence every `q >= 2` dividing `C + 1` is odd. -/
theorem gap_le_twice_of_dvd_odd_state {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 1) (hq : 2 ≤ q) (hdvd : q ∣ C + 1) : r - s ≤ 2 * q :=
  gap_le_twice_of_dvd_odd hstep hDconst hr hq
    (q_odd_of_dvd_succ_of_even (horizon_even_of_state hstep.1) hdvd) hdvd

/-! ## Axiom audit -/

#print axioms q_odd_of_dvd_odd
#print axioms q_odd_of_dvd_succ_of_even
#print axioms exists_even_multiple_of_q
#print axioms exists_odd_two_less_multiple_of_q
#print axioms odd_branch_needs_q_odd
#print axioms gap_le_twice_of_dvd_even
#print axioms gap_le_twice_of_dvd_odd
#print axioms horizon_even_of_state
#print axioms gap_le_twice_of_dvd_even_state
#print axioms gap_le_twice_of_dvd_odd_state

end A166944Research
