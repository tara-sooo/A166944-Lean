import Mathlib.Tactic

/-!
# Growing low-prime cutoff: finite arithmetic and event-clock accounting

This file isolates the deterministic pieces of the MIN-wheel argument.
It is not a Lean formalization of the asymptotic prime-counting input,
nor does it identify its abstract event paths with the canonical MIN orbit.

All results have explicit premises; in particular, finite_twin_of_budget
assumes a no-twin event-clock inequality supplied by the orbit analysis.
-/

set_option autoImplicit false

namespace MinGrowingCutoff

/-- An odd selected divisor cannot cross the next even multiple of that
divisor. This proof is adapted from the independently verified
PrimePowerRefireCharge.even_barrier on the other research branch. -/
theorem even_barrier {C J p : Nat} (hC2 : 2 ≤ C) (hCJ : C ≤ J)
    (hC_even : C % 2 = 0) (hJ_even : J % 2 = 0)
    (hp_odd : p % 2 = 1) (hpJ : p ∣ J)
    (hactive : p ∣ C - 1 ∨ p ∣ C + 1) :
    C + (p - 1) ≤ J := by
  obtain ⟨k, hk⟩ := hpJ
  rcases hactive with hm | hp
  · obtain ⟨j, hj⟩ := hm
    by_contra bad
    have hjlt : p * j < p * k := by omega
    have jk : j < k := Nat.lt_of_mul_lt_mul_left hjlt
    have hz : p * (j + 1) ≤ p * k := Nat.mul_le_mul_left p (by omega)
    rw [Nat.mul_succ] at hz
    omega
  · obtain ⟨j, hj⟩ := hp
    by_contra bad
    by_cases hjk : j < k
    · have hz : p * (j + 1) ≤ p * k := Nat.mul_le_mul_left p (by omega)
      rw [Nat.mul_succ] at hz
      omega
    · by_cases heq : j = k
      · subst j
        omega
      · have hz : p * (k + 1) ≤ p * j := Nat.mul_le_mul_left p (by omega)
        rw [Nat.mul_succ] at hz
        omega

/-- A LOW-only event: time and frozen-horizon state, with the
prime-clock gap dt ≤ 2p. The recurrence-specific first-hit
property is represented by the explicit clock premise. -/
structure LowEvent (L : Nat) (a b : Nat × Nat) : Type where
  primeLabel : Nat
  odd : primeLabel % 2 = 1
  atLeastThree : 3 ≤ primeLabel
  dividesL : primeLabel ∣ L
  evenHorizon : a.2 % 2 = 0
  horizonAtLeastTwo : 2 ≤ a.2
  active : primeLabel ∣ a.2 - 1 ∨ primeLabel ∣ a.2 + 1
  clock : b.1 ≤ a.1 + 2 * primeLabel
  update : b.2 = a.2 + (primeLabel - 1)

/-- Any finite consecutive series of low-only events. -/
inductive LowPath (L : Nat) (start : Nat × Nat) : Nat × Nat → Prop
  | refl : LowPath L start start
  | more {a b : Nat × Nat} :
      LowPath L start a → LowEvent L a b → LowPath L start b

/-- The first invariant is the even-multiple barrier. The second
charges each selected low event's elapsed time to three times its gain. -/
theorem low_path_budget {L J : Nat} {start finish : Nat × Nat}
    (hLJ : L ∣ J) (hJ_even : J % 2 = 0)
    (hstart : start.2 ≤ J)
    (hpath : LowPath L start finish) :
    finish.2 ≤ J ∧
      finish.1 + 3 * start.2 ≤ start.1 + 3 * finish.2 := by
  induction hpath with
  | refl =>
      constructor
      · exact hstart
      · omega
  | more _ step ih =>
      obtain ⟨hC, hT⟩ := ih
      have hbar := even_barrier step.horizonAtLeastTwo hC
        step.evenHorizon hJ_even step.odd
        (dvd_trans step.dividesL hLJ) step.active
      have hprime : 2 * step.primeLabel ≤ 3 * (step.primeLabel - 1) := by
        omega
      constructor
      · rw [step.update]
        exact hbar
      · rw [step.update]
        omega

/-- A low-only block has cumulative gain < L and event-clock travel < 3L,
provided its initial horizon lies before an even multiple J of L
with J < initial horizon + L. -/
theorem low_path_elapsed_lt_threeL
    {L J : Nat} {start finish : Nat × Nat}
    (hLJ : L ∣ J) (hJ_even : J % 2 = 0)
    (hstart : start.2 ≤ J) (hnear : J < start.2 + L)
    (hpath : LowPath L start finish) :
    finish.2 < start.2 + L ∧ finish.1 < start.1 + 3 * L := by
  obtain ⟨hC, hT⟩ :=
    low_path_budget hLJ hJ_even hstart hpath
  constructor <;> omega

/-- Split the number of selections of one prime along one source into
its first appearance and its repetitions. -/
theorem first_plus_repetitions (n : Nat) :
    n = (if n = 0 then 0 else 1) + (n - 1) := by
  cases n with
  | zero => simp
  | succ k => simp [Nat.add_comm]

/-- Summing a per-orbit interval bound. There is one LOW segment before
each high event and one after the last high event. -/
theorem sum_orbit_clock_budget {α : Type*}
    (sources : Finset α) (travel high : α → Nat) (B L : Nat)
    (hclock : ∀ a ∈ sources,
      travel a ≤ (high a + 1) * (2 * B + 3 * L)) :
    Finset.sum sources travel ≤
      (Finset.sum sources high + sources.card) * (2 * B + 3 * L) := by
  calc
    Finset.sum sources travel ≤
        Finset.sum sources (fun a => (high a + 1) * (2 * B + 3 * L)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact hclock a ha
    _ = (Finset.sum sources (fun a => high a + 1)) * (2 * B + 3 * L) := by
          rw [Finset.sum_mul]
    _ = (Finset.sum sources high + sources.card) * (2 * B + 3 * L) := by
          simp [Finset.sum_add_distrib]

/-- Exact finite dyadic threshold. The no-twin premise is supplied by
the terminal primality test and sum_orbit_clock_budget, not by this
inequality theorem. Equivalently:
  (9 X^2 / 16) - (5 X / 4) > (2B+3L)(R+F+X/2)
forces a successful terminal. Natural numbers avoid division on the left. -/
theorem finite_twin_of_budget
    (hasTwinTerminal : Prop) (X B L R F : Nat)
    (hno : ¬hasTwinTerminal →
      9 * X * X ≤
        20 * X + 16 * (2 * B + 3 * L) * (R + F + X / 2))
    (hstrict :
      20 * X + 16 * (2 * B + 3 * L) * (R + F + X / 2) <
        9 * X * X) :
    hasTwinTerminal := by
  by_contra hn
  have hbound := hno hn
  omega

#print axioms even_barrier
#print axioms low_path_budget
#print axioms low_path_elapsed_lt_threeL
#print axioms first_plus_repetitions
#print axioms sum_orbit_clock_budget
#print axioms finite_twin_of_budget

end MinGrowingCutoff
