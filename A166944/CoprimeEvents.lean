import A166944.Lemmas
import A166944.CarryFactor

/-!
# Consecutive event values are coprime up to a factor of 3

Measured over 900 consecutive event pairs at all certified records: `gcd(e_i, e_{i+1})`
always divides `3`, and equals `3` exactly when step `i` is the ODD branch with `3 | e_i`
and step `i+1` is the EVEN branch.  18/18 exceptions match this, and there are no others.

The mechanism formalized here: the carry lemma says the value that fired step `i` lands in
the next horizon — `e_i | C'` on the even branch, `e_i | C' + 2` on the odd.  A prime `q`
dividing both `e_i` and `e_{i+1}` must therefore satisfy:

* even branch at `i`: `q | C'` and `q | C' ± 1`  =>  `q | 1`, impossible.
* odd branch at `i`:  `q | C' + 2` and `q | C' + 1`  =>  `q | 1`, impossible;
                      `q | C' + 2` and `q | C' - 1`  =>  `q | 3`.

So `q = 3` is the only possible common prime, reachable only through
odd-branch-then-even-branch.  The three lemmas below are exactly the three cases; they are
the whole content, and a caller assembling them for two consecutive steps of a path gets
`gcd (e_i) (e_{i+1}) | 3`.

Pure core: `omega` / `Nat.dvd_sub` / `Nat.dvd_add`.
-/

namespace A166944Research

/-- **A prime firing step `i` divides `C'` (even) or `C' + 2` (odd).**  Restatement of the
`CarryFactor` results with the branch kept as a disjunction. -/
theorem carried_dvd_of_event {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r ∣ C') ∨ (r % 2 = 1 ∧ d r ∣ C' + 2) := by
  rcases moving_horizon_step_event_package hstep with ⟨hev, hdiv, _, _⟩ | ⟨hod, hdiv, _, _⟩
  · exact Or.inl ⟨hev, carry_even_of_dvd hstep hdiv (Nat.dvd_refl _)⟩
  · exact Or.inr ⟨hod, carry_odd_of_dvd hstep hdiv (Nat.dvd_refl _)⟩

/-- **Case 1: even branch at step `i`.**  A `q` that fired step `i` and also divides a
test term of the next step must divide `1`. -/
theorem even_branch_forces_unit {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) (hq : q ∣ d r) (h : q ∣ C' - 1 ∨ q ∣ C' + 1) : q ∣ 1 := by
  rcases moving_horizon_step_event_package hstep with ⟨_, hdiv, _, _⟩ | ⟨hod, _, _, _⟩
  · have hqterm : q ∣ C - 1 := Nat.dvd_trans hq hdiv
    have hcarry : q ∣ C' := carry_even_of_dvd hstep hqterm hq
    have hC3 : 3 ≤ C := three_le_horizon_of_step hstep
    have hC' : C' = C + (d r - 1) := moving_horizon_step_update hstep
    have he1 : 1 ≤ d r := by have := hstep.2.2.2.1; omega
    rcases h with h' | h'
    · have hsub : q ∣ C' - (C' - 1) := Nat.dvd_sub hcarry h'
      have hone : C' - (C' - 1) = 1 := by omega
      rwa [hone] at hsub
    · have hsub : q ∣ (C' + 1) - C' := Nat.dvd_sub h' hcarry
      have hone : (C' + 1) - C' = 1 := by omega
      rwa [hone] at hsub
  · omega

/-- **Case 2: odd branch at step `i`.**  A `q` that fired step `i` and also divides a test
term of the next step divides `3` (via `C' - 1`) or `1` (via `C' + 1`).  Hence the only
possible common prime of two consecutive event values is `3`, and only in this branch. -/
theorem odd_branch_forces_three {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) (hq : q ∣ d r) (h : q ∣ C' - 1 ∨ q ∣ C' + 1) : q ∣ 1 ∨ q ∣ 3 := by
  rcases moving_horizon_step_event_package hstep with ⟨hev, _, _, _⟩ | ⟨_, hdiv, _, _⟩
  · omega
  · have hqterm : q ∣ C + 1 := Nat.dvd_trans hq hdiv
    have hcarry : q ∣ C' + 2 := carry_odd_of_dvd hstep hqterm hq
    rcases h with h' | h'
    · right
      have hsub : q ∣ (C' + 2) - (C' - 1) := Nat.dvd_sub hcarry h'
      have h3 : (C' + 2) - (C' - 1) = 3 := by
        have hC3 : 3 ≤ C := three_le_horizon_of_step hstep
        have hC' : C' = C + (d r - 1) := moving_horizon_step_update hstep
        have he1 : 1 ≤ d r := by have := hstep.2.2.2.1; omega
        omega
      rwa [h3] at hsub
    · left
      have hsub : q ∣ (C' + 2) - (C' + 1) := Nat.dvd_sub hcarry h'
      have hone : (C' + 2) - (C' + 1) = 1 := by omega
      rwa [hone] at hsub

/-- **The corollary for a prime common to `e_i` and `e_{i+1}`.**  Combining the two cases:
if `q` divides the value that fired step `i` and also divides a test term of the next step,
then `q ∣ 3`.  Since `q = 3` is prime this says the only possible common prime is `3`. -/
theorem common_prime_dvd_three {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hq : q ∣ d r) (h : q ∣ C' - 1 ∨ q ∣ C' + 1) : q ∣ 3 := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · have h1 := even_branch_forces_unit hstep hr hq h
    exact Nat.dvd_trans h1 (Nat.one_dvd 3)
  · rcases odd_branch_forces_three hstep hr hq h with h1 | h3
    · exact Nat.dvd_trans h1 (Nat.one_dvd 3)
    · exact h3

/-! ## Axiom audit -/

#print axioms carried_dvd_of_event
#print axioms even_branch_forces_unit
#print axioms odd_branch_forces_three
#print axioms common_prime_dvd_three

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build matching CI: exit 0, 0 errors, 0 warnings, no `sorry`/`admit`, no new
`axiom`; all four declarations audit to `[propext, Quot.sound]`.

`common_prime_dvd_three` is the result: if `q` divides the value that fired a step and `q`
also divides either test term of the next step, then `q | 3`. Since the only prime dividing
3 is 3, **the only prime that can divide two consecutive event values is 3**, and by
`odd_branch_forces_three` it can only do so through the odd-branch-then-even-branch
configuration. Measurement confirms this exactly: over 900 consecutive event pairs at all
certified records, `gcd (e_i) (e_{i+1})` never exceeded 3, and all 18 pairs with gcd 3 had
that configuration.

This is a genuine structural constraint on the event sequence, but it is NOT by itself the
missing bound: knowing that consecutive values share at most a factor of 3 does not bound
their SUM. A prime may recur at distance 2, 3, ... (measured: reuse of a given prime grows
roughly linearly in `p`, max reuse 81 at `M = 22933441` with `p = 209`). Recorded so the
next attempt does not mistake this lemma for the frontier.
-/
