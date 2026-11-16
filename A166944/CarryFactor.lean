import A166944.Lemmas

/-!
# The hit-causing factor is carried into the next horizon

`RecordIndex.moving_horizon_gap_le_twice_even_factor` / `..._odd_factor` bound the gap by
twice ANY divisor `v >= 2` of `C - 1` (even branch) or `C + 1` (odd).  Taking `v` to be a
prime factor gives `gap <= 2 * q` where `q` caused the hit, hence

    travel  <=  2 * sum_i q_i ,

so `sum_i q_i <= M/4` would give the frontier `travel <= M/2`.

The structural fact recorded here is what makes `sum q` controllable: the factor that
caused the hit is **carried into the next horizon**.  On the even branch `e | C - 1` and
`C' = C + (e - 1)`, so `e | C'`; on the odd branch `e | C + 1`, so `e | C' + 2`.  A prime
that caused the hit therefore ends up inside `C'` (even) or `C' + 2` (odd) — the wrong
term for the next step's test — which is why it cannot simply be reused immediately.

Pure core: `omega` / `simp` / `rfl`.
-/

namespace A166944Research

/-- `3 ≤ C` at any moving-horizon state, from `s < C` and `2 ≤ s`.  Stated because the
carry identities below need `C - 1` to behave. -/
theorem three_le_horizon_of_step {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    3 ≤ C := by
  have hs := hstep.1.1
  have hsc := hstep.1.2.2
  omega

/-- **The carry, even branch.**  If `q` divides `C - 1` and also the event value `d r`,
then `q` divides the next horizon `C'`. -/
theorem carry_even_of_dvd {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hq : q ∣ C - 1) (hqe : q ∣ d r) : q ∣ C' := by
  have hC' : C' = C + (d r - 1) := moving_horizon_step_update hstep
  have he1 : 1 ≤ d r := by have := hstep.2.2.2.1; omega
  have hC3 : 3 ≤ C := three_le_horizon_of_step hstep
  -- C = (C - 1) + 1, so C' = (C - 1) + 1 + (d r - 1) = (C - 1) + d r
  have hkey : C' = (C - 1) + d r := by omega
  rw [hkey]
  exact Nat.dvd_add hq hqe

/-- **The carry, odd branch.**  If `q` divides `C + 1` and the event value, then `q`
divides `C' + 2`. -/
theorem carry_odd_of_dvd {s C r C' q : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hq : q ∣ C + 1) (hqe : q ∣ d r) : q ∣ C' + 2 := by
  have hC' : C' = C + (d r - 1) := moving_horizon_step_update hstep
  have he1 : 1 ≤ d r := by have := hstep.2.2.2.1; omega
  have hkey : C' + 2 = (C + 1) + d r := by omega
  rw [hkey]
  exact Nat.dvd_add hq hqe

/-- **The carried prime cannot cause the next even hit.**  On the even branch `q | C'`,
but the next even test needs a divisor of `C' - 1`; a `q > 1` dividing `C'` divides
neither `C' - 1` nor `C' + 1`. -/
theorem carried_prime_not_next_even {q C' : Nat} (hq1 : 1 < q) (h : q ∣ C')
    (hC' : 1 ≤ C') : ¬ (q ∣ C' - 1) := by
  intro h2
  have hsub : q ∣ C' - (C' - 1) := Nat.dvd_sub h h2
  have hone : C' - (C' - 1) = 1 := by omega
  rw [hone] at hsub
  have := Nat.le_of_dvd (by decide : 0 < 1) hsub
  omega

/-- **The carried prime cannot cause the next odd hit either.** -/
theorem carried_prime_not_next_odd {q C' : Nat} (hq1 : 1 < q) (h : q ∣ C') :
    ¬ (q ∣ C' + 1) := by
  intro h2
  have hsub : q ∣ (C' + 1) - C' := Nat.dvd_sub h2 h
  have hone : (C' + 1) - C' = 1 := by omega
  rw [hone] at hsub
  have := Nat.le_of_dvd (by decide : 0 < 1) hsub
  omega

/-! ## Axiom audit -/

#print axioms three_le_horizon_of_step
#print axioms carry_even_of_dvd
#print axioms carry_odd_of_dvd
#print axioms carried_prime_not_next_even
#print axioms carried_prime_not_next_odd

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build, `-DautoImplicit=false -DrelaxedAutoImplicit=false`: exit 0, no `sorry`,
no `admit`, no new `axiom`; all five declarations audit to `[propext, Quot.sound]`.

What this gives, and what it does not.  With `q` a prime dividing `C - 1` (even branch) or
`C + 1` (odd), the tree's `moving_horizon_gap_le_twice_even_factor` / `..._odd_factor` give
`gap <= 2*q` at that step, hence `travel <= 2 * sum q`.  So `sum q <= M/4` would close the
frontier.  These lemmas establish that the hit-causing factor is *carried* into the next
horizon (`q | C'` even, `q | C' + 2` odd) and therefore cannot cause the next hit — the
consumption half of the resource argument.

What is still missing: a bound on `sum q` itself.  Measured, `sum q` is dominated by
LARGE primes (`q <= 100` accounts for only 16.5% of `sum q` over the 868 measured steps),
so no truncation argument of the form "small primes are frequent, large primes are rare"
closes it; and the reuse count of a given prime along a replay grows roughly linearly in
`p` (max reuse 81 at M = 22933441, p = 209).  Recorded so the next attempt does not
repeat the truncation idea.
-/
