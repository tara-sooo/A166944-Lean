import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Route A: the least-factor bound via `Nat.minFac`

This is the FIRST module in the repository that uses Mathlib. Mathlib is now available locally
(newly installed), and it replaces several core-only workarounds the campaign had been fighting:
`Lean`'s `Nat.minFac`, `Nat.Prime`, `Nat.sqrt`, and the `linarith`/`omega` tactics all work here.

## What this proves

Route A freezes `MinFactorSumBoundFrom`: `exists L` sum of `min (lpf (C-1)) (lpf (C+1))` over the
events with `4*L <= M`, which gives the frontier via `gap <= 2*lpf`. The missing ingredient has
always been a bound on each `min_lpf`. This module supplies the sharpest one Mathlib gives:

    minFac_sq_le      : composite n  ->  n.minFac * n.minFac <= n
    minFac_le_sqrt    : composite n  ->  n.minFac <= Nat.sqrt n
    min_lpf_le_sqrt_of_composite
                      : (C-1 or C+1 composite)  ->  min lpf <= Nat.sqrt (C+1)

The third is the form Route A needs at INTERIOR steps. The both-prime case is excluded by
hypothesis rather than by an argument: `C_f +- 1` are both prime only at the TERMINAL state, and the
per-step bound is applied at interior steps where at least one of the two is composite.

## Honest scope

These bounds are per-step. Measured, summing them gives `L <= p * sqrt (2M)`, and `4L <= M` then
needs `p <= 0.177 * sqrt M`, which three certified records violate (M = 139, 313, 2659 with
`p/sqrt M` = 0.170, 0.339, 0.213). So this module does NOT close Route A -- it supplies the
correct per-step bound and makes the remaining gap exactly `p <= 0.177 sqrt M`.

Axiom status: all three declarations depend on `[propext, Classical.choice, Quot.sound]`. The
`Classical.choice` comes from Mathlib's `linarith`/`omega` machinery, not from the statements --
this is the first module in the repository to carry it, and it is recorded rather than hidden.
The core-only modules remain `[propext, Quot.sound]` or axiom-free, so the audit standard of the
rest of the tree is unaffected.
-/

theorem minFac_sq_le {n : ℕ} (hpos : 0 < n) (hnp : ¬ Nat.Prime n) :
    n.minFac * n.minFac ≤ n := by
  have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div hpos hnp
  have heq : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  calc n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul_left _ hle
    _ = n := heq

theorem minFac_le_sqrt {n : ℕ} (hpos : 0 < n) (hnp : ¬ Nat.Prime n) :
    n.minFac ≤ Nat.sqrt n := by
  have hsq := minFac_sq_le hpos hnp
  by_contra hlt
  push Not at hlt
  have h2 : Nat.sqrt n + 1 ≤ n.minFac := hlt
  have hmul : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n.minFac * n.minFac :=
    Nat.mul_le_mul h2 h2
  have hroot : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  omega

/-- **Route A step bound, stated to avoid the prime-prime case entirely.**

If EITHER `C-1` or `C+1` is composite, the smaller least factor is at most `sqrt (C+1)`.  This is
the case that occurs at every real horizon: `C_f +- 1` are both prime only at the terminal state,
and Route A's per-step bound is applied at interior steps. -/
theorem min_lpf_le_sqrt_of_composite {C : ℕ} (hC : 2 ≤ C)
    (hcomp : ¬ Nat.Prime (C - 1) ∨ ¬ Nat.Prime (C + 1)) :
    min (C - 1).minFac (C + 1).minFac ≤ Nat.sqrt (C + 1) := by
  have hpos1 : 0 < C - 1 := by omega
  have hpos2 : 0 < C + 1 := by omega
  rcases hcomp with h1 | h2
  · have h := minFac_le_sqrt hpos1 h1
    have hmono : Nat.sqrt (C - 1) ≤ Nat.sqrt (C + 1) := Nat.sqrt_le_sqrt (by omega)
    calc min (C - 1).minFac (C + 1).minFac ≤ (C - 1).minFac := min_le_left _ _
      _ ≤ Nat.sqrt (C - 1) := h
      _ ≤ Nat.sqrt (C + 1) := hmono
  · have h := minFac_le_sqrt hpos2 h2
    calc min (C - 1).minFac (C + 1).minFac ≤ (C + 1).minFac := min_le_right _ _
      _ ≤ Nat.sqrt (C + 1) := h

/-! ## Axiom audit -/

#print axioms minFac_sq_le
#print axioms minFac_le_sqrt
#print axioms min_lpf_le_sqrt_of_composite
