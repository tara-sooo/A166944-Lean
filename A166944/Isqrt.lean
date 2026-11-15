/-
A square root that exists in every environment.

Lean v4.29.0-rc3 -- the environment of the Twin Prime Conjecture mission on
Prove2Me -- has no `Init.Data.Nat.Sqrt`: the module is absent from the toolchain,
`isqrt` is absent from `Init`, and `#check @isqrt` fails. Under v4.33.1 the
kernel grew both, and this development imported them, which is why the
recurrence side stopped building when it was transplanted.

The root is only ever used through three facts:

* `isqrt_sq_le  n : sqrt n * sqrt n <= n`
* `lt_succ_isqrt n : n < (sqrt n + 1) * (sqrt n + 1)`
* `isqrt_le_isqrt : m <= n -> sqrt m <= sqrt n`

so a replacement only has to supply those. The one below is an upward scan:
start at `0` and advance while the next square still fits. It needs `n + 1` steps
of fuel, because `(k+1) * (k+1) <= n` is false once `k` reaches `n`, so the scan
can never advance past `n` and always stops in time for `k * k <= n` to have been
preserved along the way. That is a purely structural recursion on the fuel, and
the whole development is core-only (`decide`, `omega`, `simp`, `rfl`).
-/
import Init

namespace A166944Research

/-- Fuel-driven upward scan. From `lo`, advance while the next square still fits
inside `n`; when it no longer does, `lo` is the answer. -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, lo => lo
  | f + 1, lo => if (lo + 1) * (lo + 1) ≤ n then isqrtGo n f (lo + 1) else lo

/-- Integer square root by upward scan with `n + 1` steps of fuel. -/
def isqrt (n : Nat) : Nat := isqrtGo n (n + 1) 0

/-- **The scan is correct whenever the fuel lasts.**

`lo * lo <= n` is the invariant that makes the stopping branch sound, and
`n + 1 <= lo + f` is what guarantees the scan stops rather than running out of
fuel: from `lo * lo <= n` we get `lo <= n`, so at most `n + 1 - lo` advances are
possible and `f` covers them.

The `f = 0` branch is vacuous: `n + 1 <= lo` together with `lo <= lo * lo <= n`
is a contradiction, discharged without touching the product nonlinearly. -/
theorem isqrtGo_spec {n f lo : Nat} (hlo : lo * lo ≤ n) (hfuel : n + 1 ≤ lo + f) :
    (isqrtGo n f lo) * (isqrtGo n f lo) ≤ n ∧
      n < (isqrtGo n f lo + 1) * (isqrtGo n f lo + 1) := by
  induction f generalizing lo with
  | zero =>
      exfalso
      have h1 : lo ≤ lo * lo := Nat.le_mul_self lo
      have h2 : lo < n + 1 :=
        Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt hlo (Nat.lt_succ_self n))
      have h3 : n + 1 ≤ lo := by simpa using hfuel
      exact absurd h3 (Nat.not_le.mpr h2)
  | succ f ih =>
      simp only [isqrtGo]
      by_cases h : (lo + 1) * (lo + 1) ≤ n
      · simp only [h, if_true]
        exact ih (by omega) (by omega)
      · simp only [h, if_false]
        exact ⟨hlo, Nat.not_le.mp h⟩

/-- **Lower bound.** The square of the root is at most the radicand. -/
theorem isqrt_sq_le (n : Nat) : isqrt n * isqrt n ≤ n :=
  (isqrtGo_spec (n := n) (f := n + 1) (lo := 0) (Nat.zero_le n) (by omega)).1

/-- **Upper bound.** The radicand is below the next square. -/
theorem lt_succ_isqrt (n : Nat) : n < (isqrt n + 1) * (isqrt n + 1) :=
  (isqrtGo_spec (n := n) (f := n + 1) (lo := 0) (Nat.zero_le n) (by omega)).2

/-- **Monotonicity.** The root is monotone in the radicand. -/
theorem isqrt_le_isqrt {m n : Nat} (h : m ≤ n) : isqrt m ≤ isqrt n := by
  by_cases hle : isqrt m ≤ isqrt n
  · exact hle
  · exfalso
    have h1 : isqrt n + 1 ≤ isqrt m := by omega
    have h2 : (isqrt n + 1) * (isqrt n + 1) ≤ isqrt m * isqrt m :=
      Nat.mul_self_le_mul_self h1
    have h3 : isqrt m * isqrt m ≤ m := isqrt_sq_le m
    have h4 : n < (isqrt n + 1) * (isqrt n + 1) := lt_succ_isqrt n
    omega

/-- **The direction a numerical witness needs.** A square below `n` bounds the
root of `n` from below, which is how a concrete radicand is discharged without
evaluating the root. -/
theorem le_isqrt_of_sq_le {n m : Nat} (h : m * m ≤ n) : m ≤ isqrt n := by
  by_cases hle : m ≤ isqrt n
  · exact hle
  · exfalso
    have h1 : isqrt n + 1 ≤ m := by omega
    have h2 : (isqrt n + 1) * (isqrt n + 1) ≤ m * m :=
      Nat.mul_self_le_mul_self h1
    have h3 : n < (isqrt n + 1) * (isqrt n + 1) := lt_succ_isqrt n
    omega

end A166944Research
