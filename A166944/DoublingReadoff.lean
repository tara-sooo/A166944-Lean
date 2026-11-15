/-
# sq2 / angle A : what determines S ?

`S = Cf - (2 * M - 2)` is the terminal excess of the canonical
moving-horizon replay at the strict record `M`, whose value is `Cf`.
This file records the exact characterisation of `S` and the kernel-checked
witnesses for it.

## The answer to "what determines S"

Let `D n = rec_a n - n` (the repository coordinate) and

    rec_E n = rec_a n - 2 * n        (the Rowland excess).

For every strict record from `M = 43` up to `M = 1427749` (measured to
`3.1e6`), the canonical replay satisfies

    Cf = D (2 * M - 2)                 -- the horizon IS the coordinate value
    S  = rec_E (2 * M - 2)                 -- so S IS the excess at that index

Equivalently, writing `C = M - 1` for the previous fixed point of `D`,

    S = 2 * C - D (2 * C) = rec_E (2 * C)  =  (rec_a (2C) - a C) - C .

So `S` is completely determined by the accumulated excess at the **single
index `2M - 2`**.  It is *not* a twin-prime-gap quantity: the twin-prime
centres that the replay passes over do not enter the formula at all.

## Why this closes the angle

* The cap `S <= (M + 4) / 2` rewrites to `4 * rec_E (2M-2) <= M + 4`, i.e.
  `rec_E n <= n / 4 + O(1)` at `n = 2M - 2`.
* The repository's global result is `rec_a n <= 3 n`
  (`CanonicalRecord.a_le_three_mul`), i.e. `rec_E n <= n`: a factor of four too weak.
* The factor four is **real**, not laziness: `rec_E 18 = 18` and `rec_E 156 = 156`
  attain the global bound, so `rec_a n <= 3 n` is sharp and no bound of the form
  "`a` grows at most `c n`" with `c < 3` exists.  The naive strengthening
  `4 * rec_E n <= n` is **false** (proved below).

Consequently the cap cannot be reached by any global growth estimate; it needs
information about `E` at the specific indices `2M - 2`, which is exactly where
the previous twelve routes stalled.

## Status of this file

All arithmetic certificates use `decide` on the raw definition, so the file is
core-only: no imports, no Mathlib, no `sorry`, no `axiom`, no `native_decide`.
`decide` needs `O(index)` stack, so the kernel-checked indices stop at `22038`;
larger indices are reported as measurements in the accompanying report and are
deliberately *not* asserted here.
-/

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

namespace A166944Research

namespace Doubling

/-- OEIS A166944: `rec_a 0 = 0`, `rec_a 1 = 2`, and for `n + 2`,
`rec_a (n+2) = rec_a (n+1) + gcd (n+2) (rec_a (n+1))` when `n + 2` is even and
`rec_a (n+2) = rec_a (n+1) + gcd n (rec_a (n+1))` when `n + 2` is odd. -/
def rec_a : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let prev := rec_a (n + 1)
    let idx := n + 2
    if idx % 2 = 0 then prev + Nat.gcd idx prev
    else prev + Nat.gcd (idx - 2) prev

/-- First difference `rec_d n = rec_a n - rec_a (n-1)`. -/
def rec_d (n : Nat) : Nat := rec_a n - rec_a (n - 1)

/-- The D-coordinate `D n = rec_a n - n`. -/
def rec_D (n : Nat) : Nat := rec_a n - n

/-- The **Rowland excess** `rec_E n = rec_a n - 2 * n`.  The repository's `rec_a n <= 3 n`
is `rec_E n <= n`; the cap needs `rec_E n <= n / 4` at `n = 2M - 2`. -/
def rec_E (n : Nat) : Nat := rec_a n - 2 * n

/-! ## 1.  `Cf = D (2M - 2)`: the horizon identity

The right-hand sides are the horizons `Cf` of the canonical replay at the
records `M = 43, 139, 313, 661`, and the doubled indices `2M - 2`. -/

theorem Cf_eq_D_doubling :
    rec_D 84 = 138 ∧ rec_D 276 = 312 ∧ rec_D 624 = 660 ∧ rec_D 1320 = 1320 ∧
      rec_D 2640 = 2658 ∧ rec_D 5316 = 5418 ∧ rec_D 10836 = 10890 := by
  decide

/-! ## 2.  `S = rec_E (2M - 2)`: the characterisation of `S`

The values are `S = 54, 36, 36, 0, 18, 102, 54` for
`M = 43, 139, 313, 661, 1321, 2659, 5419`.  Nothing about twin primes occurs. -/

theorem S_eq_E_doubling :
    rec_E 84 = 54 ∧ rec_E 276 = 36 ∧ rec_E 624 = 36 ∧ rec_E 1320 = 0 ∧
      rec_E 2640 = 18 ∧ rec_E 5316 = 102 ∧ rec_E 10836 = 54 := by
  decide

/-- The two readings agree: `S = D (2M-2) - (2M-2) = rec_E (2M-2)`. -/
theorem S_is_horizon_minus_index :
    rec_D 84 - 84 = 54 ∧ rec_D 276 - 276 = 36 ∧ rec_D 624 - 624 = 36 ∧
      rec_D 1320 - 1320 = 0 ∧ rec_D 2640 - 2640 = 18 ∧ rec_D 5316 - 5316 = 102 ∧
      rec_D 10836 - 10836 = 54 := by
  decide

/-- The fixed points of `D` reached by the replay (`D t = t`), together with
`a t = 2 t` there.  This is why the horizon reading and the excess reading of
`S` coincide: at a fixed point `a t = 2 t`, so `E t = 0` and `D t = t`. -/
theorem D_fixed_points :
    rec_D 42 = 42 ∧ rec_D 138 = 138 ∧ rec_D 312 = 312 ∧ rec_D 660 = 660 ∧
      rec_D 1320 = 1320 ∧ rec_D 2658 = 2658 ∧ rec_D 5418 = 5418 ∧ rec_D 10890 = 10890 := by
  decide

theorem a_eq_two_mul_at_fixed :
    rec_a 42 = 2 * 42 ∧ rec_a 138 = 2 * 138 ∧ rec_a 312 = 2 * 312 ∧ rec_a 660 = 2 * 660 ∧
      rec_a 1320 = 2 * 1320 ∧ rec_a 2658 = 2 * 2658 ∧ rec_a 5418 = 2 * 5418 := by
  decide

/-- The previous record value plus one is the fixed point, i.e. `M = C + 1`, so
`2M - 2 = 2C` is *twice the previous record value*.  This is the index at which
`S` is read, and it depends only on the record value `M`, not on any replay
detail. -/
theorem index_is_twice_previous_record :
    84 = 2 * 42 ∧ 276 = 2 * 138 ∧ 624 = 2 * 312 ∧ 1320 = 2 * 660 ∧
      2640 = 2 * 1320 ∧ 5316 = 2 * 2658 ∧ 10836 = 2 * 5418 := by
  decide

/-- The cap in excess form: since `S = rec_E (2M-2)`, the cap `S <= (M+4)/2` is
`2 * rec_E (2M-2) <= M + 4`.  In terms of the read-off index `n = 2M - 2` this asks
for `rec_E n <= n/4 + O(1)`; the global bound `rec_E n <= n` is a factor of four too
weak.  The three lemmas below make that arithmetic exact. -/
theorem cap_in_excess_form {M S : Nat} (hS : S = rec_E (2 * M - 2)) :
    2 * S ≤ M + 4 ↔ 2 * rec_E (2 * M - 2) ≤ M + 4 := by
  rw [hS]

/-- **What would suffice.**  A bound `rec_E n <= n / 4` at `n = 2M - 2`, i.e. `E` at
a quarter of its index, implies the cap. -/
theorem cap_of_quarter_bound {M : Nat} (h : 4 * rec_E (2 * M - 2) ≤ 2 * M - 2) :
    2 * rec_E (2 * M - 2) ≤ M + 4 := by
  omega

/-- **What the global bound gives.**  The best global result available is
`rec_E n <= n`; at `n = 2M - 2` it yields `2 * rec_E (2M-2) <= 4M - 4`. -/
theorem global_bound_consequence {M : Nat} (h : rec_E (2 * M - 2) ≤ 2 * M - 2) :
    2 * rec_E (2 * M - 2) ≤ 4 * M - 4 := by
  omega

/-- The two differ by exactly the factor the route cannot cross: for `M >= 4` the
target `M + 4` is strictly below the free consequence `4 * M - 4`. -/
theorem target_strictly_below_global_consequence {M : Nat} (hM : 4 ≤ M) :
    M + 4 < 4 * M - 4 := by
  omega

/-- The rewritten cap at every kernel-feasible record.  It holds, with the
margin growing: `S / M` falls from `0.259` at `M = 139` to `0.010` at
`M = 5419`. -/
theorem cap_holds_at_records :
    2 * rec_E 276 ≤ 139 + 4 ∧ 2 * rec_E 624 ≤ 313 + 4 ∧ 2 * rec_E 1320 ≤ 661 + 4 ∧
      2 * rec_E 2640 ≤ 1321 + 4 ∧ 2 * rec_E 5316 ≤ 2659 + 4 ∧
      2 * rec_E 10836 ≤ 5419 + 4 := by
  decide

/-- The cap fails at `M = 43`: `S = 54 > (43+4)/2 = 23.5`.  This is the
smallest record where the relaxed cap is violated, which is why every statement
in the repository carries a threshold such as `968 ≤ M`. -/
theorem cap_fails_at_43 : ¬ (2 * rec_E 84 ≤ 43 + 4) := by decide

/-! ## 4.  The factor four is real

`rec_a n <= 3 n` is attained, so `rec_E n <= n` cannot be improved globally, and the
strengthening the route would need is false. -/

theorem E_eq_self_at_18 : rec_E 18 = 18 := by decide
theorem E_eq_self_at_156 : rec_E 156 = 156 := by decide
theorem a_18_eq_three_mul : rec_a 18 = 3 * 18 := by decide
theorem a_156_eq_three_mul : rec_a 156 = 3 * 156 := by decide

/-- **REFUTATION.**  `4 * rec_E n <= n` for all `n` is false.  Hence the cap cannot
follow from any estimate of the shape "`rec_a n` grows at most `c * n`" with
`c < 3`; the special position of the indices `2M - 2` is indispensable. -/
theorem quarter_bound_is_false : ¬ (∀ n : Nat, 4 * rec_E n ≤ n) := by
  intro h
  have h18 := h 18
  rw [E_eq_self_at_18] at h18
  omega

theorem quarter_bound_is_false_at_156 : ¬ (4 * rec_E 156 ≤ 156) := by
  rw [E_eq_self_at_156]
  omega

/-- **`decide`-checked cap at the largest feasible record** (`M = 1427749` needs
index `2855496`, beyond the kernel's stack budget for `decide`).  The largest
record whose excess is checkable here is `M = 5419`. -/
theorem largest_feasible_excess : rec_E 10836 = 54 ∧ 4 * rec_E 10836 ≤ 5419 + 4 := by
  decide

/-! ## 5.  Why twin primes are irrelevant to `S`

`S` is the value of `E` at the single index `2M - 2`, an index determined by the
previous *record value* alone.  Whatever twin-prime centres the replay visits or
skips in between cannot change it.  The kernel-checkable content of that remark
is that `S` is reproducible from `a` at that one index: -/

theorem S_139_from_single_index :
    rec_E 276 = 36 ∧ rec_D 276 = 312 ∧ 276 = 2 * 138 ∧ rec_D 138 = 138 := by
  decide

/-- At `M = 139` the replay's start index `156` is *smaller* than `2M - 2 = 276`,
so the read-off index `2M - 2` is not even the start of the quiet tail.  This is
what makes the "distance to the first twin-prime centre" reading impossible. -/
theorem readoff_index_exceeds_start :
    156 < 276 ∧ 276 = 2 * 138 ∧ 138 < 156 := by
  decide

end Doubling

end A166944Research

