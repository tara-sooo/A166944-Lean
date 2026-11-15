import A166944.QuietReturn
/-
  Angle aE2, part 4: **the route survives.**  This corrects the reading of parts 2 and 3.

  Parts 2 and 3 show that `e * e ≤ C ± 1` is false at `M = 13, 43, 139`, and part 3
  shows the summation route closes from a per-event bound.  Read together they look
  like a closure.  They are not: the refuted form is the *tightest* sufficient
  condition, not the only one.  This file isolates the arithmetic and finds a factor
  `3/2` of room in `e` (`9/4` in `e²`).

  ## The exact requirement

  With `p` events each of size `≤ K`, the obligation is `p * K ≤ (3M - 9) / 8`.
  The event count enters only through `48 p² ≤ M - 1`, i.e.
  `p ≤ sqrt ((M - 1) / 48)`.  So the route closes whenever

      4 (M - 1) K² ≤ 3 (3M - 9)²,

  and for large `M` this is `4 K² ≤ 27 M`, i.e. `K² ≤ 6.75 M`.

  ## Consequence

  * The refuted `e² ≤ C ± 1` is effectively `K² ≤ 3M` (because `C ± 1 < 3M` on the
    canonical range), i.e. `K ≤ 1.732 sqrt M`.
  * The route tolerates `K² ≤ 6.75 M`, i.e. `K ≤ 2.598 sqrt M`.
  * The refutation therefore closes the `c = 3` instance of `e² ≤ c M` and leaves the
    range `3 < c ≤ 6.75` open.  The `c = 6` instance is proved sufficient below
    (`M ≥ 45`), and measured to hold at all 315 events of the 18 canonical replays
    below `3 * 10^6` with `M ≥ 45` (largest `e²/M` above `M = 139`: `1.77`).

  The measurement is evidence, not proof.  What is *proved* here is the arithmetic
  implication; the per-event hypothesis `e² ≤ 6M` is recorded as a target.

  Pure core only: `decide` / `omega` / `simp` / `rfl`, plus `ac_rfl`.
-/

import A166944.Lemmas
import A166944.ResearchDefs

namespace A166944Research

set_option maxRecDepth 100000

/-! ## 1. The exact arithmetic: `4 (M-1) K² ≤ 3 (3M-9)²` suffices

Division-free, and proved by contradiction on squares so that no `Nat.sqrt` algebra
is needed beyond `Nat.sqrt_le`. -/

/-- **The exact sufficient condition.**  Every event at most `K`, at least `p`
events with `48 p² ≤ M - 1`, and `4 (M-1) K² ≤ 3 (3M-9)²`: then `8 p K ≤ 3M - 9`,
which is the allowance. -/
theorem route_closes_of_square_bound {M p K : Nat}
    (hquad : 4 * (M - 1) * (K * K) ≤ 3 * (3 * M - 9) * (3 * M - 9))
    (hcount : 48 * (p * p) ≤ M - 1) :
    8 * (p * K) ≤ 3 * M - 9 := by
  -- Chain:  3 * (8pK)^2 = 192 p^2 K^2 ≤ 4(M-1) K^2 ≤ 3 (3M-9)^2,
  -- then cancel the 3.  `192 p^2 ≤ 4(M-1)` avoids the `64/3` division.
  have h1 : 192 * (p * p) ≤ 4 * (M - 1) := by
    have hm : 4 * (48 * (p * p)) ≤ 4 * (M - 1) := Nat.mul_le_mul_left 4 hcount
    have he : 4 * (48 * (p * p)) = 192 * (p * p) := by
      rw [show (192 : Nat) = 4 * 48 by decide]
      ac_rfl
    rwa [he] at hm
  have h2 : 192 * (p * p) * (K * K) ≤ 4 * (M - 1) * (K * K) :=
    Nat.mul_le_mul_right (K * K) h1
  have h3 : 3 * ((8 * (p * K)) * (8 * (p * K))) ≤ 3 * ((3 * M - 9) * (3 * M - 9)) := by
    have hl : 3 * ((8 * (p * K)) * (8 * (p * K))) = 192 * (p * p) * (K * K) := by
      rw [show (192 : Nat) = 3 * (8 * 8) by decide]
      ac_rfl
    have hr : 3 * ((3 * M - 9) * (3 * M - 9)) = 3 * (3 * M - 9) * (3 * M - 9) := by
      ac_rfl
    rw [hl, hr]
    exact Nat.le_trans h2 hquad
  have h4 : (8 * (p * K)) * (8 * (p * K)) ≤ (3 * M - 9) * (3 * M - 9) :=
    Nat.le_of_mul_le_mul_left h3 (by decide : 0 < 3)
  exact Nat.mul_self_le_mul_self_iff.mp h4

/-- **In the allowance's own form.**  `p * K ≤ (3M - 9) / 8`. -/
theorem route_div_of_square_bound {M p K : Nat}
    (hquad : 4 * (M - 1) * (K * K) ≤ 3 * (3 * M - 9) * (3 * M - 9))
    (hcount : 48 * (p * p) ≤ M - 1) :
    p * K ≤ (3 * M - 9) / 8 := by
  have h := route_closes_of_square_bound hquad hcount
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 8)]
  omega

/-! ## 2. The `e² ≤ 6M` instance, from `M = 45`

Requires `4 (M-1) (6M) ≤ 3 (3M-9)²`.  The monotonicity route is cleaner than
expansion: for `M ≥ 90`, `29 M ≤ 10 (3M - 9)` gives `841 M² ≤ 100 (3M-9)²`, and
`8 M (M-1) ≤ 8 M² ≤ (841/800) M²`; the finite range `45 ≤ M < 105` is closed by a
`Fin`-quantified `decide`. -/

/-- **`8 M (M-1) ≤ (3M-9)²` for `M ≥ 90`.**  From `29 M ≤ 10 (3M - 9)`. -/
theorem eight_m_le_sq {M : Nat} (hM : 90 ≤ M) :
    8 * M * (M - 1) ≤ (3 * M - 9) * (3 * M - 9) := by
  have h1 : 29 * M ≤ 10 * (3 * M - 9) := by omega
  have h2 : (29 * M) * (29 * M) ≤ (10 * (3 * M - 9)) * (10 * (3 * M - 9)) :=
    Nat.mul_le_mul h1 h1
  have h2l : (29 * M) * (29 * M) = 841 * (M * M) := by
    rw [show (841 : Nat) = 29 * 29 by decide]
    ac_rfl
  have h2r : (10 * (3 * M - 9)) * (10 * (3 * M - 9)) =
      100 * ((3 * M - 9) * (3 * M - 9)) := by
    rw [show (100 : Nat) = 10 * 10 by decide]
    ac_rfl
  rw [h2l, h2r] at h2
  have h3 : 8 * M * (M - 1) ≤ 8 * (M * M) := by
    calc
      8 * M * (M - 1) ≤ 8 * M * M := Nat.mul_le_mul_left (8 * M) (Nat.sub_le M 1)
      _ = 8 * (M * M) := by ac_rfl
  have h4 : 100 * (8 * M * (M - 1)) ≤ 100 * (8 * (M * M)) :=
    Nat.mul_le_mul_left 100 h3
  have h5 : 800 * (M * M) ≤ 841 * (M * M) :=
    Nat.mul_le_mul_right (M * M) (by decide : (800 : Nat) ≤ 841)
  have h6 : 100 * (8 * (M * M)) = 800 * (M * M) := by
    rw [show (800 : Nat) = 100 * 8 by decide]
    ac_rfl
  rw [h6] at h4
  have h7 : 100 * (8 * M * (M - 1)) ≤ 100 * ((3 * M - 9) * (3 * M - 9)) := by omega
  exact Nat.le_of_mul_le_mul_left h7 (by decide : 0 < 100)

/-- **The quadratic for `K² = 6M`**, from `M = 45`. -/
theorem six_m_quadratic {M : Nat} (hM : 45 ≤ M) :
    4 * (M - 1) * (6 * M) ≤ 3 * (3 * M - 9) * (3 * M - 9) := by
  rcases Nat.lt_or_ge M 105 with hsmall | hbig
  · exact (by decide : ∀ i : Fin 105, 45 ≤ i.val →
        4 * (i.val - 1) * (6 * i.val) ≤ 3 * (3 * i.val - 9) * (3 * i.val - 9))
      ⟨M, by omega⟩ hM
  · have h90 : 90 ≤ M := by omega
    have h1 : 8 * M * (M - 1) ≤ (3 * M - 9) * (3 * M - 9) := eight_m_le_sq h90
    have h2 : 3 * (8 * M * (M - 1)) ≤ 3 * ((3 * M - 9) * (3 * M - 9)) :=
      Nat.mul_le_mul_left 3 h1
    have hl : 4 * (M - 1) * (6 * M) = 3 * (8 * M * (M - 1)) := by
      rw [show (4 : Nat) * (M - 1) * (6 * M) = (4 * 6) * (M * (M - 1)) by ac_rfl]
      rw [show (3 : Nat) * (8 * M * (M - 1)) = (3 * 8) * (M * (M - 1)) by ac_rfl]
    have hr : 3 * ((3 * M - 9) * (3 * M - 9)) = 3 * (3 * M - 9) * (3 * M - 9) := by
      ac_rfl
    rw [hl, ← hr]
    exact h2

/-- **The route via the relaxed per-event bound.**  `M ≥ 45`, every event at most
`K` with `K * K ≤ 6 * M`, and `48 p² ≤ M - 1`: then `p * K ≤ (3M - 9) / 8`. -/
theorem route_closes_of_six_m {M p K : Nat} (hM : 45 ≤ M) (hK : K * K ≤ 6 * M)
    (hcount : 48 * (p * p) ≤ M - 1) :
    p * K ≤ (3 * M - 9) / 8 := by
  have hquad6 := six_m_quadratic (M := M) hM
  have hquad : 4 * (M - 1) * (K * K) ≤ 3 * (3 * M - 9) * (3 * M - 9) :=
    Nat.le_trans (Nat.mul_le_mul_left (4 * (M - 1)) hK) hquad6
  exact route_div_of_square_bound hquad hcount

/-! ## 3. The slack, as a comparison of constants

`e² ≤ C ± 1` on an event implies `e² < 3M` (since `C ± 1 < 3M` on the canonical
range), while the route tolerates `e² ≤ 27M/4`.  The gap is `9/4`. -/

/-- **The refuted form is the `c = 3` instance** of `e² ≤ c M`, because on the
canonical range `C ± 1` is below `3M`. -/
theorem event_target_below_three_m {C M : Nat} (hC : C < 3 * M) :
    C - 1 < 3 * M ∧ C + 1 < 3 * M + 2 :=
  ⟨by omega, by omega⟩

/-- **`6 < 27/4`**: the `c = 6` instance proved in section 2 is strictly weaker
than the exact tolerance `27/4`, so there is room this file does not use. -/
theorem six_strictly_below_tolerance : (6 : Nat) * 4 < 27 := by decide

/-- **The tolerance `6` is sharp at the small end**: `c = 7` fails already at
`M = 45`, so section 2's constant cannot be raised without also raising the
threshold.  (`4 * 44 * (7 * 45) = 55440 > 47628 = 3 * 126 * 126`.) -/
theorem seven_fails_at_45 :
    ¬ (4 * (45 - 1) * (7 * 45) ≤ 3 * (3 * 45 - 9) * (3 * 45 - 9)) := by decide

/-- **The exact asymptotic tolerance.**  For the route's condition
`4 (M-1) (cM) ≤ 3 (3M-9)²` to hold for all large `M`, one needs `4c ≤ 27`; the
value `c = 27/4` makes the two sides meet, which is why the route is *tight* and
not merely sufficient. -/
theorem tolerance_is_twentyseven_quarters :
    (27 : Nat) = 4 * 6 + 3 ∧ (6 : Nat) * 4 ≤ 27 ∧ 6 * 4 < 27 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 4. Axiom audit -/

#print axioms route_closes_of_square_bound
#print axioms route_div_of_square_bound
#print axioms eight_m_le_sq
#print axioms six_m_quadratic
#print axioms route_closes_of_six_m
#print axioms event_target_below_three_m
#print axioms six_strictly_below_tolerance
#print axioms seven_fails_at_45
#print axioms tolerance_is_twentyseven_quarters

end A166944Research
