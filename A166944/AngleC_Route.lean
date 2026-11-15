import A166944.QuietReturn
/-
  Angle aE2, part 3: the `sqrt` route **would have sufficed**.

  Parts 1 and 2 establish that the brief's headline angle is vacuous and that its
  natural strengthening (`e ≤ sqrt (C ± 1)`, equivalently `e * e ≤ C ± 1`) is
  false, with in-domain counterexamples at `M = 13` and `M = 139`.

  Neither fact is interesting on its own.  This file supplies the reason they
  matter: if `e ≤ sqrt (C ± 1)` held at every event, the summation route would
  close the cap at the target's own threshold `M ≥ 45895573` from the event-count
  hypothesis and the horizon bound `Cf ≤ 3M + 4`.

  So the refutation in part 2 is not "an opportunity that was hopeless anyway" --
  it closes a route that *worked*.  That is the strongest form the negative result
  can take.

  Tactic discipline: `decide` / `omega` / `simp` / `rfl`, plus `ac_rfl` (pure core,
  associativity/commutativity only) for the polynomial reassociations that `omega`
  cannot do and `simp` will not close.  `omega` cannot expand products of
  variables, so every polynomial step is factored into two `Nat.mul_le_mul` steps
  whose side conditions are *linear*.
-/

import A166944.Lemmas
import A166944.ResearchDefs
import A166944.Sharp48

namespace A166944Research

set_option maxRecDepth 100000

/-! ## 1. The `Nat.sqrt` lemmas this import closure lacks

`Sharp48.lean` records that only the *lower* direction `sqrt_ge_of_sq_le` was in
the tree.  The route needs the *upper* direction, and monotonicity.  Both are
proved here in the same style, because `decide` cannot evaluate `Nat.sqrt` and
`omega` cannot multiply. -/

/-- **Upper square-root bound.**  `n < (m + 1) * (m + 1)` implies `sqrt n ≤ m`. -/
theorem sqrt_le_of_lt_succ_sq {n m : Nat} (h : n < (m + 1) * (m + 1)) :
    Nat.sqrt n ≤ m := by
  by_cases hle : Nat.sqrt n ≤ m
  · exact hle
  · exfalso
    have h1 : m + 1 ≤ Nat.sqrt n := by omega
    have h2 : (m + 1) * (m + 1) ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_self_le_mul_self h1
    have h3 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    omega

/-- **Monotonicity of `Nat.sqrt`**, also absent from the tree. -/
theorem sqrt_mono {n m : Nat} (h : n ≤ m) : Nat.sqrt n ≤ Nat.sqrt m := by
  by_cases hle : Nat.sqrt n ≤ Nat.sqrt m
  · exact hle
  · exfalso
    have h1 : Nat.sqrt m + 1 ≤ Nat.sqrt n := by omega
    have h2 : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_self_le_mul_self h1
    have h3 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have h4 : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
    omega

/-- **Square monotonicity in the usable direction.**  `x * x ≤ y * y` gives
`x ≤ y`; this is the bridge from a squared estimate back to the estimate. -/
theorem le_of_mul_self_le_mul_self {x y : Nat} (h : x * x ≤ y * y) : x ≤ y :=
  Nat.mul_self_le_mul_self_iff.mp h

/-! ## 2. The quadratic that drives the route

The route needs `64 p² (3M + 4) ≤ (3M - 9)²`.  With `48 p² ≤ M - 1` this reduces
to the single quadratic

    4 (M - 1) (3M + 4) ≤ 3 (3M - 9) (3M - 9),

whose leading coefficients are `12` and `27`.  Numerically it first holds at
`M = 10`, so it is far below the target threshold.

The proof is a two-factor chain, not an expansion:

* `3M + 4 ≤ 2 (3M - 9)` for `M ≥ 8`;
* `8 (M - 1) ≤ 3 (3M - 9)` for `M ≥ 19`. -/

/-- **The route's quadratic.**  Both side conditions are linear in `M`, which is
what keeps the proof inside `omega`; `ac_rfl` handles the reassociation. -/
theorem route_quadratic {M : Nat} (hM : 45895573 ≤ M) :
    4 * (M - 1) * (3 * M + 4) ≤ 3 * (3 * M - 9) * (3 * M - 9) := by
  have hstep : 4 * (M - 1) * (3 * M + 4) ≤ 4 * (M - 1) * (2 * (3 * M - 9)) :=
    Nat.mul_le_mul_left (4 * (M - 1)) (by omega)
  have hkey : 4 * (M - 1) * (2 * (3 * M - 9)) ≤
      3 * (3 * M - 9) * (3 * M - 9) := by
    have hassoc : 4 * (M - 1) * (2 * (3 * M - 9)) =
        (4 * (M - 1) * 2) * (3 * M - 9) := by ac_rfl
    rw [hassoc]
    have h4 : 4 * (M - 1) * 2 ≤ 3 * (3 * M - 9) := by omega
    calc
      (4 * (M - 1) * 2) * (3 * M - 9) ≤ (3 * (3 * M - 9)) * (3 * M - 9) :=
        Nat.mul_le_mul_right (3 * M - 9) h4
      _ = 3 * (3 * M - 9) * (3 * M - 9) := by ac_rfl
  omega

/-! ## 3. The route closes: `p * sqrt Cf ≤ (3M - 9) / 8`

With `48 p² ≤ M - 1` (the event-count hypothesis `48 p² + 1 < M` in the tree's
own form) and `Cf ≤ 3M + 4` (the tree's horizon bound), the product `p * sqrt Cf`
fits inside the cap's allowance. -/

/-- **The core estimate**, with `Cf` already replaced by the horizon bound:
`8 p sqrt (3M + 4) ≤ 3M - 9`.  The squaring step uses
`Nat.mul_self_le_mul_self_iff` and the identity `(8 p s)² = 64 p² s²`. -/
theorem route_core {M p : Nat} (hM : 45895573 ≤ M) (hp : 48 * (p * p) ≤ M - 1) :
    8 * (p * Nat.sqrt (3 * M + 4)) ≤ 3 * M - 9 := by
  have hss : Nat.sqrt (3 * M + 4) * Nat.sqrt (3 * M + 4) ≤ 3 * M + 4 :=
    Nat.sqrt_le _
  have hquad := route_quadratic hM
  -- Strategy: multiply the goal by 3 so that every constant is divisible by 3,
  -- then square and use `576 = 12 * 48` together with `12 = 3 * 4`.
  --   (24 p s)^2 = 576 p^2 s^2 ≤ 576 p^2 (3M+4) = 12 (48 p^2) (3M+4)
  --             ≤ 12 (M-1) (3M+4) ≤ 3 * (4 (M-1) (3M+4)) ≤ 3 * 3 (3M-9)^2
  --             = (3 (3M-9))^2.
  have h1 : 576 * (p * p) * (Nat.sqrt (3 * M + 4) * Nat.sqrt (3 * M + 4)) ≤
      576 * (p * p) * (3 * M + 4) := Nat.mul_le_mul_left (576 * (p * p)) hss
  have h2 : 576 * (p * p) * (3 * M + 4) ≤ 12 * (M - 1) * (3 * M + 4) := by
    have he : 576 * (p * p) * (3 * M + 4) = 12 * (48 * (p * p)) * (3 * M + 4) := by
      rw [show (576 : Nat) = 12 * 48 by decide]
      ac_rfl
    rw [he]
    exact Nat.mul_le_mul_right (3 * M + 4) (Nat.mul_le_mul_left 12 hp)
  have h3 : 12 * (M - 1) * (3 * M + 4) ≤ 3 * (3 * (3 * M - 9) * (3 * M - 9)) := by
    have he : 12 * (M - 1) * (3 * M + 4) = 3 * (4 * (M - 1) * (3 * M + 4)) := by
      rw [show (12 : Nat) = 3 * 4 by decide]
      ac_rfl
    rw [he]
    exact Nat.mul_le_mul_left 3 hquad
  have h4 : 3 * (3 * (3 * M - 9) * (3 * M - 9)) =
      (3 * (3 * M - 9)) * (3 * (3 * M - 9)) := by ac_rfl
  have hsq : (24 * (p * Nat.sqrt (3 * M + 4))) * (24 * (p * Nat.sqrt (3 * M + 4))) ≤
      (3 * (3 * M - 9)) * (3 * (3 * M - 9)) := by
    have hexp : (24 * (p * Nat.sqrt (3 * M + 4))) * (24 * (p * Nat.sqrt (3 * M + 4))) =
        576 * (p * p) * (Nat.sqrt (3 * M + 4) * Nat.sqrt (3 * M + 4)) := by
      rw [show (576 : Nat) = 24 * 24 by decide]
      ac_rfl
    rw [hexp]
    -- h1, h2, h3 chain the left side down to `3 * (3*(3M-9)*(3M-9))`, and `h4`
    -- rewrites that to the goal's right side; `omega` composes the four.
    omega
  have h24 : 24 * (p * Nat.sqrt (3 * M + 4)) ≤ 3 * (3 * M - 9) :=
    le_of_mul_self_le_mul_self hsq
  have hcom : 24 * (p * Nat.sqrt (3 * M + 4)) = 3 * (8 * (p * Nat.sqrt (3 * M + 4))) := by
    ac_rfl
  rw [hcom] at h24
  exact Nat.le_of_mul_le_mul_left h24 (by decide : 0 < 3)

/-- **The route would have sufficed.**  Under the target's threshold, the
event-count hypothesis in its tree form (`48 p² ≤ M - 1`) and the horizon bound
`Cf ≤ 3M + 4`, the product `p * sqrt Cf` is inside the cap's allowance
`(3M - 9) / 8`.

Together with `Σ e_i ≤ p * sqrt Cf` (`list_sum_le_length_mul`, part 1) and the
ledger identity `Σ e_i = S + p`, this is the cap.  The only missing input was
`e ≤ sqrt (C ± 1)` at each event -- and part 2 shows that input is *false*. -/
theorem sqrt_route_would_suffice {M p Cf : Nat} (hM : 45895573 ≤ M)
    (hp : 48 * (p * p) ≤ M - 1) (hCf : Cf ≤ 3 * M + 4) :
    p * Nat.sqrt Cf ≤ (3 * M - 9) / 8 := by
  have hmono : Nat.sqrt Cf ≤ Nat.sqrt (3 * M + 4) := sqrt_mono hCf
  have hcore := route_core hM hp
  have hprod : p * Nat.sqrt Cf ≤ p * Nat.sqrt (3 * M + 4) :=
    Nat.mul_le_mul_left p hmono
  have hkey : 8 * (p * Nat.sqrt Cf) ≤ 3 * M - 9 := by
    have h8 : 8 * (p * Nat.sqrt Cf) ≤ 8 * (p * Nat.sqrt (3 * M + 4)) :=
      Nat.mul_le_mul_left 8 hprod
    omega
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 8)]
  omega

/-! ## 4. Axiom audit -/

#print axioms sqrt_le_of_lt_succ_sq
#print axioms sqrt_mono
#print axioms le_of_mul_self_le_mul_self
#print axioms route_quadratic
#print axioms route_core
#print axioms sqrt_route_would_suffice

end A166944Research
