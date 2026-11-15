import A166944.RoomQuantum
import A166944.CanonicalRecord
import A166944.RoomLedger
import A166944.BandReentry
import A166944.ExcessGap

/-!
# Angle rq-2: characterising the degenerate (pinned) branch of the room quantum

`RoomQuantum.moving_horizon_room_quantum` splits every moving-horizon step into a
*pinned* branch (`C' - r = 2 * d r` for even `r`, `C' - r + 4 = 3 * d r` for odd `r`)
and a *non-degenerate* branch carrying one further quantum of room.  Measured on the
canonical replays below `2 * 10 ^ 6` there are 230 steps, of which exactly **three**
are pinned -- and all three sit at `M = 13` and `M = 43`, the two records where the
cap breaks.  This file settles what can and cannot be proved about that branch.

## Results

**R1 (characterisation).**  Pinned even is *equivalent* to `C - 1 = r + d r`, and
pinned odd to `C + 3 = r + 2 * d r`.  Both are `↔`.  This is the answer to "when does
the degenerate branch occur": *exactly* when the two divisibilities
`d r ∣ r` and `d r ∣ C - 1` share the whole of `C - 1 - r` with no room to spare.

**R2 (cofactor forced).**  Writing `r = d r * c` and `C - 1 = d r * t` (the quotient
normal form), pinned even is *exactly* `t = c + 1`; pinned odd is *exactly*
`t = c + 2`.  So the branch is a **codimension-one condition on the quotient pair**,
not a condition on `c` alone.  In particular pinned even does *not* force `c = 2`:
the minimal case is `c = 2`, `t = 3`, which is what the three measured instances
have, but larger cofactors are arithmetically consistent.

**R3 (room on the branch) -- COROLLARY, NOT NEW.**  Pinned even gives the *exact*
room `C - s = (r - s) + d r + 1`; pinned odd gives `C - s = (r - s) + (2 * d r - 3)`.
Both are the *first disjunct* of the committed `RoomCount.moving_horizon_room_dichotomy_even`
/ `_odd`, so they add no strength.  Recorded for completeness and explicitly marked
as prior art, not as the "new input" the angle hoped for.  See section 10.

**R4 (the branch is real, in a capped replay).**  The exclusion is *false* as a
theorem.  `M = 43` has a genuine capped canonical replay whose fifth step is pinned
even, entered with the cap intact.

**R5 (why no local argument can exclude it).**  The pinned condition is a *single
linear equation* on `(r, C, d r)`; the local step system therefore has pinned
solutions for the whole two-parameter family, exhibited below.  Any exclusion must
use the ordered-history/global constraint, and `M = 43` shows that constraint does
not exclude it either.

Everything is pure core (`decide` / `omega` / `simp` / `rfl`, `rw`); no `ring`,
`linarith`, `norm_num`, `positivity` or `interval_cases`.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. Arithmetic core

These are pure-`Nat` facts about the step law `C' = C + (e - 1)` and the two pinned
equations.  They are separated out because `omega` handles them far more reliably in
the abstract form (no `Nat` truncating subtraction on *unknown* values) than inline.
Each is stated with exactly the side conditions needed, so no hidden hypothesis
enters the main theorems. -/

private theorem even_pin_arith {C r e C' : Nat} (he : 1 ≤ e)
    (hupd : C' = C + (e - 1)) (hpin : C' - r = 2 * e) : C - 1 = r + e := by omega

private theorem even_unpin_arith {C r e C' : Nat} (he : 1 ≤ e)
    (hupd : C' = C + (e - 1)) (hpin : C - 1 = r + e) : C' - r = 2 * e := by omega

private theorem odd_pin_arith {C r e C' : Nat} (he : 1 ≤ e) (hrC : r ≤ C)
    (hupd : C' = C + (e - 1)) (hpin : C' - r + 4 = 3 * e) : C + 3 = r + 2 * e := by
  omega

private theorem odd_unpin_arith {C r e C' : Nat} (he : 1 ≤ e) (hrC : r ≤ C)
    (hupd : C' = C + (e - 1)) (hpin : C + 3 = r + 2 * e) : C' - r + 4 = 3 * e := by
  omega

private theorem even_quot_gap {C r e t c : Nat} (he : 0 < e) (hr : r = e * c)
    (hC : C - 1 = e * t) (hpin : C - 1 = r + e) : t = c + 1 := by
  have h1 : e * t = r + e := by omega
  rw [hr] at h1
  exact Nat.eq_of_mul_eq_mul_left he (by omega)

private theorem odd_quot_gap {C r e t c : Nat} (he : 0 < e) (hr2 : 2 ≤ r)
    (hr : r - 2 = e * c) (hC : C + 1 = e * t) (hpin : C + 3 = r + 2 * e) : t = c + 2 := by
  have h1 : e * t = (r - 2) + 2 * e := by omega
  rw [hr] at h1
  have h2 : e * (c + 2) = e * c + 2 * e := by rw [Nat.mul_add, Nat.mul_comm e 2]
  exact Nat.eq_of_mul_eq_mul_left he (by omega)

private theorem even_flat_of_succ {C r e t c : Nat} (hr : r = e * c)
    (hC : C - 1 = e * t) (htc : t = c + 1) : C - 1 = r + e := by
  have hec : e * (c + 1) = e * c + e := Nat.mul_succ e c
  rw [hC, htc, hr, hec]

private theorem odd_flat_of_succ {C r e t c : Nat} (hr : r = e * c + 2)
    (hC : C + 1 = e * t) (htc : t = c + 2) : C + 3 = r + 2 * e := by
  have h2 : e * (c + 2) = e * c + 2 * e := by rw [Nat.mul_add, Nat.mul_comm e 2]
  have hAdd : C + 1 = e * c + 2 * e := by rw [hC, htc, h2]
  omega

private theorem even_room_arith {C s r e : Nat} (he : 1 ≤ e) (hrC : r ≤ C)
    (hsr : s ≤ r) (h : C - 1 = r + e) : C - s = (r - s) + e + 1 := by
  have hCk : C = r + (e + 1) := by omega
  rw [hCk, Nat.sub_add_comm hsr, Nat.add_assoc]

private theorem odd_room_arith {C s r e : Nat} (he3 : 3 ≤ e) (hsr : s ≤ r)
    (h : C + 3 = r + 2 * e) : C - s = (r - s) + (2 * e - 3) := by
  have hCk : C = r + (2 * e - 3) := by omega
  rw [hCk, Nat.sub_add_comm hsr]

/-! ## 2. R1: the pinned branch as an exact linear condition on `(r, C)`

The left-to-right direction is immediate from the step law.  The converse needs the
divisibility: the pinned equation says `C - 1 - r = d r`, so `d r ∣ C - 1 - r`; but
`d r` divides both `r` and `C - 1`, hence divides the *difference*, giving
`d r ∣ d r` on the nose and the two sides are equal.  That is the whole mechanism,
and it is why the condition is codimension one. -/

/-- **R1, even: pinned is exactly `C - 1 = r + d r`.** -/
theorem moving_horizon_pinned_even_iff_horizon_eq {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    C' - r = 2 * d r ↔ C - 1 = r + d r := by
  have he1 : 1 ≤ d r := by have := moving_horizon_step_event_ge_three hstep; omega
  have hupd := moving_horizon_step_update hstep
  refine ⟨fun hpin => even_pin_arith he1 hupd hpin, fun hflat => ?_⟩
  exact even_unpin_arith he1 hupd hflat

/-- **R1, odd: pinned is exactly `C + 3 = r + 2 * d r`.** -/
theorem moving_horizon_pinned_odd_iff_horizon_eq {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    C' - r + 4 = 3 * d r ↔ C + 3 = r + 2 * d r := by
  have he1 : 1 ≤ d r := by have := moving_horizon_step_event_ge_three hstep; omega
  have hupd := moving_horizon_step_update hstep
  have hrC : r ≤ C := hstep.2.2.1
  refine ⟨fun hpin => odd_pin_arith he1 hrC hupd hpin, fun hflat => ?_⟩
  exact odd_unpin_arith he1 hrC hupd hflat

/-! ## 3. R2: the branch is `t = c + 1` (even) / `t = c + 2` (odd) on the quotients

`RoomQuantum` records the quotient pair implicitly: `C - s = (r - s) + 1 + d r * q`
(even) and `C - s + 3 = (r - s) + d r * q` (odd), with `q` the *room* quotient.  The
horizon quotient `t = (C - 1) / d r` is what the pinned condition pins down.  Both
statements are `↔`, so they can be used in either direction, and neither assumes
`c = 2`. -/

/-- **R2, even: pinned is exactly `t = c + 1`, given `r = d r * c` and
`C - 1 = d r * t`.** -/
theorem moving_horizon_pinned_even_iff_quotient_succ {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) {c t : Nat}
    (hc : r = d r * c) (ht : C - 1 = d r * t) :
    C' - r = 2 * d r ↔ t = c + 1 := by
  have hepos : 0 < d r := by have := moving_horizon_step_event_ge_three hstep; omega
  have he1 : 1 ≤ d r := hepos
  have hupd := moving_horizon_step_update hstep
  constructor
  · intro hpin
    have hflat := (moving_horizon_pinned_even_iff_horizon_eq hstep hr).1 hpin
    exact even_quot_gap hepos hc ht hflat
  · intro htc
    exact (moving_horizon_pinned_even_iff_horizon_eq hstep hr).2
      (even_flat_of_succ hc ht htc)

/-- **R2, odd: pinned is exactly `t = c + 2`, given `r - 2 = d r * c` and
`C + 1 = d r * t`.** -/
theorem moving_horizon_pinned_odd_iff_quotient_succ {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) {c t : Nat}
    (hc : r - 2 = d r * c) (ht : C + 1 = d r * t) :
    C' - r + 4 = 3 * d r ↔ t = c + 2 := by
  have hepos : 0 < d r := by have := moving_horizon_step_event_ge_three hstep; omega
  have he1 : 1 ≤ d r := hepos
  have hr2 : 2 ≤ r := by
    have hr3 : 3 ≤ r :=
      Nat.le_trans (Nat.succ_le_succ hstep.1.1) (Nat.succ_le_of_lt hstep.2.1)
    omega
  have hrC : r ≤ C := hstep.2.2.1
  constructor
  · intro hpin
    have hflat := (moving_horizon_pinned_odd_iff_horizon_eq hstep hr).1 hpin
    exact odd_quot_gap hepos hr2 hc ht hflat
  · intro htc
    have hcr : r = d r * c + 2 := by omega
    exact (moving_horizon_pinned_odd_iff_horizon_eq hstep hr).2
      (odd_flat_of_succ hcr ht htc)

/-- **R2 corollary: pinned even forces `d r ∣ r - d r` and the cofactor gap is
exactly one.**  `r = d r * c` and `t = c + 1` give `C - 1 - r = d r`, so the *only*
way the two divisors can interlock is with a single quantum of slack between
`C - 1 - r` and `d r`. -/
theorem moving_horizon_pinned_even_slack_eq_event {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0)
    (hpin : C' - r = 2 * d r) : C - 1 - r = d r := by
  have hflat := (moving_horizon_pinned_even_iff_horizon_eq hstep hr).1 hpin
  have hrC : r ≤ C := hstep.2.2.1
  omega

/-- **The odd analogue.** -/
theorem moving_horizon_pinned_odd_slack_eq_two_mul_event {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1)
    (hpin : C' - r + 4 = 3 * d r) : C + 1 - (r - 2) = 2 * d r := by
  have hflat := (moving_horizon_pinned_odd_iff_horizon_eq hstep hr).1 hpin
  have hr2 : 2 ≤ r := by
    have hr3 : 3 ≤ r :=
      Nat.le_trans (Nat.succ_le_succ hstep.1.1) (Nat.succ_le_of_lt hstep.2.1)
    omega
  omega

/-! ## 4. R3: the room on the pinned branch, exactly -- prior art, restated

**Novelty warning.**  These are *not* new.  `RoomCount.moving_horizon_room_dichotomy_even`
(committed, `a9256a7`) already states `C - s = (r - s) + d r + 1 ∨ (r - s) + d r + 3 ≤ C - s`,
and its first disjunct is exactly the pinned case.  The theorem below is that
disjunct, obtained from the pinned hypothesis; it is recorded because the angle
asked for it, but it must not be double-counted as progress.  Same for the odd form.
The genuinely new content of this file is R1, R2, R4 and R5. -/

/-- **R3, even: the room is exactly `(r - s) + d r + 1`.** -/
theorem moving_horizon_pinned_even_room_eq {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0)
    (hpin : C' - r = 2 * d r) : C - s = (r - s) + d r + 1 := by
  have hflat := (moving_horizon_pinned_even_iff_horizon_eq hstep hr).1 hpin
  have he1 : 1 ≤ d r := by have := moving_horizon_step_event_ge_three hstep; omega
  exact even_room_arith he1 hstep.2.2.1 (Nat.le_of_lt hstep.2.1) hflat

/-- **R3, odd: the room is exactly `(r - s) + (2 * d r - 3)`.** -/
theorem moving_horizon_pinned_odd_room_eq {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1)
    (hpin : C' - r + 4 = 3 * d r) : C - s = (r - s) + (2 * d r - 3) := by
  have hflat := (moving_horizon_pinned_odd_iff_horizon_eq hstep hr).1 hpin
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  exact odd_room_arith he3 (Nat.le_of_lt hstep.2.1) hflat

/-- **R3, even, the room lower bound in the usable direction.** -/
theorem moving_horizon_pinned_even_room_lower {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0)
    (hpin : C' - r = 2 * d r) : (r - s) + d r + 1 ≤ C - s :=
  Nat.le_of_eq (moving_horizon_pinned_even_room_eq hstep hr hpin).symm

/-- **R3, odd, the room lower bound in the usable direction.** -/
theorem moving_horizon_pinned_odd_room_lower {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1)
    (hpin : C' - r + 4 = 3 * d r) : (r - s) + (2 * d r - 3) ≤ C - s :=
  Nat.le_of_eq (moving_horizon_pinned_odd_room_eq hstep hr hpin).symm

/-! ## 5. R4: the pinned branch occurs in a genuine capped canonical replay

This is the refutation of the hoped-for exclusion.  It is *not* a hypothetical: the
repository's `path43`/`max43` are a certified six-step canonical replay at `M = 43`,
and `step43_5` is pinned even.  The step is entered with room `40 ≤ 43`, so the cap
is intact when the pinned branch is taken -- the branch is not an artefact of an
already-violated cap. -/

/-- **The `M = 43` pinned step, certified.** -/
theorem step43_5_pinned :
    IsMovingHorizonStep 60 100 66 132 ∧ 66 % 2 = 0 ∧ 132 - 66 = 2 * d 66 :=
  ⟨step43_5, by decide, by decide⟩

/-- **Its shape: `C' = 2 * r` and `d r = 33`, with `C - 1 = r + d r`.** -/
theorem step43_5_pinned_shape :
    132 - 66 = 2 * d 66 ∧ 132 = 2 * 66 ∧ d 66 = 33 ∧ 100 - 1 = 66 + d 66 := by
  decide

/-- **The pinned branch occurs inside a genuine capped canonical replay.**
`path43` and `max43` are the certified replay and attained maximum; one of its steps
is pinned.  Hence "the degenerate branch can be excluded from the moving-horizon
hypotheses" is **false**. -/
theorem pinned_branch_occurs_in_capped_replay :
    HasMovingHorizonPathTo (43 + 2) (2 * 43 - 2) 79 138 6 ∧
      IsAttainedPreviousMaximum 43 79 ∧
      IsMovingHorizonStep 60 100 66 132 ∧ 132 - 66 = 2 * d 66 :=
  ⟨path43, max43, step43_5, by decide⟩

/-- **The cap is intact when the pinned step is entered.** -/
theorem step43_5_entered_inside_band : 100 - 60 = 40 ∧ 100 - 60 ≤ 43 := by
  decide

/-- **And the pinned step is exactly the shape predicted by R2 with `c = 2`, `t = 3`:**
`r = d r * 2` and `C - 1 = d r * 3`. -/
theorem step43_5_quotients : 66 = d 66 * 2 ∧ 100 - 1 = d 66 * 3 := by
  decide

/-! ## 6. R4': the two pinned steps at `M = 13`, one of each parity

`M = 13` is the only measured record carrying *both* parities of the pinned branch,
and they occur consecutively.  Recording them makes the `M = 13` exceptionality
explicit rather than anecdotal. -/

/-- **The odd pinned step at `M = 13`:** `r = 17`, `d r = 5`, `r - 2 = 3 * d r`. -/
theorem step13_1_pinned :
    IsMovingHorizonStep 15 24 17 28 ∧ 17 % 2 = 1 ∧ 17 = 3 * d 17 + 2 ∧
      24 + 1 - (17 - 2) = 2 * d 17 :=
  ⟨step13_1, by decide, by decide, by decide⟩

/-- **The even pinned step at `M = 13`:** `r = 18`, `d r = 9`, `C - 1 = r + d r`. -/
theorem step13_2_pinned :
    IsMovingHorizonStep 17 28 18 36 ∧ 18 % 2 = 0 ∧ 18 = 2 * d 18 ∧
      28 - 1 = 18 + d 18 :=
  ⟨step13_2, by decide, by decide, by decide⟩

/-- **Both parities of the pinned branch occur at `M = 13`, consecutively.** -/
theorem both_parities_pinned_at_thirteen :
    (IsMovingHorizonStep 15 24 17 28 ∧ 17 = 3 * d 17 + 2) ∧
      (IsMovingHorizonStep 17 28 18 36 ∧ 18 = 2 * d 18) :=
  ⟨⟨step13_1, by decide⟩, ⟨step13_2, by decide⟩⟩

/-! ## 7. R5: no local argument can exclude the branch

The pinned condition is one linear equation in `(r, C, d r)`, and the step law is
another.  Two equations in three unknowns leave a one-parameter family, so the local
system is never contradictory -- for *every* event value `e` there is a pinned datum
with arbitrarily large cofactor.  The kernel-checkable form of this is the
`∃`-statement below: for arbitrary `e ≥ 3` and arbitrary even cofactor `c ≥ 2` there
is a `C` making the pinned equation hold.

This is exactly why the three measured instances could not be removed by any
rearrangement of the local hypotheses, and why the exclusion has to be a *global*
statement.  It also shows that the tempting converse "pinned forces `c = 2`" is
false: `c` is free. -/

/-- **The pinned even equation is solvable with an arbitrary cofactor.**  Given
`e ≥ 1` and any `c`, take `r = e * c` and `C = r + e + 1`; then the pinned equation
`C - 1 = r + e` holds by `rfl`-level arithmetic.  So the cofactor `c = r / e` is not
constrained by the branch. -/
theorem pinned_even_cofactor_free (e c : Nat) (he : 0 < e) :
    let r := e * c
    let C := r + e + 1
    C - 1 = r + e ∧ r = e * c := by
  intro r C
  exact ⟨by simp only [C]; omega, rfl⟩

/-- **The pinned even equation with the step law, at a prescribed event value.**
For `e ≥ 3` and any `c ≥ 1` the triple `(r, C, C') = (e * c, r + e + 1, C + e - 1)`
satisfies both the pinned equation and the step law -- the two equations that the
step imposes on `(r, C, C')` beyond divisibility. -/
theorem pinned_even_local_system_solvable (e c : Nat) (he : 3 ≤ e) (hc : 1 ≤ c) :
    ∃ r C C' : Nat, e ≤ r ∧ C' = C + (e - 1) ∧ C' - r = 2 * e ∧ r = e * c := by
  refine ⟨e * c, e * c + e + 1, e * c + 2 * e, ?_, ?_, ?_, rfl⟩
  · calc e = e * 1 := (Nat.mul_one e).symm
      _ ≤ e * c := Nat.mul_le_mul_left e hc
  · omega
  · omega

/-- **The odd analogue:** for `e ≥ 3` and any `c ≥ 1` the triple
`(r, C, C') = (e * c + 2, r + 2 * e - 3, C + e - 1)` satisfies the pinned odd
equation and the step law. -/
theorem pinned_odd_local_system_solvable (e c : Nat) (he : 3 ≤ e) (hc : 1 ≤ c) :
    ∃ r C C' : Nat, 3 ≤ r ∧ C' = C + (e - 1) ∧ C' - r + 4 = 3 * e ∧ r - 2 = e * c := by
  have hle : e ≤ e * c := by
    calc e = e * 1 := (Nat.mul_one e).symm
      _ ≤ e * c := Nat.mul_le_mul_left e hc
  refine ⟨e * c + 2, e * c + 2 + 2 * e - 3, e * c + 2 + 2 * e - 3 + (e - 1),
    by omega, rfl, ?_, by omega⟩
  omega

/-! ## 8. The `c = 2` case is exactly the `M = 43` shape

The three measured pinned steps all have the minimal cofactor (`c = 2` even,
`c = 3` odd).  Recording the implication "minimal cofactor ⟹ `C' = 2 * r`" makes the
measured shape a theorem rather than a coincidence, and it isolates the case the
frontier replays actually realise. -/

/-- **Minimal even cofactor: `r = 2 * d r` implies `C' = 2 * r`.** -/
theorem moving_horizon_pinned_even_two_mul_event_horizon {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0)
    (hpin : C' - r = 2 * d r) (hmin : r = 2 * d r) : C' = 2 * r := by
  have hflat := (moving_horizon_pinned_even_iff_horizon_eq hstep hr).1 hpin
  have hupd := moving_horizon_step_update hstep
  omega

/-- **Minimal odd cofactor: `r = 3 * d r + 2` pins the room to `r - 6`.**  The odd
branch's minimal cofactor does *not* give `C' = 2 * r` (that is the even branch's
shape): it gives the room `C' - r` exactly, as a function of `r` alone. -/
theorem moving_horizon_pinned_odd_min_cofactor_room {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1)
    (hpin : C' - r + 4 = 3 * d r) (hmin : r = 3 * d r + 2) :
    (C' - r) + 6 = r := by
  have hflat := (moving_horizon_pinned_odd_iff_horizon_eq hstep hr).1 hpin
  have hupd := moving_horizon_step_update hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  omega

end A166944Research

/-! ## 9. Novelty audit -- what is new and what is not

Recorded so this file is not mistaken for more progress than it is.

| result | status |
| --- | --- |
| R1 even `↔ C - 1 = r + d r` | **new** as an `↔`; `Lemmas.moving_horizon_critical_predecessor_factorization` (line 5977) has the forward direction only, under the `critical` hypothesis |
| R1 odd `↔ C + 3 = r + 2 * d r` | **new** (no prior statement found by grep) |
| R2 `↔ t = c + 1` / `t = c + 2` | **new** as an `↔`; the `critical` special case is inside `moving_horizon_critical_predecessor_factorization` |
| R3 room equality | **NOT new** -- first disjunct of the committed `RoomCount.moving_horizon_room_dichotomy_{even,odd}` |
| R4 refutation at `M = 43` | **new as an assembly**; `path43`/`max43`/`step43_5` are existing, their combination as a refutation of branch-exclusion is new |
| R5 local solvability | **new** |

The negative half of this file (R4, R5) is the load-bearing part: it closes the route
"exclude the pinned branch from the hypotheses" rather than opening it. -/

/-! ## 10. Axiom audit -/

#print axioms A166944Research.moving_horizon_pinned_even_iff_horizon_eq
#print axioms A166944Research.moving_horizon_pinned_odd_iff_horizon_eq
#print axioms A166944Research.moving_horizon_pinned_even_iff_quotient_succ
#print axioms A166944Research.moving_horizon_pinned_odd_iff_quotient_succ
#print axioms A166944Research.moving_horizon_pinned_even_slack_eq_event
#print axioms A166944Research.moving_horizon_pinned_odd_slack_eq_two_mul_event
#print axioms A166944Research.moving_horizon_pinned_even_room_eq
#print axioms A166944Research.moving_horizon_pinned_odd_room_eq
#print axioms A166944Research.step43_5_pinned
#print axioms A166944Research.step43_5_pinned_shape
#print axioms A166944Research.pinned_branch_occurs_in_capped_replay
#print axioms A166944Research.step43_5_entered_inside_band
#print axioms A166944Research.step43_5_quotients
#print axioms A166944Research.step13_1_pinned
#print axioms A166944Research.step13_2_pinned
#print axioms A166944Research.both_parities_pinned_at_thirteen
#print axioms A166944Research.pinned_even_cofactor_free
#print axioms A166944Research.pinned_even_local_system_solvable
#print axioms A166944Research.pinned_odd_local_system_solvable
#print axioms A166944Research.moving_horizon_pinned_even_two_mul_event_horizon
#print axioms A166944Research.moving_horizon_pinned_odd_min_cofactor_room
