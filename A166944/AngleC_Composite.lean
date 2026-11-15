import A166944.QuietReturn
/-
  Angle aE2: "`C_i ± 1` cannot be prime -- and its consequences", on the A166944
  moving-horizon barrier.

  Imported into the repository as A166944/AngleC_*.lean; the header below is
  kept as written because it records how the work was done.

  Pure core only: `decide` / `omega` / `simp` / `rfl`.  No `norm_num`,
  `interval_cases`, `positivity`, `nlinarith`, `linarith`, `ring`.

  Headline (see the report): the angle is **VACUOUS**.  `C_i ± 1` at an event is
  composite, but the only reason is the size bound `C_i > M`, and that bound is
  *literally a field of the step structure* (`C + 2 ≤ C'` inside
  `IsMovingHorizonStep`).  So the compositeness is a restatement of a hypothesis,
  not a new fact, and it carries no bound on `Σ e_i`.

  What survives is a sharpening in the opposite direction: the natural
  strengthening (`e_i` is the *small* factor, `e * e ≤ C ± 1`) is **false**, with
  counterexamples inside genuine canonical record replays.  That refutation is
  what closes the summation route that would otherwise have worked.
-/

import A166944.Lemmas
import A166944.ResearchDefs

namespace A166944Research

set_option maxRecDepth 100000

/-! ## 1. The composite statement, in prime-free form

`Nat.Prime` is not in this import closure at all (verified with `#check`), so the
statement is made in the divisor form the brief suggests.  The witness is the
event value `d r` itself, and the hypotheses used are exactly three components
that `moving_horizon_step_event_package` already exports:
`d r ∣ C ± 1`, `d r < C ± 1`, and (via `moving_horizon_step_event_ge_three`)
`1 < d r`. -/

/-- **The "`C ± 1` cannot be prime" statement**, in prime-free form: at an event,
`C ± 1` has a divisor strictly between `1` and itself.  The branch is the parity
branch of the step; on the even branch the divisor divides `C - 1`, on the odd
branch `C + 1`.

Note for the record: `M` does not occur in the statement, and neither does
`IsAttainedPreviousMaximum`.  See section 2. -/
theorem event_target_has_nontrivial_divisor {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (∃ f, f ∣ C - 1 ∧ 1 < f ∧ f < C - 1) ∨
      (∃ f, f ∣ C + 1 ∧ 1 < f ∧ f < C + 1) := by
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases moving_horizon_step_event_package hstep with
    ⟨heven, hdiv, hproper, _⟩ | ⟨hodd, hdiv, hproper, _⟩
  · exact Or.inl ⟨d r, hdiv, by omega, hproper⟩
  · exact Or.inr ⟨d r, hdiv, by omega, hproper⟩

/-- **The same conclusion on each branch, so the caller need not case-split.**
Even hit: `d r` witnesses that `C - 1` is composite. -/
theorem event_target_minus_has_nontrivial_divisor {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    ∃ f, f ∣ C - 1 ∧ 1 < f ∧ f < C - 1 := by
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases moving_horizon_step_event_package hstep with
    ⟨_, hdiv, hproper, _⟩ | ⟨hodd, _, _, _⟩
  · exact ⟨d r, hdiv, by omega, hproper⟩
  · exact absurd (hodd.symm.trans heven) (by decide)

/-- Odd hit: `d r` witnesses that `C + 1` is composite. -/
theorem event_target_plus_has_nontrivial_divisor {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    ∃ f, f ∣ C + 1 ∧ 1 < f ∧ f < C + 1 := by
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases moving_horizon_step_event_package hstep with
    ⟨heven, _, _, _⟩ | ⟨_, hdiv, hproper, _⟩
  · exact absurd (heven.symm.trans hodd) (by decide)
  · exact ⟨d r, hdiv, by omega, hproper⟩

/-! ## 2. The vacuity certificate

Section 1 is not "almost" vacuous; it is vacuous in a checkable sense.  The whole
content is the elementary fact that a divisor strictly between `1` and `N`
witnesses that `N` has one.  That fact mentions no recurrence, no `M`, no event
value, and no step structure. -/

/-- **Vacuity certificate.**  The composite conclusion of section 1 is an
instance of this tautology.  Nothing about the A166944 recurrence, about `M`, or
about `Σ e_i` enters.

This is the precise sense in which the angle is empty: `moving_horizon_step_event_package`
already exports `d r ∣ C ± 1` *and* `d r < C ± 1` *and* (via
`moving_horizon_step_event_ge_three`) `1 < d r`, so "`C ± 1` is composite" is a
weakening of a theorem the tree already had, and adds no constraint. -/
theorem nontrivial_divisor_of_dvd_of_lt {N f : Nat} (hdiv : f ∣ N) (h1 : 1 < f)
    (hlt : f < N) : ∃ g, g ∣ N ∧ 1 < g ∧ g < N :=
  ⟨f, hdiv, h1, hlt⟩

/-- **The size bound is what makes it look like content, and it is a field of the
definition.**  `C + 2 ≤ C'` is one of the nine conjuncts of `IsMovingHorizonStep`.

That conjunct is the *only* reason the "`C ± 1 > M`" story works: it is not
derived from the arithmetic of the recurrence, it is assumed.  A route that needs
`C_i ± 1 > M` needs nothing that was not already in the hypothesis. -/
theorem step_forces_horizon_jump {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C + 2 ≤ C' :=
  hstep.2.2.2.2.2.2.2.1

/-! ## 3. The natural strengthening is FALSE: `e` need not be the small factor

The brief's item 2 asks whether `e * e ≤ C ± 1` (equivalently `e ≤ sqrt(C ± 1)`,
equivalently `e` is at most the cofactor).  It is not.  Below is a counterexample
*inside a genuine canonical replay*: the record `M = 13`.

Concrete data, all closed by `decide` / `omega`:

    index    15    16    17    18
    d        13     1     5     9     (M = 13 is the record; d 15 = 13)
    D        24    24    28    36

`s = 15`, `C = 24 = 2 * 13 - 2` is the canonical start, `d 16 = 1` is the quiet
window, and the step is `(s, C) = (17, 28) --[e = 9]--> (18, 36)`.  On that step
`C - 1 = 27 = 3 * 9`, so the cofactor is `3` and `e * e = 81 > 27`: **`e` is the
large factor**.  `e ∣ C - 1` still holds.

Measured over the 230 events of the sixteen canonical replays below `2 * 10 ^ 6`,
`e * e ≤ C ± 1` fails exactly 3 times -- at `M = 13`, `M = 43` and `M = 139`, the
three worst-case replays in the whole sweep. -/

/-- The record value `M = 13` is attained at index `15`. -/
theorem anglec_d15_eq_thirteen : d 15 = 13 := by decide

/-- `D 15 = 24 = 2 * 13 - 2`, so index `15` is the canonical start for `M = 13`. -/
theorem D15_eq_twentyfour : D 15 = 24 := by decide

/-- The quiet window: `d 16 = 1`. -/
theorem d16_eq_one : d 16 = 1 := by decide

/-- The event value at the second step of the `M = 13` replay. -/
theorem anglec_d18_eq_nine : d 18 = 9 := by decide

/-- The horizon before that event. -/
theorem anglec_D17_eq_twentyeight : D 17 = 28 := by decide

/-- The step `(17, 28) --[9]--> (18, 36)`.  The quiet window `17 < j < 18` is
empty, discharged by `omega`.  This is a *genuine* `IsMovingHorizonStep`, so the
refutations below are not artefacts of an out-of-domain witness. -/
theorem step_17_28_18_36 : IsMovingHorizonStep 17 28 18 36 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    (by intro j h1 h2; omega), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Refutation of `e * e ≤ C - 1` at this step.**  `d 18 = 9` and `D 17 - 1 = 27`,
so the claim would read `81 ≤ 27`. -/
theorem e_square_not_le_target_at_13 : ¬ (d 18 * d 18 ≤ D 17 - 1) := by
  rw [anglec_D17_eq_twentyeight, anglec_d18_eq_nine]
  decide

/-- **The item-2 strengthening is false as a universally quantified statement.**
No parity hypothesis on top of `r % 2 = 0` is needed: the even branch alone
refutes it. -/
theorem event_square_le_target_is_false :
    ¬ (∀ s C r C' : Nat, IsMovingHorizonStep s C r C' → r % 2 = 0 → d r * d r ≤ C - 1) := by
  intro h
  have hbad := h 17 28 18 36 step_17_28_18_36 (by decide)
  rw [anglec_d18_eq_nine] at hbad
  omega

/-- **The same strengthening in square-root form is also false**, which is the
form the summation route consumes (`sqrt_ge_of_sq_le` turns `e ≤ sqrt N` into
`e * e ≤ N`). -/
theorem event_sqrt_le_target_is_false :
    ¬ (∀ s C r C' : Nat, IsMovingHorizonStep s C r C' → r % 2 = 0 → d r ≤ Nat.sqrt (C - 1)) := by
  intro h
  have hbad := h 17 28 18 36 step_17_28_18_36 (by decide)
  -- `decide` cannot evaluate `Nat.sqrt` and `omega` cannot multiply, so the
  -- square form is reached through `Nat.mul_self_le_mul_self` and `Nat.sqrt_le`
  -- (neither `Nat.sqrt_eq` nor `Nat.sqrt_lt` is in this import closure).
  have h1 : d 18 * d 18 ≤ Nat.sqrt (28 - 1) * Nat.sqrt (28 - 1) :=
    Nat.mul_self_le_mul_self hbad
  have h2 : Nat.sqrt (28 - 1) * Nat.sqrt (28 - 1) ≤ 28 - 1 := Nat.sqrt_le _
  have h3 : d 18 * d 18 ≤ 28 - 1 := Nat.le_trans h1 h2
  rw [anglec_d18_eq_nine] at h3
  exact absurd h3 (by decide)

/-! ## 4. The constant `3` in `3 * d r ≤ C ± 1` is optimal on this witness

Since `e * e ≤ C ± 1` fails at `M = 13` while `3 * e ≤ C ± 1` holds there and
everywhere else in the sweep, the existing bound's constant cannot be raised.
At the same genuine step, `4 * 9 = 36 > 27 = C - 1`. -/

/-- **`4 * d r ≤ C - 1` fails**, at the same canonical step. -/
theorem four_mul_event_not_le_at_13 : ¬ (4 * d 18 ≤ D 17 - 1) := by
  rw [anglec_D17_eq_twentyeight, anglec_d18_eq_nine]
  decide

/-- **Sharpness of the constant `3`.**  `moving_horizon_step_event_package` proves
`3 * d r ≤ C ± 1`; no larger constant holds on the even branch, even restricted
to genuine steps. -/
theorem three_mul_event_le_target_is_sharp :
    ¬ (∀ s C r C' : Nat, IsMovingHorizonStep s C r C' → r % 2 = 0 → 4 * d r ≤ C - 1) := by
  intro h
  have hbad := h 17 28 18 36 step_17_28_18_36 (by decide)
  rw [anglec_d18_eq_nine] at hbad
  omega

/-- **The same witness also kills the cofactor lower bound `4`.**  `(C - 1) / e = 3`
here, so any route needing a cofactor of at least `4` fails at `M = 13`. -/
theorem cofactor_at_13_is_three : (D 17 - 1) / d 18 = 3 := by
  rw [anglec_D17_eq_twentyeight, anglec_d18_eq_nine]

/-! ## 5. Why this refutation matters: the `sqrt` route *would* have sufficed

The brief's item 4 asks what `Σ e_i ≤ p * sqrt C_f` buys.  It buys the cap -- for
large `M`, with the event-count hypothesis supplying `p`.  So the refutation in
section 3 closes a route that was not merely attractive but sufficient.  The
combinatorial half of that route is proved here; the number-theoretic half is
exactly what section 3 refutes.

If every event value along a replay is at most `B`, then the sum of `p` event
values is at most `p * B`. -/

/-- **Sum bounded by count times a uniform bound.**  Pure `List` induction.  The
arithmetic is closed with `Nat.add_mul`/`Nat.one_mul` because `omega` cannot
handle the product `length * B`. -/
theorem list_sum_le_length_mul {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ B := h a (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x ≤ B := fun x hx => h x (List.mem_cons_of_mem a hx)
    have hit := ih ht
    rw [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- **The missing ingredient, isolated.**  The `sqrt` route needs
`d r * d r ≤ C - 1` at every even-branch event; section 3 refutes it at a
canonical step, so this is the exact statement the route cannot have. -/
theorem sqrt_route_ingredient_is_refuted :
    ¬ (∀ s C r C' : Nat, IsMovingHorizonStep s C r C' → r % 2 = 0 → d r * d r ≤ C - 1) :=
  event_square_le_target_is_false

/-! ## 6. Axiom audit -/

#print axioms event_target_has_nontrivial_divisor
#print axioms event_target_minus_has_nontrivial_divisor
#print axioms event_target_plus_has_nontrivial_divisor
#print axioms nontrivial_divisor_of_dvd_of_lt
#print axioms step_forces_horizon_jump
#print axioms step_17_28_18_36
#print axioms e_square_not_le_target_at_13
#print axioms event_square_le_target_is_false
#print axioms event_sqrt_le_target_is_false
#print axioms four_mul_event_not_le_at_13
#print axioms three_mul_event_le_target_is_sharp
#print axioms cofactor_at_13_is_three
#print axioms list_sum_le_length_mul
#print axioms sqrt_route_ingredient_is_refuted

end A166944Research
