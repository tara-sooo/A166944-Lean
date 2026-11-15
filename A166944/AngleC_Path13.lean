import A166944.QuietReturn
import A166944.ConsecutiveEventGcd
/-
  Angle aE2, part 2: the `M = 13` refutation, placed inside a *full* canonical
  replay carrying the target's own hypotheses.

  Part 1 (`Composite.lean`) shows the brief's headline angle is vacuous, and that
  the natural strengthening `e * e ≤ C ± 1` fails at a single genuine step.  This
  file removes the last possible objection: that the failing step is somehow not
  part of a legal replay under the target's hypotheses.

  It is.  `M = 13` has `d (M + 2) = 13`, the four-step canonical replay from
  `(s, C) = (15, 24)` runs to `Cf = 42`, and the failing event `e = 9` with
  `e * e = 81 > 27` is its **second** step.

  The contrast in section 5 is the point of the whole angle: at the *terminal*
  horizon `Cf = 42` both `Cf - 1 = 41` and `Cf + 1 = 43` have no proper factor,
  while every event *target* on the way is composite.  So the compositeness of
  event targets and the primality of terminal horizons are not in tension, and
  neither one bounds `Σ e_i`.

  Pure core only: `decide` / `omega` / `simp` / `rfl`.  No `interval_cases`: the
  finite upper bound is proved by a `Fin 25`-quantified `decide`.
-/

import A166944.Lemmas
import A166944.ResearchDefs
import A166944.RecordReplay

namespace A166944Research

set_option maxRecDepth 100000

/-! ## 0. A uniform quiet-window helper (no `interval_cases`)

The quiet-window component of `IsMovingHorizonStep` is
`∀ j, s < j → j < r → d j = 1`.  Proving it by `omega` fails because `d j` is a
recurrence value, not a linear term.  The helper below converts it to a
`Fin (r - s - 1)`-indexed statement, which `decide` *can* enumerate.  This keeps
the file inside the allowed tactic set while still evaluating the window rather
than assuming it. -/

/-- **Quiet window from a finite enumeration.**  If `d` is `1` at the
`s + 1 + i` for every `i < r - s - 1`, it is `1` throughout `(s, r)`. -/
theorem quiet_window_of_fin {s r : Nat}
    (h : ∀ i : Fin (r - s - 1), d (s + 1 + i.val) = 1) :
    ∀ j : Nat, s < j → j < r → d j = 1 := by
  intro j h1 h2
  have hidx : j = s + 1 + (j - s - 1) := by omega
  rw [hidx]
  exact h ⟨j - s - 1, by omega⟩

/-! ## 1. The `M = 13` replay data, all closed by `decide` -/

theorem p2_d15 : d 15 = 13 := by decide
theorem p2_D15 : D 15 = 24 := by decide
theorem p2_d16 : d 16 = 1 := by decide
theorem p2_d17 : d 17 = 5 := by decide
theorem p2_D17 : D 17 = 28 := by decide
theorem p2_d18 : d 18 = 9 := by decide
theorem p2_d19 : d 19 = 1 := by decide
theorem p2_d20 : d 20 = 5 := by decide
theorem p2_d21 : d 21 = 1 := by decide
theorem p2_d23 : d 23 = 1 := by decide
theorem p2_d24 : d 24 = 3 := by decide
theorem p2_D24 : D 24 = 42 := by decide

/-! ## 2. The canonical start and the four steps

`IsMovingHorizonStep` has nine components; each step below discharges the quiet
window (`∀ j, s < j → j < r → d j = 1`) by `omega` on the empty/two-element
interior, so nothing is assumed. -/

/-- **The canonical start for `M = 13`**: `D 15 = 24 = 2 * 13 - 2` and `d 15 = 13`. -/
theorem p2_canonical_start : d 15 = 13 ∧ D 15 = 24 :=
  ⟨p2_d15, p2_D15⟩

/-- Step 1: `(15, 24) --[5]--> (17, 28)`. -/
theorem p2_step1 : IsMovingHorizonStep 15 24 17 28 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- Step 2: `(17, 28) --[9]--> (18, 36)`.  **This is the failing step**:
`C - 1 = 27` and `e = 9`, so the cofactor is `3` and `9 * 9 = 81 > 27`. -/
theorem p2_step2 : IsMovingHorizonStep 17 28 18 36 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- Step 3: `(18, 36) --[5]--> (20, 40)`. -/
theorem p2_step3 : IsMovingHorizonStep 18 36 20 40 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- Step 4: `(20, 40) --[3]--> (24, 42)`. -/
theorem p2_step4 : IsMovingHorizonStep 20 40 24 42 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- **The four-step replay as one chain.**  `HasMovingHorizonPathTo 15 24 24 42 4`. -/
theorem p2_replay_path : HasMovingHorizonPathTo 15 24 24 42 4 :=
  ⟨⟨by decide, by decide, by decide⟩, 17, 28, p2_step1,
    ⟨⟨by decide, by decide, by decide⟩, 18, 36, p2_step2,
      ⟨⟨by decide, by decide, by decide⟩, 20, 40, p2_step3,
        ⟨⟨by decide, by decide, by decide⟩, 24, 42, p2_step4,
          ⟨rfl, rfl, ⟨by decide, by decide, by decide⟩⟩⟩⟩⟩⟩

/-- **Four steps, stated as the replay count.**  Consumed by the counting
predicates; `HasMovingHorizonPathTo` is indexed by the step count. -/
theorem p2_replay_has_four_steps : HasMovingHorizonPathTo 15 24 24 42 (2 + 2) :=
  p2_replay_path

/-! ## 3. `IsAttainedPreviousMaximum 13 24`

The finite upper bound is proved by a `Fin 25`-quantified `decide` (no
`interval_cases`, which is forbidden here), then transported to the `Nat` form. -/

/-- **The upper-bound half.**  `d j ≤ 13` for every `2 ≤ j ≤ 24`. -/
theorem p2_upper_bound : ∀ j : Nat, 2 ≤ j → j ≤ 24 → d j ≤ 13 := by
  intro j h2 _h24
  exact (by decide : ∀ i : Fin 25, 2 ≤ i.val → d i.val ≤ 13) ⟨j, by omega⟩ h2

/-- **The attainment half**, witnessed at index `15` (`d 15 = 13`). -/
theorem p2_attainment : ∃ r : Nat, 2 ≤ r ∧ r ≤ 24 ∧ d r = 13 :=
  ⟨15, by decide, by decide, by decide⟩

/-- **`IsAttainedPreviousMaximum 13 24` holds.**  So the target's third hypothesis
is satisfiable at the counterexample, with `sf = 24`. -/
theorem p2_attained_previous_maximum : IsAttainedPreviousMaximum 13 24 :=
  ⟨p2_upper_bound, p2_attainment⟩

/-! ## 4. The refutation under the full hypothesis set -/

/-- **All three target hypotheses hold simultaneously at `M = 13`, and the
`e * e ≤ C - 1` claim fails on an interior step of that very replay.**

Concretely: `M = 13`, `sf = 24`, `Cf = 42`, `p = 4`, and

* `d (M + 2) = d 15 = 13 = M`  (`p2_d15`),
* `HasMovingHorizonPathTo (M+2) (2*M-2) 24 42 4`  (`p2_replay_path`),
* `IsAttainedPreviousMaximum M 24`  (`p2_attained_previous_maximum`),

while on the replay's second step `(17, 28) --[9]--> (18, 36)` we have
`d 18 * d 18 = 81 > 27 = D 17 - 1`.

This bundle is the reason the item-2 strengthening is not merely unproved but
unprovable. -/
theorem p2_full_hypotheses_with_refutation :
    d (13 + 2) = 13 ∧
      HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 ∧
      IsAttainedPreviousMaximum 13 24 ∧
      ¬ (d 18 * d 18 ≤ D 17 - 1) :=
  ⟨p2_d15, p2_replay_path, p2_attained_previous_maximum,
    by rw [p2_D17, p2_d18]; decide⟩

/-- **The same bundle with the square-root form of the strengthening.**
`d 18 = 9 > 5 = Nat.sqrt 27`, so the route's ingredient fails here too. -/
theorem p2_full_hypotheses_with_sqrt_refutation :
    d (13 + 2) = 13 ∧
      HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 ∧
      IsAttainedPreviousMaximum 13 24 ∧
      ¬ (d 18 ≤ Nat.sqrt (D 17 - 1)) := by
  refine ⟨p2_d15, p2_replay_path, p2_attained_previous_maximum, ?_⟩
  intro h
  have h1 : d 18 * d 18 ≤ Nat.sqrt (D 17 - 1) * Nat.sqrt (D 17 - 1) :=
    Nat.mul_self_le_mul_self h
  have h2 : Nat.sqrt (D 17 - 1) * Nat.sqrt (D 17 - 1) ≤ D 17 - 1 := Nat.sqrt_le _
  have h3 : d 18 * d 18 ≤ D 17 - 1 := Nat.le_trans h1 h2
  rw [p2_d18, p2_D17] at h3
  exact absurd h3 (by decide)

/-- **Every event target on the replay is composite, in the strong sense that it
has a divisor strictly between `1` and itself** -- the prime-free form of the
brief's headline.  Targets: `25` (step 1, odd hit), `27` (step 2, even hit),
`35` (step 3), `39` (step 4). -/
theorem p2_all_targets_composite :
    (∃ f, f ∣ 25 ∧ 1 < f ∧ f < 25) ∧
      (∃ f, f ∣ 27 ∧ 1 < f ∧ f < 27) ∧
      (∃ f, f ∣ 35 ∧ 1 < f ∧ f < 35) ∧
      (∃ f, f ∣ 39 ∧ 1 < f ∧ f < 39) :=
  ⟨⟨5, by decide, by decide, by decide⟩,
   ⟨9, by decide, by decide, by decide⟩,
   ⟨5, by decide, by decide, by decide⟩,
   ⟨3, by decide, by decide, by decide⟩⟩

/-! ## 5. The contrast: at the terminal horizon, primality *holds*

`NoProperFactor N` (from `RecordReplay.lean`) is the prime-free "no proper
divisor" predicate already in the tree.  At `Cf = 42`:

* `Cf - 1 = 41` has no proper factor,
* `Cf + 1 = 43` has no proper factor,

while `41` and `43` are of course not on the list of event targets above.  This is
the contrast the brief's measurement (0/148 prime event targets) and
`ANALYSIS_WHY_STUCK.md` section C (terminal horizons both prime) describe from
opposite sides: they are compatible, because the terminal horizon is reached by an
*event* but is not itself an *event target*. -/

/-- `Cf - 1 = 41` is factor-free. -/
theorem p2_terminal_minus_factor_free : NoProperFactor (D 24 - 1) := by
  rw [p2_D24]
  unfold NoProperFactor
  decide

/-- `Cf + 1 = 43` is factor-free. -/
theorem p2_terminal_plus_factor_free : NoProperFactor (D 24 + 1) := by
  rw [p2_D24]
  unfold NoProperFactor
  decide

/-- **The two facts side by side.**  Event targets on the replay are all
composite; the terminal horizon's two neighbours are both factor-free.  Neither
statement constrains `Σ e_i`, which is the angle's verdict. -/
theorem p2_targets_composite_but_terminal_factor_free :
    (∃ f, f ∣ 27 ∧ 1 < f ∧ f < 27) ∧
      NoProperFactor (D 24 - 1) ∧ NoProperFactor (D 24 + 1) ∧
      ¬ (d 18 * d 18 ≤ D 17 - 1) :=
  ⟨⟨9, by decide, by decide, by decide⟩,
   p2_terminal_minus_factor_free, p2_terminal_plus_factor_free,
   by rw [p2_D17, p2_d18]; decide⟩

/-! ## 6. The `M = 139` witness, recorded because it is the one the tree cites

`EventCountFails.lean` records the `M = 139` replay as `(141, 276) --[25]--> (150, 300)
--[13]--> (156, 312)`, i.e. `p = 2`.  Its first step is a **second** instance of
the same failure: `C - 1 = 275 = 11 * 25` and `e = 25`, so `e * e = 625 > 275`. -/

theorem p2_d150 : d 150 = 25 := by decide
theorem p2_D149 : D 149 = 276 := by decide
theorem p2_d156 : d 156 = 13 := by decide
theorem p2_D155 : D 155 = 300 := by decide

/-- **The `M = 139` failure of `e * e ≤ C - 1`.**  `d 150 = 25` against
`D 149 - 1 = 275`, so `625 ≤ 275` is false. -/
theorem p2_e_square_fails_at_139 : ¬ (d 150 * d 150 ≤ D 149 - 1) := by
  rw [p2_d150, p2_D149]
  decide

/-- The `M = 139` first step is genuine, so this failure is also in-domain. -/
theorem p2_step_141_276_150_300 : IsMovingHorizonStep 141 276 150 300 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Two independent in-domain failures**, at `M = 13` and `M = 139` -- the two
records `ANALYSIS_WHY_STUCK.md` and `EventCountFails.lean` identify as the
worst-case replay (largest `Σ e_i` relative to the allowance) in the sweep. -/
theorem p2_two_independent_failures :
    ¬ (d 18 * d 18 ≤ D 17 - 1) ∧ ¬ (d 150 * d 150 ≤ D 149 - 1) :=
  ⟨by rw [p2_D17, p2_d18]; decide,
   by rw [p2_d150, p2_D149]; decide⟩

/-! ## 7. Axiom audit -/

#print axioms p2_d15
#print axioms p2_replay_path
#print axioms p2_upper_bound
#print axioms p2_attained_previous_maximum
#print axioms p2_full_hypotheses_with_refutation
#print axioms p2_full_hypotheses_with_sqrt_refutation
#print axioms p2_all_targets_composite
#print axioms p2_terminal_minus_factor_free
#print axioms p2_terminal_plus_factor_free
#print axioms p2_targets_composite_but_terminal_factor_free
#print axioms p2_e_square_fails_at_139
#print axioms p2_step_141_276_150_300
#print axioms p2_two_independent_failures

end A166944Research
