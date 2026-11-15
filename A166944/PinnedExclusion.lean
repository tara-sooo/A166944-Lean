import A166944.RoomQuantum
import A166944.RoomLedger
import A166944.BandReentry
import A166944.BandExcursion

set_option maxRecDepth 100000

/-!
# Red-team checks on `RoomQuantum` (round 5)

The module advertises a **dichotomy**:

    even r:  C' - r = 2 * d r  OR  4 * d r <= C' - r
    odd  r:  C' - r + 4 = 3 * d r  OR  5 * d r <= C' - r + 4

Three questions are settled here by the kernel, not by prose:

1. Is the dichotomy *exclusive*, as "dichotomy" suggests?
2. What does the dichotomy plus the band condition `room' <= M` give?  (The module
   never states this consequence; it is the only place the quantum has an upward
   content.)
3. Which canonical replays actually sit on the first (pinned) branch?
-/

namespace A166944Research

/-! ## 1. The dichotomy is exclusive only because `3 <= d r` -/

/-- Both disjuncts of the even branch hold exactly when `2 * d r = 0 = 4 * d r`,
i.e. `d r = 0`; `moving_horizon_step_event_ge_three` rules that out.  So the
"dichotomy" is a genuine dichotomy on steps, but the exclusivity is an *extra*
input, not part of the theorem. -/
theorem even_both_branches_iff (e room' : Nat) :
    (room' = 2 * e ∧ 4 * e ≤ room') ↔ e = 0 ∧ room' = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    omega
  · intro h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    decide

/-- On a real step the even dichotomy is exclusive. -/
theorem even_branches_exclusive {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) : ¬ (C' - r = 2 * d r ∧ 4 * d r ≤ C' - r) := by
  intro h
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  obtain ⟨h1, h2⟩ := h
  omega

/-- On a real step the odd dichotomy is exclusive. -/
theorem odd_branches_exclusive {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) : ¬ (C' - r + 4 = 3 * d r ∧ 5 * d r ≤ C' - r + 4) := by
  intro h
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  obtain ⟨h1, h2⟩ := h
  omega

/-! ## 2. The missed consequence: the quantum bounds the event value from above

The band condition for a canonical replay is `room' <= M` (this is the cap that
`HasMovingHorizonCappedOldPath` / the definition of the capped band carries).
Combining it with the dichotomy gives an upper bound on `e = d r` that is **twice as
good as the library's `e <= M`** on the pinned even branch, and better still off it:
-/

/-- **Even hit, in band: `2 * d r <= M`.**  The pinned branch forces
`2 * d r = room' <= M`; the other branch forces `4 * d r <= room' <= M`.  Both give
`d r <= M / 2`, and the pinned branch is the binding one. -/
theorem even_event_le_half_M_of_room_le {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) (hband : C' - r ≤ M) :
    2 * d r ≤ M := by
  rcases moving_horizon_room_quantum_even hstep hr with h | h
  · omega
  · omega

/-- **Odd hit, in band: `3 * d r ≤ M + 4`.**  Both branches give it: pinned is
`3 * d r = room' + 4 <= M + 4`, and off it `5 * d r <= room' + 4 <= M + 4` is stronger
still. -/
theorem odd_event_le_of_room_le {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) (hband : C' - r ≤ M) :
    3 * d r ≤ M + 4 := by
  rcases moving_horizon_room_quantum_odd hstep hr with h | h
  · omega
  · omega

/-- **Uniform form.**  For `8 <= M` every in-band step satisfies `2 * d r <= M`,
replacing the library's `d r <= M` by a factor of two.  This is the content the
quantum actually has; it is *not* stated anywhere in `RoomQuantum.lean`. -/
theorem event_le_half_M_of_room_le {M s C r C' : Nat} (hM : 8 ≤ M)
    (hstep : IsMovingHorizonStep s C r C') (hband : C' - r ≤ M) :
    2 * d r ≤ M := by
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · exact even_event_le_half_M_of_room_le hstep heven hband
  · have h := odd_event_le_of_room_le hstep hodd hband
    omega

/-- The improvement is not vacuous: `M / 2` is strictly below the budget `M` and it
is a real restriction, since the pinned branch is attained (`M = 43`, `r = 66`,
`e = 33`, `room' = 66 = 2 * 33 <= 43` fails -- so that step is at the *exit*). -/
theorem half_M_is_the_best_the_quantum_gives (M : Nat) (h : 4 ≤ M) :
    M / 2 < M := by omega

/-! ## 3. Which canonical replays sit on the pinned branch -/

/-- `M = 13`, step 0: odd hit at `r = 17`, `e = 5`.  `room' = 28 - 17 = 11` and
`11 + 4 = 15 = 3 * 5`, so this is the **odd pinned** branch (the `q = 2` case). -/
theorem m13_step0_odd_pinned :
    (28 : Nat) - 17 + 4 = 3 * 5 ∧ ¬ (5 * 5 ≤ (28 : Nat) - 17 + 4) := by
  constructor <;> decide

/-- `M = 13`, step 1: even hit at `r = 18`, `e = 9`.  `room' = 36 - 18 = 18 = 2 * 9`,
so this is the **even pinned** branch (the `q = 1` case). -/
theorem m13_step1_even_pinned :
    (36 : Nat) - 18 = 2 * 9 ∧ ¬ (4 * 9 ≤ (36 : Nat) - 18) := by
  constructor <;> decide

/-- `M = 43`, step 4: even hit at `r = 66`, `e = 33`.  `room' = 132 - 66 = 66 = 2*33`,
the **even pinned** branch, with a *large* event. -/
theorem m43_step4_even_pinned :
    (132 : Nat) - 66 = 2 * 33 ∧ ¬ (4 * 33 ≤ (132 : Nat) - 66) := by
  constructor <;> decide

/-- `M = 139` has no pinned step at all: both steps are strictly off the first
branch.  So `M = 13` and `M = 43` are the *only* two canonical replays below
`2 * 10 ^ 6` with a pinned step, matching the direct count. -/
theorem m139_no_pinned :
    ¬ ((150 : Nat) = 2 * 25) ∧ 4 * 25 ≤ (150 : Nat) ∧
      ¬ ((156 : Nat) = 2 * 13) ∧ 4 * 13 ≤ (156 : Nat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- A single pinned step at `M = 43` already exceeds the whole per-record budget
`(3 * 43 - 9) / 8 = 15`: `33 > 15`. -/
theorem m43_pinned_event_beats_budget : (3 * 43 - 9) / 8 = 15 ∧ 15 < 33 := by
  constructor <;> decide

/-! ## 4. Prior art: the pinned even branch predates `RoomQuantum` by two months

`moving_horizon_normalized_new_max_even` (`Lemmas.lean:3099`, added 2026-09-07)
already concludes exactly `r % 2 = 0 ∧ C' - r = 2 * d r`.  The two statements are
inter-derivable; the check below is that the left one is *not* new content. -/

#check @moving_horizon_normalized_new_max_even

/-- Same conclusion as the left disjunct of `moving_horizon_room_quantum_even`, from
the September theorem, with the September hypotheses. -/
theorem pinned_even_is_prior_art {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hnew : P < d r) (hPodd : P % 2 = 1) :
    C' - r = 2 * d r :=
  (moving_horizon_normalized_new_max_even hstep hnorm hnew hPodd).2

/-! ## 5. Prior art: the quotient is *already* bounded below by 3

`ANALYSIS_WHY_STUCK.md` and `RoomQuantum.lean` both say the quotient `(C +- 1)/e` "was
previously unbounded from below in the library" / "nothing in the library bounds that
quotient from below".  `moving_horizon_step_event_package` (`Lemmas.lean:2848`,
2026-09-08) already proves `3 * d r <= C - 1` (even) and `3 * d r <= C + 1` (odd),
which *is* exactly `3 <= (C +- 1) / d r`. -/

#check @moving_horizon_step_event_package

/-- The quotient is at least 3, from the September theorem, with no new input. -/
theorem quotient_ge_three_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) : 3 * d r ≤ C - 1 := by
  rcases moving_horizon_step_event_package hstep with h | h
  · exact h.2.2.2
  · exact absurd (h.1.symm.trans heven) (by decide)

theorem quotient_ge_three_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hodd : r % 2 = 1) : 3 * d r ≤ C + 1 := by
  rcases moving_horizon_step_event_package hstep with h | h
  · exact absurd (h.1.symm.trans hodd) (by decide)
  · exact h.2.2.2

-- And the *pinned* even branch (`room' = 2e`) is likewise already in the September
-- factor-pair theorem: `C' = e * (v + 1)` with `r = e * u` gives
-- `C' - r = e * (v + 1 - u)`, and `v - u = q` is odd and `>= 1`, so the pinned case
-- `q = 1` is exactly `moving_horizon_normalized_new_max_even`.
#check @moving_horizon_even_factor_pair
#check @moving_horizon_odd_factor_pair

end A166944Research
