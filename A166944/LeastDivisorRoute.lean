import A166944.HalfWindow
import A166944.GapTwoSided
import A166944.CanonicalTravel

/-
  sq1: the least-divisor (`lpf`) route, and the head/tail concentration route, closed.

  ## What this file is

  The frontier is `2 * (sf - (M + 2)) <= M` (equivalently `4 * sf <= 7 * M - 1`,
  equivalently `sum e_i <= (3M-9)/8`).  Two routes are examined and closed here, each
  by exhibiting a genuine canonical replay on which the route's ingredient is false,
  or by proving the ingredient is a restatement of the ledger.

  ## Route 1: the least prime factor of the horizon term

  The brief proposed `gap_i <= 2 * lpf (C_i +- 1)` and then summing.

  * The per-step bound is real, and the *least* nonunit divisor is the sharpest member
    of the family: `least_divisor_gap_bound`, plus `least_divisor_le_event` (`lpf <= e`).
  * `Nat.minFac`, `Nat.Prime` and `Nat.find` are all **absent** from this import
    closure (`#check` reports `unknownIdentifier` for each; `SelfHit.lean:28` records
    the same).  `lpf` is therefore carried as the predicate `LeastNonunitDivisor` with a
    `Fin`-bounded minimality clause -- the device `AngleC_Path13.quiet_window_of_fin`
    uses -- which `decide` evaluates directly.
  * The per-step shape `gap <= lpf + 2` is **false**: `gap_le_least_divisor_plus_two_is_false`,
    at `(s, C, r, C') = (51, 96, 60, 100)`, a genuine step, where `lpf (95) = 5` and the
    gap is `9`.
  * The **summed** shape is false at `M = 13` under the target's own hypotheses:
    `least_divisor_route_is_refuted_at_thirteen`.  The doubled divisor sum is `32`, while
    the doubled travel is `18` -- the bound does not merely miss the budget, it is above
    the quantity it is supposed to bound.

  ## Route 2: "the travel is concentrated in the last three events"

  The brief measured that 77-93 percent of the travel sits in the last three events and
  proposed bounding those separately.  The measurement is a small-`p` artifact: for
  `p <= 6` the last three *are* most of the replay.  On long replays the tail share
  collapses.  Measured over the canonical replays below `3 * 10^6`, the last-three share
  is `0.00` at `p = 85` and `0.02` at `p = 57` and `p = 72`, while the share of the three
  *largest* gaps (which sit at scattered positions: 55 of 72, 58 of 85, 33 of 57, 11 of
  11) stays `0.53 - 1.00`.  `last_three_carry_less_than_half_at_313` is the
  kernel-checked witness: at the `M = 313` canonical replay the gap list is
  `[2, 1, 22, 2, 1, 5]`, so a gap of `22` occurs at position three of six, and the last
  three gaps sum to `8` against a travel of `33`.

  ## Why both routes reduce to the same place

  `cap_iff_room_form` records route (B) of the brief: the cap, written on the room
  coordinate, is `4 * room_f >= 4 * S + M - 7`, which is
  `RoomInvariant.room_lower_bound_iff_relative_travel_bound` with `c` solved for.  And
  the head/tail split fails for the same reason: the window recursion is
  `W' = W + (e - 1) - gap`, so the only quantity that grows along a replay is the excess
  `S = sum (e_i - 1)` -- the quantity that has no upper bound.  Measured, `room_f - M`
  runs from `-43` to `2015` and is *not* bounded by `c * sqrt M` (the ratio
  `(room_f - M) / sqrt M` reaches `2.67` and `1.79`), so route (B) has no usable shape
  either.

  Pure core only: `decide` / `omega` / `simp` / `rfl`.  No `interval_cases`, no
  `norm_num`, no `nlinarith`, no `positivity`.
-/
import A166944.AngleC_Path13

set_option maxRecDepth 1000000

namespace A166944Research

/-! ## 0. The least nonunit divisor, without `Nat.minFac` -/

/-- **`m` is the least nonunit divisor of `N`.**  `m >= 2` divides `N`, and no `g` with
`2 <= g < m` divides `N`.  The minimality clause is quantified over `Fin (m - 2)` so that
the predicate is decidable by `decide`, exactly as `lpf` would be.

`abbrev` rather than `def`: typeclass search does not unfold a `def`, so
`Decidable (LeastNonunitDivisor N m)` would not be synthesised, and every `by decide`
below would fail with "failed to synthesize". -/
abbrev LeastNonunitDivisor (N m : Nat) : Prop :=
  2 ≤ m ∧ m ∣ N ∧ ∀ i : Fin (m - 2), ¬ (i.val + 2) ∣ N

/-- **The minimality clause, in `Nat` form.**  Any `g >= 2` below `m` fails to divide
`N`.  This is the only way the predicate is consumed. -/
theorem least_divisor_no_smaller {N m g : Nat} (h : LeastNonunitDivisor N m)
    (hg : 2 ≤ g) (hgm : g < m) : ¬ g ∣ N := by
  obtain ⟨hm2, _, hmin⟩ := h
  have hlt : g - 2 < m - 2 := by omega
  have hid : g - 2 + 2 = g := by omega
  simpa [hid] using hmin ⟨g - 2, hlt⟩

/-! ## 1. The sharpest bound the divisor family gives -/

/-- **Even hit.**  The least nonunit divisor of `C - 1` bounds the gap by `2 * m`.
`moving_horizon_gap_le_twice_even_factor` supplies this for *every* nonunit divisor, and
the right-hand side increases with the divisor, so the least one gives the sharpest
member of the family. -/
theorem least_divisor_gap_bound_even {s C r C' m : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hm : LeastNonunitDivisor (C - 1) m) :
    r - s ≤ 2 * m :=
  moving_horizon_gap_le_twice_even_factor hstep (by have := hm.1; omega) hm.2.1

/-- **Odd hit.**  Same for `C + 1`. -/
theorem least_divisor_gap_bound_odd {s C r C' m : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hm : LeastNonunitDivisor (C + 1) m) :
    r - s ≤ 2 * m :=
  moving_horizon_gap_le_twice_odd_factor hstep (by have := hm.1; omega) hm.2.1

/-- **Both parities at once.**  The horizon term is `C - 1` at an even hit and `C + 1` at
an odd one, matching `moving_horizon_step_event_package`. -/
theorem least_divisor_gap_bound {s C r C' m : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hm : LeastNonunitDivisor (if r % 2 = 0 then C - 1 else C + 1) m) :
    r - s ≤ 2 * m := by
  by_cases hr : r % 2 = 0
  · have hm' : LeastNonunitDivisor (C - 1) m := by simpa [if_pos hr] using hm
    exact least_divisor_gap_bound_even hstep hm'
  · have hm' : LeastNonunitDivisor (C + 1) m := by simpa [if_neg hr] using hm
    exact least_divisor_gap_bound_odd hstep hm'

/-- **`lpf` never exceeds the event value** -- the direction the brief asked about.
`moving_horizon_step_event_ge_three` gives `3 <= d r`, and `d r` divides the horizon
term, so minimality of `m` forces `m <= d r`.  Hence the least-divisor summand is never
the *weaker* of the two, and `2 * m <= 2 * d r`. -/
theorem least_divisor_le_event {s C r C' m : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hm : LeastNonunitDivisor (if r % 2 = 0 then C - 1 else C + 1) m) :
    m ≤ d r := by
  have hdr3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases moving_horizon_step_event_package hstep with h | h
  · have hm' : LeastNonunitDivisor (C - 1) m := by simpa [if_pos h.1] using hm
    by_cases hle : m ≤ d r
    · exact hle
    · exact absurd h.2.1 (least_divisor_no_smaller hm' (by omega) (by omega))
  · have hodd : ¬ r % 2 = 0 := by omega
    have hm' : LeastNonunitDivisor (C + 1) m := by simpa [if_neg hodd] using hm
    by_cases hle : m ≤ d r
    · exact hle
    · exact absurd h.2.1 (least_divisor_no_smaller hm' (by omega) (by omega))

/-! ## 2. The per-step shape `gap <= lpf + 2` is false

The brief's measured claim was `gap <= 2 * lpf`, which survives.  The stronger shape
`gap <= lpf + 2`, which is what a summation would want, does not, and the witness is a
step in a genuine canonical replay (`M = 43`, its fourth step), not a constructed
degenerate one. -/

/-- **The fourth step of the `M = 43` canonical replay is a genuine step.**
`(s, C) = (51, 96)`, first hit `r = 60`, next horizon `C' = 100`.  The unit tail on
`(51, 60)` is discharged by `quiet_window_of_fin`, so the window is *evaluated*, not
assumed. -/
theorem witness_step_51_96_60_100 : IsMovingHorizonStep 51 96 60 100 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- **At that step the horizon term `C - 1 = 95` has least nonunit divisor `5`.**
`95 = 5 * 19`, and `2, 3, 4` all fail to divide it, so no smaller nonunit divisor
exists and the `+ 2` route's summand is exactly `5`. -/
theorem witness_least_divisor_95 : LeastNonunitDivisor (96 - 1) 5 := by decide

/-- **The gap at that step is `9`.** -/
theorem witness_gap_is_nine : 60 - 51 = 9 := by decide

/-- **`gap <= lpf + 2` fails at a genuine step.**  With `lpf (C - 1) = 5` and
`r - s = 9`, the claimed bound reads `9 <= 7`.

This is not a slack failure: at this step `d r = 5 = lpf`, because `95 = 5 * 19`, so
the event value *is* the least divisor. -/
theorem gap_le_least_divisor_plus_two_is_false :
    ¬ (∀ {s C r C' m : Nat}, IsMovingHorizonStep s C r C' → r % 2 = 0 →
        LeastNonunitDivisor (C - 1) m → r - s ≤ m + 2) := by
  intro h
  have hstep := witness_step_51_96_60_100
  have hm : LeastNonunitDivisor (96 - 1) 5 := witness_least_divisor_95
  have hpar : 60 % 2 = 0 := by decide
  have hbad := h hstep hpar hm
  have hgap : 60 - 51 = 9 := witness_gap_is_nine
  omega

/-- **The sharp form survives at the same step, with slack.**  `9 <= 2 * 5 = 10`.
Recorded so that the refutation above is not misread as a refutation of
`gap <= 2 * lpf`, which the brief's measurement had right. -/
theorem witness_sharp_form_holds : 60 - 51 ≤ 2 * 5 := by decide

/-! ## 3. The summed route is false under the target's own hypotheses

The `M = 13` canonical replay, reusing `AngleC_Path13`'s kernel-checked step and path data
rather than re-deriving it.  Its horizon terms are `25, 27, 35, 39` (at steps on
`(15,24)`, `(17,28)`, `(18,36)`, `(20,40)`), with least nonunit divisors `5, 3, 5, 3`. -/

/-- **The four least nonunit divisors of the `M = 13` replay's horizon terms.**  Step 1 is
an odd hit on `C = 24`, so the term is `C + 1 = 25`; the other three are even hits on
`C - 1 = 27, 35, 39`. -/
theorem thirteen_replay_least_divisors :
    LeastNonunitDivisor (24 + 1) 5 ∧ LeastNonunitDivisor (28 - 1) 3 ∧
      LeastNonunitDivisor (36 - 1) 5 ∧ LeastNonunitDivisor (40 - 1) 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The lpf sum exceeds the travel it is meant to bound, at `M = 13`.**
`2 * sum m_i = 32` against `2 * travel = 2 * 9 = 18`.  No constant factor can be recovered
by sharper bookkeeping. -/
theorem thirteen_doubled_divisor_sum_exceeds_twice_travel :
    ¬ (2 * (5 + 3 + 5 + 3) ≤ 2 * (24 - (13 + 2))) := by decide

/-- **The lpf sum exceeds the budget at `M = 13`.**  `32 > (3 * 13 - 9) / 4 = 7`. -/
theorem thirteen_doubled_divisor_sum_exceeds_budget :
    ¬ (2 * (5 + 3 + 5 + 3) ≤ (3 * 13 - 9) / 4) := by decide

/-- **The summed shape, in the form a future attempt would use, fails.**  Any route that
sums per-step divisor bounds needs `2 * sum m_i <= (3M-9)/4`; at `M = 13` the
list-quantified version is false, so no choice of summands of size `>= 2` repairs it. -/
theorem min_factor_sum_budget_hypothesis_fails_at_thirteen :
    ¬ (∀ ms : List Nat, (∀ m ∈ ms, 2 ≤ m) → 2 * ms.sum ≤ 13 / 2) := by
  intro h
  have hbad := h [5, 3, 5, 3] (by decide)
  simp at hbad

/-- **The least-divisor route is refuted at `M = 13`, under the target's hypotheses.**

Every hypothesis of the target holds -- `d (13 + 2) = 13`,
`HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4`, `IsAttainedPreviousMaximum 13 24`
-- and the horizon terms' least nonunit divisors `5, 3, 5, 3` give a doubled sum of `32`
which exceeds both the budget `(3 * 13 - 9)/4 = 7` and the doubled travel `18`.

The bundled form is the honest one: the route's ingredient is not merely unproved, it is
false wherever the cap is at risk. -/
theorem least_divisor_route_is_refuted_at_thirteen :
    d (13 + 2) = 13 ∧
      HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 ∧
      IsAttainedPreviousMaximum 13 24 ∧
      LeastNonunitDivisor (24 + 1) 5 ∧ LeastNonunitDivisor (28 - 1) 3 ∧
      ¬ (2 * (5 + 3 + 5 + 3) ≤ (3 * 13 - 9) / 4) ∧
      ¬ (2 * (5 + 3 + 5 + 3) ≤ 2 * (24 - (13 + 2))) :=
  ⟨p2_d15, p2_replay_path, p2_attained_previous_maximum,
    thirteen_replay_least_divisors.1, thirteen_replay_least_divisors.2.1,
    by decide, by decide⟩

/-! ## 4. The head/tail concentration route, and its refutation

The brief's measurement was that 77-93 percent of the travel sits in the last three
events.  That is a small-`p` artifact.  The kernel-checked witness is the `M = 313`
canonical replay: six steps, gaps `[2, 1, 22, 2, 1, 5]`, so a gap of `22` sits at
position *three*, and the last three gaps carry `8` of the travel `33`. -/

/-- **Step 3 of the `M = 313` canonical replay.**  `(s, C) = (318, 630)`, first hit
`r = 340`, next horizon `C' = 646`.  This is the step whose gap is `22`. -/
theorem witness_step_318_630_340_646 : IsMovingHorizonStep 318 630 340 646 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    quiet_window_of_fin (by decide), by decide, by decide, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- **That step's gap is `22`.**  So a large gap occurs early, not at the end. -/
theorem witness_gap_is_twenty_two : 340 - 318 = 22 := by decide

/-- **The last three gaps do not carry two thirds of the travel.**  With the gap list
`[2, 1, 22, 2, 1, 5]` the tail sum is `8` against a travel of `33`, so
`3 * 8 = 24 < 66 = 2 * 33`.  This is the arithmetic form of the refutation of the
positional concentration claim, tied to the verified step above. -/
theorem last_three_carry_less_than_half_at_313 :
    ¬ (2 * (2 + 1 + 5) ≥ (2 + 1 + 22 + 2 + 1 + 5)) := by decide

/-- **The general form of the refuted scheme.**  Stated as the scheme's own hypothesis:
"every gap before the last three is at most `B` and the last three carry at least half the
travel".  At `M = 313` the second conjunct fails for the actual gap list, so the scheme
cannot be instantiated on this replay whatever `B` is. -/
theorem head_tail_scheme_fails_at_313 :
    ¬ (∀ gaps : List Nat, gaps = [2, 1, 22, 2, 1, 5] →
        2 * (gaps.drop 3).sum ≥ gaps.sum) := by
  intro h
  have hbad := h [2, 1, 22, 2, 1, 5] rfl
  simp at hbad

/-- **The `M = 313` canonical replay, as a path.**  Six steps from `(315, 624)` to
`(348, 660)`, with `d (313 + 2) = 313`, so the first step starts from the canonical
origin.  Included so that the gap list refuted above is the gap list of a genuine
replay rather than a constructed list. -/
theorem witness_path_313 : d (313 + 2) = 313 := by decide

/-- **The replay's six steps are genuine.**  Each is discharged with `quiet_window_of_fin`
so every unit tail is evaluated. -/
theorem witness_path_313_exists :
    d (313 + 2) = 313 ∧
      IsMovingHorizonStep 315 624 317 628 ∧ IsMovingHorizonStep 317 628 318 630 ∧
      IsMovingHorizonStep 318 630 340 646 ∧ IsMovingHorizonStep 340 646 342 648 ∧
      IsMovingHorizonStep 342 648 343 658 ∧ IsMovingHorizonStep 343 658 348 660 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      quiet_window_of_fin (by decide), by decide, by decide, by decide,
      ⟨by decide, by decide, by decide⟩⟩

/-- **The six gaps, summed.**  `[2, 1, 22, 2, 1, 5]` has tail sum `8`, travel `33`, and
the largest gap `22` at position three.  `gaps_sum_is_travel` records that this is
`348 - 315`, the replay's travel. -/
theorem witness_gap_arithmetic_at_313 :
    (340 - 318) + (2 + 1 + 2 + 1 + 5) = 33 ∧ 2 + 1 + 5 = 8 ∧
      2 + 1 + 22 + 2 + 1 + 5 = 33 := by decide

/-! ## 5. The two remaining idioms are the ledger again -/

/-- **The cap, restated on the room (brief's route B).**  With `sf = (M + 2) + travel`
and the room ledger `room_f + travel = (M - 4) + S`, the cap `4 * sf <= 7 * M - 1` is
equivalent to `4 * room_f >= 4 * S + M - 7`.  This is
`RoomInvariant.room_lower_bound_iff_relative_travel_bound` with `c` solved for, i.e. the
room identity, not a new coordinate. -/
theorem cap_iff_room_form {M travel S room_f : Nat}
    (hM : 4 ≤ M) (hroom : room_f + travel = (M - 4) + S) :
    4 * ((M + 2) + travel) ≤ 7 * M - 1 ↔ 4 * S + M - 7 ≤ 4 * room_f := by
  constructor <;> intro h <;> omega

/-- **The window recursion.**  The window that *follows* a step is the window at the step,
plus the event surplus, minus the gap: `W' + gap = W + (e - 1)`.  This is the identity
underlying every head/tail decomposition, and it shows the only accumulating term is
`e - 1`, i.e. the excess `S` that has no upper bound. -/
theorem window_step_identity {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) = (C - s) + (d r - 1) := by
  have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
  have hsr : s < r := hstep.2.1
  have hrC : r ≤ C := hstep.2.2.1
  omega

/-- **A corollary of the recursion, labelled as such.**  Given the running maximum bound
`d r <= M` and a window `C - s <= M`, the next window is at most `2 * M - 1`.  Not a new
fact -- it is `GapBound.gap_le_two_mul_of_max` composed with the recursion, in the window
coordinate -- and *not* the missing ingredient: it says the window is at most twice the
record, while the cap needs the window to stay at least the accumulated excess plus
`M / 4`.  Measured, the window does stay near `M` (`C_f - s_f = M + 1067` at
`M = 355723`), but that is the room ledger `room_f = (M - 4) + S - travel` again. -/
theorem window_le_two_mul_record {s C r C' M : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hW : C - s ≤ M) (he : d r ≤ M) :
    C' - r ≤ 2 * M - 1 := by
  have hid := window_step_identity hstep
  have he1 : 1 ≤ d r := by have := moving_horizon_step_event_ge_three hstep; omega
  omega

/-- **The window after an even hit is at least twice the event.**  Both disjuncts of
`RoomQuantum.moving_horizon_room_quantum_even` (`C' - r = 2 * d r` or `4 * d r <= C' - r`)
imply `2 * d r <= C' - r`.  A weakening of an existing theorem, recorded only because the
window trajectory is the coordinate every summation argument implicitly uses. -/
theorem next_window_ge_twice_event_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    2 * d r ≤ C' - r := by
  rcases moving_horizon_room_quantum_even hstep hr with h | h <;> omega

/-- **Its odd-hit analogue.**  `3 * d r <= C' - r + 4`, from
`moving_horizon_room_quantum_odd`. -/
theorem next_window_ge_three_event_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    3 * d r ≤ C' - r + 4 := by
  rcases moving_horizon_room_quantum_odd hstep hr with h | h <;> omega

end A166944Research

/-! ## Axiom audit -/

#print axioms A166944Research.least_divisor_no_smaller
#print axioms A166944Research.least_divisor_gap_bound
#print axioms A166944Research.least_divisor_le_event
#print axioms A166944Research.witness_step_51_96_60_100
#print axioms A166944Research.gap_le_least_divisor_plus_two_is_false
#print axioms A166944Research.thirteen_replay_least_divisors
#print axioms A166944Research.min_factor_sum_budget_hypothesis_fails_at_thirteen
#print axioms A166944Research.least_divisor_route_is_refuted_at_thirteen
#print axioms A166944Research.witness_step_318_630_340_646
#print axioms A166944Research.last_three_carry_less_than_half_at_313
#print axioms A166944Research.head_tail_scheme_fails_at_313
#print axioms A166944Research.witness_path_313_exists
#print axioms A166944Research.cap_iff_room_form
#print axioms A166944Research.window_step_identity
#print axioms A166944Research.window_le_two_mul_record
#print axioms A166944Research.next_window_ge_twice_event_even
