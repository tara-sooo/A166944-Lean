import A166944.CanonicalTravel
import A166944.GapBound
import A166944.BCapDictionary
import A166944.BIntegrate

/-!
# The room ledger, the excess sum, and the `M = 13` obstruction

Three findings from direct numerical experiment on the canonical capped replay.
Nothing here proves the frontier theorem. One result is a structural reduction,
one is negative (a candidate route collapses to a known quantity), and the third
**refutes** the threshold-free form of the target.

## 1. The room ledger reduces to the same excess sum `S`

With `room (s,C) = C - s`, `moving_horizon_slack_transition` reads

    room'  =  room + (d r - 1) - (r - s)

i.e. the room earns the event excess and pays the gap. So the room is **not**
monotone. Dropping the gap and integrating from the canonical start, whose room is
exactly `M - 4`:

    Cf - sf  <=  (M - 4) + S,     S = accumulated sum of (d r - 1).

That is `room_le_start_add_excess_path`. `BIntegrate` proves the reservoir ledger
`B sf + (sf - s) = B s + S` with the *same kind* of accumulated excess. So the room
route and the reservoir route are controlled by one quantity, and the room route
adds no input. `canonical_room_le_M_of_excess_le_four` states what would be
needed -- `S <= 4` -- against a measured `S = 2388` at `M = 355723`.

## 2. Two of my own derivations were refuted, and the exact identity

Two claims are recorded as **false**, because both are natural and both were caught
by numerics rather than by a proof:

* the exit room does **not** saturate `m - 6` (it is exactly `B sf - 2`);
* `travel <= M` is **not** equivalent to `S <= B sf + 2`
  (`M = 13`, `M = 43` satisfy the second and violate the first).

What is exact is `Cf - sf = (M - 4) + S - travel`, which makes the frontier an
*algebraic rearrangement* of the reservoir ledger: `2*travel <= M` is equivalent to
`2*S + M <= 2*B sf + 4` with no new content. The finding is negative and useful:
nothing inside the room/reservoir coordinates can supply the missing bound, so a
proof must bound `S` (equivalently `p`) directly.

## 3. The threshold is load-bearing: the target is FALSE without it

`target_of_travel_bound_from_22933441` consumes `CanonicalTravelBoundFrom 22933441`
and `GATE_MAP.md` warns that `M = 13` "does not refute any gate that is actually
consumed". This file sharpens the warning: the statement obtained by dropping
*only* the lower bound is false, with a fully finite witness at `M = 13`. The
witness is a genuine 4-step path from the true canonical start `(15, 24)`:

    (15,24) -d 17 = 5-> (17,28) -d 18 = 9-> (18,36) -d 20 = 5-> (20,40)
            -d 24 = 3-> (24,42)

with `sf = 24`, travel `9`, and `2 * 9 = 18 > 13`. It satisfies
`IsAttainedPreviousMaximum 13 24`, since the running maximum of `d` through 24 is
`13`, attained at `d 15 = 13` -- the canonical start itself. So `M >= 45895573` is
an essential input and no threshold-free argument can be sound.

## Proved / not proved

Proved: the room ledger and its integrated form; the exact room identity
`Cf - sf = B sf - 2`; the rearrangement `travel <= M <-> 2S + M <= 2B sf + 4`; the
one valid implication `travel -> S <= B sf + 2` together with a proof that its
converse is false; the count corollary; the `M = 13` path and witness; and the
refutation of the threshold-free statement. Two intermediate claims of mine are
recorded as refuted (§2). **Not** proved, not claimed: any bound on `S`, hence on
`sf`, hence the frontier theorem. Numerics to `10^6` are evidence, not proof.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The room ledger -/

/-- **The room ledger for one step**: earn `d r - 1`, pay the gap `r - s`.  This
is `moving_horizon_slack_transition` (`Lemmas.lean:2651`) rearranged, and it shows
the room coordinate is not monotone. -/
theorem room_step_decomposition {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C' - r = (C - s) + (d r - 1) - (r - s) := by
  have h := moving_horizon_slack_transition hstep
  have hd1 : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  omega

/-- **The room is at most the start room plus the excess just earned.**  The
subtracted gap is what makes the room non-monotone, so dropping it is the whole
step. -/
theorem room_le_start_add_excess {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C' - r ≤ (C - s) + (d r - 1) := by
  have h := room_step_decomposition hstep
  omega

/-- **Integrated room bound along any moving-horizon path.**  There is an
accumulated excess `S` with `Cf - sf <= (C - s) + S`; the gaps never contribute
positively. -/
theorem room_le_start_add_excess_path {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, Cf - sf ≤ (C - s) + S := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, hCf, _⟩ := hpath
      subst hsf
      subst hCf
      exact ⟨0, by omega⟩
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hS'⟩ := ih htail
      refine ⟨S' + (d r - 1), ?_⟩
      have hroom := room_le_start_add_excess hstep
      omega

/-- **The canonical start room is `M - 4`.**  This is the only head start a
canonical replay has before its first event. -/
theorem canonical_start_room {M : Nat} (hM : 4 ≤ M) :
    (2 * M - 2) - (M + 2) = M - 4 := by omega

/-- **The canonical room bound.**  `Cf - sf <= (M - 4) + S` for an accumulated
event excess `S`. -/
theorem room_le_canonical_start_add_excess {M sf Cf p : Nat}
    (hM : 4 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    ∃ S : Nat, Cf - sf ≤ (M - 4) + S := by
  obtain ⟨S, hS⟩ := room_le_start_add_excess_path hpath
  exact ⟨S, by have := canonical_start_room hM; omega⟩

/-- **What the inequality form of the room route needs.**  Given the integrated
bound, `Cf - sf <= M` follows from `S <= 4`.  The measured value is `S = 2388` at `M = 355723`, so the
room route is hopeless in this form: it is not a weaker target than the frontier,
it merely re-exposes the missing bound. -/
theorem canonical_room_le_M_of_excess_le_four {M sf Cf S : Nat} (hM : 4 ≤ M)
    (hbound : Cf - sf ≤ (M - 4) + S) (hS : S ≤ 4) : Cf - sf ≤ M := by omega

/-- **The room route and the reservoir route share one quantity.**  Both the
integrated room bound and `BIntegrate`'s `B sf + (sf - s) = B s + S` are governed
by the accumulated excess, so the room coordinate supplies no independent input. -/
theorem room_and_reservoir_share_excess {M sf Cf S T : Nat}
    (hroom : Cf - sf ≤ (M - 4) + S) (hsame : S = T) :
    Cf - sf ≤ (M - 4) + T := by omega

/-! ## 2. The exact room identity, and two claims of mine that the data refuted

Two statements I derived here did not survive checking, and both are recorded
because the failure is informative. The numerics are reproduced in
`~/p2m_scratch/frontier1/eq2.py` and `eq3.py`.

**Refuted claim A.** I read the exit room as saturating an arithmetic ceiling
`m - 6` for the lesser twin `m`. False: the exit room is exactly `B sf - 2`, and
the two agree only at the tiny exits. The room is not pinned to any ceiling; it
grows with the accumulated excess.

**Refuted claim B.** I then claimed the equivalence
`travel <= M  <->  S <= B sf + 2`. Also false, and the small exits refute it:
at `M = 13` we have `S = 18 <= B 24 + 2 = 22` while `2 * travel = 18 > 13`; same at
`M = 43`. The implication `travel <= M -> S <= B sf + 2` does hold at every tested
exit, but its converse does not.

What *is* true is exact and algebraic, not an inequality in disguise. The reservoir
ledger `B sf + travel = (M - 2) + S` together with `Cf - sf = B sf - 2` gives

    Cf - sf = (M - 4) + S - travel,

and substituting `travel = B sf + S - M + 2` turns the frontier conclusion into the
*identity-level* form

    2 * travel <= M   <->   2 * S + M <= 2 * B sf + 4 .

The right-hand side is not a new theorem -- it is the left-hand side rewritten --
and that is the finding: in the room/reservoir coordinates the frontier is an
equation rearrangement, so no amount of manipulation inside these coordinates can
supply the missing bound. The missing input has to bound `S` or `p`, full stop.
Both forms were checked against all 16 canonical starts up to `4 * 10^5` with no
disagreement. -/

/-- **The room is the reservoir shifted by two**, at any moving-horizon state.
Immediate from `moving_horizon_state_B_add_index` (`BCapDictionary`). -/
theorem room_eq_B_sub_two {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    Cf - sf = B sf - 2 := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-- **The dictionary in truncation-free form.**  Since a moving-horizon state has
`sf < Cf`, the reservoir is exactly the room plus two: `B sf = (Cf - sf) + 2`.  This
is the form to use in arithmetic, because no truncated subtraction is inverted. -/
theorem B_eq_room_add_two {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    B sf = (Cf - sf) + 2 := by
  have h := moving_horizon_state_B_add_index hstate
  have hlt : sf < Cf := hstate.2.2
  omega

/-- **The exact room identity.**  Head start `M - 4`, plus everything earned `S`,
minus everything spent (`travel`).  The inequality of §1 is this with the spent
term dropped, which is precisely why §1 is too weak to finish. -/
theorem room_eq_start_add_excess_sub_travel {M sf Cf S : Nat}
    (hstate : IsMovingHorizonState sf Cf) (hM : 4 ≤ M)
    (hres : B sf + (sf - (M + 2)) = (M - 2) + S) :
    (Cf - sf) + (sf - (M + 2)) = (M - 4) + S := by
  have hroom : B sf = (Cf - sf) + 2 := B_eq_room_add_two hstate
  omega

/-- **The frontier rewritten in excess/reservoir coordinates.**  Given the exact
room identity and the room/reservoir dictionary, the frontier conclusion is
*equivalent* to `2 * S + M <= 2 * B sf + 4`.  This is a rearrangement and not a
weakening -- recorded as the negative result that these coordinates cannot supply
the missing bound, so any route through them is closed. -/
theorem travel_iff_scaled_excess {M sf Cf S : Nat} (hM : 4 ≤ M)
    (hroom : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S)
    (hB : B sf = (Cf - sf) + 2) :
    2 * (sf - (M + 2)) ≤ M ↔ 2 * S + M ≤ 2 * B sf + 4 := by omega

/-- **The one direction that does hold.**  Travel implies the un-scaled excess
bound `S <= B sf + 2`.  The converse fails at `M = 13` and `M = 43`, which is why
the equivalence cannot be strengthened to it -- recorded so the failed form is not
re-derived. -/
theorem excess_le_reservoir_of_travel {M sf Cf S : Nat} (hM : 4 ≤ M)
    (hroom : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S)
    (hB : B sf = (Cf - sf) + 2)
    (htravel : 2 * (sf - (M + 2)) ≤ M) : S ≤ B sf + 2 := by omega

/-- **The count corollary, in the direction that actually holds.**  Each event is at
least `3`, so `S >= 2 * p`; the scaled form `2*S + M <= 2*B sf + 4` therefore
*implies* the count form `2*(2*p) + M <= 2*B sf + 4`. This is the only direction
available: `S >= 2p` makes the scaled left-hand side larger, so a lower bound on `S`
can never deliver the conclusion. The count form is thus a *weaker* consequence of
travel, not a route to it -- consistent with `REACH.md`'s finding that `p` itself is
what has no upper bound. -/
theorem count_form_of_scaled_excess {M Bsf p S : Nat} (hSp : 2 * p ≤ S)
    (hscaled : 2 * S + M ≤ 2 * Bsf + 4) :
    2 * (2 * p) + M ≤ 2 * Bsf + 4 := by omega

/-! ## 3. The `M = 13` witness: the threshold is load-bearing -/

/-- The canonical start increment at `M = 13`: `d 15 = 13`. -/
theorem d15_eq_thirteen : d (13 + 2) = 13 := by decide

/-- First event of the `M = 13` replay: `d 17 = 5`. -/
theorem d17_eq_five : d 17 = 5 := by decide

/-- Second event: `d 18 = 9` (no unit tail at all). -/
theorem d18_eq_nine : d 18 = 9 := by decide

/-- Third event: `d 20 = 5`. -/
theorem d20_eq_five : d 20 = 5 := by decide

/-- Terminal event: `d 24 = 3`, reaching `D 24 = 42`. -/
theorem d24_eq_three : d 24 = 3 := by decide

/-- **Step 1 of the `M = 13` replay**, in the repository's existing style for
finite steps: unfold the state, close the unit tail by `omega` plus `decide`, and
reduce the coordinates. -/
theorem step13_1 : IsMovingHorizonStep 15 24 17 28 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    have hj : j = 16 := by omega
    subst j
    decide
  · simp [IsMovingHorizonState, D, a]

/-- **Step 2**: from `(17, 28)`, the very next index is already an event. -/
theorem step13_2 : IsMovingHorizonStep 17 28 18 36 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    omega
  · simp [IsMovingHorizonState, D, a]

/-- **Step 3**. -/
theorem step13_3_unit_tail : ∀ j : Nat, 18 < j → j < 20 → d j = 1 := by
  intro j hsj hjr
  have hj : j = 19 := by omega
  subst j
  decide

theorem step13_3 : IsMovingHorizonStep 18 36 20 40 := by
  refine ⟨?_, by decide, by decide, by decide, step13_3_unit_tail, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · simp [IsMovingHorizonState, D, a]

/-- **Step 4**: the terminal step, reaching the exit state `(24, 42)`. -/
theorem step13_4_unit_tail : ∀ j : Nat, 20 < j → j < 24 → d j = 1 := by
  intro j hsj hjr
  have hj : j = 21 ∨ j = 22 ∨ j = 23 := by omega
  rcases hj with rfl | rfl | rfl <;> decide

theorem step13_4 : IsMovingHorizonStep 20 40 24 42 := by
  refine ⟨?_, by decide, by decide, by decide, step13_4_unit_tail, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · simp [IsMovingHorizonState, D, a]

/-- The endpoint state of step 4, extracted by projection so the assembly below
does not depend on the exact nesting of `IsMovingHorizonStep`'s components. -/
theorem endpoint13_4 : IsMovingHorizonState 24 42 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := step13_4
  exact h9

/-- **The `M = 13` canonical replay is a genuine 4-step moving-horizon path** from
`(13 + 2, 2 * 13 - 2)` to `(24, 42)`, assembled from the four verified steps.  No
hypothesis is assumed anywhere. -/
theorem path13 : HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 :=
  ⟨step13_1.1, 17, 28, step13_1,
    ⟨step13_2.1, 18, 36, step13_2,
      ⟨step13_3.1, 20, 40, step13_3,
        ⟨step13_4.1, 24, 42, step13_4, ⟨rfl, rfl, endpoint13_4⟩⟩⟩⟩⟩

/-- **The finite maximum check** for the `M = 13` exit.  Quantifying over `Fin 23`
keeps the statement decidable, which is what the pure-core policy (`decide`
allowed, `interval_cases` not) requires: the index `j` with `2 <= j <= 24` is
`j = k.val + 2` for a unique `k : Fin 23`. -/
theorem d_le_thirteen_upto_24 : ∀ k : Fin 23, d (k.val + 2) ≤ 13 := by decide

/-- **`IsAttainedPreviousMaximum 13 24` holds at the `M = 13` exit.**  The running
maximum of `d` through index 24 is `13`, attained at the canonical start itself
(`d 15 = 13`), so the witness is not an artefact of a gap in the data. -/
theorem max13 : IsAttainedPreviousMaximum 13 24 := by
  refine ⟨?_, ⟨15, by decide, by decide, by decide⟩⟩
  intro j hj2 hj24
  have hfin := d_le_thirteen_upto_24 ⟨j - 2, by omega⟩
  have hidx : j - 2 + 2 = j := by omega
  simpa only [Fin.val_mk, hidx] using hfin

/-- **The travel conclusion fails at `M = 13`**: `2 * (24 - 15) = 18 > 13`. -/
theorem travel13_fails : ¬ (2 * (24 - (13 + 2)) ≤ 13) := by decide

/-- **The frontier target is FALSE without its threshold.**  The only hypothesis
dropped from `CanonicalTravelBoundFrom` is the lower bound on `M`, and `M = 13`
satisfies every remaining hypothesis while violating the conclusion.  So the
threshold `22933441` (and the `45895573` used at the top) is an essential input:
no threshold-free argument, and no "small `M` is harmless" shortcut, can be sound. -/
theorem travel_bound_without_threshold_is_false :
    ¬ (∀ {M sf Cf p : Nat}, d (M + 2) = M →
        HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
        IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M) := by
  intro h
  exact travel13_fails (h d15_eq_thirteen path13 max13)

/-- **The obstruction at `M = 13`, assembled in one statement.**  All frontier
hypotheses except `45895573 <= M` hold, and the conclusion fails. -/
theorem threshold_is_only_obstruction_at_thirteen :
    d (13 + 2) = 13 ∧ HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 ∧
      IsAttainedPreviousMaximum 13 24 ∧ ¬ (2 * (24 - (13 + 2)) ≤ 13) :=
  ⟨d15_eq_thirteen, path13, max13, travel13_fails⟩

/-- **The converse is false, and here is the arithmetic witness.**  At `M = 13` the
excess bound holds (`18 <= 22`) while travel fails (`18 > 13`); `path13` and
`max13` in §3 give the genuine replay.  This is the refutation of claim B, isolated
so that no future attempt re-derives the equivalence. -/
theorem excess_bound_does_not_give_travel :
    ¬ (∀ M sf Cf S : Nat, 2 ≤ M →
        (Cf - sf) + (sf - (M + 2)) = (M - 4) + S → B sf = (Cf - sf) + 2 →
        S ≤ B sf + 2 → 2 * (sf - (M + 2)) ≤ M) := by
  intro h
  have hroom : ((42 : Nat) - 24) + (24 - (13 + 2)) = (13 - 4) + 18 := by decide
  have hB : B 24 = ((42 : Nat) - 24) + 2 := by decide
  have hexcess : (18 : Nat) ≤ B 24 + 2 := by decide
  have hbad := h 13 24 42 18 (by decide) hroom hB hexcess
  exact travel13_fails hbad

end A166944Research
