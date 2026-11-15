import A166944.ExcessLower
import A166944.RoomLedger
import A166944.RelaxedCap

/-!
# The excess criterion: its normal form, its consequence, and its refutation

The excess criterion is

    8 * (S + p) <= 3 * M - 9,

with `S` the accumulated excess and `p` the step count of a canonical replay. It is
worth knowing that this is **not** a new route to the relaxed index cap, and this
module records why, together with a refutation of its threshold-free form.

## The refutation

Without the threshold the criterion is false, and not because of a bad choice of `S`:
the ledger `Cf = (2*M-2) + S` pins `S` uniquely, so the counterexample at `M = 13` is
forced. `excess_criterion_without_threshold_is_false_for_every_S` states it in the
form that closes the loophole -- for *every* `S`, not merely for the ledger's.

The canonical starts below `139` are exactly `7`, `13`, `43`
(`canonical_start_solutions_below_139`), so `139` is the **optimal threshold of this
route**, not an incidental small case. That matters because a natural reading of the
earlier `ExcessLower` note was that the failures at `M = 43` and `M = 139` are far
below the working threshold and therefore harmless. The first half is arithmetic and
the inference is wrong.

## Why it is not a new route

Substituting the ledger turns the criterion into an affine inequality in `(Cf, p)`;
adding `2*p <= S` (`ExcessLower.two_mul_count_le_excess`) reduces it to

    8 * S <= 3 * M - 9,

which is the bound on the accumulated excess that `REACH.md` names as the one missing
input. So the excess criterion is the same obstruction in different coordinates, and
the quarter bound `4*S <= M-3` is strictly stronger than it while failing at `139`.

## What is kept

The arithmetic identities, the refutation, and the optimal threshold. The
observation table from the run is not reproduced here; the three criteria agree at
every canonical start examined, which follows from `travel <= 2*(S+p)` being proved
rather than being independent evidence.
-/

namespace A166944Research

-- The `decide` checks below elaborate deep recursions over `Fin` ranges; the
-- default limit is too low for them.
set_option maxRecDepth 4000000


/-! ## 0. Two finite-check helpers

`RoomLedger` discharged the unit tails of its `M = 13` replay one index at a time.
The lemmas below replace that with a single `decide` on a `Fin` type, which is what
makes the six-step canonical replays of §4 cheap to certify (about 5 s each). -/

/-- **A unit tail, from a finite check.**  If every index of the block
`s + 1, ..., r - 1` has `d = 1`, the whole tail is unit. -/
theorem unit_tail_of_fin {s r : Nat}
    (h : ∀ k : Fin (r - s - 1), d (s + 1 + k.val) = 1) :
    ∀ j : Nat, s < j → j < r → d j = 1 := by
  intro j hsj hjr
  have hk : j - (s + 1) < r - s - 1 := by omega
  have hfin := h ⟨j - (s + 1), hk⟩
  have hidx : s + 1 + (j - (s + 1)) = j := by omega
  simpa [hidx] using hfin

/-- **A running maximum, from a finite check.**  If `d <= P` on `2, ..., k`, then
`IsAttainedPreviousMaximum P k` follows once a witness for `d r = P` at `r <= k` is
supplied. -/
theorem max_of_fin {P k : Nat} (h : ∀ i : Fin (k - 1), d (i.val + 2) ≤ P) :
    ∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ P := by
  intro j hj2 hjk
  have hlt : j - 2 < k - 1 := by omega
  have hfin := h ⟨j - 2, hlt⟩
  have hidx : j - 2 + 2 = j := by omega
  simpa [hidx] using hfin

/-! ## 1. Truncation-free arithmetic normal forms

`omega` mishandles a coefficient applied to a truncated subtraction, so each
truncated expression below is named once, with no coefficient attached. -/

/-- `3 * M - 9` is not truncated once `9 ≤ M`. -/
theorem three_mul_sub_nine_add {M : Nat} (hM : 9 ≤ M) : 3 * M - 9 + 9 = 3 * M :=
  Nat.sub_add_cancel (by omega)

/-- `19 * M - 25` is not truncated once `9 ≤ M`. -/
theorem nineteen_mul_sub_25_add {M : Nat} (hM : 9 ≤ M) : 19 * M - 25 + 25 = 19 * M :=
  Nat.sub_add_cancel (by omega)

/-- The canonical start base, scaled by eight, with the subtraction distributed. -/
theorem eight_mul_base {M : Nat} (hM : 1 ≤ M) : 8 * (2 * M - 2) = 16 * M - 16 := by
  have h : 2 * M - 2 = 2 * (M - 1) := by omega
  have h16 : 8 * 2 = 16 := rfl
  rw [h, ← Nat.mul_assoc, h16, Nat.mul_sub_left_distrib, Nat.mul_one]

/-! ## 2. (EXC) in horizon coordinates

`HorizonLedger.canonical_horizon_eq_base_add_excess` supplies `S` with
`Cf = (2 * M - 2) + S`.  Substituting it removes `sf` entirely: the criterion is a
joint affine bound on the terminal horizon and the event count. -/

/-- **(EXC) is an affine inequality in `(Cf, p)`.**  With `Cf = (2*M-2) + S`,

    8 * (S + p) <= 3 * M - 9   <->   8 * Cf + 8 * p <= 19 * M - 25 .

The content is that the accumulated horizon growth `Cf - (2*M-2) = S` plus the
event count is at most `(3*M - 25)/8`. -/
theorem excess_criterion_iff_horizon_form {M S p Cf : Nat} (hM : 9 ≤ M)
    (hCf : Cf = 2 * M - 2 + S) :
    8 * (S + p) ≤ 3 * M - 9 ↔ 8 * Cf + 8 * p ≤ 19 * M - 25 := by
  subst hCf
  have h8 := eight_mul_base (M := M) (by omega)
  have h3 := three_mul_sub_nine_add hM
  have h19 := nineteen_mul_sub_25_add hM
  constructor <;> intro h <;> omega

/-- **The horizon-growth reading of (EXC).**  `S >= 2 * p` is unconditional (§3), so
(EXC) forces the accumulated excess itself under `3 * M / 8`:

    8 * S <= 3 * M - 9 .

Contrast the horizon cap `Cf <= 3 * M + 4` the tree currently carries, which in
these coordinates permits `S <= M + 6`.  (EXC) is sharper by a factor of about
`8/3`, and that is the whole of its content. -/
theorem excess_criterion_forces_horizon_growth {M S p : Nat} (hM : 9 ≤ M)
    (hSp : 2 * p ≤ S) (hcrit : 8 * (S + p) ≤ 3 * M - 9) : 8 * S ≤ 3 * M - 9 := by
  omega

/-! ## 3. The count consequence: (EXC) forces `8 * p <= M - 3`

`CountFromIndex.horizon_ge_start_add_twice_count` gives `2 * M - 2 + 2 * p <= Cf`
along any canonical path; with `Cf = (2*M-2) + S` this is exactly `2 * p <= S`.  So
(EXC), which is `8 * S + 8 * p <= 3 * M - 9` with `S >= 2 * p`, controls `p` only
linearly in `M` -- against the `sqrt (M / 48)` of the event-count criterion. -/

/-- **The accumulated excess dominates twice the event count.**  A named identity:
`CountFromIndex`'s count bound read in the excess coordinate. -/
theorem canonical_excess_ge_twice_count {M sf Cf p S : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : Cf = (2 * M - 2) + S) : 2 * p ≤ S := by
  have h := horizon_ge_start_add_twice_count hpath
  omega

/-- **(EXC) forces `8 * p <= M - 3`.**  `2*p <= S` and `8*S + 8*p <= 3*M - 9` give
`24 * p <= 3 * M - 9`. -/
theorem excess_criterion_forces_count {M S p : Nat} (hM : 9 ≤ M) (hSp : 2 * p ≤ S)
    (hcrit : 8 * (S + p) ≤ 3 * M - 9) : 8 * p ≤ M - 3 := by omega

/-- The same, composed with the path: (EXC) at a canonical start forces
`8 * p <= M - 3`. -/
theorem excess_criterion_forces_count_of_path {M sf Cf p S : Nat} (hM : 9 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : Cf = (2 * M - 2) + S) (hcrit : 8 * (S + p) ≤ 3 * M - 9) :
    8 * p ≤ M - 3 :=
  excess_criterion_forces_count hM (canonical_excess_ge_twice_count hpath hS) hcrit

/-- `45895573 / 8 = 5736946`, so (EXC) at the frontier threshold permits `p` up to
`M / 8`. -/
theorem threshold_div_eight : 45895573 / 8 = 5736946 := by decide

/-- **The count (EXC) permits at the threshold is far above what the event-count
criterion needs.**  `8 * p <= M - 3` allows `p = 5736946`; `48 * p * p + 1 < M`
allows only `p <= 977`.  So the excess route is weaker by a factor of about `5870`
in the count coordinate, and (EXC) cannot discharge the event-count criterion. -/
theorem excess_count_allowance_is_far_above_event_count :
    48 * 5736946 * 5736946 + 1 > 45895573 := by decide

/-! ## 4. Position among the other forms: quarter bound, cap (B), travel

`2 * p <= S` makes `4 * S <= M - 3` sufficient for (EXC), and (EXC) in turn gives
cap (B) because `travel <= 2 * (S + p)`.  Both inclusions are strict. -/

/-- **The quarter bound suffices for (EXC).** -/
theorem quarter_bound_suffices {M S p : Nat} (hM : 9 ≤ M) (hSp : 2 * p ≤ S)
    (hS : 4 * S ≤ M - 3) : 8 * (S + p) ≤ 3 * M - 9 := by omega

/-- **(EXC) does not imply the quarter bound.**  Witness: `M = 139`, `S = 36`,
`p = 2` -- the certified canonical replay at the first start where the event-count
criterion fails. -/
theorem quarter_bound_is_strictly_stronger :
    ¬ (∀ M S p : Nat, 9 ≤ M → 2 * p ≤ S → 8 * (S + p) ≤ 3 * M - 9 →
        4 * S ≤ M - 3) := by
  intro h
  have hbad := h 139 36 2 (by decide) (by decide) (by decide)
  exact absurd hbad (by decide)

/-- The separating arithmetic, stated alone so the numbers are visible: (EXC) holds
at `M = 139` while the quarter bound fails. -/
theorem quarter_bound_fails_while_excess_holds_at_139 :
    8 * (36 + 2) ≤ 3 * 139 - 9 ∧ ¬ (4 * 36 ≤ 139 - 3) := by decide

/-- **(EXC) implies cap (B).**  With `travel <= 2 * (S + p)` this is
`relaxed_cap_of_excess_sum`; stated here in the arithmetic form so the strictness
comparison below is visible. -/
theorem excess_criterion_implies_capB {M S p travel : Nat} (hM : 9 ≤ M)
    (htravel : travel ≤ 2 * (S + p)) (hcrit : 8 * (S + p) ≤ 3 * M - 9) :
    4 * travel ≤ 3 * M - 9 := by omega

/-- **cap (B) evaluated AT the travel bound is exactly (EXC).**  The a priori
inequality `travel <= 2 * (S + p)` is the only link between the two coordinates, so
substituting its tightest case `travel = 2 * (S + p)` into cap (B) returns (EXC)
with no slack at all: `4 * (2 * (S + p)) = 8 * (S + p)`.  So the excess route
carries exactly the same content as the travel route, and the factor `S + p` versus
`travel` is not a loss -- it is where the whole difficulty sits. -/
theorem capB_at_travel_bound_iff_excess {M S p : Nat} (hM : 9 ≤ M) :
    4 * (2 * (S + p)) ≤ 3 * M - 9 ↔ 8 * (S + p) ≤ 3 * M - 9 := by omega

/-- **(EXC) is strictly stronger than cap (B) as a statement.**  `travel = 0`
satisfies cap (B) for every `M`, while (EXC) fails at `M = 139` as soon as
`S + p > (3*M - 9)/8`.  The gap is entirely the slack in `travel <= 2 * (S + p)`,
which is why the `M = 13` obstruction -- a statement about travel, where `travel`
is at the bound -- is inherited by (EXC) verbatim rather than diluted. -/
theorem capB_does_not_imply_excess_criterion :
    ¬ (∀ M S p travel : Nat, 9 ≤ M → 4 * travel ≤ 3 * M - 9 →
        8 * (S + p) ≤ 3 * M - 9) := by
  intro h
  have hbad := h 139 100 10 0 (by decide) (by decide)
  exact absurd hbad (by decide)

/-! ## 5. The refutation at `M = 13`

`RoomLedger` carries a genuine four-step canonical replay at `M = 13`,

    (15,24) --d 17 = 5--> (17,28) --d 18 = 9--> (18,36) --d 20 = 5--> (20,40)
            --d 24 = 3--> (24,42)

with `sf = 24`, `Cf = 42`, `p = 4` and `IsAttainedPreviousMaximum 13 24`.  Every
hypothesis of (EXC) except a lower bound on `M` holds.  `HorizonLedger` then forces
`S = 18` (`42 = (2*13 - 2) + S`), and `8 * (18 + 4) = 176 > 3 * 13 - 9 = 30`. -/

/-- **The excess at the `M = 13` exit is forced to be `18`.**  Any `S` with
`Cf = (2 * M - 2) + S` at `M = 13`, `Cf = 42` equals `18`. -/
theorem forced_excess_at_thirteen {S : Nat} (h : (42 : Nat) = (2 * 13 - 2) + S) :
    S = 18 := by omega

/-- **The `M = 13` excess criterion, in the `S` coordinate.** -/
theorem excess_criterion_fails_at_thirteen : ¬ (8 * (18 + 4) ≤ 3 * 13 - 9) := by decide

/-- **(EXC) IS FALSE WITHOUT ITS THRESHOLD**, in the strongest available form: not
merely for the existential `S` of `HorizonLedger`, but for EVERY `S` consistent
with the canonical replay ledger.  The `M = 13` replay supplies all other
hypotheses. -/
theorem excess_criterion_without_threshold_is_false_for_every_S :
    ¬ (∀ {M sf Cf p S : Nat}, d (M + 2) = M →
        HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
        IsAttainedPreviousMaximum M sf → Cf = (2 * M - 2) + S →
        8 * (S + p) ≤ 3 * M - 9) := by
  intro h
  have hbad := h d15_eq_thirteen path13 max13 (S := 18) (by decide)
  exact absurd hbad (by decide)

/-- The same refutation in the horizon-only form of §2: there is no threshold-free
proof of `8 * Cf + 8 * p <= 19 * M - 25` either. -/
theorem horizon_form_without_threshold_is_false :
    ¬ (∀ {M sf Cf p : Nat}, d (M + 2) = M →
        HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
        IsAttainedPreviousMaximum M sf →
        8 * Cf + 8 * p ≤ 19 * M - 25) := by
  intro h
  have hbad := h d15_eq_thirteen path13 max13
  exact absurd hbad (by decide)

/-! ## 6. The `M = 139` canonical replay, certified

Measured replay: `(141,276) --d 150 = 25--> (150,300) --d 156 = 13--> (156,312)`.
So `p = 2`, `Cf = 312`, and `S = 312 - 276 = 36`. -/

theorem st139_0 : IsMovingHorizonState 141 276 := ⟨by decide, by decide, by decide⟩
theorem st139_1 : IsMovingHorizonState 150 300 := ⟨by decide, by decide, by decide⟩
theorem st139_2 : IsMovingHorizonState 156 312 := ⟨by decide, by decide, by decide⟩

theorem step139_1 : IsMovingHorizonStep 141 276 150 300 :=
  ⟨st139_0, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st139_1⟩

theorem step139_2 : IsMovingHorizonStep 150 300 156 312 :=
  ⟨st139_1, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st139_2⟩

/-- **The `M = 139` canonical replay is a genuine two-step moving-horizon path.** -/
theorem path139 : HasMovingHorizonPathTo (139 + 2) (2 * 139 - 2) 156 312 2 :=
  ⟨st139_0, 150, 300, step139_1, ⟨st139_1, 156, 312, step139_2, ⟨rfl, rfl, st139_2⟩⟩⟩

/-- **`IsAttainedPreviousMaximum 139 156`** -- the running maximum of `d` through
156 is `139`, attained at the canonical start index `141`. -/
theorem max139 : IsAttainedPreviousMaximum 139 156 :=
  ⟨max_of_fin (by decide), ⟨141, by decide, by decide, by decide⟩⟩

/-- **`ExcessCriterion`'s `decide`-level claim at `139`, upgraded to a genuine
recurrence statement**: the path and the attained maximum are real objects here, not
literals, and `S = 36` is forced by the ledger. -/
theorem criterion_at_139_from_path :
    ∃ sf Cf p S : Nat, HasMovingHorizonPathTo (139 + 2) (2 * 139 - 2) sf Cf p ∧
      IsAttainedPreviousMaximum 139 sf ∧ Cf = (2 * 139 - 2) + S ∧
      8 * (S + p) ≤ 3 * 139 - 9 :=
  ⟨156, 312, 2, 36, path139, max139, by decide, by decide⟩

/-- **The `M = 139` numbers, pinned by the ledger rather than asserted.** -/
theorem excess_data_139_forced {S : Nat} (h : (312 : Nat) = (2 * 139 - 2) + S) :
    S = 36 := by omega

/-! ## 7. The `M = 313` canonical replay, certified

Measured replay, six steps:

    (315,624) --317,5--> (317,628) --318,3--> (318,630) --340,17-->
    (340,646) --342,3--> (342,648) --343,11--> (343,658) --348,3--> (348,660)

So `p = 6`, `Cf = 660`, `S = 660 - 624 = 36`. -/

theorem st313_0 : IsMovingHorizonState 315 624 := ⟨by decide, by decide, by decide⟩
theorem st313_1 : IsMovingHorizonState 317 628 := ⟨by decide, by decide, by decide⟩
theorem st313_2 : IsMovingHorizonState 318 630 := ⟨by decide, by decide, by decide⟩
theorem st313_3 : IsMovingHorizonState 340 646 := ⟨by decide, by decide, by decide⟩
theorem st313_4 : IsMovingHorizonState 342 648 := ⟨by decide, by decide, by decide⟩
theorem st313_5 : IsMovingHorizonState 343 658 := ⟨by decide, by decide, by decide⟩
theorem st313_6 : IsMovingHorizonState 348 660 := ⟨by decide, by decide, by decide⟩

theorem step313_1 : IsMovingHorizonStep 315 624 317 628 :=
  ⟨st313_0, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_1⟩
theorem step313_2 : IsMovingHorizonStep 317 628 318 630 :=
  ⟨st313_1, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_2⟩
theorem step313_3 : IsMovingHorizonStep 318 630 340 646 :=
  ⟨st313_2, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_3⟩
theorem step313_4 : IsMovingHorizonStep 340 646 342 648 :=
  ⟨st313_3, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_4⟩
theorem step313_5 : IsMovingHorizonStep 342 648 343 658 :=
  ⟨st313_4, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_5⟩
theorem step313_6 : IsMovingHorizonStep 343 658 348 660 :=
  ⟨st313_5, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st313_6⟩

/-- **The `M = 313` canonical replay is a genuine six-step moving-horizon path.** -/
theorem path313 : HasMovingHorizonPathTo (313 + 2) (2 * 313 - 2) 348 660 6 :=
  ⟨st313_0, 317, 628, step313_1,
    ⟨st313_1, 318, 630, step313_2,
      ⟨st313_2, 340, 646, step313_3,
        ⟨st313_3, 342, 648, step313_4,
          ⟨st313_4, 343, 658, step313_5,
            ⟨st313_5, 348, 660, step313_6, ⟨rfl, rfl, st313_6⟩⟩⟩⟩⟩⟩⟩

/-- **`IsAttainedPreviousMaximum 313 348`** -- the running maximum through 348 is
`313`, attained at `d 315 = 313`. -/
theorem max313 : IsAttainedPreviousMaximum 313 348 :=
  ⟨max_of_fin (by decide), ⟨315, by decide, by decide, by decide⟩⟩

/-- **`ExcessCriterion`'s claim at `313`, upgraded to a genuine recurrence
statement.**  `Cf = 660 = 624 + 36`, `p = 6`. -/
theorem criterion_at_313_from_path :
    ∃ sf Cf p S : Nat, HasMovingHorizonPathTo (313 + 2) (2 * 313 - 2) sf Cf p ∧
      IsAttainedPreviousMaximum 313 sf ∧ Cf = (2 * 313 - 2) + S ∧
      8 * (S + p) ≤ 3 * 313 - 9 :=
  ⟨348, 660, 6, 36, path313, max313, by decide, by decide⟩

/-! ## 8. The `M = 43` canonical replay, certified, with (EXC) failing

Six steps ending at `(79, 138)`: `p = 6`, `Cf = 138`, `S = 138 - 84 = 54`.  The
criterion reads `8 * 60 = 480 > 3 * 43 - 9 = 120`.  This is the second of the two
small canonical starts at which (EXC) fails, and certifying it makes the refutation
independent of any `decide` on a bare arithmetic literal. -/

theorem st43_0 : IsMovingHorizonState 45 84 := ⟨by decide, by decide, by decide⟩
theorem st43_1 : IsMovingHorizonState 47 88 := ⟨by decide, by decide, by decide⟩
theorem st43_2 : IsMovingHorizonState 48 90 := ⟨by decide, by decide, by decide⟩
theorem st43_3 : IsMovingHorizonState 51 96 := ⟨by decide, by decide, by decide⟩
theorem st43_4 : IsMovingHorizonState 60 100 := ⟨by decide, by decide, by decide⟩
theorem st43_5 : IsMovingHorizonState 66 132 := ⟨by decide, by decide, by decide⟩
theorem st43_6 : IsMovingHorizonState 79 138 := ⟨by decide, by decide, by decide⟩

theorem excessg_step43_1 : IsMovingHorizonStep 45 84 47 88 :=
  ⟨st43_0, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_1⟩
theorem excessg_step43_2 : IsMovingHorizonStep 47 88 48 90 :=
  ⟨st43_1, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_2⟩
theorem excessg_step43_3 : IsMovingHorizonStep 48 90 51 96 :=
  ⟨st43_2, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_3⟩
theorem excessg_step43_4 : IsMovingHorizonStep 51 96 60 100 :=
  ⟨st43_3, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_4⟩
theorem excessg_step43_5 : IsMovingHorizonStep 60 100 66 132 :=
  ⟨st43_4, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_5⟩
theorem step43_6 : IsMovingHorizonStep 66 132 79 138 :=
  ⟨st43_5, by decide, by decide, by decide, unit_tail_of_fin (by decide),
    by decide, by decide, by decide, st43_6⟩

/-- **The `M = 43` canonical replay is a genuine six-step moving-horizon path.** -/
theorem path43 : HasMovingHorizonPathTo (43 + 2) (2 * 43 - 2) 79 138 6 :=
  ⟨st43_0, 47, 88, excessg_step43_1,
    ⟨st43_1, 48, 90, excessg_step43_2,
      ⟨st43_2, 51, 96, excessg_step43_3,
        ⟨st43_3, 60, 100, excessg_step43_4,
          ⟨st43_4, 66, 132, excessg_step43_5,
            ⟨st43_5, 79, 138, step43_6, ⟨rfl, rfl, st43_6⟩⟩⟩⟩⟩⟩⟩

/-- **`IsAttainedPreviousMaximum 43 79`** -- the running maximum through 79 is
`43`, attained at `d 45 = 43`. -/
theorem max43 : IsAttainedPreviousMaximum 43 79 :=
  ⟨max_of_fin (by decide), ⟨45, by decide, by decide, by decide⟩⟩

/-- **(EXC) fails at `M = 43`, with the path and the maximum certified.**  The
ledger forces `S = 54` from `Cf = 138 = 84 + 54`, and `p = 6`, so the criterion
reads `480 <= 120`. -/
theorem criterion_fails_at_43_from_path :
    ∃ sf Cf p S : Nat, HasMovingHorizonPathTo (43 + 2) (2 * 43 - 2) sf Cf p ∧
      IsAttainedPreviousMaximum 43 sf ∧ Cf = (2 * 43 - 2) + S ∧
      ¬ (8 * (S + p) ≤ 3 * 43 - 9) :=
  ⟨79, 138, 6, 54, path43, max43, by decide, by decide⟩

/-- **The threshold-free (EXC) is refuted a second time, at `M = 43`.** -/
theorem excess_criterion_without_threshold_false_at_43 :
    ¬ (∀ {M sf Cf p S : Nat}, d (M + 2) = M →
        HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
        IsAttainedPreviousMaximum M sf → Cf = (2 * M - 2) + S →
        8 * (S + p) ≤ 3 * M - 9) := by
  intro h
  obtain ⟨sf, Cf, p, S, hpath, hmax, hS, hbad⟩ := criterion_fails_at_43_from_path
  exact absurd (h (M := 43) (by decide) hpath hmax hS) hbad

/-! ## 9. Where the threshold has to sit: exactly `139`

The `M` that can start a canonical replay are those with
`IsMovingHorizonState (M + 2) (2 * M - 2)`, i.e. `2 ≤ M`, `D (M + 2) = 2 * M - 2`,
`M + 2 < 2 * M - 2`, together with `d (M + 2) = M`.  Below `139` there are exactly
three: `7`, `13`, `43`.  The criterion holds at `7` (no event fits in the window
`(9, 12]`, so `p = 0`, `S = 0`, and it reads `0 <= 12`) and fails at `13` and `43`.
So the optimal threshold for (EXC) is `139` -- not the target's `45895573`.

`M = 3` is the trap in this finite check: it satisfies both arithmetic conditions
(`d 5 = 3`, `D 5 = 4 = 2*3 - 2`) but fails the state condition `3 + 2 < 2*3 - 2`, so
no path can start there.  The state clause is therefore not redundant. -/

/-- **Only `7`, `13`, `43` start a canonical replay below `139`.** -/
theorem canonical_start_solutions_below_139 :
    ∀ k : Fin 139, 2 ≤ k.val → D (k.val + 2) = 2 * k.val - 2 →
      k.val + 2 < 2 * k.val - 2 → d (k.val + 2) = k.val →
      k.val = 7 ∨ k.val = 13 ∨ k.val = 43 := by decide

/-- **`M = 3` satisfies the arithmetic but cannot start a path.** -/
theorem three_satisfies_arithmetic_but_not_the_state :
    d (3 + 2) = 3 ∧ D (3 + 2) = 2 * 3 - 2 ∧ ¬ (3 + 2 < 2 * 3 - 2) := by decide

/-- **No canonical start lies in the open interval `(43, 139)`.**  With the finite
family above, `139` is the first candidate after the two counterexamples, which is
what makes `139` the optimal threshold and not merely a sufficient one. -/
theorem no_canonical_start_between_43_and_139 :
    ∀ k : Fin 139, 43 < k.val → 2 ≤ k.val → D (k.val + 2) = 2 * k.val - 2 →
      k.val + 2 < 2 * k.val - 2 → d (k.val + 2) = k.val → False := by decide

/-- `M = 7` is a canonical start; the window `(9, 12]` holds no event above `1`, so
`p = 0`, `S = 0` and (EXC) holds trivially. -/
theorem seven_is_a_canonical_start :
    d (7 + 2) = 7 ∧ D (7 + 2) = 2 * 7 - 2 ∧ 7 + 2 < 2 * 7 - 2 := by decide

/-- `M = 43` is a canonical start (the replay itself is `path43` in §8). -/
theorem fourtythree_is_a_canonical_start :
    d (43 + 2) = 43 ∧ D (43 + 2) = 2 * 43 - 2 ∧ 43 + 2 < 2 * 43 - 2 := by decide

/-- **The classified family is real, not vacuous.**  `D` at the three starts agrees
with `2 * M - 2` and the state condition holds, so §9 is about genuine states. -/
theorem canonical_start_below_139_data :
    D (7 + 2) = 2 * 7 - 2 ∧ D (13 + 2) = 2 * 13 - 2 ∧ D (43 + 2) = 2 * 43 - 2 := by
  decide

/-! ## 10. Axiom audit -/

#print axioms excess_criterion_iff_horizon_form
#print axioms excess_criterion_forces_horizon_growth
#print axioms canonical_excess_ge_twice_count
#print axioms excess_criterion_forces_count
#print axioms excess_criterion_forces_count_of_path
#print axioms excess_count_allowance_is_far_above_event_count
#print axioms quarter_bound_suffices
#print axioms quarter_bound_is_strictly_stronger
#print axioms excess_criterion_implies_capB
#print axioms capB_at_travel_bound_iff_excess
#print axioms capB_does_not_imply_excess_criterion
#print axioms forced_excess_at_thirteen
#print axioms excess_criterion_without_threshold_is_false_for_every_S
#print axioms horizon_form_without_threshold_is_false
#print axioms criterion_at_139_from_path
#print axioms criterion_at_313_from_path
#print axioms criterion_fails_at_43_from_path
#print axioms excess_criterion_without_threshold_false_at_43
#print axioms canonical_start_solutions_below_139
#print axioms no_canonical_start_between_43_and_139

end A166944Research
