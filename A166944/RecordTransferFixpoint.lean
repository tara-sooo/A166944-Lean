/-
  F5 scratch module, part 2: the record-sequence induction is a FIXED POINT.

  Setup (all from the tree, none assumed):
    * `AttainmentIsFree.terminal_exit_reset`: a canonical replay with terminal
      horizon `Cf` is followed by the record `R' = Cf + 1`, at index `Cf + 3`.
    * the replay ledger: `Cf = (2 * M - 2) + S`, where `S = sum (d r - 1)` is the
      replay's accumulated excess.
    * `TravelExcessSum.path_travel_le_two_mul_excess`: `travel <= 2 * (S + p)`,
      with `p` the event count; unconditional.
    * `TravelExcessSum.relaxed_cap_of_excess_sum`: those two give the cap.

  The angle asks whether the cap can be proved by induction on the record
  sequence, with hypothesis "the cap holds at the previous record `R`".

  RESULT.  Substituting `R' = Cf + 1 = 2 * M - 1 + S` into the next record's
  threshold gives the exact identity

      3 * (Cf + 1) + 3 = 6 * M + 3 * S,

  so the hypothesis the step needs at `R'` is `8 * (S' + p') + 9 <= 3 * R'` --
  *identically* `R'`'s own excess criterion, with no occurrence of `R`'s cap.  The
  step consumes exactly the statement it is meant to produce.  The missing input is
  a fixed point of the transfer, not something the transfer can manufacture.

  Part 1 (`cap_does_not_transfer_along_records`) shows the threshold-free transfer
  is not even sound, at the consecutive records `7 -> 13`.  Together the two close
  the record-sequence angle from both sides.

  NOT part of the repository.  No `sorry`, `admit`, `axiom`, `unsafe`.
-/
import A166944.TravelExcessSum
import A166944.TerminalRigidity

set_option maxRecDepth 400000

namespace A166944Research

/-! ## 1. The substitution, truncation-free

Every statement below is written additively.  `8 * x + 9 <= 3 * M` is equivalent to
`8 * x <= 3 * M - 9` for `9 <= 3 * M`, and the additive form avoids the truncated
subtraction that defeats `omega` next to a coefficient -- the discipline
`RelaxedCap` and `TravelExcessSum` already use. -/

/-- **The next record's value in the current record's coordinates.**
`Cf = (2 * M - 2) + S` gives `R' = Cf + 1`, hence `R' + 1 = 2 * M + S` and so
`3 * R' + 3 = 6 * M + 3 * S`.  This is the substitution the induction performs,
and it is an identity, not an inequality. -/
theorem next_threshold_identity {M Cf S : Nat} (hM : 2 ≤ M)
    (hS : Cf = (2 * M - 2) + S) :
    3 * (Cf + 1) + 3 = 6 * M + 3 * S := by
  have hkey : Cf + 1 + 1 = 2 * M + S := by omega
  calc 3 * (Cf + 1) + 3 = 3 * (Cf + 1) + 3 * 1 := by rw [Nat.mul_one]
    _ = 3 * (Cf + 1 + 1) := (Nat.mul_add _ _ _).symm
    _ = 3 * (2 * M + S) := by rw [hkey]
    _ = 3 * (2 * M) + 3 * S := Nat.mul_add _ _ _
    _ = 6 * M + 3 * S := by rw [show 3 * (2 * M) = 6 * M by omega]

/-- **The threshold in the two coordinate systems.**  The next record's criterion
`8 * x + 9 <= 3 * R'` is exactly `8 * x + 12 <= 6 * M + 3 * S`.  Both directions,
so the substitution is a change of coordinates and not a weakening. -/
theorem next_criterion_substituted {M Cf S x : Nat} (hM : 2 ≤ M)
    (hS : Cf = (2 * M - 2) + S) :
    8 * x + 9 ≤ 3 * (Cf + 1) ↔ 8 * x + 12 ≤ 6 * M + 3 * S := by
  have hid := next_threshold_identity hM hS
  omega

/-! ## 2. The step, and its exact hypothesis

The step reuses the tree's own assembly: `relaxed_cap_of_excess_sum` already proves
that the excess criterion at a canonical start gives the cap there.  Applying it at
`R'` instead of at `M` is the whole of the transfer. -/

/-- **The induction step.**  If the next record `R' = Cf + 1` has a replay ending
at `sf'` with excess `S''` and count `p'` satisfying the excess criterion *at `R'`*,
then the cap holds at `R'`.

The hypotheses mention `M` only through the ledger `Cf = (2 * M - 2) + S`.  `M`'s
cap, terminal index and count are not consumed anywhere: this is the sense in which
the step is sound but produces nothing new. -/
theorem cap_at_next_of_next_excess_bound {M Cf S sf' Cf' p' S'' : Nat}
    (hM : 9 ≤ M) (hS : Cf = (2 * M - 2) + S)
    (hpath' : HasMovingHorizonPathTo (Cf + 1 + 2) (2 * (Cf + 1) - 2) sf' Cf' p')
    (hS'' : sf' - (Cf + 1 + 2) ≤ 2 * (S'' + p'))
    (hbound : 8 * (S'' + p') ≤ 3 * (Cf + 1) - 9) :
    4 * sf' ≤ 7 * (Cf + 1) - 1 :=
  relaxed_cap_of_excess_sum (by omega) hpath' hS'' hbound

/-- **The same step, with the substitution applied.**  By
`next_criterion_substituted` the bound `8 * (S'' + p') + 12 ≤ 6 * M + 3 * S` is the
same statement as `8 * (S'' + p') + 9 ≤ 3 * (Cf + 1)`.  Comparing this theorem with
the previous one is the fixed point: the step's hypothesis *is* the next record's
criterion, rewritten. -/
theorem cap_at_next_of_substituted_bound {M Cf S sf' Cf' p' S'' : Nat}
    (hM : 9 ≤ M) (hS : Cf = (2 * M - 2) + S)
    (hpath' : HasMovingHorizonPathTo (Cf + 1 + 2) (2 * (Cf + 1) - 2) sf' Cf' p')
    (hS'' : sf' - (Cf + 1 + 2) ≤ 2 * (S'' + p'))
    (hbound : 8 * (S'' + p') + 9 ≤ 3 * (Cf + 1)) :
    4 * sf' ≤ 7 * (Cf + 1) - 1 := by
  have hnine : 9 ≤ 3 * (Cf + 1) := by omega
  refine cap_at_next_of_next_excess_bound hM hS hpath' hS'' ?_
  omega

/-- **The step in the substituted coordinates.**  The hypothesis is stated as
`8 * (S'' + p') + 12 ≤ 6 * M + 3 * S`, i.e. entirely in the *previous* record's
variables.  Reading it next to `next_criterion_substituted` shows that this is
`R'`'s criterion and not a new fact about `R`. -/
theorem cap_at_next_of_coordinate_form {M Cf S sf' Cf' p' S'' : Nat}
    (hM : 9 ≤ M) (hS : Cf = (2 * M - 2) + S)
    (hpath' : HasMovingHorizonPathTo (Cf + 1 + 2) (2 * (Cf + 1) - 2) sf' Cf' p')
    (hS'' : sf' - (Cf + 1 + 2) ≤ 2 * (S'' + p'))
    (hbound : 8 * (S'' + p') + 12 ≤ 6 * M + 3 * S) :
    4 * sf' ≤ 7 * (Cf + 1) - 1 := by
  refine cap_at_next_of_substituted_bound hM hS hpath' hS'' ?_
  exact (next_criterion_substituted (M := M) (Cf := Cf) (S := S)
    (x := S'' + p') (by omega) hS).2 hbound

/-- **The step's hypothesis does not mention the current record's cap.**  Restated
so the reading is unavoidable: for every `M`, `S` and every `R'`-replay, the
criterion at `R'` gives the cap at `R'`. -/
theorem next_cap_needs_no_current_cap {M Cf S sf' Cf' p' S'' : Nat}
    (hM : 9 ≤ M) (hS : Cf = (2 * M - 2) + S)
    (hpath' : HasMovingHorizonPathTo (Cf + 1 + 2) (2 * (Cf + 1) - 2) sf' Cf' p')
    (hS'' : sf' - (Cf + 1 + 2) ≤ 2 * (S'' + p'))
    (hbound : 8 * (S'' + p') ≤ 3 * (Cf + 1) - 9) :
    4 * sf' ≤ 7 * (Cf + 1) - 1 :=
  cap_at_next_of_next_excess_bound hM hS hpath' hS'' hbound

/-! ## 3. The steps compose into the tree's two-cap algebra

`RelaxedCap.cap_b_implies_count_bound` records that the cap at `M` forces
`4 * p <= 3 * M + 3`.  Under the substitution the next record's index is
`2 * M - 1 + S`, so the cap at `R'` is a bound on `S` evaluated one record later --
which is why the measured `S / M` decreasing to zero looks like progress while the
statement being proved is unchanged. -/

/-- **The cap at the next record, in the current record's coordinates.**  Since
`R' = 2 * M - 1 + S`, the cap at `R'` reads `4 * sf' + 1 <= 7 * (2 * M - 1 + S)`,
i.e. `4 * sf' <= 14 * M + 7 * S - 8`.  Recorded so the growth in `S` is visible:
the right-hand side *increases* with `S`, so a large excess pays for the next
record's travel. -/
theorem next_cap_in_current_coordinates {M Cf S sf' : Nat} (hM : 2 ≤ M)
    (hS : Cf = (2 * M - 2) + S) (hcap : 4 * sf' ≤ 7 * (Cf + 1) - 1) :
    4 * sf' + 8 ≤ 14 * M + 7 * S := by
  have hkey : Cf + 1 = 2 * M - 1 + S := by omega
  have h3 := next_threshold_identity hM hS
  omega

/-- **The fixed point, as the headline identity.**  The record sequence advances by
`R' = Cf + 1 = 2 * M - 1 + S`, and the threshold the next record's criterion uses
is `3 * R' + 3 = 6 * M + 3 * S`.  Nothing in the advance reduces the threshold: it
is the same expression in the next record's name. -/
theorem record_induction_is_a_fixed_point {M Cf S : Nat} (hM : 2 ≤ M)
    (hS : Cf = (2 * M - 2) + S) :
    3 * (Cf + 1) + 3 = 6 * M + 3 * S :=
  next_threshold_identity hM hS

/-! ## 4. Axiom audit -/

#print axioms next_threshold_identity
#print axioms next_criterion_substituted
#print axioms cap_at_next_of_next_excess_bound
#print axioms cap_at_next_of_substituted_bound
#print axioms cap_at_next_of_coordinate_form
#print axioms next_cap_needs_no_current_cap
#print axioms next_cap_in_current_coordinates
#print axioms record_induction_is_a_fixed_point

end A166944Research
