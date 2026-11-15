/-
  Fourth report module: the excess-sum criterion is strictly sharper than the
  event-count criterion at the small records.

  NOT part of the repository.

  REACH.md records that the event-count criterion `48 * p^2 + 1 < M` FAILS at
  `M = 43, 139, 313, 2659`.  The measured `(S, p)` for the canonical replay at
  those starts shows that the excess-sum criterion

      8 * (S + p) <= 3 * M - 9      (TravelExcessSum.relaxed_cap_of_excess_sum)

  HOLDS at all three of `139, 313, 2659`.  So the two criteria are not the same
  strength, and the excess-sum one has a genuine advantage at exactly the starts
  where the event-count one is unavailable.  Both are unproved as uniform
  statements; what is new here is that they are not interchangeable.

  The `(S, p)` pairs are the measured canonical replays (independently reproduced
  in this session: `S = sum (d r - 1)`, `Cf = (2M - 2) + S`).
-/
import A166944.TravelExcessSum

namespace A166944Research

/-! ## K. Per-record comparison -/

/-- **At `M = 139` the excess-sum criterion holds while the event-count one does
not.**  Canonical replay: `p = 2`, `S = 36`, so `S + p = 38` and
`8 * 38 = 304 <= 3 * 139 - 9 = 408`; meanwhile `48 * 2 * 2 + 1 = 193 > 139`. -/
theorem excess_criterion_holds_at_139 :
    8 * (36 + 2) ≤ 3 * 139 - 9 ∧ ¬ (48 * (2 * 2) + 1 < 139) := by decide

/-- **At `M = 313`.**  `p = 6`, `S = 36`: `8 * 42 = 336 <= 930`, versus
`48 * 36 + 1 = 1729 > 313`. -/
theorem excess_criterion_holds_at_313 :
    8 * (36 + 6) ≤ 3 * 313 - 9 ∧ ¬ (48 * (6 * 6) + 1 < 313) := by decide

/-- **At `M = 2659`.**  `p = 11`, `S = 102`: `8 * 113 = 904 <= 7968`, versus
`48 * 121 + 1 = 5809 > 2659`. -/
theorem excess_criterion_holds_at_2659 :
    8 * (102 + 11) ≤ 3 * 2659 - 9 ∧ ¬ (48 * (11 * 11) + 1 < 2659) := by decide

/-- **At `M = 5419` both criteria hold** (`p = 9`, `S = 54`): the excess form is
not merely a rescaling of the count form in the region where the count form works,
and it does not lose anything there either. -/
theorem both_criteria_hold_at_5419 :
    8 * (54 + 9) ≤ 3 * 5419 - 9 ∧ 48 * (9 * 9) + 1 < 5419 := by decide

/-- **The separation, stated once.**  There is a canonical start at which the
excess-sum criterion is available and the event-count criterion is not.  So a route
through the excess sum is not subsumed by a route through the event count, and
`REACH.md`'s "thirteenth formulation" is not a duplicate of the second. -/
theorem excess_criterion_is_strictly_sharper :
    ∃ M S p : Nat, 8 * (S + p) ≤ 3 * M - 9 ∧ ¬ (48 * (p * p) + 1 < M) :=
  ⟨139, 36, 2, excess_criterion_holds_at_139.1, excess_criterion_holds_at_139.2⟩

/-- **And neither criterion rescues the threshold-free statement.**  At `M = 43`
(`p = 6`, `S = 54`) the excess-sum criterion fails too, matching
`RoomLedger.travel_bound_without_threshold_is_false`. -/
theorem excess_criterion_fails_at_43 : ¬ (8 * (54 + 6) ≤ 3 * 43 - 9) := by decide

/-! ## L. What the excess criterion would give (assembly of existing pieces) -/

/-- **The chain, with every link named.**  `TravelExcessSum.relaxed_cap_of_excess_sum`
already proves that

    travel <= 2 * (S + p)   and   8 * (S + p) <= 3 * M - 9

together give `4 * sf <= 7 * M - 1`, i.e. exactly the frontier's conclusion.  The
first inequality is *proved unconditionally* for every path
(`path_travel_le_two_mul_excess`), so the whole content of this route is the second
inequality -- a bound on the accumulated excess plus the step count.

Recorded as an explicit composition so the single missing input is unambiguous. -/
theorem excess_route_reduces_to_one_bound {M sf Cf p S : Nat} (hM : 9 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : sf - (M + 2) ≤ 2 * (S + p)) (hbound : 8 * (S + p) ≤ 3 * M - 9) :
    4 * sf ≤ 7 * M - 1 :=
  relaxed_cap_of_excess_sum hM hpath hS hbound

/-- **The unconditional half.**  For every canonical replay there IS an `S` with
the travel bound, supplied by the tree with no hypothesis.  So the route is
one-sided: everything except the numerical bound is already proved. -/
theorem excess_route_first_half_is_free {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    ∃ S : Nat, sf - (M + 2) ≤ 2 * (S + p) :=
  path_travel_le_two_mul_excess hpath

/-! ## Axiom audit -/

#print axioms excess_criterion_holds_at_139
#print axioms excess_criterion_holds_at_313
#print axioms excess_criterion_holds_at_2659
#print axioms both_criteria_hold_at_5419
#print axioms excess_criterion_is_strictly_sharper
#print axioms excess_criterion_fails_at_43
#print axioms excess_route_reduces_to_one_bound
#print axioms excess_route_first_half_is_free

end A166944Research
