/-
  Third report module: the sharpest form of the negative result.

  NOT part of the repository.

  The point.  Every conceivable "record-structure" input is a predicate `Q M sf`
  on the endpoint.  If `Q` is entailed by the canonical hypothesis plus the path,
  then it cannot strengthen the frontier.  The statements below make that
  precise, and then exhibit the two concrete `Q`'s the task suggested
  (attainment of `M` at some `r <= sf`; attainment at `r = M + 2`) as instances.
-/
import A166944.RelaxedCap
import A166944.CapBCandidates
import A166944.OrphanHarvest

namespace A166944Research

/-! ## I. A generic criterion for "this extra input is free" -/

/-- **Generic absorption.**  Given any `Q : Nat → Nat → Prop` that holds at every
`(M, sf)` reachable from a canonical start, the target's conclusion cannot depend
on `Q`: a proof from `Q` transports to a proof without it, at the same strength and
with no extra hypothesis.

This is the criterion the task's angle has to pass, and it is the reason the
second component of `IsAttainedPreviousMaximum` is unusable. -/
theorem extra_hypothesis_is_absorbed
    (Q : Nat → Nat → Prop)
    (hQ : ∀ {M sf Cf p : Nat}, d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p → Q M sf)
    (h : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p → Q M sf → 4 * sf ≤ 7 * M - 1) :
    ∀ {M sf Cf p : Nat}, 45895573 ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p → 4 * sf ≤ 7 * M - 1 := by
  intro M sf Cf p hM hcanon hpath
  exact h hM hcanon hpath (hQ hcanon hpath)

/-- **Instance: attainment at an arbitrary index.**  The predicate
"`∃ r ≤ sf, d r = M`" satisfies the criterion above, so adding it to the
hypotheses of the frontier changes nothing. -/
theorem attainment_predicate_is_absorbed :
    ∀ {M sf Cf p : Nat}, d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = M := by
  intro M sf Cf p hcanon hpath
  exact ⟨M + 2, by omega, moving_horizon_path_index_le hpath, hcanon⟩

/-- **Instance: attainment at the canonical start itself.**  The stronger predicate
"`d (M + 2) = M ∧ M + 2 ≤ sf`" is also absorbed -- it is literally the canonical
hypothesis plus the tree's unconditional index bound.  So neither the weak nor the
strong reading of "the second component" carries information. -/
theorem attainment_at_start_is_absorbed :
    ∀ {M sf Cf p : Nat}, d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      d (M + 2) = M ∧ M + 2 ≤ sf :=
  fun hcanon hpath => ⟨hcanon, moving_horizon_path_index_le hpath⟩

/-! ## J. The frontier as an inequality in the excess sum

`BIntegrate` gives `B sf + (sf - (M + 2)) = (M - 2) + S`; `RoomLedger` gives
`Cf - sf = B sf - 2`.  Composing them turns the cap into a statement about `S` and
the travel alone.  Stated here because it is the coordinate system in which the
"record structure" input would have to act, and it shows the input needed is an
upper bound on a *sum over the replay*, not a property of the endpoint. -/

/-- **Why an excess-sum bound is the wrong target.**  With the two ledgers the cap
is *equivalent* to `4 * travel <= 3 * M - 9` -- it bounds the travel and says
nothing about `S`.  A bound on `S` alone therefore cannot imply the cap, which is
`CapBCandidates.candidate1_route_is_circular` (`excess_only_gives_identity`) read
in this direction.  Recorded so the "bound S" angle is not re-attempted. -/
theorem excess_bound_alone_cannot_give_cap {M S travel Bsf : Nat} (hM : 4 ≤ M)
    (hB : Bsf + travel = (M - 2) + S) :
    (2 * S + M ≤ 2 * Bsf + 4 ↔ 2 * travel ≤ M) :=
  excess_only_gives_identity hM hB

/-- **The concise true form.**  The cap is exactly `4 * travel <= 3 * M - 9`
(`CapBCandidates.capB_iff_travel_form`), so in excess coordinates it reads
`4 * (sf - (M + 2)) <= 3 * M - 9`: the *travel*, not the endpoint, is what has to
be bounded, and the endpoint's attainment structure never enters. -/
theorem cap_is_a_travel_bound {M sf : Nat} (hM : 9 ≤ M) (h : M + 2 ≤ sf) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * (sf - (M + 2)) ≤ 3 * M - 9 :=
  capB_iff_travel_form hM h

/-! ## Axiom audit -/

#print axioms extra_hypothesis_is_absorbed
#print axioms attainment_predicate_is_absorbed
#print axioms attainment_at_start_is_absorbed
#print axioms excess_bound_alone_cannot_give_cap
#print axioms cap_is_a_travel_bound

end A166944Research
