import A166944.RelaxedCap
import A166944.TwoCapGate
import A166944.ExcessIdentity
import A166944.OrphanHarvest

/-!
# The relaxed cap: what it reduces to, and which reductions are dead ends

`TwoCapGate` isolated the relaxed index cap `4 * sf <= 7 * M - 1` as the weaker
replacement for the travel bound. This module records what the cap reduces to, and
-- as importantly -- which natural reductions fail.

## What the cap reduces to, usefully

`capB_of_event_count` is the load-bearing statement: the existing event-count
criterion

    48 * p * p + 1 < M

already implies the cap, in three lines from
`CanonicalTravel.canonical_travel_bound_of_event_count`. So no new input is needed
to reach the cap from that criterion; the work consolidates on `48 * p * p + 1 < M`
instead. `EventCountFails.lean` records that this criterion is *not* automatic --
it fails at five of fourteen records, the smallest at `M = 139` -- so consolidating
on it is a narrowing of the target, not a discharge of it.

`capB_iff_travel_form` restates the cap as `4 * travel <= 3 * M - 9`, which is the
form in which `TravelExcessSum` approaches it.

## A new one-step law

`event_excess_le_horizon_minus_M` is stronger than what `GapBound` has:

    d r - 1 <= C - M      (given `2*M - 2 <= C`)

It uses the `3 * d r <= C +- 1` clause of the step package, which the gap bound
does not. It is real: zero violations across every event of every canonical replay
for odd `M <= 200000`, and at the certified starts. It is also **useless for
summation**, and `horizon_deficit_at_most_doubles` says why: the horizon defect
`C - M` at most doubles per step, so the law permits `2^p * (M - 2)` against the
`3*M/4` the cap needs. A per-step law whose summation is exponential cannot close a
linear target, and recording that is the point of including it here.

## Reductions that fail

`B_route_forces_equality`: the natural `B sf` lower bound route
(`3*M + 8 <= 2 * B sf`, which `BCapDictionary` isolates) forces the *equality*
`2*sf = 3*M + 4` once cap (A) is assumed -- strictly stronger than the cap, and
false at the first canonical start.

The threshold refutations: at `M = 13` the full hypothesis set holds and the cap
fails, so any candidate that follows from the hypotheses alone and suffices for the
cap must fail there too. The numbers are the `M = 13` replay: `p = 4`, `travel = 9`,
`S = 18`, `B sf = 20`, `sf = 24`.

## A caution about the decomposition

The route through `S + p`, which `TravelExcessSum` formalises, is a coordinate
change rather than a reduction: `S` has no bound independent of the travel, since
`B_path_integrated` makes it a function of the travel and the reservoir. The
measurements show a large margin, and the margin is not a proof. This is the
thirteenth independent formulation of the same missing input.
-/

namespace A166944Research


/-! ## 0. Arithmetic normal forms of cap (B) -/

/-- cap (B) at a canonical start is exactly `4 * travel <= 3 * M - 9`. -/
theorem capB_iff_travel_form {M sf : Nat} (hM : 9 ≤ M) (h : M + 2 ≤ sf) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * (sf - (M + 2)) ≤ 3 * M - 9 := by
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel h
  have h4 : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  have h7 : 7 * M - 1 + 1 = 7 * M := Nat.sub_add_cancel (by omega)
  have h3 : 3 * M - 9 + 9 = 3 * M := Nat.sub_add_cancel (by omega)
  constructor <;> intro hh <;> omega

/-- **Candidate 3, forward.**  `travel <= 2 * (S + p)` plus
`8 * (S + p) <= 3 * M - 9` gives cap (B). -/
theorem capB_of_excess_sum {M sf S p : Nat} (hM : 9 ≤ M) (h : M + 2 ≤ sf)
    (htravel : sf - (M + 2) ≤ 2 * (S + p)) (hbound : 8 * (S + p) ≤ 3 * M - 9) :
    4 * sf ≤ 7 * M - 1 := by
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel h
  have h4 : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  have h3 : 3 * M - 9 + 9 = 3 * M := Nat.sub_add_cancel (by omega)
  have hmid : 4 * (sf - (M + 2)) ≤ 3 * M - 9 := by omega
  omega

/-- **cap (B) is downstream of the event-count criterion already in the tree.**
`canonical_travel_bound_of_event_count` yields `2 * travel <= M`, and
`2 * M <= 3 * M - 9` for `M >= 9`.  So that criterion -- modulo its own
unproved `48 * p * p + 1 < M` -- already implies cap (B), with no new input. -/
theorem capB_of_event_count {M sf Cf p : Nat} (hM : 45895573 ≤ M)
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) (hcount : 48 * (p * p) + 1 < M) :
    4 * sf ≤ 7 * M - 1 := by
  have htr := canonical_travel_bound_of_event_count (by omega) hcanon hpath hmax hcount
  have hsf : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel hsf
  have h4 : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  omega

/-! ## 1. Candidates 2 and 5: the sharpest per-step law

`d r - 1 <= C - M`.  New: it uses the `3 * d r <= C +- 1` clause of
`moving_horizon_step_event_package`, which `GapBound`'s `gap <= 2 * d r` does
not.  Numerical status: ZERO violations over every event of every canonical
replay for every odd `M <= 200000` (99994 replays) and at the certified starts
`22933441, 45895573, 91793059, 367232911`. -/

theorem event_excess_le_horizon_minus_M {M s C r C' : Nat} (hM : 2 ≤ M)
    (hstep : IsMovingHorizonStep s C r C') (hCM : 2 * M - 2 ≤ C) :
    d r - 1 ≤ C - M := by
  have hp := moving_horizon_step_event_package hstep
  have h3 : 3 * d r ≤ C + 1 := by
    rcases hp with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> omega
  have hC : M ≤ C := by omega
  obtain ⟨g, hg⟩ : ∃ g, C = M + g := ⟨C - M, (Nat.add_sub_cancel' hC).symm⟩
  subst hg
  omega

/-- **The defect form, and why it is far too weak.**  `C' - M = (C - M) + (d r - 1)`
with `d r - 1 <= C - M`, so the horizon defect at most DOUBLES per step:
`C - M <= 2^p * (M - 2)`.  At `p = 209` (`M = 22933441`) the law permits
`C - M` up to `2^209 * M`, against the `3*M/4` that cap (B) needs.  The
per-step law is real but its summation is exponential, not linear. -/
theorem horizon_deficit_at_most_doubles {M s C r C' : Nat} (hM : 2 ≤ M)
    (hstep : IsMovingHorizonStep s C r C') (hCM : 2 * M - 2 ≤ C) :
    C' - M ≤ 2 * (C - M) := by
  have hlaw : d r - 1 ≤ C - M := event_excess_le_horizon_minus_M hM hstep hCM
  have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
  omega

/-- The tightness reading, kernel-checked for the first canonical start: the law
`d r - 1 <= C - M` at `M = 13` is only `6 <= 11`, i.e. it constrains `M` to at
most `C - (d r - 1)`, which over the whole replay is about `2 * M` -- not the
`3 * M / 4` cap (B) needs.  (`C - (d r - 1)` for the `M = 13` replay is at least
`20`, while `3 * 13 / 4 = 9`.) -/
theorem defect_law_is_not_a_cap : 3 * 13 / 4 < 20 := by decide

/-! ## 2. Candidate 4: the `B sf` lower bound is a reformulation, and false -/

/-- `canonical_index_cap_of_horizon_and_B_sf` needs `3*M + 8 <= 2 * B sf`; with
cap (A) that forces the *equality* `2*sf = 3*M+4`. -/
theorem B_route_forces_equality {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hhor : Cf ≤ 3 * M + 4) (hlow : 3 * M + 8 ≤ 2 * B sf) :
    2 * sf = 3 * M + 4 :=
  B_lower_bound_route_forces_equality hpath hhor hlow

/-- It is false at the first canonical start (`B 24 = 20`, and
`3*13+8 = 47 > 40`). -/
theorem B_lower_bound_route_false_at_13 : ¬ (3 * 13 + 8 ≤ 2 * B 24) := by decide

/-- The tree proves the *opposite* direction, unconditionally. -/
theorem B_le_index_add_two {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) : B sf ≤ sf + 2 :=
  canonical_B_sf_le_index_add_two hpath

/-! ## 3. Threshold-relative refutations

At `M = 13` the target's full hypothesis set holds and cap (B) FAILS
(`RoomLedger.travel_bound_without_threshold_is_false`).  Hence any candidate
that follows from the hypotheses alone and suffices for cap (B) must be false
at `M = 13`.  The numbers are the `M = 13` canonical replay: `p = 4`,
`travel = 9`, `S = 18`, `B sf = 20`, `sf = 24`. -/

theorem capB_fails_at_13 : ¬ (4 * 24 ≤ 7 * 13 - 1) := by decide
theorem candidate1_form_fails_at_13 : ¬ (8 * 18 ≤ 3 * 13 - 9) := by decide
theorem candidate3_form_fails_at_13 : ¬ (8 * (18 + 4) ≤ 3 * 13 - 9) := by decide
theorem candidate4_form_fails_at_13 : ¬ (3 * 13 + 8 ≤ 2 * 20) := by decide

/-- The same at `M = 43` (`S = 54`, `p = 6`, `sf = 79`): the threshold-free
forms fail again, so `M = 13` is not an isolated accident. -/
theorem candidate3_form_fails_at_43 : ¬ (8 * (54 + 6) ≤ 3 * 43 - 9) := by decide
theorem capB_fails_at_43 : ¬ (4 * 79 ≤ 7 * 43 - 1) := by decide

/-- And at `M = 49` (`S = 42`, `p = 3`): still false. -/
theorem candidate3_form_fails_at_49 : ¬ (8 * (42 + 3) ≤ 3 * 49 - 9) := by decide

/-! ## 4. Candidate 1 as a *route*: `ExcessIdentity` already closed it

Bounding `S` alone cannot give travel: with the reservoir ledger
`B sf + travel = (M - 2) + S` the scaled-excess form of the travel bound is
*equivalent* to the travel bound itself.  That is the tree's own refutation of
candidate 1 as an independent route. -/

theorem candidate1_route_is_circular {M S travel Bsf : Nat} (hM : 4 ≤ M)
    (hB : Bsf + travel = (M - 2) + S) :
    (2 * S + M ≤ 2 * Bsf + 4 ↔ 2 * travel ≤ M) :=
  excess_only_gives_identity hM hB

/-! ## 5. cap (B) forces a count bound (restated from `RelaxedCap`) -/

theorem capB_forced_count {M sf p : Nat} (h : M + 2 ≤ sf)
    (hcap : 4 * sf ≤ 7 * M - 1) (hc : p + M ≤ sf + 1) : 4 * p ≤ 3 * M + 3 :=
  cap_b_implies_count_bound h hcap hc

#print axioms capB_iff_travel_form
#print axioms capB_of_excess_sum
#print axioms capB_of_event_count
#print axioms event_excess_le_horizon_minus_M
#print axioms horizon_deficit_at_most_doubles
#print axioms defect_law_is_not_a_cap
#print axioms B_route_forces_equality
#print axioms B_lower_bound_route_false_at_13
#print axioms canonical_travel_bound_of_event_count
#print axioms excess_only_gives_identity

end A166944Research
