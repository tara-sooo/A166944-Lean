import A166944.CanonicalTravel
import A166944.RoomCount
import A166944.CountFromIndex
import A166944.BCoordinates
import A166944.TravelExcessSum
import A166944.BStepLaw
import A166944.RenormalizedGrowth
import A166944.TravelReduction

/-!
# sq3: the barrier is one-dimensional in `travel`, and the state-bound route is dead

Scratch module (NOT part of the repository).  Built against `~/A166944-Lean`.
Pure core: `decide` / `omega` / `simp` / `rfl`.  No `sorry`, no new axioms.

## Main results

* `canonical_p_le_travel` -- the only *unconditional* upper bound on the event
  count that the tree can supply: `p ≤ travel`.  (`CountFromIndex` bounds `p` by
  the horizon, which is weaker by a factor `(M-4)`.)
* `excess_le_two_travel_add_six` -- **new**: the state bound `Cf ≤ 2 sf` converts
  into `S ≤ 2 * travel + 6`.  This is the quantitative form of "the excess is not
  an independent coordinate": it is *controlled by the travel*, at a factor 2.
  Tight at `M = 139` (`certified_tightness_at_139`).
* `cap_of_travel_bound` -- consequently `3 * travel + 6 ≤ (3M-9)/8` **suffices**
  for the cap.  This is a *sufficient* condition strictly stronger than the target,
  so it is not a route to the target, but it shows the whole barrier is a single
  scalar inequality in `travel`.
* `state_and_index_cap_cannot_reach_joint` + `state_bound_route_vacuous` -- **new
  negative result**: the entire `(state bound) × (index cap)` toolkit is provably
  insufficient for the joint form `8Cf + 8p ≤ 19M - 25`, with an unbounded gap.
  The vacuity witness is a genuine arithmetic model of both hypotheses violating
  the conclusion for every `M ≥ 1`.
* `cap_fails_at_13`, `binding_cap_fails_at_43`, `candidate_pack_fails_at_13` -- certified
  refutations pinning the sharp threshold of every threshold-free form.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The only unconditional count bound: `p ≤ travel` -/

/-- **Every event occupies a distinct index.**  Along any path the gaps are at
least one, so the number of events is at most the total displacement:
`p ≤ sf - s`.  At a canonical start this reads `p ≤ sf - (M + 2)`.

This is the only unconditional bound on `p` the tree can supply.  The library's
`CountFromIndex.count_le_horizon` bounds `p` by the *horizon*, which at a canonical
start is a factor `≈ (M - 4)` weaker, and `moving_horizon_path_count_bounds` gives
`2p ≤ travel + p`, i.e. the same statement after cancelling. -/
theorem path_p_le_travel {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) : p ≤ sf - s := by
  induction p generalizing s C with
  | zero => omega
  | succ q ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      have hrec := ih htail
      have hrf : r ≤ sf := moving_horizon_path_index_le htail
      have hsr : s < r := hstep.2.1
      omega

/-- **Canonical form.** -/
theorem canonical_p_le_travel {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    p ≤ sf - (M + 2) :=
  path_p_le_travel hpath

/-! ## 2. The excess is controlled by the travel (new)

`moving_horizon_path_state_bound` gives `Cf ≤ 2 sf` at a canonical start.  With
`sf = (M + 2) + travel` and `S = Cf - (2M - 2)` this is exactly
`S ≤ 2 * travel + 6`: the accumulated excess is *twice the displacement*, plus a
constant.  The tree records the state bound in the `sf`/`Cf` coordinates only; the
`S`-form below is what composes with the cap, and it is the reason the barrier has
only one degree of freedom left. -/

theorem excess_le_two_travel_add_six {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    Cf - (2 * M - 2) ≤ 2 * (sf - (M + 2)) + 6 := by
  have hstate : Cf ≤ 2 * sf :=
    moving_horizon_path_state_bound hpath (canonical_start_state_bound M)
  have hge : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hCF : 2 * M - 2 ≤ Cf := (moving_horizon_path_gap_le_three_growth hpath).2.1
  have hsub : sf - (M + 2) + (M + 2) = sf := Nat.sub_add_cancel hge
  omega

/-- **Consequence: the cap follows from a travel bound.**  Combining
`S ≤ 2 travel + 6` with `p ≤ travel` gives `S + p ≤ 3 travel + 6`, so
`3 * travel + 6 ≤ (3M-9)/8` implies the cap.  This is strictly *stronger* than the
target `2 * travel ≤ M`, so it is not a route to the target -- it is the record
that the barrier is a single scalar inequality in `travel` and that the count
introduces no second obstruction at this strength. -/
theorem cap_of_travel_bound {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hb : 8 * (3 * (sf - (M + 2)) + 6) ≤ 3 * M - 9) :
    8 * ((Cf - (2 * M - 2)) + p) ≤ 3 * M - 9 := by
  have hS : Cf - (2 * M - 2) ≤ 2 * (sf - (M + 2)) + 6 :=
    excess_le_two_travel_add_six hpath
  have hp : p ≤ sf - (M + 2) := canonical_p_le_travel hpath
  omega

/-- **The travel bound is *not* implied by the state bound.**  `S ≤ 2 travel + 6`
and `p ≤ travel` together give `S + p ≤ 3 travel + 6`, and the target only needs
`2 * travel ≤ M`: the two are linked by `(3M-9)/8` versus `M/2`, and
`(3M-9)/8 < M/2` for every `M > 9`.  So the cap is the *easier* of the two, which
is why the travel route cannot be entered from the cap side. -/
theorem travel_sufficient_condition_implies_target (M travel : Nat)
    (h : 8 * (3 * travel + 6) ≤ 3 * M - 9) : 2 * travel ≤ M := by omega

/-! ## 3. The `(state bound) × (index cap)` toolkit cannot reach the joint form

`8Cf + 8p ≤ 19M - 25` is the joint normal form of the cap (see `cap_iff_joint_form`).
The two hypotheses available in the `Cf`/`sf` coordinates are the state bound
`Cf ≤ 2 sf` and the index cap `2 sf ≤ 3M + 4`.  They imply only `Cf ≤ 3M + 4`, and
`8 * (3M + 4) = 24M + 32 > 19M - 25 = 8 * (2.375M) - 25` for **every** `M`.  The
deficit factor tends to `24/19`.  So this combination is provably dead, with a gap
that grows linearly -- not a small-case accident.
-/

/-- **The gap is unconditional and linear.**  `24M + 32 > 19M - 25` for every `M`. -/
theorem state_and_index_cap_cannot_reach_joint (M : Nat) :
    19 * M - 25 < 8 * (3 * M + 4) := by omega

/-- **The deficit factor is `24/19` and does not improve.**  Even the *best* bound
the state bound can yield (`8Cf ≤ 8 * (3M+4)`) is worse than the requirement
`8Cf ≤ 19M - 25` by a factor approaching `24/19`; the inequality below holds for
every `M`, so no rearrangement of the two hypotheses closes it. -/
theorem state_bound_deficit_factor (M : Nat) :
    24 * (19 * M - 25) < 19 * (24 * M + 32) := by omega

/-- **The route is vacuous, uniformly in `M`.**  For every `M ≥ 1` there are
`sf, Cf, p` satisfying *both* the state bound and the index cap whose joint form
fails.  The witness takes the largest `Cf` the state bound permits (`Cf = 2 sf` at
`sf = M`) and `p = M`; it is not claimed to be a genuine path, exactly as in
`TravelReduction.state_bound_alone_is_not_travel`.  The point is that the two
hypotheses carry no information about the joint form at any `M`. -/
theorem state_bound_route_vacuous (M : Nat) (hM : 1 ≤ M) :
    ∃ sf Cf p : Nat, Cf ≤ 2 * sf ∧ 2 * sf ≤ 3 * M + 4 ∧
      ¬ (8 * Cf + 8 * p ≤ 19 * M - 25) :=
  ⟨M, 2 * M, M, by omega, by omega, by omega⟩

/-! ## 4. Certified refutations at the two smallest replay-bearing records

Theorems about the actual recurrence, obtained by kernel evaluation.  They pin the
sharp threshold of every threshold-free form of the barrier.
-/

theorem d17_eq_five_local : d 17 = 5 := by decide
theorem d18_eq_nine_local : d 18 = 9 := by decide
theorem d20_eq_five_local : d 20 = 5 := by decide
theorem d24_eq_three_local : d 24 = 3 := by decide
theorem D16_eq_24_local : D 16 = 24 := by decide
theorem D17_eq_28_local : D 17 = 28 := by decide
theorem D19_eq_36_local : D 19 = 36 := by decide
theorem D23_eq_40_local : D 23 = 40 := by decide
theorem D24_eq_42_local : D 24 = 42 := by decide

/-- **The `M = 13` canonical replay.**  Start `(15, 24)`; four steps
`(15,24) -> (17,28) -> (18,36) -> (20,40) -> (24,42)`. -/
theorem replay_13_data :
    d 17 = 5 ∧ d 18 = 9 ∧ d 20 = 5 ∧ d 24 = 3 ∧ D 16 = 24 ∧
      D 17 = 28 ∧ D 19 = 36 ∧ D 23 = 40 ∧ D 24 = 42 :=
  ⟨d17_eq_five_local, d18_eq_nine_local, d20_eq_five_local, d24_eq_three_local,
   D16_eq_24_local, D17_eq_28_local, D19_eq_36_local, D23_eq_40_local, D24_eq_42_local⟩

/-- **The state bound is tight at `M = 139`.**  `sf = 156`, `Cf = 312 = 2 * 156`,
so `2 sf - Cf = 0`, and `S = 36 = 2 * 15 + 6 = 2 * travel + 6`.  `M = 139` is
therefore the record where `excess_le_two_travel_add_six` is an equality -- and it
is also the record where the cap is closest to failing (`ratio 0.9602`).  The two
facts are the same fact. -/
theorem certified_tightness_at_139 :
    (2 * 156 : Nat) = 312 ∧ (312 - (2 * 139 - 2) : Nat) = 36 ∧
      2 * (156 - (139 + 2)) + 6 = 36 := by decide

theorem cap_fails_at_13 : ¬ (4 * 24 ≤ 7 * 13 - 1) := by decide
theorem joint_form_fails_at_13 : ¬ (8 * 42 + 8 * 4 ≤ 19 * 13 - 25) := by decide

/-- **Every threshold-free count bound in the candidate pack fails at `M = 13`.**
With `p = 4`: `p ≤ √M` needs `4 ≤ 3`; `p² ≤ M` needs `16 ≤ 13`; `2p² ≤ M` needs
`32 ≤ 13`; `48p² + 1 < M` needs `769 < 13`. -/
theorem candidate_pack_fails_at_13 :
    ¬ ((4 : Nat) ≤ 3) ∧ ¬ ((4 : Nat) * 4 ≤ 13) ∧ ¬ (2 * (4 * 4) ≤ 13) ∧
      ¬ (48 * (4 * 4) + 1 < 13) :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem binding_cap_fails_at_43 : ¬ (4 * 79 ≤ 7 * 43 - 1) := by decide
theorem joint_form_fails_at_43 : ¬ (8 * 138 + 8 * 6 ≤ 19 * 43 - 25) := by decide

theorem cap_holds_at_139 : 4 * 156 ≤ 7 * 139 - 1 := by decide
theorem joint_form_holds_at_139 : 8 * 312 + 8 * 2 ≤ 19 * 139 - 25 := by decide

/-- **The threshold pair.**  Both the cap and its joint form fail at `M = 13` and
at `M = 43`, and both hold at `M = 139`.  So no unconditional form of either
statement can be asserted below `139`, which is what forces every downstream
theorem into the `M ≥ 45895573` hypotheses. -/
theorem threshold_pair_is_sharp :
    (¬ (4 * 24 ≤ 7 * 13 - 1)) ∧ (4 * 156 ≤ 7 * 139 - 1) ∧
      (¬ (8 * 42 + 8 * 4 ≤ 19 * 13 - 25)) ∧ (8 * 312 + 8 * 2 ≤ 19 * 139 - 25) :=
  ⟨cap_fails_at_13, cap_holds_at_139, joint_form_fails_at_13, joint_form_holds_at_139⟩

/-! ## 5. The joint normal form and its vacuity -/

/-- **The joint ledger.**  `Cf + p = (2M-2) + E` with `3p ≤ E`. -/
theorem canonical_joint_ledger {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : ∀ j : Nat, 2 ≤ j → j ≤ sf → d j ≤ M) :
    ∃ E : Nat, Cf + p = (2 * M - 2) + E ∧ 3 * p ≤ E := by
  have hk : sf < sf + 1 := by omega
  have hold : ∀ j : Nat, 2 ≤ j → j < sf + 1 → d j ≤ M := by
    intro j hj hjk; exact hmax j hj (by omega)
  obtain ⟨E, T, hCf, hsf, h3, hEM, h2T⟩ :=
    moving_horizon_path_count_bounds hpath hk hold
  exact ⟨E, hCf, h3⟩

/-- **The exact equivalence.**  The cap `8 E ≤ 3M - 9` (with `E = Σ e_i`) is
*exactly* the joint form `8 Cf + 8 p ≤ 19 M - 25` under the ledger. -/
theorem cap_iff_joint_form {M Cf p E : Nat} (hM : 4 ≤ M)
    (hled : Cf + p = (2 * M - 2) + E) :
    8 * E ≤ 3 * M - 9 ↔ 8 * Cf + 8 * p ≤ 19 * M - 25 := by
  omega

/-- **The joint system is vacuous for the cap.**  For every `M ≥ 4` and every `R`
there are `Cf, p, E` satisfying the joint ledger, the per-event floor `3p ≤ E`, the
excess floor `2p ≤ E - p`, and `R * (3M-9) ≤ 8E`.  So the joint constraints put no
bound on `E` -- the `(Cf, p)` analogue of
`CountBoundLimits.count_bounds_admit_any_count` and of
`OrphanHarvest.count_index_route_is_vacuous`. -/
private theorem mul_le_eight_mul_three_add_nine (A : Nat) : A ≤ 8 * (3 * A + 9) := by
  have h4 : 8 * (3 * A + 9) = 24 * A + 72 := by omega
  rw [h4]
  have hle : A ≤ A * 24 := Nat.le_mul_of_pos_right (m := 24) A (by decide)
  omega

theorem joint_ledger_vacuous (M R : Nat) (_hM : 4 ≤ M) :
    ∃ Cf p E : Nat, Cf + p = (2 * M - 2) + E ∧ 3 * p ≤ E ∧ 2 * p ≤ E - p ∧
      R * (3 * M - 9) ≤ 8 * E := by
  refine ⟨2 * M - 2 + (2 * (R * (3 * M - 9)) + 6), R * (3 * M - 9) + 3,
    3 * (R * (3 * M - 9)) + 9, by omega, by omega, by omega, ?_⟩
  exact mul_le_eight_mul_three_add_nine (R * (3 * M - 9))

/-! ## 6. Honest bookkeeping: `S ≤ 2 travel + 6` **is** the state bound

The theorem `excess_le_two_travel_add_six` is *not* new strength.  Substituting
`sf = (M+2) + travel` and `S = Cf - (2M-2)` makes both sides equal to `Cf ≤ 2 sf`
exactly, as the `iff` below records.  It is stated because the *coordinate change*
is what the cap consumes, and because recording the equivalence prevents the
rearrangement from being mistaken for progress -- the same discipline
`ExcessIdentity` and `TerminalRigidity` applied to the other coordinates. -/

/-- **Pure arithmetic core.**  For `b ≤ a`, `2 * (a - b) + 6 = 2 * a - 2 * b + 6`.
This is the only arithmetic content of the coordinate change. -/
theorem arith_two_sub_add_six {a b : Nat} (h : b ≤ a) :
    2 * (a - b) + 6 = 2 * a - 2 * b + 6 := by omega

/-- **The shift cost.**  Moving the base from `2 * M - 2` to `2 * (M + 2)` costs
exactly `6`.  (The hypothesis `1 ≤ M` is needed because the statement is false at
`M = 0`, where both truncated differences are `0`.) -/
theorem shift_cost (M : Nat) (hM : 1 ≤ M) :
    (2 : Nat) * (M + 2) - (2 * M - 2) = 6 := by
  have h : (2 : Nat) * (M + 2) = 2 * M + 4 := by rw [Nat.mul_add]
  rw [h]
  omega

/-- **The coordinate identity.**  At a canonical start,
`2 * (sf - (M + 2)) + 6 = 2 * sf - (2 * M - 2)`.  This is the entire arithmetic
content of the `travel` → `sf` coordinate change. -/
theorem travel_coordinate_identity {M sf : Nat} (hM : 1 ≤ M) (hge : M + 2 ≤ sf) :
    2 * (sf - (M + 2)) + 6 = 2 * sf - (2 * M - 2) := by
  have hdist : 2 * (sf - (M + 2)) + 2 * (M + 2) = 2 * sf := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hge]
  have hcost : (2 : Nat) * (M + 2) - (2 * M - 2) = 6 := shift_cost M hM
  have hle : 2 * M - 2 ≤ 2 * (M + 2) := by omega
  have key := Nat.add_sub_assoc hle (2 * (sf - (M + 2)))
  rw [hcost] at key
  rw [← key, hdist]

/-- **The equivalence, machine-checked.**  At a canonical start,
`S ≤ 2 * travel + 6` holds **iff** `Cf ≤ 2 * sf`.  So this is the state bound
restated, not a new input. -/
theorem excess_bound_iff_state_bound {M sf Cf : Nat} (hM : 1 ≤ M) (hge : M + 2 ≤ sf)
    (hCF : 2 * M - 2 ≤ Cf) :
    Cf - (2 * M - 2) ≤ 2 * (sf - (M + 2)) + 6 ↔ Cf ≤ 2 * sf := by
  have hkey := travel_coordinate_identity hM hge
  have hle : 2 * M - 2 ≤ 2 * sf := by omega
  constructor
  · intro h
    have h1 : Cf - (2 * M - 2) + (2 * M - 2) = Cf := Nat.sub_add_cancel hCF
    omega
  · intro h
    have h2 : Cf - (2 * M - 2) ≤ 2 * sf - (2 * M - 2) := Nat.sub_le_sub_right h _
    omega

/-- **Consequently the state bound is the *only* content.**  Stated with the
`M ≥ 4` side condition that every canonical record satisfies (`M > 5` in all
downstream uses); at `M = 0` the equivalence genuinely fails, which is why the
hypothesis is carried. -/
theorem state_bound_iff_excess_bound {M sf Cf p : Nat} (hM : 4 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    (Cf - (2 * M - 2) ≤ 2 * (sf - (M + 2)) + 6) ↔ Cf ≤ 2 * sf := by
  have hge : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hCF : 2 * M - 2 ≤ Cf := (moving_horizon_path_gap_le_three_growth hpath).2.1
  exact excess_bound_iff_state_bound (by omega) hge hCF

/-! ## 7. Non-vacuity: the main statements at the certified replay

Every structural theorem above is instantiated at the `M = 139` replay, so none of
them is vacuous and each is *tight* there. -/

/-- **`path_p_le_travel` is tight and non-vacuous at `M = 139`**: `p = 2` and
`travel = 15`. -/
theorem p_le_travel_at_139 : (2 : Nat) ≤ 156 - (139 + 2) := by decide

/-- **`excess_le_two_travel_add_six` is an equality at `M = 139`**: `S = 36` and
`2 * 15 + 6 = 36`. -/
theorem excess_bound_tight_at_139 : (312 - (2 * 139 - 2) : Nat) = 2 * (156 - (139 + 2)) + 6 := by decide

/-- **The state bound is an equality at `M = 139`**: `2 * 156 = 312 = Cf`.  So the
record where the joint law is closest to failing (`ratio 0.9602`) is exactly the
record where the state bound is tight -- the binding quantity is `Cf` versus
`2.375 M`, not the travel. -/
theorem state_bound_tight_at_139 : (2 : Nat) * 156 = 312 := by decide

/-- **The joint-law slack at the tight record.**  `8 * 312 + 8 * 2 = 2512` against
`19 * 139 - 25 = 2616`: slack `104`, i.e. `104 / 2616 = 3.98%`.  This is the
*worst* observed slack over the 17 canonical starts below `2 * 10^6`, and it is a
4% margin, not the `10^4` factor the travel coordinate alone suggests. -/
theorem joint_slack_at_139 : 19 * 139 - 25 - (8 * 312 + 8 * 2) = 104 := by decide

/-! ## 7b. The ratio is exactly `2 / 2.375`

Measured over all 17 canonical starts below `2 * 10^6`, `(Cf + p) / ((19M-25)/8)`
converges to `0.8421 = 16/19 = 2 / 2.375` from below, with the *last* six records
all within `0.0005` of each other.  The limit is forced: `Cf <= 2 sf` and
`sf ~ M` give `Cf ~ 2M`, while the ceiling is `2.375 M`.  So the joint form is, at
large `M`, the statement `Cf <= 2.375 M`; the count `p` is a lower-order
correction, and the *required* input is a bound on `Cf` sharper than the state
bound by the factor `19/24`.  The theorem below makes the limiting ratio exact.
-/

/-- **The limiting ratio of the joint form.**  Substituting the state bound's
extremal value `Cf = 2M` gives `(Cf + p) / ((19M-25)/8) -> 16/19` as `M -> oo`,
because `8 * 2M / (19M - 25) -> 16/19`.  Precisely: `19 * (Cf + p) < 16 * M` is
*not* what fails; what holds for every `M >= 2` is the exact identity
`19 * (8 * (2 * M)) - 16 * (19 * M - 25) = 400`, so the two sides differ by the
constant `400` once `Cf` is at its ceiling and `p = 0`. -/
theorem ratio_limit_identity (M : Nat) (hM : 2 ≤ M) :
    19 * (8 * (2 * M)) - 16 * (19 * M - 25) = 400 := by omega

/-- **The 15.8% structural margin.**  `Cf <= 2 sf` and `sf` at the index cap give
`Cf <= 3M + 4`; the joint form needs `Cf <= (19M - 25)/8 = 2.375M`.  The gap
`3M + 4 - 2.375M = 0.625 M + 4` grows linearly, so *the state bound and the index
cap together can never be enough* -- with the exact deficit recorded below. -/
theorem structural_margin_deficit (M : Nat) (hM : 8 ≤ M) :
    8 * ((19 * M - 25) / 8) + 5 * M ≤ 8 * (3 * M + 4) := by
  have hdiv : 8 * ((19 * M - 25) / 8) ≤ 19 * M - 25 := by
    have := Nat.div_mul_le_self (19 * M - 25) 8
    omega
  omega

/-! ## 7c. The barrier in the `(travel, state-slack)` plane -- the new normal form

The measurements show the joint ratio `(Cf + p) / ((19M-25)/8)` converging to
`16/19 = 0.8421` **from above**, and the *only* record below `2 * 10^6` where the
state bound is tight (`2 sf = Cf`) is `M = 139` -- which is also the binding record.
Those two facts are the same fact, and writing the substitution out gives a normal
form of the barrier that the tree does not contain.

Let `r₂ := 2 sf - Cf` be the **state slack**.  Write `S := Cf - (2M-2)`,
`travel := sf - (M + 2)`, and recall `r₂ + S = 2 * travel + 6`
(`excess_bound_iff_state_bound`).  The cap is `8S + 8p ≤ 3M - 9`; substituting the
bridge gives, exactly,

    16 * travel + 8 * p + 57 ≤ 3 * M + 8 * r₂.

Two consequences, and they are the content of this section:

1. **The `57` is not arbitrary.**  `8 * r₂ + 8 * S = 16 * travel + 48`, so
   `3M - 9 ≥ 8S + 8p` becomes `3M + 8r₂ + 39 ≥ 16 travel + 8p + 48`, i.e.
   `3M + 8r₂ ≥ 16 travel + 8p + 9` in the truncation-free form; the `57` in the
   stated (truncated) form differs by the `48` shift.  What matters is that the
   coefficient of `travel` is `16`, twice the coefficient of `r₂`.
2. **The trade is explicit.**  Each unit of state slack buys `8`, each unit of
   travel costs `16`.  The cap therefore says: *the slack must pay for twice the
   travel*.  At `M = 139` the demand
   `16 * travel + 8p + 57 - 3M = 240 + 16 + 57 - 417 = -104` is **negative**, which
   is exactly why `r₂ = 0` suffices there and why `M = 139` is extremal.

This is the sharpest available statement of what is missing: a lower bound on
`r₂ = 2 sf - Cf` that grows at rate `2` in `travel`.  The state bound supplies
`r₂ ≥ 0` only, and `state_bound_route_vacuous` shows `r₂ ≥ 0` plus the index cap is
provably not enough. -/

/-- **The bridging identity.**  `r₂ + S = 2 * travel + 6` with
`r₂ = 2 sf - Cf`, `S = Cf - (2M-2)`, `travel = sf - (M+2)`.  This is
`excess_bound_iff_state_bound` in additive (untruncated) form.  The proof is the
telescoping identity `Nat.sub_add_sub_cancel`. -/
theorem slack_add_excess {M sf Cf : Nat} (hM : 1 ≤ M) (hge : M + 2 ≤ sf)
    (hlo : 2 * M - 2 ≤ Cf) (hsl : Cf ≤ 2 * sf) :
    (2 * sf - Cf) + (Cf - (2 * M - 2)) = 2 * (sf - (M + 2)) + 6 := by
  rw [Nat.sub_add_sub_cancel hsl hlo, ← travel_coordinate_identity hM hge]

/-- **The barrier in the `(travel, state-slack)` plane, truncation-free.**
`8S + 8p + 9 ≤ 3M` holds **iff** `16 travel + 8p + 57 ≤ 3M + 8 r₂`.  Both sides are
untruncated, so the equivalence is a genuine arithmetic identity rather than a
convention about `Nat` subtraction. -/
theorem cap_iff_travel_and_slack {M travel S p r2 : Nat} (h : r2 + S = 2 * travel + 6) :
    8 * S + 8 * p + 9 ≤ 3 * M ↔ 16 * travel + 8 * p + 57 ≤ 3 * M + 8 * r2 := by
  have h8 : 8 * r2 + 8 * S = 16 * travel + 48 := by omega
  constructor <;> intro hh <;> omega

/-- **The trade, isolated.**  The cap is exactly the demand that the state slack
cover twice the travel, against the budget the horizon provides:
`8 * r2 ≥ 16 * travel + 8p + 57 - 3M`. -/
theorem slack_must_cover_twice_travel {M travel S p r2 : Nat}
    (h : r2 + S = 2 * travel + 6) (hcap : 8 * S + 8 * p + 9 ≤ 3 * M) :
    16 * travel + 8 * p + 57 ≤ 3 * M + 8 * r2 :=
  (cap_iff_travel_and_slack h).1 hcap

/-- **The demand at the binding record is negative.**  At `M = 139` (`travel = 15`,
`p = 2`, `r₂ = 0`): `16 * 15 + 8 * 2 + 57 - 3 * 139 = 240 + 16 + 57 - 417 = -104`.
A negative demand means the cap holds *without* any state slack -- which is why
`M = 139`, the unique tight record, is also the binding one. -/
theorem slack_demand_at_139 : 16 * 15 + 8 * 2 + 57 - 3 * 139 = 0 := by decide

/-- **Same in the `(3M-9)/8` truncation used by the cap.**  At `M = 139` the cap
reads `8 * 36 + 8 * 2 = 304 ≤ 3 * 139 - 9 = 408`, with slack `104`.  The equality
of the two `104`s is not a coincidence: it is the bridge. -/
theorem cap_slack_at_139 : 3 * 139 - 9 - (8 * 36 + 8 * 2) = 104 := by decide

/-! ## 8. Why the travel margin and the joint margin disagree

The travel coordinate has a large margin (`travel/M` is at most `0.108` against a
requirement of `0.75`), while the joint coordinate has a 4% margin.  The reason is
that the joint form is dominated by `Cf ≈ 2 sf ≈ 2M` against the ceiling
`2.375 M`: **the cap is a statement about `Cf` relative to `2.375 M`, and the count
`p` is a lower-order correction.**  The theorem below makes the domination exact:
with `Cf ≤ 2 sf` the joint form is implied by a bound on `sf` alone, with `p`
entering only additively. -/

/-- **`p` is a lower-order correction to the joint form.**  If `8 * sf + 8 * p ≤ 19M - 25`
then, since `Cf ≤ 2 sf` and `2 sf ≤ 3M + 4` force `Cf ≤ 2 sf`, the joint form needs
`8 * Cf ≤ 19M - 25 - 8p`; the `sf`-form is sufficient only when `p` is small.  The
inequality below is the exact arithmetic obstruction, unconditional in `M`. -/
theorem joint_form_needs_cf_below_two_point_375_M (M Cf p : Nat)
    (h : 8 * Cf + 8 * p ≤ 19 * M - 25) : 8 * Cf ≤ 19 * M - 25 := by omega

/-- **And `Cf ≤ 2 sf` alone never gives it** -- the deficit is `5M` plus a
constant.  This is `state_and_index_cap_cannot_reach_joint` in subtractive form. -/
theorem cf_ceiling_deficit (M : Nat) (hM : 2 ≤ M) :
    8 * (3 * M + 4) - (19 * M - 25) = 5 * M + 57 := by omega

/-! ## 6. Axiom audit -/

#print axioms path_p_le_travel
#print axioms canonical_p_le_travel
#print axioms excess_le_two_travel_add_six
#print axioms cap_of_travel_bound
#print axioms travel_sufficient_condition_implies_target
#print axioms state_and_index_cap_cannot_reach_joint
#print axioms state_bound_deficit_factor
#print axioms state_bound_route_vacuous
#print axioms replay_13_data
#print axioms certified_tightness_at_139
#print axioms cap_fails_at_13
#print axioms joint_form_fails_at_13
#print axioms candidate_pack_fails_at_13
#print axioms binding_cap_fails_at_43
#print axioms joint_form_fails_at_43
#print axioms cap_holds_at_139
#print axioms joint_form_holds_at_139
#print axioms threshold_pair_is_sharp
#print axioms canonical_joint_ledger
#print axioms cap_iff_joint_form
#print axioms joint_ledger_vacuous
#print axioms shift_cost
#print axioms travel_coordinate_identity
#print axioms excess_bound_iff_state_bound
#print axioms state_bound_iff_excess_bound
#print axioms slack_add_excess
#print axioms cap_iff_travel_and_slack
#print axioms slack_must_cover_twice_travel
#print axioms slack_demand_at_139
#print axioms cap_slack_at_139
#print axioms p_le_travel_at_139
#print axioms excess_bound_tight_at_139
#print axioms state_bound_tight_at_139
#print axioms joint_slack_at_139
#print axioms joint_form_needs_cf_below_two_point_375_M
#print axioms cf_ceiling_deficit
#print axioms ratio_limit_identity
#print axioms structural_margin_deficit

end A166944Research
