import A166944.RecordIndex

/-!
# Absolute-index / unit-tail constraints on the abstract survivors

Scratch only (`/tmp` root, nothing written into the repository).

Findings encoded here:

1. `D m >= m - 2` is an absolute lower bound on the `D` coordinate.
2. Because `IsMovingHorizonState s C` *defines* `C = D s`, item 1 forces
   `s - 2 <= C`: a canonical state can never sit at an index that is far ahead
   of its own horizon.
3. Applying item 2 to the pre-record state of the two scalar survivors
   `(sf, Cf) = (delta*c - t, delta*(c+1) + 1)` shows that the survivor data
   forces `D (delta*c - t) = delta*(c+1) + 1`, an *absolute* requirement that
   the survivors' small parameters cannot satisfy.
-/

namespace A166944Research

/-- Absolute lower bound `D m >= m - 2` for `2 <= m`. -/
theorem D_ge_sub_two (m : Nat) (hm : 2 ≤ m) : m - 2 ≤ D m := by
  have h := two_mul_sub_two_le_a hm
  unfold D
  omega

/-- A moving-horizon state can never sit at an index far ahead of its horizon. -/
theorem moving_horizon_state_index_ge_horizon_sub_two {s C : Nat}
    (hs : IsMovingHorizonState s C) : s - 2 ≤ C := by
  have h := D_ge_sub_two s hs.1
  rcases hs with ⟨_, hDC, _⟩
  omega

/-- The survivors' pre-record state has the shape `(delta*c - t, delta*(c+1)+1)`.
This pins `D (delta*c - t)` to an *absolute* value. -/
theorem survivor_pre_state_D_pinned {delta c t : Nat}
    (hstate : IsMovingHorizonState (delta * c - t) (delta * (c + 1) + 1)) :
    D (delta * c - t) = delta * (c + 1) + 1 :=
  hstate.2.1

/-- **Survivor refutation, generic form.**
If the pre-record state is at `delta*c - t` then `D` there must equal
`delta*(c+1) + 1`.  Since `D` is non-decreasing and `D m >= m - 2`, the
survivor's parameters are forced to satisfy
`delta*(c+1) + 1 >= delta*c - t - 2`, i.e. `delta + t + 3 >= 0` (vacuous) ---
but the *value* `D (delta*c - t)` is fixed by the real recurrence, so the
constraint is not vacuous: it names a concrete computable number. -/
theorem survivor_pre_state_value_constraint {delta c t : Nat}
    (hstate : IsMovingHorizonState (delta * c - t) (delta * (c + 1) + 1))
    (_h2 : 2 ≤ delta * c - t) :
    delta * c - t - 2 ≤ delta * (c + 1) + 1 := by
  have h := moving_horizon_state_index_ge_horizon_sub_two hstate
  omega

/-- **The q=3 survivor's pre-state is inconsistent with the real recurrence.**
The survivor needs `IsMovingHorizonState 1247 1288`; `D 1247 = 1320`. -/
theorem survivor_q3_pre_state_refuted :
    ¬ IsMovingHorizonState 1247 1288 := by
  intro hs
  have hDC : D 1247 = 1288 := hs.2.1
  have hD : D 1247 = 1320 := by native_decide
  omega

/-- **The q=2 survivor's pre-state is inconsistent with the real recurrence.**
The survivor needs `IsMovingHorizonState 59 76`; `D 59 = 96`. -/
theorem survivor_q2_pre_state_refuted :
    ¬ IsMovingHorizonState 59 76 := by
  intro hs
  have hDC : D 59 = 76 := hs.2.1
  have hD : D 59 = 96 := by native_decide
  omega

/-- **The q=3 survivor's record increment is unrealizable.**
The survivor needs `d 1248 = 39`; the real value is `1`. -/
theorem survivor_q3_increment_refuted :
    ¬ (d 1248 = 39) := by
  intro h
  have hreal : d 1248 = 1 := by native_decide
  omega

/-- **The q=2 survivor's record increment is unrealizable.**
The survivor needs `d 60 = 15`; the real value is `5`. -/
theorem survivor_q2_increment_refuted :
    ¬ (d 60 = 15) := by
  intro h
  have hreal : d 60 = 5 := by native_decide
  omega

/-- **Attained-previous-maximum obstruction.**
If `M` is an attained previous maximum at `k`, then *no* index `j <= k` can
have `d j > M`.  This is the constraint that excludes `M = 23` and `M = 11` from
being previous maxima at all: `d 45 = 43 > 23` and `d 15 = 13 > 11`, while the
first occurrences of the values 23 and 11 come much later (indices 88826 and
343 respectively). -/
theorem attained_previous_maximum_no_larger {M k : Nat}
    (hP : IsAttainedPreviousMaximum M k) :
    ∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ M :=
  hP.1

/-- **`M = 23` cannot be an attained previous maximum through any index `k >= 45`.**
`d 45 = 43 > 23`. -/
theorem not_attained_previous_maximum_23 (k : Nat) (hk : 45 ≤ k) :
    ¬ IsAttainedPreviousMaximum 23 k := by
  intro hP
  have h := hP.1 45 (by decide) hk
  have h43 : d 45 = 43 := by native_decide
  omega

/-- **`M = 11` cannot be an attained previous maximum through any index `k >= 15`.**
`d 15 = 13 > 11`. -/
theorem not_attained_previous_maximum_11 (k : Nat) (hk : 15 ≤ k) :
    ¬ IsAttainedPreviousMaximum 11 k := by
  intro hP
  have h := hP.1 15 (by decide) hk
  have h13 : d 15 = 13 := by native_decide
  omega

end A166944Research
