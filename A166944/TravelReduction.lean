import A166944.RenormalizedGrowth
import A166944.FirstHitArithmetic

/-!
# What the travel hypothesis actually is

The travel conclusion `2 * (sf - (M + 2)) <= M` at a canonical start is, under
`M + 2 <= sf`, *exactly* the index cap `2 * sf <= 3 * M + 4` -- it never mentions
`Cf` at all. So `travel_of_index_cap` shows the whole content is one global
bound on the terminal index.

Two consequences worth recording:

* The state bound `Cf <= 2 * sf` is available at every canonical start
  unconditionally (`canonical_start_state_bound` needs no hypothesis on `M`), but
  it cannot deliver travel: `state_bound_alone_is_not_travel` exhibits arithmetic
  data satisfying the invariant while violating the conclusion. The invariant
  says nothing about `sf`.
* The finite bridges in `Verified*.lean` establish the cap only at single points
  (`M = 45895573` and successors); between and beyond them the cap is assumed
  (`ResidualCrossingBudgetCondition210`). That gap is the real obstruction.
-/

namespace A166944Research

/-- At a canonical start `s = M + 2`, `C = 2 * M - 2` the state bound
`C ≤ 2 * s` is unconditional: it holds for every `M`, with no lower bound. -/
theorem canonical_start_state_bound (M : Nat) : 2 * M - 2 ≤ 2 * (M + 2) := by omega

/-- Hence `moving_horizon_path_state_bound` applies at *every* canonical start:
`Cf ≤ 2 * sf` needs no hypothesis on `M` beyond `M < 50000000`. -/
theorem canonical_path_state_bound {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) : Cf ≤ 2 * sf :=
  moving_horizon_path_state_bound hpath (canonical_start_state_bound M)

/-- **The travel inequality at a canonical start never mentions `Cf`.**
Given `M + 2 ≤ sf` it is exactly a cap on the terminal *index*. -/
theorem canonical_travel_iff_index_cap {M sf : Nat} (h : M + 2 ≤ sf) :
    2 * (sf - (M + 2)) ≤ M ↔ 2 * sf ≤ 3 * M + 4 := by omega

/-- **The missing ingredient, isolated.** Travel at a canonical start follows
from *one* global index cap and nothing else -- no path, no `Cf`, no bound on `M`. -/
theorem travel_of_index_cap {M sf : Nat} (hcap : 2 * sf ≤ 3 * M + 4) :
    2 * (sf - (M + 2)) ≤ M := by omega

/-- Consequently `Cf ≤ 2 * sf` cannot by itself deliver travel: this arithmetic
witness satisfies the state bound and fails the travel conclusion at 50000000.
(It is not claimed to be a genuine path; the point is that the *invariant*
carries no information about `sf`.) -/
theorem state_bound_alone_is_not_travel :
    ∃ sf Cf : Nat, Cf ≤ 2 * sf ∧ ¬ (2 * (sf - (50000000 + 2)) ≤ 50000000) :=
  ⟨120000000, 240000000, by decide, by decide⟩

/-- The slack form recorded in `RenormalizedGrowth`, instantiated at a canonical
start: the slack never exceeds the index. -/
theorem canonical_path_slack_le_index {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) : Cf - sf ≤ sf :=
  moving_horizon_path_slack_le_index hpath (canonical_start_state_bound M)

end A166944Research
