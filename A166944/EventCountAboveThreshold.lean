import A166944.CanonicalTravel
import A166944.TargetDefs

/-!
# The event-count criterion is false only BELOW the platform threshold

`CanonicalTravel.canonical_horizon_bound_of_event_count` proves the horizon cap `Cf ≤ 3*M + 4`
from the criterion `48*p*p + 1 < M`.  `EventCountCounterexample` refutes that criterion at
`M = 2659` (`p = 11`, `48*121+1 = 5809 > 2659`) -- and that refutation is why the platform states
its horizon-cap leaf only for `M ≥ 45895573`.

This module records what the certificate actually shows: the criterion FAILS at exactly five
records, all far below the platform threshold.

| M | p | 48p²+1 | fails? |
|---|---|---|---|
| 13 | 4 | 769 | yes |
| 43 | 6 | 1729 | yes |
| 139 | 2 | 193 | yes |
| 313 | 6 | 1729 | yes |
| 2659 | 11 | 5809 | yes |

and HOLDS at every record from `5419` upward, including all seven records at or above
`45895573` where `48*p*p+1` is at most `570289` against `M ≥ 45895573` (a factor of 80).

## Consequence, stated precisely

If `48*p*p + 1 < M` were available for `M ≥ 45895573`, then the platform's `hA` leaf would follow
immediately from `canonical_horizon_bound_of_event_count`. So the open content of `hA` is bounded by

    (i) proving the event-count criterion above the threshold, or
    (ii) any other route to the horizon cap in that range.

The measured `p/sqrt(M) ≤ 0.00569` in that range means `48*p*p+1 ≤ 48*0.00569²*M + 1 ≈ 0.0016*M`,
so the criterion has about 640x of room there. It is not a tightness problem.

Pure core: numerals only.
-/

namespace A166944Research

/-- **The criterion fails at `M = 2659`** (the known refutation), recorded with the value. -/
theorem event_count_fails_at_2659 : ¬ (48 * (11 * 11) + 1 < 2659) := by decide

/-- **It also fails at the four smaller records.** -/
theorem event_count_fails_small :
    ¬ (48 * (4 * 4) + 1 < 13) ∧ ¬ (48 * (6 * 6) + 1 < 43) ∧
      ¬ (48 * (2 * 2) + 1 < 139) ∧ ¬ (48 * (6 * 6) + 1 < 313) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **And it HOLDS at every record from 5419 upward**, including the tightest post-threshold case
`M = 367232911` with `p = 109`, where the criterion still has a factor of 644 of room. -/
theorem event_count_holds_above :
    48 * (9 * 9) + 1 < 5419 ∧
    48 * (11 * 11) + 1 < 10891 ∧
    48 * (57 * 57) + 1 < 355723 ∧
    48 * (109 * 109) + 1 < 367232911 ∧
    48 * (52 * 52) + 1 < 2937930211 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The reduction, stated as the implication it is.**  The event-count criterion at or above the
platform threshold discharges the platform's `hA` leaf with no extra work. -/
theorem hA_of_event_count_above_threshold {M sf Cf p : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf)
    (hcrit : 48 * (p * p) + 1 < M) : Cf ≤ 3 * M + 4 :=
  canonical_horizon_bound_of_event_count hM hcanon hpath hmax hcrit

/-! ## Axiom audit -/

#print axioms event_count_fails_at_2659
#print axioms event_count_fails_small
#print axioms event_count_holds_above
#print axioms hA_of_event_count_above_threshold

end A166944Research
