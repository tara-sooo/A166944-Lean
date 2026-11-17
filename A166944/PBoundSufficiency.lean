import A166944.CanonicalTravel
import A166944.TargetDefs

/-!
# What `p` bound actually suffices for the horizon cap, and how much room there is

`CanonicalTravel.canonical_horizon_bound_of_event_count` turns `48*p*p + 1 < M` into the horizon
cap `Cf ≤ 3*M + 4`, which is the platform's `hA` leaf. That criterion looks fragile -- and indeed
`EventCountCounterexample` refutes it at `M = 2659` -- but the refutation is entirely below the
platform threshold, and above it the criterion has enormous room.

This module records the arithmetic of that room, so the size of the remaining gap is exact rather
than impressionistic. Unwinding the counting estimate
(`previous_record_le_of_long_travel`: `M < 2*(k*Q) -> M ≤ 48k² + 1` with
`Q = isqrt (4*(3M+4))`, about `2*sqrt(3M)`) gives

    `48*p*p + 1 < M`   is what the tree proves,
    and the p-bound it delivers is   `p <= 0.2165 * sqrt M`   roughly,

whereas the measured `p/sqrt M` above the threshold is at most `0.00569` -- a factor of 38 of slack.
So the horizon cap is NOT being blocked by the counting criterion's tightness in the leaf's range.

## What this does not do

It does not prove the criterion. The measured `p/sqrt M <= 0.00569` is a measurement over the seven
certified records at or above the threshold, not a theorem, and `p` is not known to be bounded by
any function of `M` in general. So `hA` remains open. What is established here is the SIZE of what
is missing, which is what makes it worth another attempt rather than a `big` rewrite.

Pure core: numerals; the reduction is the tree's own lemma.
-/

namespace A166944Research

/-- **The measured `p` ratio above the threshold.**  The worst case is `M = 367232911` with
`p = 109`, giving `p * p * 1000000 <= 33 * M`: that is `p/sqrt M <= sqrt 33 / 1000 ~ 0.00574`,
stated without `sqrt` by cross-multiplying. -/
theorem p_ratio_worst_case : 109 * 109 * 1000000 ≤ 33 * 367232911 := by decide

/-- **The criterion's own slack at the tight post-threshold record.**  `48*109^2 + 1 = 570289`
against `M = 367232911`, a factor of 643.9 -- so 643 is the largest kernel-checkable multiple. -/
theorem event_count_slack_at_367232911 : 643 * (48 * (109 * 109) + 1) ≤ 367232911 := by decide

/-- **And at the smallest post-threshold record.**  `48*37^2+1 = 65713` against `45895573`,
a factor of 698. -/
theorem event_count_slack_at_45895573 : 698 * (48 * (37 * 37) + 1) ≤ 45895573 := by decide

/-- **The reduction, isolated**: the counting criterion at any `M` discharges `hA` outright. -/
theorem hA_of_event_count {M sf Cf p : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf)
    (hcrit : 48 * (p * p) + 1 < M) : Cf ≤ 3 * M + 4 :=
  canonical_horizon_bound_of_event_count hM hcanon hpath hmax hcrit

/-! ## Axiom audit -/

#print axioms p_ratio_worst_case
#print axioms event_count_slack_at_367232911
#print axioms event_count_slack_at_45895573
#print axioms hA_of_event_count

end A166944Research
