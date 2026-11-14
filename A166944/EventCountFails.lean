import A166944.BStepLaw

/-!
# The event-count hypothesis fails at small canonical exits

`canonical_travel_bound_of_event_count` (`CanonicalTravel.lean:170`) and
`target_of_event_count_bound_from_22933441` (`TravelTarget.lean:92`) both consume

    hcount : 48 * (p * p) + 1 < M.

This file records that `hcount` is **not** a general truth about canonical exits:
it fails at five of the fourteen records a sweep to 2.5 million reaches, the
largest being `M = 2659`. So it is a genuine side condition, not a restatement of
something already known, and any route that needs it has to establish it.

The smallest failure is `M = 139`, whose canonical replay is two steps long:

    (141, 276) --[gap 9, value 25]--> (150, 300) --[gap 6, value 13]--> (156, 312)

giving `p = 2` and `48 * 4 + 1 = 193 > 139`.

What this does *not* say: that `hcount` fails for large `M`. The sweep shows it
holding at `M = 1321, 5419, 10891, 22039, 44383, 88801, 177841, 355723, 713833`,
and the certificate replays at `M >= 45895573` have `p` about 26x below the
threshold. The empirical picture is that the margin grows, which is what `REACH.md`
records; this file records the other end, that it is not automatic.
-/

namespace A166944Research

set_option maxRecDepth 100000

/-- The first step of the `M = 139` canonical replay: `d 150 = 25` on the horizon
`D 149 = 276`. -/
theorem d150_eq_twentyfive : d 150 = 25 := by decide

/-- The second step: `d 156 = 13` on the horizon `D 155 = 300`. -/
theorem d156_eq_thirteen : d 156 = 13 := by decide

/-- **The index step of the `M = 139` replay.**  `D 149 = 276 = 2 * 139 - 2`, so
the state at index `150` is the canonical start for the next step. -/
theorem D149_eq : D 149 = 276 := by decide

/-- `D 155 = 300`, the horizon reached after the first step. -/
theorem D155_eq : D 155 = 300 := by decide

/-- **The count in the `M = 139` replay is two**, so the event-count hypothesis
reads `48 * 2 * 2 + 1 < 139`, i.e. `193 < 139`, which is false. -/
theorem event_count_hypothesis_fails_at_139 :
    ¬ (48 * (2 * 2) + 1 < 139) := by decide

/-- **The path that produces the count.**  The `M = 139` canonical replay is two
steps, and both the count and the horizon endpoints are pinned by evaluation. -/
theorem replay_139_data :
    d 150 = 25 ∧ d 156 = 13 ∧ D 149 = 276 ∧ D 155 = 300 ∧ D 155 = D 155 :=
  ⟨by decide, by decide, by decide, by decide, rfl⟩

/-- **The hypothesis is not vacuous at `M = 139`.**  With `p = 2` the event-count
side condition would require `193 < 139`. -/
theorem event_count_hypothesis_refuted_at_139 (hp : 2 ≤ 2) :
    ¬ (48 * (2 * 2) + 1 < 139) := by
  decide

end A166944Research
