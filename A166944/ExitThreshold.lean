import A166944.ExitCoordinates
import A166944.HorizonCrossing

/-!
# The exit sits at two thirds of the crossing threshold

`HorizonCrossing.lean` studies what happens when a canonical replay *crosses*
`3 * M + 4`, the threshold at which the index cap fails. The exit of a canonical
replay does not cross it:

    Cf / (3 * M + 4)  ->  2/3

at all fourteen canonical exits the sweep reaches for `M >= 1321`, and the only
crossing in the data is at `M = 43`. So the exit sits well below the crossing
threshold, at two thirds of it, which is the same statement as `Cf ~ 2 * M`
(`ExitCoordinates`) written against the threshold rather than against `M`.

## What this does and does not give

It does *not* give the index cap. The crossing theorems constrain what a crossing
would look like -- it needs a common even multiple `P` with `M + 21 < 4 * P`, and
an earlier old increment of at least 9 -- but those are constraints on a
hypothetical crossing, not a bound on where the replay stops. To use them one
would have to show the replay *cannot* stop below the crossing without violating
them, which is the missing step.

What it does give is a reformulation of the objective in the crossing language:
since the exit is at `2/3` of the threshold and the replay is monotone in `C`,
proving `Cf <= 3 * M + 3` (i.e. "the replay never crosses") is *equivalent* to
proving that no crossing occurs, and `HorizonCrossing` already supplies the shape
any crossing must have. That equivalence is recorded here rather than left
implicit, because it relocates the problem from "bound `sf`" to "forbid the
crossing shape", and the second has proved lemmas attached to it.
-/

namespace A166944Research

/-! ## The crossing reformulation, and why it is not yet usable

The exit sits at roughly two thirds of the crossing threshold: numerically
`Cf / (3 * M + 4) -> 2/3` at all fourteen canonical exits the sweep reaches for
`M >= 1321`, with the only crossing in the data at `M = 43`. Written against `M`
this is the same statement as `Cf ~ 2 * M` from `ExitCoordinates`.

It would be tempting to conclude `Cf <= 3 * M + 3` from the slack bound. That does
not work, and the arithmetic says so plainly:

    ExitBand:      Cf - sf <= 2*M - 4
    ExitBand:      sf <= 2*M - 4                    (hypothesis)
    therefore:     Cf <= 4*M - 8

and `4*M - 8 <= 3*M + 3` only for `M <= 11`. So the slack bound is *far* too weak
to forbid a crossing; forbidding it needs `Cf ~ 2*M`, which is a statement of a
different strength and is exactly what is missing.

What is available, and what this file records, is the equivalence on the horizon
alone: a crossing is by definition `3*M + 4 < Cf`, so "no crossing" and the
horizon cap `Cf <= 3*M + 4` are the same proposition. `HorizonCrossing` then
supplies the shape any crossing must have -- a common even multiple `P` with
`M + 21 < 4*P`, and an earlier old increment of at least 9 in the prefix. That
relocates the objective from "bound `sf`" to "forbid the crossing shape", and the
second has proved lemmas attached to it.

Whether that relocation helps is not addressed here. The file records the
equivalence and the shape, and says explicitly that the slack bound cannot bridge
them.

-/

/-- **No crossing is the horizon cap.**  By definition a crossing is
`3 * M + 4 < Cf`, so forbidding one and bounding the horizon are the same
proposition. Stated because `HorizonCrossing.lean` characterises what a crossing
must look like, so the objective can be phrased as "that shape does not occur"
rather than "`sf` is small" -- and the first has proved lemmas attached. -/
theorem no_crossing_iff_horizon_cap {M Cf : Nat} :
    ¬ (3 * M + 4 < Cf) ↔ Cf ≤ 3 * M + 4 := by
  omega

/-- **The slack bound cannot forbid a crossing.**  `Cf - sf <= 2 * M - 4` with
`sf <= 2 * M - 4` gives only `Cf <= 4 * M - 8`, and `4 * M - 8 <= 3 * M + 3` holds
only for `M <= 11`. Recorded as a theorem so that the route is not attempted
again: forbidding a crossing needs `Cf ~ 2 * M`, not the slack bound. -/
theorem slack_does_not_forbid_crossing (M : Nat) (hM : 12 ≤ M) :
    ¬ (4 * M - 8 ≤ 3 * M + 3) := by
  omega

end A166944Research
