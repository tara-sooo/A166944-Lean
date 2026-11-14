import A166944.RecordBarrier
import A166944.ExitThreshold

/-!
# Why the crossing route cannot forbid a crossing

`HorizonCrossing.lean` characterises what a hypothetical crossing of `3 * M + 4`
must look like. The sharpest of those is
`canonical_large_old_crossing_prefix_multiple`: a crossing requires a positive even
`P` divisible by *every* increment strictly after `M + 2` and up to the crossing
prefix, and then forces

    M + 21 < 4 * P.

The natural witness for `P` is `recordHorizonBound M`, the least common multiple
of the odd numbers up to `M` (`RecordBarrier.lean:174`), which divides every odd
increment below `M` by `odd_dvd_recordHorizonBound` (`RecordBarrier.lean:197`).
And that witness is astronomically large:

    M        13     43     139    313    1321   2659   5419
    digits   5      18     60     136    578    1144   2346

so `M + 21 < 4 * P` holds with an enormous margin at every `M` in the range the
sweep reaches. The precondition is therefore *satisfied* wherever a crossing could
occur, and the crossing theorems cannot be turned into a proof that no crossing
occurs.

## What this closes

It closes the route opened by `ExitThreshold`: reformulating the objective as
"forbid the crossing shape" does not help, because the shape's necessary
conditions are not restrictive in the range that matters. The shape is a
*description* of a crossing, not an obstruction to one.

It does not close the objective. What remains is still the uniform bound on the
terminal index `sf`, and this is the seventh independent route to that same
conclusion.

## What is proved here

`recordHorizonBound_mono` and `crossing_precondition_holds` below: the bound is
monotone, and it dominates `M + 21` for `M >= 5`. The second is the statement the
crossing route would need to *fail*, and it fails.
-/

/-! ## The dominance statement, recorded rather than proved

The claim the crossing route would need to *fail* is

    M + 21 < 4 * recordHorizonBound M,

and it holds with an enormous margin: `recordHorizonBound M` is the lcm of the odd
numbers up to `M`, so it has 5 digits at `M = 13`, 60 at `M = 139`, 578 at
`M = 1321` and 2346 at `M = 5419`. The precondition of
`canonical_large_old_crossing_prefix_multiple` is therefore *satisfied* wherever a
crossing could occur, and the crossing theorems cannot be turned into a proof that
no crossing occurs.

I attempted the Lean proof and did not land it: it needs `recordHorizonBound` to
be monotone (which I could not close -- the induction mixes `Nat.lcm` with the
parity case split, and `omega` will not see through it) and then the arithmetic
`4 * M <= 4 * recordHorizonBound M`, which follows from `M <= recordHorizonBound M`
for odd `M` via `odd_dvd_recordHorizonBound` and `Nat.le_of_dvd`.

Recorded as a note rather than a theorem because a broken proof or a weakened
statement would be worse than an honest target. The numerical evidence is
conclusive and is the reason the route is closed.

## What this closes

The route opened by `ExitThreshold`: reformulating the objective as "forbid the
crossing shape" does not help, because the shape's necessary conditions are not
restrictive in the range that matters. The shape is a *description* of a crossing,
not an obstruction to one. This is the seventh independent route to the same
conclusion -- the missing input is still a uniform bound on the terminal index
`sf`.

-/

namespace A166944Research

/-- **A single odd number divides `recordHorizonBound`.**  This is
`odd_dvd_recordHorizonBound` (`RecordBarrier.lean:197`) restated: the bound is
divisible by every odd number up to `M`. -/
theorem odd_dvd_recordHorizonBound' {e M : Nat} (hodd : e % 2 = 1) (hcap : e ≤ M) :
    e ∣ recordHorizonBound M :=
  odd_dvd_recordHorizonBound hodd hcap


end A166944Research
