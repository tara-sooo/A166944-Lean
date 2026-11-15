# Gate map: what actually has to be proved

Status as of 2026-11-15. Every claim below is read off the sources in
`A166944/`; nothing here is proved by this document. Line numbers are from the
tree at the commit named in `git log -1`.

## Why this file exists

Reports about this project have repeatedly said "the obstruction is narrowed to
three things" or "the obstruction is now one inequality". Neither matches the
repository. The README states the standing obstruction in entirely different
terms (`5E.3 critical obstruction`: rule out the `q = 3` and `q = 2` quotient
families), and the code contains **thirteen** separate `target_of_*` entry
points. This file records the entry points and the implication edges between
them so that "what is left" can be read off instead of asserted.

## The thirteen entry points to `Target`

| Theorem | File | Hypothesis |
| --- | --- | --- |
| `target_of_reserve_condition210` | `TwinReserveTarget210.lean:38` | `ResidualReserveCondition210 multiplier` |
| `target_of_signed_reserve_condition210` | `TwinSignedReserveTarget210.lean:49` | `ResidualSignedReserveCondition210` |
| `target_of_crossing_budget_condition210` | `TwinCrossingBudget210.lean:72` | `ResidualCrossingBudgetCondition210` |
| `target_of_scaled_crossing_budget_condition210` | `ResidualScaledPotential210.lean:321` | `ScaledCrossingBudgetCondition210` |
| `target_of_rebalanced_crossing_budget_condition210` | `ResidualRebalancedCosts210.lean:331` | `RebalancedCrossingBudgetCondition210` |
| `target_of_rebalanced_boundary210` | `RebalancedBoundary210.lean:412` | `RebalancedBoundaryCondition210` |
| `target_of_rebalanced_overlap_crossings210` | `RebalancedOverlapBudget210.lean:402` | `RebalancedOverlapCrossingCondition210` |
| `target_of_rebalanced_remaining_crossings210` | `RebalancedCrossingGrowth210.lean:264` | `RebalancedRemainingCrossingCondition210` |
| `target_of_rebalanced_remaining_crossings_from_1468965061` | `RebalancedCrossingGrowth210.lean:268` | same, from `M >= 1468965061` |
| `target_of_travel_bound_from_22933441` | `TravelTarget.lean:83` | `CanonicalTravelBoundFrom 22933441` |
| `target_of_twin_prime_travel_bound_from_22933441` | `TravelTarget.lean:76` | `TwinPrimeTravelBoundFrom 22933441` |
| `target_of_event_count_bound_from_22933441` | `TravelTarget.lean:89` | event-count form |
| `target_of_twin_travel_from_fifty_million` | `VerifiedFiftyMillionBridge.lean:97` | `TwinPrimeTravelBoundFrom 50000000` |

## Implication edges between the gates

Extracted mechanically from the theorem signatures in `A166944/` (38 edges).
An arrow means "the source is sufficient for the target". Every edge below is a
theorem that exists; none is inferred.

### Edges into `Target`

```
ResidualReserveCondition210          -> Target   target_of_reserve_condition210            TwinReserveTarget210.lean:38
ResidualSignedReserveCondition210    -> Target   target_of_signed_reserve_condition210     TwinSignedReserveTarget210.lean:49
ResidualCrossingBudgetCondition210   -> Target   target_of_crossing_budget_condition210    TwinCrossingBudget210.lean:72
ScaledCrossingBudgetCondition210     -> Target   target_of_scaled_crossing_budget_...210   ResidualScaledPotential210.lean:321
RebalancedCrossingBudgetCondition210 -> Target   target_of_rebalanced_crossing_budget_...  ResidualRebalancedCosts210.lean:331
RebalancedBoundaryCondition210       -> Target   target_of_rebalanced_boundary210          RebalancedBoundary210.lean:412
RebalancedOverlapCrossingCondition210-> Target   target_of_rebalanced_overlap_crossings210 RebalancedOverlapBudget210.lean:402
RebalancedRemainingCrossingCondition210 -> Target  target_of_rebalanced_remaining_...     RebalancedCrossingGrowth210.lean:264
CanonicalTravelBoundFrom 22933441    -> Target   target_of_travel_bound_from_22933441      TravelTarget.lean:83
TwinPrimeTravelBoundFrom 22933441    -> Target   target_of_twin_prime_travel_bound_...     TravelTarget.lean:76
TwinPrimeTravelBoundFrom 50000000    -> Target   target_of_twin_travel_from_fifty_million  VerifiedFiftyMillionBridge.lean:97
```

### Edges into `TwinPrimeTravelBoundFrom`

```
ResidualReserveCondition210          -> TwinPrimeTravelBoundFrom 50000000   TwinReserveTarget210.lean:23
ResidualSignedReserveCondition210    -> TwinPrimeTravelBoundFrom 50000000   TwinSignedReserveTarget210.lean:33
ResidualCrossingBudgetCondition210   -> TwinPrimeTravelBoundFrom 50000000   TwinCrossingBudget210.lean:58
RebalancedRemainingCrossingConditionFrom210 -> TwinPrimeTravelBoundFrom 367232911  RebalancedCrossingGrowth210.lean:260
IsTravelPotential210 & PotentialCrossingBudgetCondition210 -> TwinPrimeTravelBoundFrom  ResidualScaledPotential210.lean
```

### Edges between budget conditions

```
ResidualReserveCondition210        -> ResidualSignedReserveCondition210    TwinSignedReserveTarget210.lean:22
ResidualSignedReserveCondition210  -> ResidualCrossingBudgetCondition210   TwinCrossingBudget210.lean:32
```

### What this shows

The `Residual*` certificate chain is a chain, not a fan:

```
ResidualReserveCondition210
  -> ResidualSignedReserveCondition210
  -> ResidualCrossingBudgetCondition210
  -> TwinPrimeTravelBoundFrom 50000000
  -> Target
```

But the **other eight entry points are siblings**. Each takes its own budget
hypothesis and produces `Target` directly; no theorem derives one budget
condition from another except the two `Residual*` edges above. In particular
nothing connects the `Rebalanced*` tower to the `Residual*` tower, and nothing
connects `ScaledCrossingBudgetCondition210` to either. The README's ordering
(`Residual*`, then `Rebalanced*`, then `Scaled*`) reflects the order in which
the estimators were written, not a dependency order.

So "which gate should we close?" has eight incomparable answers, not one. That
is the actual state of the reduction.

## The threshold that matters

`ResidualCrossingBudgetCondition210` (`TwinCrossingBudget210.lean:23`) is
quantified over `50000000 <= M`. `TwinPrimeTravelBoundFrom` is quantified over
`lower <= M` for whatever `lower` is passed, and the value actually used at the
top is `45895573` (`VerifiedFiftyMillionBridge.lean:91`).

This is why counterexamples at `M = 13` and `M = 43` -- which appear repeatedly
in scratch reports -- are **outside the quantified range** and do not refute any
gate that is actually used. They refute only the version of the statement with
the lower bound dropped, which no `target_of_*` theorem consumes.

## What is genuinely missing

`T` (the total displacement) has no upper bound anywhere in the tree. The
available count bounds are

```
moving_horizon_capped_old_path_count_bounds   Lemmas.lean:3851
    3 * q <= E  /\  E <= M * q  /\  2 * q <= T
moving_horizon_path_count_bounds              Lemmas.lean:7355
    3 * q <= E  /\  E <= M * q  /\  2 * q <= T
```

Each gives a *lower* bound on `T` and a lower and upper bound on `E`. Travel is
equivalent to `2 * (T - q) <= M`, so the missing ingredient is an upper bound on
`T`, and none of these three conjuncts supplies one.

Two independent scratch reports concluded that the event-count hypothesis
`48 * (q * q) + 1 < M` is "the one remaining input". That is not a separate
input: `canonical_travel_bound_of_event_count` (`CanonicalTravel.lean:170`)
derives travel **from** that hypothesis, so the two formulations are
interchangeable, not stacked.

## How this file should be used

Before reporting that the obstruction has been "narrowed", check the claim
against this table. If it is not one of the thirteen rows above, or not an edge
printed above, then it is a new statement and it needs its own theorem.

## What the entry points actually assume

An audit of the reference structure turned up a fact this file did not state: **seven
of the eight `*210` entry points assume the travel bound internally.**

| entry point | assumes `2*(s-(M+2)) ≤ M`? |
| --- | --- |
| `ResidualReserveCondition210` (`TwinReserveTarget210`) | yes |
| `ResidualSignedReserveCondition210` (`TwinSignedReserveTarget210`) | yes |
| `ResidualCrossingBudgetCondition210` (`TwinCrossingBudget210`) | yes, three times |
| `RebalancedRemainingCrossingCondition210` (`RebalancedCrossingGrowth210`) | yes |
| `RebalancedOverlapCrossingCondition210` (`RebalancedOverlapBudget210`) | yes |
| `ResidualScaledCrossingBudgetCondition210` (`ResidualScaledPotential210`) | yes |
| `ResidualRebalancedCostCondition210` (`ResidualRebalancedCosts210`) | yes |
| `RebalancedBoundaryCondition210` (`RebalancedBoundary210`) | **no** |

So the "thirteen conditional entry points" are not thirteen independent ways in. Seven
of them take the travel bound as a hypothesis and contribute an additional condition on
top of it; they are strictly stronger assumptions than the bound, not alternatives to
it. Working through the travel bound, as this development has done, was therefore not
a choice among equals.

`RebalancedBoundaryCondition210` is the exception and is worth a look for that reason
alone.

### And they are unreachable in the reference graph

The same audit counted references: of the seventeen `target_of_*` declarations named in
this file, **five have zero references anywhere** and six more are referenced only
inside their own module. They are proved, they conclude `Target`, and nothing calls
them. The whole library has 1478 theorems of which **387 are orphans** in that sense,
133 of them in the `*210` files.

That is not a soundness problem -- an unreferenced theorem is still a theorem -- but it
is a reachability problem: the entry points a reader would find here are, for the most
part, not connected to anything. `Attempt.lean` (1871 lines) is the extreme case and
has no importer at all.
