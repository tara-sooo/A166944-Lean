# Reach: how far the finite certificates actually go

Status as of 2026-11-15. Every number and name below was read off the tree; the
counts were produced mechanically, not from notes.

## Why this file exists

`GATE_MAP.md` records the *conditional* routes to `Target`. This file records
the *unconditional* reach: the finite replay certificates that are already
kernel-checked, and the exact form of what is missing to extend them.

The distinction matters because the two are routinely confused. A certificate
that verifies "every record up to `N`" is unconditional and finite. A `target_of_*`
theorem is a conditional implication into `Target`. Neither one is progress
toward the other by itself: the first is bounded, the second assumes.

## The unconditional certificates

Every row is a kernel-checked theorem. The left column is the theorem, the right
is the bound it certifies.

| Theorem | Bound | Module |
| --- | --- | --- |
| `hprefix` (in `records_verified_through_9`) | `9` | `RecordReplay.lean:351` |
| `records_verified_through_22933443` | `22933443` | `VerifiedRecordPrefix.lean:138` |
| `records_verified_through_45895575` | `45895575` | `VerifiedTravelExtension.lean:94` |
| `records_verified_through_91793061` | `91793061` | `VerifiedFiftyMillionBridge.lean:68` |
| `prefixThrough183616425` (private) | `183616425` | `VerifiedRecordExtension.lean:45` |
| `verified_prefix_through_367232913` | `367232913` | `VerifiedRecordExtension.lean:65` |
| `verified_prefix_through_1468965063` | `1468965063` | `VerifiedLaterRecordExtension.lean:71` |
| `verified_prefix_through_11751795063` | `11751795063` | `VerifiedBoundaryRecordExtension.lean:41` |

The four `verified_prefix_through_*` theorems are stated in the stronger form

    d N = N - 2  /\  IsAttainedPreviousMaximum (N - 2) N  /\  RecordsVerifiedThrough N

so they carry the record value and the attained-maximum witness alongside the
prefix claim. The two `records_verified_through_*` theorems state only the last
conjunct.

The strongest of these is `verified_prefix_through_11751795063`, which asserts for
every strict record `5 < R` with `R <= 11751795063`:

    n = R + 2  /\  NoProperFactor (R - 2)  /\  NoProperFactor R

## From certified to prime

`prime_of_no_proper_factor` (`VerifiedTwinPrimePrefix.lean:14`) converts the
Mathlib-free predicate:

    NoProperFactor N  ->  N.Prime      (for 2 <= N)

`NoProperFactor N` is `forall f : Fin N, 2 <= f.val -> not (f.val | N)`, i.e. no
proper divisor. It is the shape the replay checker can decide, and it is
deliberately independent of Mathlib so the recurrence-side iteration stays light.

Composing the two gives the unconditional finite targets:

    target_for_records_le_22933441,  ..._le_45895573,  ..._le_91793059,
    target_for_records_le_367232911,  ..._le_1468965061

Each says: every strict record `5 < R` up to the stated bound is a greater twin
prime. These are real theorems about the actual recurrence, not conditionals.

## What is missing, in one sentence

**An upper bound on the number of events `p` in a canonical capped replay.**

The earlier version of this file said "a bound on the terminal index `sf`",
and then "no upper bound on `T`". Both were imprecise, and the correction
matters because it changes what a proof attempt should aim at.

What already exists, from `CanonicalTravel.lean`:

    moving_horizon_path_travel_bound   (line 38)
        sf - s <= p * sqrt (4 * (U + 1))      -- for any horizon bound U

    canonical_travel_bound_of_event_count   (line 170)
        (hcount : 48 * (p * p) + 1 < M)  ->  2 * (sf - (M + 2)) <= M

So the *displacement* `sf - s` is already bounded, in terms of `p`, and the step
from `hcount` to travel is already proved. Substituting `U = 3M + 4` and
requiring `2 * (sf - (M + 2)) <= M` gives

    2 * p * sqrt (4 * (3M + 4)) <= M        approximately,
    i.e.  p <= sqrt(M) / 7                  approximately.

At `M = 45895573` that is `p <= 977`. The `hcount` form `48p^2 + 1 < M` says the
same thing: `p <= sqrt((M-1)/48)`, which is `977` at that `M`.

Numercially, the verified certificates have

    M = 45895573    p = 37      (26.4x of slack)
    M = 91793059    p = 53      (26.1x)
    M = 367232911   p = 109     (25.4x)

so the observed event counts are more than twenty-five times below what is
needed. That is an empirical margin, **not a proof margin**, and it is the whole
of the gap.

## Why `T` is not the right object

`moving_horizon_path_count_bounds` (`Lemmas.lean:7355`) states its bounds in terms
of a `T` defined by the ledger `sf + q = s + T`, so that `T` is the displacement
*plus* the event count. `moving_horizon_path_travel_bound` bounds the displacement
directly. Bounding either one from above is equivalent to bounding `p`, so
phrasing the gap as "`T` has no upper bound" is true but not the useful form: the
missing input is the count.

## 12 formulations of the same missing bound

Recorded because each was found separately and they agree, which is the strongest
evidence available that the diagnosis is right and not an artefact of one
formulation. All 12 are kernel-checked in the modules named.

| route | module | statement |
| --- | --- | --- |
| travel is an index cap | `TravelReduction.lean` | travel `2*(sf-(M+2)) <= M` is *exactly* `2*sf <= 3*M+4`, and `Cf <= 2*sf` cannot supply it (`state_bound_alone_is_not_travel`) |
| count from the index | `CountFromIndex.lean` | `2*p <= B sf + sf - 2 - (2*M - 2)` |
| count bounds cannot bound the count | `CountBoundLimits.lean` | `3q <= E`, `E <= M*q`, `2q <= T` admit any `q` |
| reservoir is pinned | `BIntegrate.lean` | `B sf + (sf - s) = B s + S` with `S = sum (d r - 1)` |
| exit band | `ExitBand.lean` | `Cf - sf <= 2*M - 4` at every canonical exit, on the hypothesis `sf <= 2*M - 4` |
| exit coordinates | `ExitCoordinates.lean` | `a` cannot bound `sf` from above: `a sf / sf` tends to `3`, so the available bound is tight |
| crossing | `ExitThreshold.lean`, `CrossingRoute.lean` | crossing is equivalent to a horizon cap, and the crossing precondition holds with enormous margin, so no crossing theorem forbids it |
| room ledger | `RoomLedger.lean` | `Cf - sf = B sf - 2` exactly, so the room coordinate carries the same information as the reservoir |
| the excess sum is not independent | `ExcessIdentity.lean` | substituting `B sf = (M-2) + S - travel` into the scaled form returns `2*travel <= M`; a bound on `S` alone cannot suffice |
| the divisor structure is slack | `ExcessSumInterval.lean` | the event value divides the horizon and the index, but is three to four orders of magnitude smaller than the index, so the constraint leaves the quotient free |
| excursions | `BandReentry.lean`, `BandExcursion.lean` | a replay leaves the capped band and re-enters it, so a tail cannot be packaged as one in-band suffix; the exit shape is `2*(r-s)+1 <= M`, which is vacuous in `M` |
| minimum form and quiet windows | `HalfWindow.lean` | the gap obeys `r - s <= 2 * min (d r) v` and a quiet window yields `C - s - 1 <= f`; but the cofactor binds in only 16 of 1050 steps, so the sum collapses to route 4, and the window statements already hold at `M = 13` |

The first five together eliminate `B sf`, leaving a relation among `p`, `sf` and
`S`; the third says the proven count bounds cannot close it; the fifth says the
slack bound needs the same index bound as everything else. The remaining 7 close the
remaining coordinates one at a time: every one of them is exact, or vacuous, or
reduces to the statement being proved. Hence:
**one uniform bound on the terminal index `sf`**, equivalently on the event count
`p`, equivalently a lower bound on the reservoir `B sf`.

Two of these are refutations rather than obstructions, and are recorded as such
because each is the first thing a new attack tries:

* the threshold `45895573` cannot be dropped -- the proposition without the lower
  bound is false, with a witnessed canonical replay at `M = 13`
  (`RoomLedger.travel_bound_without_threshold_is_false`);
* a replay does not stay out of the band once it leaves
  (`BandReentry.replay_reenters_capped_band`).

Neither is a reason the problem is hard; both are reasons a particular argument
does not work. Recording them saves the next attempt from re-deriving them.

## What a proof of the missing bound has to look like

It has to bound `p`, the number of nonunit events, by roughly `sqrt(M)/7`, using
only `d (M + 2) = M`, the path, and `IsAttainedPreviousMaximum M sf`. The
available count bounds (`Lemmas.lean:3851`, `:7355`) give `3q <= E`,
`E <= M * q` and `2q <= T` -- a lower bound on `T` and both bounds on `E`. None
of them bounds `q`.

## What is measured, what is proved, what is refuted

Kept separate because conflating them is the most common failure in this
development, including several times in the work that produced this file.

**Proved, unconditional.** The certificates in the table above; the eleven route
statements; the two refutations. Each is kernel-checked in the named module, with
`#print axioms` reporting at most `propext` and `Quot.sound`.

**Measured, not proved.** Every quantitative margin in this file:

| quantity | observation | where |
| --- | --- | --- |
| `2*travel <= M` | holds for every record from `M = 139` to `M = 1427749`; fails only at `M = 13` and `M = 43` | canonical replay sweep, `n <= 3*10^6` |
| `S / M` | at most `0.115` for `M >= 313`, `0.0067` at `M = 355723` | same sweep |
| excursion length | 54 steps at `M = 355723`, 70 at `M = 1427749`; grows far slower than `M` | same sweep |
| `2*(r-s)+3 <= M` at exits | 9642 exits, no violation | `BandExcursion` sweep |
| the divisor ratio `e / r` | max `0.5`, typical `10^-4` | `n <= 3*10^7` |

These are margins, not proof margins. The distinction matters because the margins
are large -- a factor of about 26 at the fifty-million certificate -- and a large
margin is exactly what makes an empirical approach feel close when it is not.

**Refuted.** Statements that are false, each with a witness rather than an
argument: the threshold-free travel bound (`M = 13`); `no-reentry`
(`M = 43`); `room` drops by at most one per step (a drop of 468 at
`s = 2861166`); `travel <= M` is equivalent to `S <= B sf + 2` (`M = 13`);
and a candidate divisor law that held in 84.5 percent of cases and turned out to
be coincidence among small divisors.

**One caution about measurement.** A sweep that stops before `C_0 = 2*M - 2`
truncates the replay and reports a shorter excursion than the real one, silently.
Every table above was recomputed after that error was found in an earlier one.
Check that the sweep horizon exceeds `2*M - 2` for the largest `M` in the table.

## How to use this file

When reporting progress, say which of these three you mean:

1. **A new certificate** -- extends the table above. Unconditional, finite.
   Say which bound and how it was computed.
2. **A conditional route** -- a `target_of_*` step. Say which hypothesis it
   consumes; it is in `GATE_MAP.md` if it already existed.
3. **The missing bound** -- a uniform statement about `sf` (equivalently `T`,
   equivalently `B sf`). Nothing in the tree supplies it.

Conflating 1 with 3 is the error this file exists to prevent. A certificate at
`11751795063` and a proof for all `M` are not the same kind of object, and the
gap between them is not narrowed by adding more certificates.
