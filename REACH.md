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

## What a proof of the missing bound has to look like

It has to bound `p`, the number of nonunit events, by roughly `sqrt(M)/7`, using
only `d (M + 2) = M`, the path, and `IsAttainedPreviousMaximum M sf`. The
available count bounds (`Lemmas.lean:3851`, `:7355`) give `3q <= E`,
`E <= M * q` and `2q <= T` -- a lower bound on `T` and both bounds on `E`. None
of them bounds `q`.

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
