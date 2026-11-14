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

**A bound on the terminal index `sf` of a canonical capped replay, uniform in `M`.**

The certificates cover a finite interval because each one was *computed*. To get
`Target` one needs the same conclusion for all `M`, and the only thing standing
between the finite certificates and that conclusion is a uniform bound on how
far a capped replay can travel.

Equivalently, by `TravelReduction.lean`:

    travel is 2 * (sf - (M + 2)) <= M,
    which under M + 2 <= sf is exactly the index cap 2 * sf <= 3 * M + 4.

And by `BCapDictionary.lean`, the same statement is `2 * Cf <= 3 * M + 2 * B sf`:
what is needed is a *lower* bound on the reservoir `B sf`, since travel is
precisely the reservoir being spent. `B` is not monotone (`B 1 = 2 > B 3 = 1`),
so no upper bound on `B` helps.

`Lemmas.lean:3851` and `:7355` give `3 q <= E`, `E <= M * q` and `2 q <= T` --
a lower bound on `T` and both bounds on `E`. There is no upper bound on `T`
anywhere in the tree.

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
