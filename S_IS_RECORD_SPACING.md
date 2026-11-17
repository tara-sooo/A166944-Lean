# What `S/M` actually is: the record-spacing identity

Campaign note, 2026-11-16, round 7. This records the answer to a question the campaign had been
circling for six rounds, found by measurement and verified arithmetically. It is a
**structural identification**, not a proof of the frontier — but it tells us we have been
attacking the wrong object.

## The identity

Let `M` be a record, `M'` the **next** record, and let the canonical replay from `M` stop at
horizon `C_f`. Then

    C_f = M' - 1                                        (24 of 25 pairs)
    S   = C_f - (2M - 2) = M' - 2M + 1                  (exact, verified 23/23)
    S/M = M'/M - 2 + 1/M                                (exact)

The second line uses the tree's own identity `S = C_f - (2M-2)` from `BindingCoordinate`, so the
only content is `C_f = M' - 1`: **the replay from a record stops exactly one below the next
record.** Spot checks: `M=13 -> 43-26+1 = 18 = S`; `M=2659 -> 5419-5318+1 = 102 = S`;
`M=22933441 -> 45895573-45866882+1 = 28692 = S`.

The single exception in the measured range is `M = 367232911`, where the replay stops at
`C_f = 734482122` while the next record is `367232913`. That record has `S/M = 4.4e-5`, so it
does not disturb any conclusion.

## Why this matters: `S` and the event values are the wrong object

`S = sum(e_i - 1)` is *by definition* a sum over the replay's events, so every attempt so far
tried to bound it by understanding the `e_i`. The identity says that is hopeless: `S` is
**exactly** determined by `(M, M')`, the record spacing. Rank correlation against `log(S/M)` over
`M >= 139` (n = 22):

| quantity | Spearman |
|---|---|
| `C_f/M - 2` | +1.0000 (restatement) |
| `(M' - 2M)/M` | **+0.9966** ← the object |
| `max(e_i)/M` | +0.9876 (spurious: both scale like `1/M`) |
| `max gap/M` | +0.9774 (spurious) |
| `p/M` | +0.9390 |
| `p^2/M` | +0.9368 |
| `#\{large e_i\}/M` | +0.2376 (no relationship) |

So `p`, the `e_i`, and the gaps are **replay dynamics**; none of them is the quantity that
controls `S`. Any proof of cap (B) phrased in terms of them is addressing the wrong object. And
"S/M is decreasing in M" is not a theorem — it is the shadow of `M'/M -> 2`.

## The sharp thresholds

Supremum of `S/M` over the record list, and the smallest threshold above which each bound holds:

| bound | smallest `M` such that it holds for all records above | witness just below |
|---|---|---|
| `S/M <= 3/8` | `M >= 139` | `M = 43` gives 1.2558 |
| `S/M <= 1/8` | `M >= 313` | `M = 139` gives 0.2590 |
| `S/M <= 0.1` | `M >= 313` | — |
| `S/M <= 0.05` | `M >= 2659` | `M = 313` gives 0.1150 |
| `S/M <= 0.024` | `M >= 10891` | `M = 2659` gives 0.0384 |

`sup S/M = 1.3846` at `M = 13`; over `M >= 139` it is `0.2590` (attained at `M = 139`).

**Consequence for target selection:** cap (B)'s constant `3/8` is 1.45x weaker than the true
supremum above its own threshold, and 9.8x weaker than the supremum above `2659`. If a uniform
statement is ever attempted, **`0.259` (attained at `M = 139`) is the right constant, not `3/8`.**

`M = 2659` is a local high in `S/M` because `M'/M = 2.0380` there, not because of its event
values — another confirmation that the spacing is what matters.

## The mechanism, and the wall it names

`C_f - 1` and `C_f + 1` are **both prime at 25 of 25 consecutive record pairs** (one distinct prime factor each):
`M=13 -> 41,43`; `M=2659 -> 5417,5419`; `M=22933441 -> 45895571,45895573`.

So every stopping horizon is a **twin-prime centre**. The chain is:

    replay stops at a twin-prime centre  ->  C_f = M' - 1  ->  S = M' - 2M + 1  ->  S/M -> 0

The last link is the existence of a twin-prime pair at each record's horizon. That is the trap
`FACTS.md` §5 warned about, now confirmed as the *actual* content of the obstacle rather than a
bypassable feature. No uniform proof of `S/M <= 3/8` can avoid it. I do not see a way around it
with the tools in this tree.

## A correction to the shared record table (again)

Subagent `sbound` reported that `367232913` is a record and `734482123` is not. **That is wrong**,
and the repository already contains a kernel proof:

```lean
-- A166944/VerifiedLaterRecordExtension.lean
private theorem replayAfter367232911_accepted :
    recordReplayCheck 367232911 367232913 734465820 hitsAfter367232911 734482122 = true := by
  decide +kernel

theorem next_record_after_367232911 :
    367232911 < 734482123 ∧ IsAttainedPreviousMaximum 367232911 734482124 ∧
      d 734482125 = 734482123 ∧ D 734482124 = 734482122
```

`decide +kernel` is unconditional, so `d 734482125 = 734482123` and `734482123` **is** a record.
The misreading came from `recordReplayCheck`'s second argument, which is the **starting index**
(`367232913`), not a record value.

**Settled record list (do not change again):**

```
3, 7, 13, 43, 139, 313, 661, 1321, 2659, 5419, 10891, 22039, 44383, 88801, 177841,
355723, 713833, 1427749, 2860771, 5725453, 11461141, 22933441, 45895573, 91793059,
183616423, 367232911, 734482123, 1468965061
```

Neither `367232913` nor `734491369` is a record.

**Method note, now confirmed twice:** when a kernel proof and a subagent measurement disagree,
the kernel proof wins. Verify record tables with the jump-form canonical replay, never a long
linear scan, and read `recordReplayCheck`'s argument list before concluding anything from it.
