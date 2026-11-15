# Why the A166944 barrier has not moved, and what would move it

Written down because the analysis itself has been the missing artifact. Sixteen rounds
of work have closed sixteen routes, corrected four of the author's errors, and made
`REACH.md` and `GATE_MAP.md` accurate -- and moved the barrier not at all. This file
records why, in enough detail to be actionable.

## The barrier's exact shape

The target is equivalent to

$$\sum_i e_i \;\le\; \frac{3M-9}{8},$$

the sum of the **event values** along a canonical replay, where an event is a step at
which the first difference exceeds 1. The equivalence goes through
`sf = (M+2) + travel`, `travel <= 2(S+p)` and `S + p = sum e_i`.

Every property of a single event value is already proved:

| property | where |
| --- | --- |
| `e_i ∣ C_i - 1` and `e_i ∣ r_i` (even hit) | `Lemmas.moving_horizon_event_divisibility_even` |
| `e_i ∣ C_i + 1` and `e_i ∣ r_i - 2` (odd hit) | `Lemmas.moving_horizon_event_divisibility_odd` |
| `3 * e_i <= C_i ± 1` | `Lemmas.moving_horizon_step_event_package` |
| `e_i <= M` | `IsAttainedPreviousMaximum`, first conjunct |
| `e_i >= 3` | `Lemmas.moving_horizon_step_event_ge_three` |
| `e_i > 1`, `C_{i+1} = C_i + e_i - 1` | `moving_horizon_step_event_package`, `moving_horizon_step_update` |

So the local structure is fully known. What is missing is a way to sum it.

## Four reasons the present toolkit cannot get there

### 1. There are upper bounds and no usable lower bounds

The hypotheses give `e <= M` (an upper bound), `e >= 3` (far too weak), and
`C' = C + e - 1` (monotone increase). But `e ∣ C ± 1` says only that `e` **is a
divisor** of `C ± 1`; it does not say `e` is small. `e = C - 1` is consistent with every
one of the six properties above.

**Correction.** This paragraph originally said "nothing in the library bounds that
quotient from below". That is false, and it was false when written:
`Lemmas.moving_horizon_step_event_package` (commit `6415319`, 2026-09-08) already
carries `3 * d r <= C - 1` on the even branch and `3 * d r <= C + 1` on the odd, which
is exactly a lower bound of 3 on the quotient. What is missing is not a bound on the
quotient but a bound on the **number of steps** and on the **sum**; the quotient is
free to be anything from 3 upward (measured: median 54750, maximum 953589).

So the honest statement of the gap is narrower than the one this file opened with.

### 2. A bound on `S` alone is not enough, and this is proved

`CapBCandidates.excess_bound_alone_does_not_give_cap`, for all `M >= 16` and all
admissible `S`, exhibits `sf, Cf, Bsf` with the ledger `Bsf + sf = Cf + 2` intact,
`Bsf >= 4`, `8S <= 3M`, and `4 sf > 7M - 1`. The witness takes the reservoir as small as
the ledger permits.

`TerminalRigidity.terminal_cap_iff_reservoir_excess` states the normal form:

$$4\,sf \le 7M-1 \quad\Longleftrightarrow\quad M + 1 + 4S \;\le\; 4\,B_{sf}.$$

The cap bounds `S` **relative to** `B sf`. Any route that assumes an upper bound on `S`
is assuming something stronger than the target, which is why such routes keep closing
without helping.

### 3. Every coordinate change is circular

`S`, `travel`, `B`, `room` and `slack` are linked by the ledger and cannot be moved
independently. `ExcessIdentity` proved the substitution returns the statement;
`TerminalRigidity` proved the same for the terminal coordinates; `AuditRoutes` proved
routes 1 and 9 are the same inequality restated. Thirteen of the sixteen closed routes
are this phenomenon.

### 4. Induction on the record sequence cannot work, and this is proved

`RecordInductionFails.cap_does_not_transfer_along_records`: the cap holds at `M = 7`
(the replay is empty, `sf = 9`, `Cf = 12`) and fails at the next record `M = 13`
(`sf = 24`, `Cf = 42`, `4*24 = 96 > 90`). So the induction hypothesis must hold below
the threshold too, which is where it fails.

And carrying the threshold gains nothing: `RecordTransferFixpoint.next_criterion_substituted`
shows the hypothesis the step needs, after substituting `Cf = (2M-2) + S`, contains no
cap on `M`, no terminal index and no event count of `M`. The step asks for what it is
meant to establish, in different letters.

This is also why the FLT analogy does not transfer. Infinite descent needs a quantity
that strictly decreases; `R' = 2R - 1 + S` increases and the threshold moves up.

## The four angles not yet tried

Each is stated as a lemma that could be attacked on its own.

### A. The factor structure of `e_i`

`e_i` divides both `C_i ± 1` and `r_i` (or `r_i - 2`), so `e_i` divides
`gcd(C_i ± 1, r_i)`. Bounding that gcd from above bounds `e_i`. Nothing in the library
evaluates this gcd. **Target lemma:** a bound on `gcd (C ± 1) r` in terms of `M`.

### B. Monotonicity of the quotient

If the quotients `(C_i ± 1)/e_i` increase along a replay, then the event values must
grow more slowly than the horizon. Measured, `e_i / M` is at most `0.18` and falls as
`M` grows. **Target lemma:** the quotient at step `i+1` is at least the quotient at
step `i`, or bounded below by a function of `i`.

### C. Factorisation of `C_i ± 1`

`C_i ± 1` is the horizon at an event; `e_i` is a divisor of it. If `C_i ± 1` has a
large prime factor then `e_i` cannot be that large unless it takes the whole factor.
Measured, `C_f - 1` and `C_f + 1` are both prime at every record examined, which makes
the quotient as large as possible at the exit -- but that is an observation, and the
mechanism needs to hold at every step, not only the last. **Target lemma:** a lower
bound on the largest prime factor of `C_i ± 1`, or on its smallest divisor above 1.

### D. Simultaneous induction on `p` and `sum e_i`

`p` alone is not boundable (`OrphanHarvest.count_index_route_is_vacuous` proved `p`
and `sf` are only constrainable jointly). But `p` and `sum e_i` together might be,
since `C + 2p <= C_f` and `C_f = (2M-2) + sum(e_i - 1)` relate them. **Target lemma:**
a joint bound showing `sum e_i` grows slower than `M` while `p` grows slower than
`sum e_i`.

## What the measurements say, as observations

`sum e_i` divided by the allowance `(3M-9)/8`:

| M | p | sum e_i | allowance | ratio |
| --- | --- | --- | --- | --- |
| 139 | 2 | 38 | 51 | 0.745 |
| 313 | 6 | 42 | 116 | 0.362 |
| 2659 | 11 | 113 | 996 | 0.114 |
| 10891 | 11 | 269 | 4083 | 0.066 |
| 355723 | 57 | 2445 | 133395 | 0.018 |

The worst case is `M = 139`, and the margin improves with `M`. That is a margin, not a
proof margin, and this development has already recorded what happens when the two are
confused.

## The honest conclusion

Not "this cannot be done". The barrier has a known shape, the local structure is fully
proved, and four specific angles remain untried -- each of which reduces to a lemma
about divisibility that the library does not contain. What has not happened yet is the
production of new number-theoretic content about `gcd(C ± 1, r)`, as opposed to further
rearrangements of what is already there.
## A correction: the square-root route was already taken, and already closed

I proposed a three-step route as if it were new: bound the gap by `sqrt(C)`, sum it to
`travel <= p sqrt(C)`, then show the sum fits the budget.

All of it was in the tree. `CanonicalTravel.moving_horizon_step_gap_le_sqrt` is
`r - s <= isqrt (4 * (U + 1))` and `moving_horizon_path_travel_bound` is
`sf - s <= p * isqrt (4 * (U + 1))`. That is steps one and two, verbatim.

And step three cannot work, which is also already proved:
`OrphanHarvest.count_index_route_is_vacuous` exhibits, for **every** `sf`, a horizon
`Cf` and a count `p` with `p + M <= sf + 1` and `sf - (M+2) <= p * isqrt (4 * (3M+5))`.
The two bounds hold simultaneously for arbitrary `sf`, so no combination of them bounds
`sf`, whatever the constant inside the root.

The file already listed this under the fourth reason it cannot get there. Proposing it
again was the same failure as the duplicate-theorem episodes, one level up: a
rediscovered strategy rather than a rediscovered lemma.
## Two more corrections, both from the same afternoon

**`room_f` is not approximately `M` in the sense the phrase suggests.** Measured over
all thirteen records below three million, `Cf - sf <= M` fails in **eight** of them:

| M | sf | Cf | room | room <= M |
| --- | --- | --- | --- | --- |
| 139 | 156 | 312 | 156 | no |
| 2659 | 2712 | 5418 | 2706 | no |
| 10891 | 11041 | 22038 | 10997 | no |
| 355723 | 357042 | 713832 | 356790 | no |
| 1427749 | 1431006 | 2860770 | 1429764 | no |

The ratio is close to 1 and the relative excess is small (at most 0.15 percent here),
but the absolute excess reaches 2015. Since the ledger is exact --
`room_f = (M-4) + S - travel` -- that is `S - travel = 2019` at that record, and
`S - travel` changes sign across the set (from -39 to +2019). So `S` and `travel` are
unordered, and no argument may treat them as interchangeable.

**And `Attempt.lean` is not a source of the room bound.** It contains
`moving_horizon_capped_old_path_endpoint : Cf - sf <= M`, which looks like exactly the
missing input -- but its hypothesis `HasMovingHorizonCappedOldPath` has `C - s <= M` and
`C' - r <= M` among its conjuncts (`ResearchDefs.lean:92`), so the conclusion is one of
the hypotheses at every step. It is a tautology, which is consistent with the audit that
found the file unreferenced: 1871 lines whose one theorem is circular.

So the room coordinate has a lower-bound theory (`RoomInvariant`) and no usable upper
bound. The upper bound is the missing input, and it is missing for a reason.

## The twin-prime-centre observation was an artefact

I recorded that `S = Cf - (2M-2)` equals the distance from `2M-2` to the first
twin-prime centre in 7 of 13 records, and treated that as structural. It is not, and
there is no 13-record window in which it is 7: over the seventeen replayable records
below three million it is **7 of 17**, and no natural window gives 13.

The mechanism is that `Cf` is *itself* a twin-prime centre -- `Cf - 1` and `Cf + 1` are
both prime at all seventeen records -- so `twinD <= S` holds automatically, and the two
agree exactly when there is no twin-prime centre strictly inside `(2M-2, Cf)`. That is a
question about twin-prime density, not about the recurrence.

Tested against the right null model, the empirical twin-centre gap distribution
(20931 centres below three million, median gap 102):

| window | n | expected matches | observed |
| --- | --- | --- | --- |
| M in [139, 713833] | 13 | 7.50 | 6 |
| M in [313, 713833] | 12 | 6.67 | 6 |
| M >= 139 | 15 | 7.50 | 6 |
| M >= 7 | 18 | 10.17 | 7 |

Observed is at or below expected in every window. The matches carry no signal.

Two further corrections from the same review. `Cf + 1` is the next record value
(16 consecutive pairs), but that is `AttainmentIsFree.terminal_exit_reset`, proved on
15 November -- not a new observation. And my "every record satisfies
`sum e / (3M/8) <= 0.731`" fails at `M = 13` (ratio 4.51) and `M = 43` (3.72); above the
threshold the binding record is `M = 139` at 0.7290, with 0.002 of margin.

What remains true is the reduction itself: `8(S+p) <= 3M-9` is equivalent to
`8Cf + 8p <= 19M - 25`, already in `ExcessGap.excess_criterion_iff_horizon_form`. And
`p` remains the only input no route supplies.

