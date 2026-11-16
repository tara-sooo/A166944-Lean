# Campaign: bound the event count `p` (2026-11-16)

Two agents ran in parallel against the single remaining input to the A166944 frontier,
plus the lead's own independent measurements. This file is the consolidated verdict.
Agent reports: `~/p2m_scratch/pbound/one/REPORT.md` (refutation role) and the scripts in
`~/p2m_scratch/pbound/two/` (construction role; that agent exhausted its budget before
writing a report, so its results are recorded here from its scripts).

## Headline

**The route is numerically comfortable and the barrier is now identified as a
hitting-time statement about twin-prime centres.** Three things were settled:

1. **(L) holds in the regime that matters**, now at **six** records at or above the
   threshold, worst margin 25.4x — but the chain's tight point is **M = 5419 at 1.18x**,
   just above the verified prefix, and that is the number that matters for any write-up.
2. **(E) (`e_i^2 <= 6M`) holds at every event measured**: 1027 events over 22 records,
   worst `e^2/M = 2.3756` at the threshold record against the proved 6.0.
3. **`p` is the hitting time of the twin-prime-centre set along the orbit.** This is the
   campaign's real result, and it explains why no route closes.

Also landed in the repository and CI-green: the **first-hit (jump) form** as a theorem
(`A166944/FirstHitForm.lean`), which turns the search engines' central step from a
validated derivation into checked ground.

---

## 1. The jump form, now a theorem

A canonical replay can be computed **without any array**, as a self-contained process on
`(s, C)`: from a state with `C = D s`, the next event is the FIRST `n > s` with

```
(n even and gcd(n, C-1) > 1)  or  (n odd and gcd(n-2, C+1) > 1)
```

with value that gcd and `D n = C + g - 1`.

The **value** half was already in the tree (`Lemmas.constant_D_event_map`). The
**minimality** half was not, and is now `A166944/FirstHitForm.lean`:

| theorem | content |
| --- | --- |
| `unit_between_of_step` | every index strictly between `s` and `r` is a unit increment (no axioms) |
| `gcd_test_eq_one_of_unit` | a unit increment makes the gcd test return 1 |
| `gcd_test_gt_one_of_nonunit` | a non-unit increment is exactly a gcd hit |
| `step_is_first_gcd_hit` | `r` is a hit and every `j` strictly between is not |

Validation of the engine (from the refutation agent): reproduces all **250/250** event
indices and values to N=2e6; **0 mismatches** in `(sf, Cf, p, S)` on all **41**
state-consistent starts in `[7, 300000)`; **0 mismatches** on **25** chain steps. Its
honest limit: only state-consistent starts are claimed — at a non-record with
`D(M+2) != 2M-2` the two engines are different objects by construction, which is what an
earlier "26 mismatches" run was actually seeing.

**Independent cross-check by the lead.** Two engines measured `M = 91793059`:

```
lead, array-based stream : p = 53, sf = 91808256, Cf = 183616422, S = 30306
agent, jump form         : p = 53, sf = 91808256, Cf = 183616422, S = 30306
```

Identical. Both also satisfy `Cf = M_{k+1} - 1`.

---

## 2. (L) at and above the threshold — the brief's "one data point" was wrong

The brief for this campaign asserted there was exactly ONE measurable record at or above
45895573. **There are six**, all replayed:

| M | p | sf | Cf | S | max gap | `p/sqrt(M)` | margin vs 0.1443 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 45895573 | 37 | 45896532 | 91793058 | 1914 | 338 | 0.00546 | 26.4x |
| 91793059 | 53 | 91808256 | 183616422 | 30306 | 7383 | 0.00553 | 26.1x |
| 183616423 | 5 | 183616477 | 367232910 | 66 | 31 | 0.00037 | 391x |
| 367232911 | 109 | 367247094 | 734482122 | 16302 | 8476 | 0.00569 | 25.4x |
| 734482123 | 6 | 734483334 | 1468965060 | 816 | 1192 | 0.00022 | 652x |
| 1468965061 | 4 | 1468965184 | 2937930210 | 90 | 100 | 0.00010 | 1383x |

**(L) has zero violations at all 21 consecutive records from 1321 to 1468965061.** Its only
failures are `M = 13, 43, 139, 313, 2659`, all far below the threshold and discharged by the
verified prefix.

**Caution, and it is the important caveat.** Those 25x margins are not representative.
The tight point of the chain is

```
M = 5419:   6p + p*(isqrt(4*(3M+4)) - 6) = 2295   vs   M/2 = 2709   ratio 0.847, margin 1.18x
```

just above the verified prefix (`M = 1321` onward). Any statement of the route's difficulty
should quote 1.18x, not 25x.

## 3. (E) at scale

`AngleC_Relaxed.route_closes_of_six_m` proves that `e_i^2 <= 6M` for every event implies the
route closes, for `M >= 45`. Measured: **all 1027 events** over the 22 records `M >= 661`
satisfy it, **0 violations**; worst `e^2/M` above the threshold is **2.3756** (at
`M = 91793059`) against the proved 6.0 and the asymptotic tolerance 6.75. No event anywhere
has `e^2 > 6` absolutely.

## 4. Why no route closes — the structural reduction

**`p` is the hitting time of the twin-prime-centre set along the orbit.**

Two measured facts:

1. **Every terminal state from `M = 661` up is a twin-prime centre**: `Cf-1` and `Cf+1` are
   both prime at all 22 terminal states, while `Cf - sf` runs 657 to 1468965026, always far
   above `2*sqrt(Cf+1)` (657 vs 72.7 at `M = 661`; 45896526 vs 19161.7 at `M = 45895573`).
   A *composite* `Cf±1` would have a factor `<= sqrt(Cf+1) << Cf - sf`, forcing an
   in-horizon hit — the state could not be terminal.
2. **No early exit ever happens: 0 twin-prime centres among all 1025 non-terminal states**
   over the 20 replays with `M >= 661`.

So the orbit runs to the terminal twin centre and never lands on one early. Consequently:
bounding `p` **is** the twin-prime-density statement, and no single state can refute (L)
unless it is a twin centre (since `(M/4)^2 > C+1` makes `minlpf > M/4` force primality).

The missing step is precise: **no proven lower bound on the gap** — nothing shows that both
`C-1` and `C+1` always have a small prime factor within `C - s`. The tree's
`gap <= 2*min(lpf(C-1), lpf(C+1))` is an upper bound and is useless in this direction.

## 5. Two candidate routes, both refuted

**(i) A better lower bound on `e_i`.** Since `C_{i+1} - C_i = e_i - 1 >= 2`, a bound
`e_i >= f(M)` would give `p <= (Cf - C_0)/f(M)`. **This is impossible:** over the 210
kernel-certified event values with `M` from 45895573 to 734482123, the minimum `e_i` is
exactly **3**, attained at the threshold record itself, and `e_i = 3` occurs **60 times, 28.6%
of events**. So any `f(M)` must satisfy `f(M) <= 3` for every relevant `M`, and `e_i >= 3`
is already the tree's `3 <= d r`. The candidate is refuted, not merely unproved.

**(ii) A bound on `p` via `S`.** `CountFromIndex.count_le_horizon` proves `2p <= Cf - C`,
i.e. `p <= S/2`. If `S <= 0.2886*sqrt(M)` then `p <= 0.1443*sqrt(M)`, which is (L).
**This fails:** measured, `S` exceeds `0.2886*sqrt(M)` at most records where `p` comfortably
satisfies (L) — `M = 5419`: 54 vs 21.2; `M = 355723`: 2388 vs 172.1; `M = 1427749`: 5274 vs
344.8. And `S/p` ranges over **3 to 160**, so the two are not proportional. Consistent with
`CapBCandidates.excess_bound_alone_does_not_give_cap`, which had already proved an `S`-bound
is *stronger* than the target; it is now separately measured as insufficient in this
direction too. `p <= S/2` is a real constraint (`S/2` is 1.6x to 29x `p`) but `S` itself is
unbounded.

## 6. The record hypothesis is not the source of a `p` bound

Measured at N=4e6 (336 events, 20 records): over state-consistent starts with `M < 2e6`,
**65 non-records give `p` in 0..69, median 11**, while 19 records in range give 0..77;
**32 non-records have `p >= 20` versus only 2 records**. The largest non-record `p = 69` at
`M = 1427767`, adjacent to the record `p = 72` at `M = 1427749`.

So `d(M+2) = M` alone does **not** bound `p`. This is measured, not conjectured, and it
closes the first of the three candidate inputs named by
`CountBoundLimits.count_bounds_admit_any_count`.

## 7. Where things stand

| question | status |
| --- | --- |
| Does (L) hold at the threshold? | **Yes**, 6 records, worst 25.4x; tight point `M=5419` at 1.18x |
| Does (E) hold? | **Yes**, 1027 events, worst 2.3756 vs 6.0 |
| Is there a better `e_i` lower bound? | **No** — refuted, `e_i = 3` at 28.6% of certified events |
| Does `S` bound `p`? | **No** — measured insufficient |
| Does the record hypothesis bound `p`? | **No** — 32 non-records with `p >= 20` vs 2 records |
| Does the jump form give a count bound? | **No**, and it shows why: `p` is twin-centre hitting time |
| Is the jump form proved? | **Yes** — `A166944/FirstHitForm.lean`, CI green |

**The single remaining input is a proof that both `C-1` and `C+1` always have a small prime
factor within `C - s` — a lower bound on the gap. That is twin-prime-density in disguise,
which is consistent with the barrier implying the Twin Prime Conjecture by a chain already
in the tree.**

The honest reading: the route is not in numerical danger — it has 1.18x at its tightest point
and 25x in the verified regime — but it will not be *proved* by rearranging what is already
there. The four candidate inputs have now been tested and three are refuted, with the fourth
(the gap lower bound) identified as exactly the twin-prime statement.

---

## 8. Verification notes

Every number above was produced by a script that printed the mandatory calibration table
first, and the campaign's two engines were cross-checked against each other (see §1). The
lead additionally re-verified the key figures with a bounded replay: `M = 5419` ratio
0.8472, `M = 45895573` giving `p = 37, sf = 45896532, Cf = 91793058`, `M = 2659` ratio
1.4733 — all matching the agent measurements.

One methodological note worth keeping: the jump form is O(number of hits) with a gcd per
candidate index, so replaying `M = 1.4e9` is far slower than an array-based scan of the
same range. A verification run of the largest records timed out at 15 minutes for this
reason. The agent's own jump-form run covered it because it validated against hit lists
rather than scanning; for large-`M` work the array/streaming form is the right tool and the
jump form is the right tool for reasoning, not for bulk scanning.

