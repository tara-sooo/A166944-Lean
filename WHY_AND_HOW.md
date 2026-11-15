# Why the barrier could not be proved, and how it could become provable

Written 2026-11-16. Every number below was measured by a replay script that was
**calibrated against the kernel-certified literals** before reporting anything
(`M = 13 -> Cf = 42, S = 18, sf = 24, p = 4`; `M = 43 -> 138, 54, 79, 6`;
`M = 139 -> 312, 36, 156, 2`; `M = 313 -> 660, 36, 348, 6`).  All four reproduce
exactly.  Scripts: `~/p2m_scratch/frontier/`.

---

## 1. The first answer: the hypothesis is Twin-Prime-Conjecture strength

This is not a metaphor.  It is a proved chain in the tree:

```
CanonicalTravelBoundFrom 22933441   (2*(sf-(M+2)) <= M)
  --target_of_travel_bound_from_22933441-->   Target
Target = forall R, 5 < R -> IsDifferenceRecord R -> R.Prime /\ (R-2).Prime
  --unbounded_greater_twin_primes_of_target-->  forall M, exists R > M with R, R-2 prime
```

and `difference_records_unbounded` (`RecordBarrier.lean:266`) is unconditional.
So the frontier hypothesis **implies the Twin Prime Conjecture**.  Whatever is
written at the top of the development is at least as hard as TPC.

That is the honest reason no route has closed, and it is not fixable by any
rearrangement.  The 16 closed routes are the symptom; this is the cause.

**But this alone is too coarse to be actionable.**  TPC-strength does not say
*where* the difficulty is.  The rest of this file locates it.

---

## 2. What is actually missing: a count bound, in one of two equivalent forms

Every live route reduces to bounding a **count of indices**, not a magnitude.

| route | hypothesis | where |
| --- | --- | --- |
| event count | `48*p*p + 1 < M` | `TravelTarget.lean:89` |
| six-cover | `exists cover, ... 2*(6p + cover.length*(isqrt(4*(3M+4)) - 6)) <= M` | `TravelTarget.lean:119` |
| cover <= p | the six-cover form with `cover.length <= p` | — |

**These two are the same inequality.**  With `cover.length <= p` the six-cover
budget is `2*p*(6 + isqrt(4*(3M+4)) - 6) = 2*p*isqrt(12M+16) <= M`, i.e.
`p <= M/(2*isqrt(12M+16))`.  Numerically:

```
M = 45895573   six-cover pmax =   977.87    48p^2 pmax =   977.83   ratio 1.0000
M = 1e12       six-cover pmax = 144337.59   48p^2 pmax = 144337.57   ratio 1.0000
```

So the development's "thirteen entry points" collapse, at the quantitative level,
to **one** unproved bound: `p ≲ sqrt(M)/7`.

`REACH.md` and `GATE_MAP.md` already say "one uniform bound"; what is new here is
that the bound is a *count* bound with a measured margin, and that its two natural
forms are the same statement.

---

## 3. Why the present toolkit cannot supply it

### 3.1 Every local property of an event is already extracted

Per event the tree has: `e | C+-1`, `3*e <= C+-1`, `e <= M`, `e >= 3`,
`C' = C + e - 1`, `gap <= 2*min(e, cofactor)`, `e | C'` (carry),
`gcd(e_i, e_{i+1}) | 3`.  Verified to hold in the replay: `gcd(e_i,e_{i+1}) <= 3`
in **215/215** consecutive pairs; `carry` in 152/230 (the exceptions are exactly
the `e = 3` odd-branch cases, which is `ConsecutiveEventGcd`'s content).

Nothing else is available locally.  A count cannot be bounded by local data.
This is the structural reason the 16 routes closed: they all try to *sum* local
data, and every sum is either vacuous or circular.

### 3.2 The three published negative results are the real obstruction

1. `OrphanHarvest.count_index_route_is_vacuous` — `travel <= p*sqrt(C)` and
   `p + M <= sf + 1` hold simultaneously for **every** `sf`.  So the sqrt route
   bounds nothing, at any constant.
2. `CapBCandidates.excess_bound_alone_does_not_give_cap` — a bound on `S` alone
   is *stronger* than the target.  Every "bound S" angle assumes what it proves.
3. `RecordInductionFails.cap_does_not_transfer_along_records` — the cap holds at
   `M = 7` and fails at `M = 13`, so induction on records must carry the
   hypothesis below the threshold, where it is false.  Infinite descent has no
   decreasing quantity (`R' = 2R - 1 + S` increases).

### 3.3 The stopping condition of the replay is itself twin-prime-flavoured

This is the sharpest reason, and it is measured, not inferred.

The replay stops when no event exists in `(s, C]` (the **quiet** branch), and the
quiet branch is the only one that leads to the primality certificate.  It needs
`2*isqrt(Cf+1) < Cf - sf`, which forbids any factor of `Cf+-1` below
`isqrt(Cf+1)` — i.e. it forces `Cf - 1` and `Cf + 1` to have **no small factor**.

Measured: at **all 17 replayable records**, `Cf - 1` and `Cf + 1` are both
**prime**.  And `AttainmentIsFree.terminal_exit_reset` proves `Cf + 1` is the next
record value.  So the replay terminates exactly at a twin-prime centre.

You cannot bound the length of a search whose termination criterion is "find a
twin centre" without twin-prime input.  That is the same statement as §1, now
localized: **the missing lemma is not about the recurrence, it is about twin
primes.**

---

## 4. Two routes that are numerically viable — and what each still needs

Both are stated as a single lemma each.  Both have measured margin at every
record above the threshold.  Neither is proved.

### Route A — the least-prime-factor sum  (new)

From `HalfWindow.gap_le_twice_min_factor`, `gap <= 2*min(e, cofactor)`, and
`min-lpf(C-1, C+1) | e` on the relevant branch:

```
travel <= 2 * Sum_i min( lpf(C_i - 1), lpf(C_i + 1) )
```

**Measured: holds at 17/17 records.**  And `2*Sum <= (3M-9)/4` holds at 15/17 —
it fails only at `M = 13` and `M = 43`, both **below** the `45895573` threshold the
top of the development already uses.  (Note the two conditions differ: the
inequality `travel <= 2*Sum` itself holds at 17/17 including `M = 13` and `43`.)

So the target lemma is (the `/8` is forced: `travel <= 2*Sum` and
`travel <= (3M-9)/4` give `2*Sum <= (3M-9)/4`):

```
Sum_i min( lpf(C_i - 1), lpf(C_i + 1) )  <=  (3M - 9) / 8
```

Measured `Sum / ((3M-9)/8)`: 0.016 at `M = 355723` (2129 vs 133395, margin
62.7x), 0.0095 at `M = 1427749` (5076 vs 535405, margin 105.5x).  The tightest
record is `M = 139` at 0.235 (margin 4.2x).

**Why it is hard:** `min-lpf` is unbounded along the replay (max observed 1129 at
`M = 1427749`, 719 at `M = 355723`), so no constant bound exists, and the
existing `LeastDivisorRoute` refutes the tight forms (`gap <= lpf + 2` is false at
`(51,96) -> (60,100)`; the summed form fails at `M = 13`).  The lemma needs a
genuine statement about the *distribution* of small factors of the specific
sequence `C_i +- 1` the recurrence generates — not about the recurrence.

### Route B — the six-cover count  (already in the tree)

`TravelResidues.moving_horizon_path_travel_by_six_cover` splits travel as
`6*(even/rough part) + cover.length * (isqrt(4*(U+1)) - 6)`, where

```
cover  =  { j : IsReplayEventStart, 6 | D j }        (the "rough" states)
```

and the non-covered states satisfy `6 !| C`, hence `gap <= 6`
(`moving_horizon_gap_le_six_of_six_not_dvd`).  The consumer
`record_index_and_twin_prime_of_six_cover_from_45895573` is already wired to
`Target`.

So the target lemma is a **pure count**:

```
cover.length  <=  (M/2 - 6p) / (isqrt(4*(3M+4)) - 6)   ~=  0.1443 * sqrt(M)
```

Measured:

| M | cover | allowed `0.1443*sqrt(M)` | margin |
| --- | --- | --- | --- |
| 2659 | 6 | 7.4 | 1.24x |
| 5419 | 6 | 10.6 | 1.77x |
| 10891 | 8 | 15.1 | 1.88x |
| 355723 | 33 | 86.1 | 2.61x |
| 1427749 | 44 | 172.4 | 3.92x |
| 2860771 | 50 | 244.1 | 4.88x |

**The route closes numerically at every record `>= 1321`.**  The full budget
`2*(6p + cover*corr) <= M` holds at every record from `M = 1321` upward.

Measured `cover/sqrt(M)` : 0.116 at `M = 2659`, falling to 0.030 at `M = 2860771`.
The allowed 0.1443 is therefore not tight — but it is not implied by anything in
the tree either.

**Why this is the better route:** the missing input is a count of a *definable,
decidable* set of indices, not a number-theoretic magnitude. It is the only route
whose gap is a counting statement rather than a factorisation statement.

---

## 5. The mod-3 structure — real, but already exploited

Measured and worth recording:

* **Every** difference record `M > 5` satisfies `M ≡ 1 (mod 3)` (18/18), and its
  index satisfies `n = M + 2 ≡ 0 (mod 3)`.
* `C_0 = 2M - 2 ≡ 0 (mod 3)` at every record start, and the terminal state always
  has `3 | Cf` (this is `CanonicalRecord.fundamental_point_mod_six`, proved).
* Along a replay, `C mod 3` takes value 0 in 189/315 states, 1 in 120, 2 in 6 —
  strongly biased but **not** an invariant: `3 | C` propagates to `3 | C'` in only
  80 of 189 cases.
* The rough states (`3 | C`, equivalently `6 | D`) carry **79% to 97.5%** of the
  travel at large `M`.  The smooth states contribute `<= 6` each.

So the mod-3 split *is* Route B, and the tree already knows it.  Recording it here
so it is not rediscovered a fourth time.

---

## 6. What would actually move the barrier

Ranked by (chance of success) x (value if it succeeds).

1. **State and attack Route B's count lemma.** It is a count, the consumer is
   already wired, the margin is 1.2x-5x, and the route closes numerically at every
   record above 1321. The lemma to prove:
   `#{ j < sf : IsReplayEventStart, 6 | D j } <= (M/2 - 6p)/(isqrt(4*(3M+4)) - 6)`.
   Anything that bounds how often the horizon can be divisible by 6 while the
   increment stays bounded is progress.

2. **State Route A's sum lemma.** New, has 4x-105x margin, fails only below the
   threshold. The lemma is `Sum min(lpf(C_i-1), lpf(C_i+1)) <= (3M-9)/8`. It
   requires new number theory about small factors, so it is harder than 1, but its
   margin is far larger.

3. **Accept the conditional result and publish it.** The reduction
   `a166944 -> TPC` is already `SKETCH_ACCEPTED` on the v4.33.1 tree, and the
   finite prefix reaches `11751795063`. A conditional theorem plus a verified
   finite range is an honest, complete, publishable artifact. It is not a proof of
   the conjecture, and the outstanding transplant (post the definitions and the
   child theorem in the v4.29 environment, submit against `a3b92c39`) is what
   makes it visible on the mission.

4. **Do not attempt:** anything that bounds `S`, any coordinate change among
   `S / travel / B / room / slack`, any route through `sqrt(C)`, and induction on
   the record sequence. All four are proved insufficient in the tree itself
   (§3.2). Further attempts cost effort and return nothing.

---

## 7. The one-sentence answer

The barrier cannot be proved because it **is** the Twin Prime Conjecture in
disguise (§1) — and more precisely, because the canonical replay terminates
exactly at a twin-prime centre (§3.3), so the missing input is not a fact about
the A166944 recurrence at all but a fact about the small-factor structure of
`C_i +- 1`. The two live targets are a factorisation bound (Route A) and a pure
count of `6 | D j` indices (Route B); both hold numerically with margin at every
record above the threshold, and neither is implied by anything currently in the
tree.
