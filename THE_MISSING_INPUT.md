# The missing input, stated precisely — and where the wall is

Campaign record, 2026-11-16 (goal `goal-b5d40fe9`). Supersedes the loose phrasings in
earlier notes. Every number here is measured with the calibration table printed first and the
engine cross-checked against the certified replays; every Lean claim named below is
CI-green.

## 1. The target, in its weakest known form

The frontier is `travel <= M/2` where `travel = sf - (M + 2)` at a canonical start `M`.
Four sufficient conditions, each measured at every record:

| condition | where it lives | worst ratio | margin |
|---|---|---|---|
| cap B: `4*sf <= 7*M - 1` | consumer `canonical_next_record_factors_of_two_caps_tight` | 0.6356 (M=313) | 1.57x |
| `S + p <= (3*M - 9)/8` | `CapBCandidates.capB_of_excess_sum` | 0.3613 (M=313) | 2.77x |
| `S <= (3*M - 9)/12` | follows from the above plus the proved `2*p <= S` | 0.4645 (M=313) | 2.15x |
| `48*p*p + 1 < M` | `CanonicalTravel.canonical_travel_bound_of_event_count` | 1.39x (M=5419) | — |

cap A (`S <= M + 6`) has 26x margin and is implied by cap B for large `M`
(`(3M-9)/8 <= M+6`), so **cap B is the binding condition**.

### Exact identities (verified at every record)

```
S = C_f - (2*M - 2) = sum(e_i - 1)
S + p = sum(e_i)                        <- cap B IS a bound on sum e_i
C_f = M_next - 1                        <- the next record
```

Hence cap B is equivalent to

```
M_next + p <= (19*M - 17)/8 ,     measured  M_next/M ~ 2.0000  against the allowed 2.375.
```

## 2. Where the wall is

**Every record `M >= 7` is the larger member of a twin prime.** Verified on all 27 records:
`M - 2` and `M` are both prime. (`M = 3` is the sole exception, `M - 2 = 1`.)

Why: at the terminal state, the window `W = C_f - s_f` is long, and the stop condition forces
every prime `q | C_f -+ 1` to satisfy `q > W/2`. Since `W/2` vastly exceeds `sqrt(C_f)`
(657 against 72.7 at `M = 661`), both `C_f - 1` and `C_f + 1` are prime. And `C_f = M_next - 1`.

So the record sequence is a subsequence of the twin-prime centres (as larger members), and

> **cap B is a bound on the twin-prime gap above `2M - 2` — a RELATIVE gap of 0.19%.**

That is far weaker than any quantitative twin-prime statement, which is why the wall is here
and not at twin primes in general. The remaining question is whether the replay's own dynamics
force such a centre to appear, with no prime-gap input.

## 3. The distance, stated exactly

Using only tree lemmas — `p <= travel` (`BindingCoordinate.canonical_p_le_travel`) and
`S <= 2*travel + 6` (`excess_le_two_travel_add_six`) — we get `S + p <= 3*travel + 6`, and
cap B follows from `travel <= (3M - 57)/24`. The tree proves `travel <= M/2`. The ratio
`(M/2) / ((3M-57)/24) = 4M/(M-19) = 4.0000` at every large record.

The same factor 4 arises independently from `2p <= S`: `S + p <= 1.5*S <= 3*travel + 9` gives
`travel <= (M-27)/8`, again 4x short. Two independent derivations agreeing on 4.0 is what makes
this the trustworthy number.

**And `S <= 2*travel + 6` is TIGHT at `M = 22933441`** (`S = 28692 = 2*14343 + 6` exactly), so
that lemma cannot be improved at that record. A factor-4 gain must come from somewhere else —
most plausibly a *lower* bound on `travel`, which is the one direction not yet attacked.

## 4. What the tree's own facts provably cannot do

`A166944/SBoundLemma.lean` (CI-green, axiom-free) settles a whole family:

* `chain_allowance_dominates_capB` — the allowance obtainable from the tree's per-step bound
  `3*e_i <= C_i + 1` plus the count bound has constant `p*p`, and dominates cap B's `(3M-9)/8`
  for every `p >= 1`. At `p = 1` it is already strictly weaker.
* `at_thirteen_chain_does_not_give_cap` — a kernel certificate that at the certified data
  `(M,p,S) = (13,4,18)` every fact the chain supplies holds while cap B is FALSE (176 vs 30).
* `canonical_start_threshold_is_necessary` — cap B fails at `M = 13` and `M = 43`, holds at
  `M = 139` and `M = 313`. Any uniform proof must carry an explicit `M`-threshold.
* `p_free_form_fails_at_the_small_starts` — the `p`-free form `4*S <= M - 3` is FALSE at
  `13, 43, 139` too, so the count `p` cannot be dropped.

Caveat preserved from the author: these are statements about an *unbounded* cap-B proposition,
not about any gate the repository actually consumes (those are quantified at `22933441` and
`45895573`, far above the starts where the failures occur).

## 5. Refuted routes (measured; do not retry)

| route | witness |
|---|---|
| `e_i = lpf(C_i -+ 1)` | false; `e` is the gcd at the FIRST multiple (81.1% agreement only). The lpf-walk reproduces the true walk in 4/21 records |
| adjacent coprimality extends to distance >= 2 | 9974/55775 = 17.9% of far pairs share a factor |
| coprimality bounds `p` from above | it bounds `p` from BELOW (`prod e <= 3^(p-1) max e` with `e_i >= 2`) |
| truncate `sum q` at small primes | primes `q <= 100` give 16.5% of `sum q`; `q > 1000` gives 97.1% of `S` at M=91793059 |
| counting argument `sum_{q in Q} W/(2q)` | overshoots `p` by 900x-2700x |
| `max e_i <= K*sqrt(M)` | worst 5.03 at M=43; even for `M >= 968`, 2.12 at M=22933441 |
| `p*max_e <= 3M/8` | false, worst 12.28 at M=43 |
| per-step `e_i <= C_i/k` for any `k >= 4` | `C_i // e_i` reaches 2.4e8 at M=367232911 |
| `travel >= S`, `S+p <= 2*travel` | false; first witness `(n,C,e,gap) = (17,24,5,2)`; worst 1.2667 at M=139 |
| `S` and `p` tightly coupled | `S/p` spans 4.5 to 571.8; neither bounds the other |
| the record ratio as an independent route | it is the same statement: exactly `S <= (3M-8)/8` |

## 6. A correction to a shared data table

A subagent's linear scan reported `734491369` as the 27th record. **That is wrong.** Three
independent confirmations:

1. The repository already KERNEL-PROVES `734482123`:
   `VerifiedLaterRecordExtension.next_record_after_367232911` gives `d 734482125 = 734482123`.
2. Canonical jump-form replay from the kernel-certified `M = 367232911` gives
   `Cf = 734482122`, hence `M_next = 734482123`.
3. Forward replay from `734482123` gives `Cf = 1468965060`, `M_next = 1468965061`, matching the
   repository's kernel-certified `returnBefore1468965061_accepted`.

The correct record list through the verified prefix is therefore

```
3, 7, 13, 43, 139, 313, 661, 1321, 2659, 5419, 10891, 22039, 44383, 88801, 177841,
355723, 713833, 1427749, 2860771, 5725453, 11461141, 22933441, 45895573, 91793059,
183616423, 367232911, 734482123, 1468965061
```

**Method note:** use the jump form to verify a record table, never a long linear scan. The jump
form derives `M_next` directly from `M`; a linear stream to `n = 7.9e8` accumulates state error
and cannot be trusted at its boundary values without independent re-verification.


---

# Round 2 (2026-11-16, later): the minimality technique, and why every route converges

## A new provable per-step bound, and the technique behind it

`A166944/Mod3Gap.lean` (CI green) proves, core-only and axiom-free:

```
gap_le_six_of_three_dvd_even : (3 | C-1)  =>  r - s <= 6
gap_le_six_of_three_dvd_odd  : (3 | C+1)  =>  r - s <= 6
```

Measured 362/362 steps with zero exceptions before proving. The mechanism is NOT the tree's
`gap <= 2*v`: that lemma requires `3` to divide the EVENT VALUE, which `3 | C+-1` does not
force. It is **MINIMALITY of the event index** (`FirstHitForm.step_is_first_gcd_hit`): no `j`
with `s < j < r` passes the gcd test, so exhibiting one admissible `j <= s + 6` suffices. On the
even branch any even multiple of 3 works; on the odd branch take `j` odd with `3 | j - 2`. Both
exist among any six consecutive integers, by a mod-6 case analysis with concrete witnesses.

**This minimality technique is the most reusable finding of the round**: it converts a *lower*
structural fact (a small admissible index exists) into an *upper* bound on `r`, which is the
direction the campaign lacked. It generalizes from `3` to any odd prime `q`, giving
`gap <= 2*q`; that generalization is being landed separately.

## Supporting structure measured

* **`C` is even at every state** (903/903). Hence `C - 1` and `C + 1` are both odd, hence every
  divisor `q >= 2` of either is ODD (measured `q % 2 = 1` at 903/903), so `q = 2` never occurs
  (908/908). A parity hypothesis in the general lemma is therefore implied on this orbit.
* **`C mod 3` never (or almost never) equals 2**: pooled over 926 states, `C%3=0` 60.9%,
  `C%3=1` 37.0%, `C%3=2` only 2.1%. Follows from `M%3 = 1` (records are twin-prime larger
  members) giving `C_0 = 2M-2 = 0 mod 3`, and then `C' = C + (e-1)` stays in `{0,1}` unless
  `e = 0 mod 3`.
* **`q = 3` fires exactly when `3` divides the branch term**: 345/345 agreement, no exceptions.

## Why every route hits the same wall — the convergence theorem

This is the round's most important negative result, and it is measurable in three lines:

```
Sigma q <= 2*S                      holds at EVERY record (worst ratio 0.5833 at M=5419)
Sigma q / S in [0.47, 1.17]
travel / S in [0.50, 1.39]          (pooled 0.61)
travel <= 2 * Sigma q               (from the per-step gap <= 2q)
```

So `travel`, `Sigma q`, `S`, `Sigma e`, `Sigma min lpf` and `M_next` are **all the same quantity
up to a bounded factor**. Introducing any of them as a new target does not lower the difficulty;
it renames it. This is why the campaign has repeatedly re-derived the same wall.

Two concrete consequences:

1. **`Sigma q <= M/4` cannot be reached through `S`.** From `Sigma q <= 2S` and (hypothetically)
   `S <= (3M-9)/12` one gets `Sigma q <= (3M-9)/6`, and `(3M-9)/6 <= M/4` only for `M <= 6`.
2. **`Sigma q / p` grows without bound** (7.00 at M=1321 -> 521.9 at M=91793059), so no
   `Sigma q <= c * p` for a constant `c` can exist. Any bound must be in terms of `M`.

## Still open

`Sigma q <= M/4` (equivalently any of the earlier forms). What is known about it: it cannot be
bounded by `c*p`; small-prime truncation fails (`q <= 100` gives 16.5% of the sum, and `q > 1000`
gives 97.1% of `S` at M=91793059); the largest contributions come from large `q` at large
records (`q = 12433` at M=91793059). The many small gaps do not help: `gap <= 6` holds at 63.1%
of steps, yet at M=22933441 over 94% of `travel` sits in the 72 gaps above 6.
