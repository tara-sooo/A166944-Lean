# The 2026-11 A166944 campaign: what was established, and what remains

Twenty-two rounds against the frontier. This document is the durable summary. It is deliberately
blunt about what did NOT work, because the negative results are the campaign's main product.

## The one remaining input

Every route in the tree reduces to a single unproved statement. In the sharpest form:

    an upper bound on `S` (equivalently on `travel`, on `p`, on `L`, ...)

because those six quantities are one another up to a bounded factor (`QuantityCollapse`,
`AUDIT_MAP.md`). The frontier `2*travel <= M` is the same statement as the horizon cap
`Cf <= 3*M+4` (`FrontierIsForced`), and it cannot be weakened: the boundary is attained at
`M = 139` (travel 69 passes, 70 fails) and `M = 313` (156 / 157).

## What the campaign PROVED (all CI-green, axiom-audited)

### Structural facts about the replay

| result | module |
|---|---|
| The firing factor is carried into the next horizon, so a prime cannot fire two consecutive events | `CarryFactor` |
| **Only the prime 3 can divide two consecutive event values** (900/900 pairs measured; 18/18 exceptions match the predicted odd-then-even configuration) | `CoprimeEvents` |
| `3 \| C+-1` implies `gap <= 6`, via **first-hit minimality** rather than the value-divisibility lemma | `Mod3Gap` |
| `gap <= 2*q` for any `q` dividing the branch term; the odd branch needs `q` odd, and the necessity is itself proved | `LpfGap` |
| `C-1` and `C+1` are coprime whenever `C` is even, since they are odd and differ by 2 | `CoprimeHorizonPair` |
| `S % 6 = 0` at every terminal canonical replay (already in `AttainmentIsFree`, re-confirmed) | — |
| The window `C_f - s_f = S + (M-4) - travel` is the tree's only control, and a successful quiet return gives a LOWER bound on `S` | `WindowControlsS` |

### The collapse

| result | module |
|---|---|
| `Cf <= 3M+4  <=>  2*sf <= 3M+4  <=>  2*travel <= M`, boundary attained | `FrontierIsForced` |
| Above `M = 139` the frontier has at least **4.63x** of room; worst ratio 0.2158 | `FrontierMargin` |
| cap (B) is exactly `travel <= (3M-9)/4`, hence LOOSER than the frontier; the observed `4/7` is an artefact of `sf/M -> 1` | `CapBThreshold` |
| `S = M' - 2M + 1` exactly, where `M'` is the next record: **`S` is the record spacing**, not a function of the event values | `S_IS_RECORD_SPACING.md` |
| Six candidate quantities (`travel`, `S`, `Sum e`, `Sum q`, `L`, `p`) are one up to a bounded factor | `QuantityCollapse` |

### What is impossible

| result | module |
|---|---|
| Dropping `p` from the statement is not merely harder, it is **false**: `p=1,S=2,M=9` separates them | `DroppingPIsWorse` |
| The event-count criterion `48p^2+1 < M` **fails at `M = 2659`** (`p=11`, 5809 > 2659) while the conclusion holds there | `EventCountCounterexample` |
| The large-increment excess lemma is **vacuous on every record**: it needs `e/sqrt(M) >= 9.8`, largest observed 2.12 | `LargeIncrementInactive` |
| Route A does not bypass the `S` wall: `L/S` stays in [0.607, 1.1667], and `L <= S` is itself false at three records | `RouteADoesNotBypassS` |
| The tree's own per-step facts cannot reach cap (B); the allowance has a `p*p` and cap (B) has `3/8` | `SBoundLemma` |
| The `p`-free form `8S <= 3M-9` is much tighter (1.42x) than cap (B) (8.81x) | `DroppingPIsWorse` |

## What the campaign got WRONG, and the lessons

Six errors, all corrected in-tree with retraction commits:

1. **Claimed cap (A) could be weakened to `C <= 2M`.** It is false (`C_f = 2M-2+S`, so this needs
   `S <= 2`). Cause: read the ratio `C_f/(2M) = 1.0188` as "close to 1, so it holds", when a ratio
   above 1 is the NEGATION of the bound. **Lesson: substitute into the identity before comparing
   ratios.**
2. **Claimed the frontier alone produces the window, so no `S`-bound is needed.** It is a special
   case of `QuietReturn.long_quiet_gap_of_short_travel`, which is **`private`** and therefore
   invisible to a grep for public lemma names. **Lesson: grep `private theorem` too.**
3. **Diagnosed a failed proof as "omega's limitation" when the lemma was one unit too weak.** The
   strict inequality needed `M/2 - 5`, not `M/2 - 4`. **Lesson: "the tactic will not do it" and
   "the lemma is off by one" look identical from omega's output.**
4. **Asserted `2*Sum q <= M/2` "at every record"** when the record list started at `M = 661`; it
   fails at 13 and 43. **Lesson: check the minimum of the list before writing "every".**
5. **Claimed eleven campaign findings as new** when six were already in the six `Audit*.lean`
   modules (56 declarations) written earlier. **Lesson: read `Audit*` first.**
6. **Wrote wrong numerals in docstrings twice** (`13*33 = 429 <= 313` described as "fails";
   `103043050` for `103032650`; inequality directions reversed; `1167` for `1166`). Each caught by
   `decide` refusing the claim. **Lesson: `decide`/`omega` failure is a truth signal, not just a
   tactic problem.**

Two resource failures of a different kind: repeated overlapping heavy Python scans crashed the
device four times, and `pkill -f` matched and killed the agent's own shell twice. Both are recorded
as operational lessons (`job_output` waits without freeing the process; `pkill -f` self-matches).

## The structural conclusion

`S = M' - 2M + 1`, and every record `M >= 7` is the larger member of a twin prime, with `C_f +- 1`
both prime at 26 of 26 records. So the frontier is a bound on **the twin-prime gap above `2M-2`**
-- a relative gap of 0.19%, far weaker than any quantitative twin-prime statement, but still
requiring a mechanism the tree does not have.

The campaign found no such mechanism. What it did establish is that **no rearrangement of the
existing tools can produce one**: every quantity collapses to the same one, every route is
downstream of the same statement, and the margin is large enough that the obstruction is purely
the absence of a mechanism.

## Where a future attempt should start

Not with another change of variable, and not with another bound on `S`. The two directions the
campaign did not exhaust:

1. **`MinFactorSumBoundFrom`** (`4L <= M`) is the only frozen statement whose hypothesis is written
   in a different arithmetic (`min(lpf)` sums rather than `(e-1)` sums). `RouteADoesNotBypassS`
   shows `L` and `S` collapse anyway on the RECORDS, but that is a measurement, not a theorem —
   if `L` had better structure at the per-step level, the argument would have to be per-step, not
   per-record.
2. **The stop condition forces a twin-prime centre.** A proof that the replay cannot stop at a
   composite `C_f +- 1` for a structural reason would close the frontier. `FACTS.md` §5 records why
   the obvious attempt (large prime factors) fails, but the `S_n % 6 = 0` and coprime-horizon
   constraints show the terminal state does have exploitable arithmetic.
