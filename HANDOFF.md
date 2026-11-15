# Handoff: state at the end of the 2026-11-15 session

Written because the session is being restarted. Everything below is verified against the
repository and the live APIs; nothing is projected.

## Repository

```
branch   main, clean, HEAD 626e9a1
size     172 modules, 2504 declarations
CI       A166944 canonical verification: success on 2de8437
guard    DECLARATIONS.json + the explicit module list in verify.yml, both 170
```

## What is proved, and what is not

The barrier is a single inequality and it has not moved:

```
cap (B)   4 * sf <= 7 * M - 1
  <=>     travel <= (3M - 9) / 4              RelaxedCap / CapBCandidates
  <=>     Sigma e_i <= (3M - 9) / 8
  <=>     Cf + p <= (19M - 25) / 8            ExcessGap.excess_criterion_iff_horizon_form
```

**The slack is not where I said it was, and this is corrected.** I reported a margin of
7x to 10000x from `travel / M` running 0.00007 to 0.108 against an allowance of 0.75. That
is the wrong coordinate. The cap's own normal form is `Cf + p <= (19M-25)/8`, and there
the ratio converges to about 0.8421 from above -- worst case `M = 139` at 0.9602, a margin
of **3.98 percent**. The travel coordinate looks roomy only because `Cf ~ 2sf ~ 2M`
dominates and travel is lower order.

`BindingCoordinate.lean` records this, along with why the obvious toolkit closes:
`cap <-> 16 travel + 8p + 57 <= 3M + 8 r2` where `r2 = 2sf - Cf`, so the cap needs the
state slack to pay twice the travel, and a state bound supplies only `r2 >= 0`. The
deficit `19M - 25 - 8(3M+4) = 5M + 57` grows linearly for every `M`, so
(state bound) x (index cap) cannot reach the joint form at all.

The difficulty is still not the inequality's size. It is that the one input every route needs -- an upper bound on the event
count `p`, independent of `sf` -- cannot be supplied, and
`OrphanHarvest.count_index_route_is_vacuous` proves that the obvious combination
(`travel <= p * sqrt(C)` plus `p + M <= sf + 1`) holds for **every** `sf`, hence bounds
nothing.

Sixteen routes have been closed. The useful record of why is `ANALYSIS_WHY_STUCK.md`
(225 lines), which now also records five of my own errors from this session:

1. the square-root route was already in the tree and already closed;
2. `room_f <= M` fails in 8 of 13 records, so `S` and `travel` are unordered;
3. `Attempt.lean`'s room bound is a tautology (its hypothesis contains the conclusion);
4. the twin-prime-centre coincidence is an artefact (observed <= expected under the
   correct null model);
5. `sum e / (3M/8) <= 0.731` fails at `M = 13` and `M = 43`.

## The barrier, in its smallest form (new, and verified independently)

`S` is not determined by twin primes. It is determined by the Rowland excess at the
doubling index. Over all fourteen replayable records below 3.2 million,

```
Cf = D (2M - 2)        and        S = E (2M - 2)
```

where `D n = a n - n` and `E n = a n - 2n`. `DoublingReadoff.lean` carries this.

The reading index `2M - 2` is **larger** than the replay's own final index (at `M = 139`,
276 against 156), so `S` is not a function of where the replay stopped. That is why the
twin-prime-centre reading was wrong for a structural reason, not just by counterexample.

The cap `S <= (M+4)/2` becomes `2 * E (2M-2) <= M + 4`, which follows from
`4 * E n <= n` at `n = 2M - 2`. The repository's global result `a n <= 3n` gives only
`E n <= n`. **The gap is a factor of four and it is attained** -- `E 18 = 18` and
`E 156 = 156` -- so no global growth bound can be improved to close it.

So the barrier is now a single statement about one window:

```
D increases by at most C/2 + O(1) across the doubling window [C, 2C]
equivalently, the mean of d over (C, 2C] is at least 3/2
```

Measured, that mean is 2.00006 to 2.11538. But `E 18 = 18` shows `d` can spike locally,
which is why every global estimate falls short by exactly this factor.

## The three most recent findings

**The gap is tiny and that is structural.** Measured over 305 events, `gap / (C - s)`
has median 0.00001 and maximum 0.0705. The mechanism is hit density: a `j` is a hit when
`gcd(j, C-1) > 1` (even) or `gcd(j-2, C+1) > 1` (odd), and that density runs from 4.6 to
28.8 percent, because the horizon factors carry many small primes. So the event is
almost always close to where the previous one ended.

**But no bound on the gap in terms of `M` is available.**
`HalfWindow.gap_le_twice_min_factor` and `LeastDivisorGap.least_divisor_gap_bound` both
bound the gap by twice a divisor of `C +- 1`, and that divisor can be as large as
`sqrt(2M)`. `gap <= lpf + 2` is **false** -- refuted by `(51,96) -> (60,100)` where the
least nonunit divisor of 95 is 5 and the gap is 9. The factor 2 is needed.

**`Cf` is always a twin-prime centre.** `Cf - 1` and `Cf + 1` are both prime at all 17
replayable records, and `Cf + 1` is the next record value
(`AttainmentIsFree.terminal_exit_reset`). But this does not bound `Cf`: the replay skips
intervening twin centres (at `M = 1427749`, the first centre above `2M-2` is 234 away
while `S = 5274`).

## Unfinished work, with locations

```
~/p2m_scratch/sq2/F.lean         17 theorems on twin centres; does not build in the
                                 core-only environment (by_contra, free variables,
                                 omega). Recoverable but needs porting work.
~/p2m_scratch/sq3/               scans only, no Lean
~/p2m_scratch/aG/, aE2/, aF/     earlier angle work, already integrated or refuted
~/p2m_scratch/tr1/port/          the v4.29 port, now on main as Isqrt.lean + repointed
                                 modules; verified 98/98 under the real v4.29 toolchain
```

## Environment rules learned the hard way

* **Do not build v4.29 locally.** Two independent downloads produced 9.8 GB and filled
  the disk to 91 percent. v4.29 verification belongs in CI (`verify-v429.yml`), which
  installs the toolchain alongside the repository's own and builds the core-only modules
  with the toolchain's `lean`, no lake.
* Regenerable Mathlib side artifacts (`*.private`, `*.server`, `*.trace`, `*.sig`,
  `*.hash`) are 3.7 GB of the 7 GB in `prove2me_workspace/.lake` and can be deleted
  freely; `olean`/`ilean`/`ir` are what the local `LEAN_PATH` checks need.
* Local checks do not apply the lakefile's `autoImplicit = false`. Use
  `~/p2m_scratch/check-module.sh <Module>`, which passes `-DautoImplicit=false`, before
  committing; two commits failed CI for this.
* `by_contra` is unavailable in the core-only environment used by several modules.

## Prove2Me

```
trust 7, 25 submissions, 8 accepted
published  8 A166944 theorems, all Open, all with mission_id None
reduction  ae8d1775 to 185e92b6 (v4.33.1 twin_prime_conjecture): SKETCH_ACCEPTED
mission    6285dbe8 "The Twin Prime Conjecture"
           main_theorem a3b92c39 (v4.29.0-rc3)  <-- our work is NOT in this tree
proposal   50448118, Draft, human submission only
```

The outstanding task is the v4.29 transplant: post the Definitions bundle and the child
theorem in the v4.29 environment and submit the reduction against `a3b92c39`. The
technical blocker is gone -- `Isqrt.lean` is core-only and 98 of 98 core modules build
under v4.29 -- what remains is the submission itself.

## The honest summary

The barrier has not moved in this session. What has changed is that the reasons are now
recorded, five of my own errors are corrected in the repository rather than in a
transcript, and the v4.29 port is done. The next honest step is either the transplant
submission or a genuinely number-theoretic input about the small-prime structure of
`C_i +- 1`; no amount of further rearrangement of the existing inequalities will help.
