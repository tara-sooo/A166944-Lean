# A166944 Lean research

A public Lean workspace for investigating OEIS A166944.

The long-term target is the conjecture formalized as `OeisA166944.conjecture` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
This repository is **research in progress**: it contains kernel-checked partial
results and reproducible experiments, not a claimed proof of the open conjecture.

Parent research tracker and final integration gate: [Issue #1](https://github.com/tara-sooo/A166944-Lean/issues/1).
Focused research tasks will use separately assigned child Issues as they are created. **No child Issue is implied to exist merely because a lane is proposed below.**

## Current structure

- `A166944/ResearchDefs.lean` — ultra-light recurrence and record definitions.
- `A166944/Lemmas.lean` — reusable Lean-verified lemmas only.
- `A166944/Attempt.lean` — active lightweight proof-search/checkpoint file.
- `A166944/TargetDefs.lean` — prime-dependent target definitions.
- `A166944/Bridge.lean` — bridge from the lightweight definitions to the pinned Formal Conjectures definitions.
- `A166944/Baseline.lean` — canonical upstream target/axiom baseline.
- `AGENTS.md` — correctness and research rules for Codex/LLM-assisted work.
- `RESEARCH_PROTOCOL.md` — external-status, novelty, semantic-fidelity, and correction checks.
- `PROVENANCE.md` — AI/tool provenance and audit ledger.

## Current research position

The current attack studies the recurrence through

- `d(n) = a(n) - a(n-1)`,
- `D(n) = a(n) - n`,
- `B(n) = a(n) - (2n-2)`,

with particular attention to difference records, fundamental points, constant-`D`
intervals, and moving-horizon first-event dynamics.

The latest canonically verified milestone is **5E.3.20**, on
[commit `003e77780ce84a76bbd65811348f2d94f6e19c30`](https://github.com/tara-sooo/A166944-Lean/commit/003e77780ce84a76bbd65811348f2d94f6e19c30)
([successful Actions run 34339879873](https://github.com/tara-sooo/A166944-Lean/actions/runs/34339879873)).
Verified infrastructure includes moving-horizon first-event paths; a mixed
event/gap ledger with exact event count, sum and displacement bounds;
canonical pre-record and post-record factor/coupling identities;
the last-old-event / critical-record / first-post-record transition package;
and conditional fundamental-point regeneration. The basic event bound
`d(r) ≤ C - s` also remains available for a first event from state `(s,C)`.

The remaining **5E.3 critical obstruction** is to rule out the `q = 3` and
`q = 2` quotient families using **ordered, actual canonical-origin recurrence
ancestry**, beyond aggregate scalar identities and local factor conditions.
Known scalar survivors are diagnostic arithmetic assignments, **not** actual
A166944 recurrence paths. No quotient family has been universally eliminated.

The record-index work branch proves that difference records are unbounded.
`A166944/RecordBarrier.lean` bounds the index of a record above any threshold
by an explicit least common multiple. `A166944/CanonicalRecord.lean` proves
that the full index theorem is equivalent to excluding a larger first hit
inside the horizon of a capped replay from a canonical record.

On that branch, `lake build A166944.TwinReserveTarget210` checks the position
and twin-primality theorems for all strict record values `5 < R ≤ 91793059`.
The replay certificates establish the horizon bound for canonical
previous records `968 ≤ M < 22933441` and the stronger short-travel
bound on the interval from `M=22933441` to its next record.
`VerifiedFiftyMillionBridge.lean` checks the 37-event replay from that
next record, `45895573`, to `91793059` at index `91793061`.
`VerifiedRecordExtension.lean` checks the next two replays with 53 and
5 nonunit events. It proves the position and twin-primality statements
for all strict records `5 < R ≤ 367232911`. The travel bridge
`twin_travel_from_367232911` reduces the unrestricted targets to short
travel from canonical greater twin primes `M ≥ 367232911`.
`TravelResidues.lean`
gives a sufficient budget that treats event starts at horizons divisible
by six separately. `TravelFactors.lean` bounds long gaps ending in
composite increments by horizon growth and gives a necessary amount of
remaining travel at a first crossing. `lake build A166944.TravelFirstUse`
checks that long gaps ending at first-used primes contribute uniformly
sublinear travel before the cutoff. For sufficiently large records, a
first crossing needs more than `M/12` from short gaps and long gaps
ending at reused primes. `TravelExcess.lean` charges those gaps against
horizon growth, gives a finite first-crossing inequality, and bounds
overlap of reuse windows within a factor-two width band. `lake build
A166944.TravelMod210` checks a residue table that bounds excess on
blocks of increments dividing 210 and reduces the overall budget to
separating-event charges. `TravelSigned210.lean` keeps their signed
balance, and `ReuseCongruences.lean` checks the index and horizon
residues at repeated uses of an increment factor. `TravelPhases210.lean`
gives a sublinear budget for the first long gap in each prime phase
and pays for a repeated phase when a single zero-excess separator
intervenes. `SeparatorBlocks210.lean` bounds complete intervals with
several separators and checks the summation of disjoint credited blocks.
`FundedPhaseCredits210.lean` bounds small startup charges and proves
conditional sublinear balance and short travel from a credit allocation
funded by first-phase gaps.
`CreditHall210.lean` characterizes allocation existence by weighted Hall
inequalities. `CreditWindows210.lean` reduces interval eligibility to
contiguous-window inequalities; it suffices to test the at most `n*n`
windows with endpoints drawn from `n` requests. The window inequalities
on arbitrary actual recurrence prefixes remain open.
`TravelCharged210.lean` sharpens long composite gaps to `24*g≤7*G`,
allowing a four-growth separating balance while preserving the travel
coefficient eleven. `ChargedPhaseCredits210.lean` proves eventual short
travel conditional on allocations for these improved costs. The bounded
search through 100000000 assigns every tested nonstartup request using negative
balances alone, with no extra first-phase funding; universal allocation
existence is still open.
`ResidualPhaseCredits210.lean` integrates the tighter residual cost into
the full path and first-crossing budgets. `ResidualStartup210.lean`
bounds each startup charge by 1478 and the distinct-key total by
23899260. `ResidualAllocation210.lean` retains unused credit `U` in the
net budget. `CreditDeficits210.lean` reduces allocation failure to a minimal
deficient window. `CreditDeficitStructure210.lean` proves that positive
requests attain its endpoints and cross every interior cut.
`ResidualEventTrace210.lean` and `ResidualIntervals210.lean` construct
the requests, negative sources and startup costs from actual ordered
events. `ResidualDeficitBounds210.lean` applies the reuse constraints
to each cut of a minimal deficient window. Each positive request
requires at least 630 horizon drift. A deficient window spanning
at most three events requires a repeated long prime in the middle.
Its earlier occurrence is before the window with at least 97230
horizon drift to the middle event. The unrestricted window condition
remains open.

`ResidualThreshold210.lean` proves that an admissible allocation and
`2*(24+c)*F_phase ≤ M+2*U` suffice for the crossing budget when
`M ≥ 50000000`, where `c` is the funding multiplier.
`TwinReserveTarget210.lean` proves the original A166944 target and
unbounded twin primes **conditional on** `ResidualReserveCondition210 c`,
which supplies these certificates on every actual short capped prefix
in that range. `ResidualIntervalBudget210.lean` proves the exact
identity `S+U=startupCost` for the constructed zero-funding allocation.
`TwinSignedReserveTarget210.lean` reduces the same targets to the single
open signed bound `2*(24*F_phase+S) ≤ M+47798520` on those prefixes.
The previous certificate condition implies this bound. The direct
signed route applies without a separate allocation hypothesis, and the
finite bridge below its threshold is proved.

`ResidualNetContributions210.lean` writes `W = 24*F_phase+S` as
an exact sum over events. The middle and final costs of a three-event
deficit fit in half of the middle prime's earlier reuse drift.
`ResidualReuseOverlap210.lean` counts the union of crossing prime
reuse intervals once. Two equal drifts for distinct primes `p,q` are
divisible by `210*p*q`, in particular when both crossing flanks
consist of consecutive corresponding events.
`ResidualGrowthAllocation210.lean` sums signed costs over disjoint
growth blocks while keeping unassigned costs in a signed remainder.
`TwinCrossingBudget210.lean` proves that `3*W ≤ 2*G+47652293`, with
`G` the horizon growth, rules out the first crossing when checked
on the applicable prefixes with `M ≥ 50000000`. A sufficient
construction would bound selected signed reuse costs by two thirds
of their disjoint block widths and bound the remainder. Both
general bounds remain open.

`ResidualStartupWeights210.lean` sharpens the startup cost bound
from 23,899,260 to 6,181,254 by counting reachable phases at each
increment and using a factor-dependent cost. `ResidualScaledPotential210.lean`
proves a second crossing reduction with potential `floor(8*V/9)`.
Every individual unsupported prime reuse, including increment 11,
fits in two thirds of its growth window. The windows to the latest
occurrences of one long prime phase key are disjoint, so the same
bound holds for their union. For mixed keys, a largest-increment
reuse and sufficient enclosed negative cost give a finite-set bound.
`signed_budget_iff_block_slack` uses the actual block widths and
slack when comparing the remaining signed sum to the first-crossing
budget. The mixed-key bound and the remaining signed sum on arbitrary
actual crossing prefixes are open.

`ResidualAdjustedCosts210.lean` separates first travel from the
scaled signed sum. The new startup bound is 4,651,452, and additional
repeated positive costs have their own same-key intervals.
`ResidualGrowthWindows210.lean` applies minimal-deficit reasoning to
growth plus enclosed negative costs. First-hit residues narrow two
long-prime requests in a deficient interval to 15 prime pairs and
width at most 5,276. A single adjusted request in a minimal deficit
requires increment 9 and width 630 or 1,260, or increment 25 and
width 1,050. If the adjusted window inequalities hold, the existing
sublinear first-phase bound pays for the remaining first travel for
sufficiently large records. The general window inequalities and the
first-travel bound down to the verified finite range remain open.

`TravelRebalanced210.lean` checks a new potential on all 22,050
states modulo 210. Its cap is 1,036, and the positive costs at
increments 9 and 25 are at most 315 and 525. In
`ResidualRebalancedCosts210.lean` every individual request fits
within two thirds of its growth window. Any deficient window
therefore has at least two positive requests. The first charge
is capped at the event's positive net cost and the startup bound
is 4,054,512. `ResidualFirstPayment210.lean` gives an explicit
cutoff bound for the sum of first charges and connects it to
the crossing budget. The window inequalities for overlapping
requests and a first-charge bound down to the verified finite
range remain open.

`ResidualRebalancedTwoRequests210.lean` pays all requests of
one phase key by using one disjoint terminal period per request.
The first-hit cost caps and endpoint offsets in
`ResidualRebalancedPairOffsets210.lean` restrict a deficit
with exactly two positive requests to 33 increment pairs on
distinct keys, width at most 5,093, and enclosed negative credit
at most 1,363. The offset checks pay the pairs (23,23) and
(9,63) from growth alone. An enclosed composite increment
of at least 295 also rules out a two-request deficit. The
remaining mixed-key cases require further control of the
enclosed credit.

`ResidualFirstPayment210.lean` bounds the full rebalanced net cost by
`W ≤ 146*G`, where `G` is the actual horizon growth along the prefix.
For `M ≥ 50000000`, `rebalanced_crossing_budget_of_small_growth210`
proves the crossing inequality whenever `150*G ≤ M`.

`RebalancedCrossingGrowth210.lean` uses a potential of at most two
modulo six to bound the actual travel `t` by `6*t ≤ 2*G+13*H+6`.
Here `H` is the growth from events with `e-1 < 3*(gap+1)`.
A first crossing with gap `g` requires `M < 5*G+2*g+2` and
`M < 13*H+6*g+16`. The square-root gap bound implies `100*M < 501*G`
and `M < 14*H`. `RebalancedRemainingCrossingCondition210` asks for
`W+24*g+11*G+V_start < 12*(M+1)+V_end` on the actual crossings
meeting these constraints from `M ≥ 367232911`. The existing finite
travel bridge and the new reduction give `Target` from this bound.
The signed bound on the remaining crossings is open.

`RebalancedFirstPaymentBudget210.lean` reduces the positive first
payments to at most 42 phase keys per prime below 127 and 30 at or
above 127. Increments dividing 210 contribute zero. With a cutoff
of at least 338, the tail is bounded using only `H`.
`RebalancedOverlapBudget210.lean` puts each positive repeat demand
`P_i` in a terminal interval of width `ceil(3*P_i/2)`. Intervals on
the same phase key are disjoint. Let `U` be their union, `O` the
duplicate width, and `Q = sum (P_i mod 2)`. The prefix budget
charges `2*O` and subtracts `2*(G-|U|)`, `Q`, the negative costs
inside `U`, and guaranteed negative costs outside `U` from large
increments with small relative gaps. The latest earlier request on
a different key bounds each interval's contribution to `O`.
`target_of_rebalanced_overlap_crossings210` reduces the target to
this budget on the remaining actual crossing candidates. Establishing
the budget uniformly on those candidates remains open.

The ordinary
`A166944.Attempt` build stays on the recurrence-side imports.

The history envelope, record-index theorem `n = R + 2`, unconditional
fundamental-point infinitude, and the original A166944 twin-primality
conjecture remain open. Unbounded records imply that the original A166944
conjecture would yield infinitely many twin primes.

## Issue-scoped parallel research workflow

**Parent / child ownership.** Issue #1 retains the overall conjecture, verified
milestone record, cross-Issue dependencies, cumulative integration, canonical
verification, and final-solution gate. A focused child Issue, once created and
assigned, is the executable specification for exactly **one** research target:
its hypotheses, exclusions, baseline commit, counterexample controls,
deliverables, acceptance criteria, worktree, and next handoff. Keep the child
self-contained; use #1 for common provenance rather than duplicating history.

**Proposed research lanes (planning only; not yet created Issues):**

- **A — ordered canonical-origin replay:** retain actual ordered event ancestry
  and connect the last old event to the critical record and post-record event.
- **B — q=3 elimination:** exclude the even first-post-record quotient branch,
  using true recurrence history; do not silently assume the result of A.
- **C — q=2 elimination:** exclude the odd first-post-record quotient branch,
  including divisibility and first-hit constraints.
- **F — first-hit arithmetic toolkit:** formally audit and, if valid, prove
  reusable divisor/gap, composite-event slack, and exact stopping criteria.
- **D — fundamental-point regeneration:** investigate composable genuine
  returns to `a(m)=2m`; distinguish finite diagnostics from an infinitude proof.
- **E — renormalized growth:** study ordered event excess/displacement and
  proposed global growth constraints, retaining counterexamples to false bounds.

Lane names and boundaries are planning labels, **not GitHub Issue numbers**.
Issue creation, scheduling, and ownership are explicit follow-up actions; this
README does not automatically start a Codex task. The currently verified common
starting point is the 5E.3.20 commit above; **recheck the desired shared base
against the public repository before launching parallel work**.

**Branching and integration.** Give each active child its own linked Git
worktree/branch. Codex may perform scoped research, compile, and push checked
child commits; it must not merge sibling results or independently declare parent
milestone closure. Issue #1 owns the final cumulative integration into `main`,
including conflicts, post-integration regression builds, and canonical GitHub
Actions verification. Do not assume a child result is integrated merely because
its branch or local build passed.

**Completion states.** Report `PROVED`, `REFUTED`, `PARTIAL`, or
`OPEN/BLOCKED`, including actual-vs-abstract counterexample classification,
exact theorem statements, local build/axiom results, remote SHA, and remaining
goals. A narrow, finite diagnostic task may close once its stated acceptance
criteria are met; an unresolved universal theorem remains open despite useful
partial progress. Child closure **never** means the overarching A166944
conjecture was solved. See `AGENTS.md` for the execution rules.

## Pinned environment

| Dependency | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.1` |
| Formal Conjectures | `google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75` |
| Mathlib | `leanprover-community/mathlib4@0df444a360eaa60ab8c11dca51a86af692955474` |

Initial setup:

```sh
lake update
lake exe cache get
```

Fast recurrence-side iteration:

```sh
lake build A166944.Attempt
```

After promoting reusable lemmas:

```sh
lake build A166944.Lemmas
```

Canonical verification additionally builds the target definitions and the
bridge back to the pinned Formal Conjectures source.

## Verification policy

A mathematical result is considered proved here only when Lean accepts the exact
statement under the repository's trust policy. Do not use `sorry`, `admit`,
new axioms, hidden proof gaps, or a weakened replacement of the target.

Computational evidence, literature facts, conjectural lemmas, and Lean-verified
lemmas must remain explicitly distinguished. For every promoted child result,
record the exact theorem, focused build commands, `#print axioms` result,
remote commit, and (after integration) canonical verification status. Only the
full conjecture is subject to the separate final-solution gate in
`RESEARCH_PROTOCOL.md`; individual child Issues follow their narrower stated
acceptance criteria without implying that the open conjecture is solved.

## Repository split

This repository is the public execution/research home for A166944 Lean work.
Private cross-conversation continuity and project-memory state remain in
`tara-sooo/ChatGPT-Context`; the Lean source of truth should evolve here.
