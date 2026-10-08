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

The history envelope, record-index theorem `n = R + 2`, unconditional
fundamental-point infinitude/record unboundedness, the original A166944
twin-primality conjecture, and the Twin Prime Conjecture all remain unproved.

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
