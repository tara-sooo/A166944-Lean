# A166944 Lean research

A public Lean workspace for investigating OEIS A166944.

The long-term target is the conjecture formalized as `OeisA166944.conjecture` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
This repository is **research in progress**: it contains kernel-checked partial
results and reproducible experiments, not a claimed proof of the open conjecture.

Public tracker: https://github.com/tara-sooo/A166944-Lean/issues/1

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

The latest verified layer packages an iterable moving-horizon state/step chain,
the constant-`D` `C±1` event arithmetic, attained-maximum transfer, cumulative
`D` growth, and the recurrence-specific local bound

`d(r) ≤ C - s`

for a first event `r` from moving-horizon state `(s,C)`.

This is not yet a termination/regeneration theorem. The history envelope,
the record-index theorem `n = R + 2`, and the original twin-prime conclusion
remain open.

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
lemmas must remain explicitly distinguished.

## Repository split

This repository is the public execution/research home for A166944 Lean work.
Private cross-conversation continuity and project-memory state remain in
`tara-sooo/ChatGPT-Context`; the Lean source of truth should evolve here.
