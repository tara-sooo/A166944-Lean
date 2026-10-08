# Codex rules for Lean research

These rules apply to all work in this repository.

Read `README.md` before starting a research task. [Issue #1](https://github.com/tara-sooo/A166944-Lean/issues/1) is the **parent research tracker** for the A166944 conjecture, verified milestones, shared blockers, and final integration. For a task assigned to a focused child Issue, read **that assigned Issue first** for its scope, target, and acceptance criteria; also read #1 for the shared verified baseline and provenance. Until child Issues are created and assigned, #1 remains the active task tracker. Neither this file nor the list of proposed lanes in `README.md` authorizes starting unassigned work.

## Correctness first

1. Never treat plausible mathematics as a proof. A result is proved only when the exact target theorem is accepted by Lean under the allowed trust policy.
2. Do not use `sorry`, `admit`, `axiom`, `unsafe` escape hatches, hidden assumptions, or equivalent mechanisms to close a research theorem.
3. Do not weaken, rewrite, or replace the target statement to make it easier. If the formalization appears wrong, stop and document the mismatch instead of silently changing the theorem.
4. Do not move the unresolved mathematical content into a helper lemma with an unproved body.
5. Standard Lean/Mathlib axioms already required by the environment may be used, but inspect the final theorem with `#print axioms` and record the result.

## Verification

6. Compile candidate proofs with the repository's pinned Lean/Mathlib environment. Do not infer success from editor state or partial tactic progress.
7. Before claiming success, check:
   - the exact target theorem compiles;
   - no forbidden proof gaps remain;
   - `#print axioms <target>` is acceptable;
   - the formal statement still matches the intended mathematical problem;
   - an independent verifier/comparator is used when the project provides one.
8. A nearly compiling proof is not "almost solved" unless the remaining goals are themselves proved to follow from established hypotheses. Inspect failed arithmetic goals semantically.

## Research method

9. Prefer small, reusable, kernel-checked lemmas. Preserve proved partial results even when the main theorem remains open.
10. Separate:
    - computational observations;
    - conjectured lemmas;
    - Lean-verified lemmas;
    - literature facts;
    - the final theorem.
11. Search for counterexamples and failure modes as aggressively as proofs.
12. Use multiple independent proof strategies when practical. Independence is valuable before merging ideas.
13. Keep experiments reproducible: record model/configuration when relevant, commands, bounds, generated data, and the exact theorem/commit tested.
14. Mathematical computation is evidence, not proof, unless Lean reduces it to a finite certified statement.

## Literature and novelty

15. Before claiming a new mathematical result, follow `RESEARCH_PROTOCOL.md`.
16. Verify that the problem is still open and that the proposed argument is not already in the literature.
17. Track provenance of imported ideas, public LLM attempts, papers, and existing formalizations. Do not present a repaired public argument as independently discovered.
18. If the public formalization disagrees with the source problem, treat semantic equivalence as an open verification task.

## Issue discipline

19. Give each independently scoped research target its own **assigned child Issue** when a child has been created. Issue #1 remains the parent and owns the overall A166944 conjecture, milestone accounting, cumulative integration, and final-solution acceptance. Do not create a second orchestration-only Issue when #1 can own that work.
20. The assigned child Issue owns its exact hypotheses, conclusions, included/excluded work, known counterexamples, acceptance criteria, working branch/worktree, and results. Record meaningful progress **in that Issue**: kernel-checked lemmas, falsified candidates, reproducible computational diagnostics, exact remaining goals, and pushed commits. Report only material verified results, changed blockers, and integration handoffs to #1; do not duplicate full child research logs there.
21. Distinguish **child acceptance** from **solving the parent conjecture**. Close a bounded child Issue only when all of its explicit acceptance criteria and the applicable Lean verification checks are met, with a remotely reachable commit and a precise result report. An open-ended universal-theorem Issue stays open after merely partial results or a proof-search timeout. A specifically bounded diagnostic Issue may close after its stated investigation is complete, even if the broader conjecture remains open; its closure must not imply that the unproved theorem was established. Never mark a mathematical claim solved because an LLM says so.


## Performance discipline

22. For interactive work on Termux, use the established lightweight module boundary. Ordinary recurrence-side proof search should run with `lake build A166944.Attempt`.
23. Do not run `lake update`, `lake exe cache get`, or a full project build on every proof iteration.
24. Do not import umbrella `Mathlib`, `FormalConjecturesUtil`, or the canonical Formal Conjectures problem file into the ordinary recurrence-side attempt. Add the smallest specific import required by a proved lemma.
25. Treat a sudden jump from the validated ~4-job incremental build to hundreds/thousands of jobs as an environment/import regression and diagnose it before continuing proof search.

## Parallel research lanes and handoffs

26. Before working, identify the assigned Issue, its parent (#1), and the exact verified base commit; check the public repository's current branch, working-tree state, and remote. When multiple lanes run, each owns a separate linked Git worktree and branch based on a deliberately selected common commit. Do not overwrite another lane's files, commits, scratch data, or uncommitted changes.
27. Partition work by **mathematical target and owned invariant**, not by which file happens to contain a lemma. Reuse another lane's verified result instead of independently reimplementing or modifying that lane's theorem. Cross-Issue needs should be recorded as a link/handoff, not silently absorbed into the wrong scope.
28. Keep each child branch's changes within its Issue's scope. A child may push a reviewable verified result, but **#1 owns cumulative integration** into the canonical main branch, conflict resolution, bridge/CI verification, and any claim about the overall A166944 milestone. Do not merge sibling branches wholesale or push competing integration changes to `main` without explicit coordination.
29. Preserve the original distinction among **actual A166944 recurrence histories**, **abstract first-hit / moving-horizon states**, and **scalar arithmetic witnesses**. A counterexample in one class must never be reported as a counterexample in a stronger class. Retain positive recurrence controls and known false monotonicity candidates when testing a new invariant.
30. A checkpoint is not task completion. When work remains, push any sound, scoped, reproducible partial result; leave the child Issue open; record the exact residual Lean goals or mathematical obstruction and the last remotely accessible commit. If no valid proof was obtained, say so. Proof-search failure is not a disproof, and an unproved mathematical question is not an external tooling blocker.
31. In the child completion report separate **PROVED** (kernel-checked exact theorem), **REFUTED** (explicit counterexample, with its semantic class), **PARTIAL** (verified subresults but open target), and **OPEN/BLOCKED** (specific missing mathematical step or genuine external dependency). Give theorem names, tested bounds, proof/build commands, `#print axioms` results, remote SHA, and the next handoff. Mark a child closed only as rule 21 allows.
32. For resource-constrained Termux parallel runs, reuse shared pinned dependencies and caches; keep mutable scratch per lane and ordinarily limit expensive Lean compilation to approximately one or two concurrent lanes. Do not clone heavyweight dependency trees per child or launch repeated `lake update` / cache downloads.
33. A private strategy/handoff repository may guide planning where available, but the assigned **public Issue must be self-contained for its executable scope and acceptance**. Public Lean code, pinned dependencies, exact GitHub Issue records, and canonical CI evidence are the reproducible authority. Do not copy private context verbatim into public Issues without need.
