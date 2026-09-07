# Codex rules for Lean research

These rules apply to all work in this repository.

Read `README.md` before starting a research task. GitHub Issue #1 is the current task-specific research tracker and source of truth for A166944 milestone state.

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

19. One research problem should have a dedicated GitHub Issue. Use the Issue to record the exact target, source/status, formalization commit, known partial results, current bottleneck, experiments, and next hypotheses.
20. Post meaningful progress to the Issue, especially:
    - a new Lean-verified lemma;
    - a disproved approach or counterexample;
    - a change in the identified bottleneck;
    - a candidate full proof and its verification status.
21. Never mark a problem solved solely because an LLM says it is solved. Close the Issue only after the verification checklist in `README.md` is satisfied.


## Performance discipline

22. For interactive work on Termux, use the established lightweight module boundary. Ordinary recurrence-side proof search should run with `lake build A166944.Attempt`.
23. Do not run `lake update`, `lake exe cache get`, or a full project build on every proof iteration.
24. Do not import umbrella `Mathlib`, `FormalConjecturesUtil`, or the canonical Formal Conjectures problem file into the ordinary recurrence-side attempt. Add the smallest specific import required by a proved lemma.
25. Treat a sudden jump from the validated ~4-job incremental build to hundreds/thousands of jobs as an environment/import regression and diagnose it before continuing proof search.
