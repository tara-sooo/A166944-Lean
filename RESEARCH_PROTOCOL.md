# Research verification protocol

This repository investigates an open mathematical conjecture. Formal correctness, semantic fidelity, and novelty/status verification are separate obligations.

## Evidence classes

Keep these categories explicit:

- **Lean-verified** — the exact statement is accepted by Lean under the repository trust policy.
- **computationally supported** — checked only to a finite bound.
- **literature-supported** — stated or proved in a cited source but not independently formalized here.
- **conjectural** — plausible but unproved.
- **false** — a counterexample or contradiction has been found.

Do not promote computation, a plausible proof sketch, or an LLM assertion into a theorem.

## External research preflight

Before making a current-status, literature, attribution, or novelty claim:

1. identify the exact proposition being checked;
2. identify the relevant date/version/commit;
3. prefer primary sources: the original paper, OEIS entry, Formal Conjectures source, repository history, or another direct artifact;
4. use search snippets only for discovery and inspect the underlying source;
5. distinguish a source's question/speculation from an asserted or proved result;
6. check later sources/versions for superseding information.

## Open-problem and novelty claims

Before claiming that A166944, a stronger intermediate theorem, or a related open problem has been solved:

1. re-check the current OEIS/formal-conjecture status;
2. search the mathematical literature and recent public preprints;
3. compare the exact theorem statement, not only keywords;
4. verify provenance of any public LLM proof attempts or borrowed ideas;
5. independently check both the original claim and any proposed correction;
6. record the search date and sources in the public research tracker.

A correct Lean proof can still fail a novelty claim if the result was already known.

## Semantic fidelity

The lightweight recurrence definitions are intentionally separate from the canonical Formal Conjectures file for performance. Therefore:

- keep `A166944/Bridge.lean` compiling against the pinned upstream source;
- do not silently change the target to make a proof easier;
- if the public formalization appears mismatched with the mathematical problem, treat that as a separate verification task;
- before a final result, audit the human mathematical meaning of every definition and the final theorem.

## Corrections

When a prior factual or mathematical claim may be wrong, do not simply invert it.

- restate the original claim and proposed correction separately;
- check positive evidence for each;
- re-check downstream lemmas or interpretations that depended on the disputed claim;
- preserve unaffected verified results;
- update the current tracker rather than leaving contradictory live statements.

## Final-solution gate

Do not claim the open conjecture solved until all applicable checks pass:

- exact final theorem kernel-checks;
- no `sorry`, `admit`, new illicit axioms, or hidden proof gaps;
- `#print axioms` is acceptable;
- the lightweight/canonical bridge is verified;
- computational evidence is not being substituted for an infinite argument;
- the formal statement matches the intended A166944 conjecture;
- current novelty/open-status research is complete;
- external mathematical review is sought before publication-level claims.
