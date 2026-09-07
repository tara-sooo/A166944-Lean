# AI and research provenance

This project deliberately uses AI systems as research tools. Human responsibility for claims, repository maintenance, and publication decisions remains separate from the tools that generate suggestions or code.

## Current workflow

- **Human maintainer (`tara-sooo`)** — selects the research direction, controls the repository, decides which claims are adopted, and is responsible for public claims.
- **ChatGPT** — research planning, decomposition, semantic/mathematical review, verification design, literature/status research, and continuity/state management.
- **Codex** — primary Lean proof-search and implementation agent for the active A166944 development, including local proof repair and milestone code changes.
- **Lean kernel / pinned toolchain** — mechanical checker for promoted formal results.

The division is operational rather than authorship credit. For any paper or formal registry submission, disclosure should be adapted to that venue's current policy.

## Public-attempt provenance

Earlier public LLM attempts and public mathematical sources may be used as provenance-bearing inputs. They are not trusted merely because they are public or long. Any useful lemma or idea must be independently checked before promotion.

In particular, a nearly compiling generated proof is not treated as evidence that the conjecture is nearly solved when its remaining goals do not follow from the established hypotheses.

## What to record going forward

For material milestones, record when practical:

- model/tool used;
- role: planning, proof search, code generation, critique, computation, or literature search;
- exact repository commit and Lean environment;
- external source/idea provenance;
- human verification performed;
- whether the result is Lean-verified, computational, literature-supported, conjectural, or a counterexample.

This ledger exists to preserve auditability and future publication/registry options. It is not evidence that the open conjecture has been solved.
