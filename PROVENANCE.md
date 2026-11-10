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

## Record-index investigation, 2026-11-10

Codex worked from the 5E.3.20 proof baseline on the pinned Lean 4.33.1
toolchain. `A166944/RecordIndex.lean` adds the following checked results.

- A nonunit divisor of either horizon term forces a first hit within twice
  that divisor. Applying this to the post-record cofactor bounds the next
  increment by `e < 2 * (c + 2)^2` in both quotient branches.
- A kernel-checked finite certificate evaluates the original recurrence for
  the possible canonical previous records below 968. Each has its next
  record at an odd index. Together with the cofactor bound this gives
  `c ≥ 22` and `D(k) ≥ 23 * (M + 1) + 1` for an actual first critical
  failure at `k+1` followed by either intermediate branch.
- The two first-hit windows impose a mod-3 restriction without a bound on
  `c`. For the even branch with gaps 1 and 2, the critical index has the
  form `(e + 1) * (e*h - 2)` and the last old increment divides
  `15 * (4*h + 1)`, where `h ≥ 1` and `3*c + 4 = 2*e*h`.
  With a capped canonical prefix the old event count satisfies `p > e*h`.

`lake build A166944.Attempt` checks the new module in the ordinary lightweight
build. The axiom audit of its public results found only the inherited
`propext`, `Quot.sound`, and `Classical.choice`.

A computational control uses the actual previous record `M = 1321` and
local parameters `e = 1325, delta = 1989, h = 7, c = 6182`. Put
`n = delta*c` and start the local replay at `(s,C) = (n-28,n+1930)`.
The eleven old (gap, increment) pairs are
`(1,7), (3,3), (6,5), (4,23), (1,3), (1,3), (3,11), (1,5), (1,3), (1,3), (5,5)`.
The constant-`D` gcd calculation gives these as first hits and then
`(1,1989), (2,1325)`. In the original recurrence the next record after
`M = 1321` is already `2659` at index `2661`. This gives a local suffix
that survives the new restrictions and fails canonical-origin compatibility.
The scalar totals `p = 9330, E = 12304678, T = 12304004` also fit this
diagnostic. Separately, an abstract start `(s,C) = (26269,26296)` at
`M = 23` has 24 old first hits within the slack cap `2*M-4`, so a count
bound `p ≤ M` for canonical starts would need information about the origin.

The universal exclusions of the two branches and the unconditional record
index remain open.
