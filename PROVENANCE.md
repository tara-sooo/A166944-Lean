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

## Even horizon bounds and canonical returns, 2026-11-10

Codex continued from the verified record-index branch commit `654e40d`.
The barrier proof uses the original recurrence. If `D(n) ≤ H`, `H` is
even, and `d(n+1) ∣ H`, then `D(n+1) ≤ H`. In the even-index case,
`D(n)-1` and `H` are multiples of the increment. In the odd-index case,
`D(n)+1` is the preceding odd multiple, and the update also stays below
the next even multiple. A unit increment leaves `D` fixed.

- `difference_records_unbounded` and `exists_difference_record_above_by_bound`
  prove an unconditional larger record for every threshold `M`, by index
  `H(M)+3`, where `H(M)` is the lcm of 2 and the odd positive integers at
  most `M`. The proof combines the barrier with the existing
  `D(n) ≥ n-2` bound. In particular the A166944 twin-primality conjecture,
  if proved, would imply unbounded twin-prime pairs.
- `capped_moving_horizon_eventual_exit` proves finite exit from an actual
  capped replay, at a fundamental point or at a larger first hit. Any
  critical quotient satisfies `delta*(c+1)+1 ≤ H(M)`. Either intermediate
  post-record branch forces every positive even common multiple of the
  old increments after the canonical start to be at least `21*M+27`.
- `a_le_three_mul` gives the unconditional upper bound `a(n) ≤ 3*n`.
  A large increment has `n = d(n)+2` exactly when `D(n-1) < n`.
  Every fundamental point `m ≥ 6` is divisible by 6 and has its
  canonical reset `d(m+3)=m+1`.
- `record_index_iff_no_canonical_escape` gives an equivalent proof
  target on actual capped replays from canonical records. With the
  initial range `M < 968` checked in Lean, a bound of `3*M+4` on the
  remaining capped replay horizons would suffice. The low-residue
  barrier lemmas give a way to certify such bounds on individual paths.

Integer diagnostics distinguish the remaining uniform bound from the
theorems above. For odd `7 ≤ M ≤ 2000001`, starting at the synthetic
`(M+2, 2*M-2)` and taking exact first hits until none remained, all
999998 cases reached the no-hit exit within 311 events. For `M ≥ 969`,
the largest observed horizon ratio was `3120/1331`. These computations
use the minimum parity-specific trigger from the odd prime divisors of
`C-1` and `C+1`, with the increment evaluated by gcd at that index.
A single low-residue barrier below `3*M+5` for all old increments does
not always exist. The actual record `M=355723` returns at `C=713832`,
and its old increment sizes exclude every such barrier in
`[713832, 3*M+4]`.

`lake build A166944.Attempt A166944.TargetDefs` passed with the pinned
4.33.1 toolchain. The new results listed above and their exported
supporting lemmas were checked with `#print axioms`. Their dependencies
are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The unconditional index theorem and the universal exclusions of the
two quotient branches are open.

## First crossing by a large old increment, 2026-11-10

Codex continued from `75eccd7` on the record-index work branch. If an
old increment `e ≤ M` takes the horizon past `3*M+4` for the first time,
the preceding horizon lies in `[2*M+6, 3*M+3]`. In the large case
`4*e > 3*M+3`, `canonical_path_large_old_crossing` forces
`r=2*e`, `C=3*e+1`, `C'=4*e`, and `a(r)=3*r`.

The first-hit test and the preceding endpoint's divisibility initially
give six pairs `(gap, preceding increment)`. `D_backward_gcd` gives
the exact inverse transition, including unit increments. Both pairs
with preceding increment 7 are incompatible with the gcd at `2*e-4`.
The pair with preceding increment 15 is impossible by a seven-index
backward calculation with a finite table of offsets, checked by Lean
for arbitrary `e ≥ 20`. The remaining pairs and necessary residues are
`(1,3)` with `e % 3 = 0`, `(1,5)` with `e % 5 = 4`, and `(6,5)` with
`e % 3 = 0` and `e % 5 = 3`.

The `(1,5)` branch has a local inverse state `(2*(e-1), 3*(e-1))`.
Every odd divisor of `e-1` satisfies the inverse gcd equation there.
The prefix from the canonical origin also matters. Every positive even
common multiple `P` of the earlier increments has `4*P > M+21`.
In particular, for `M ≥ 968` some earlier increment must be at least 9.

Run `python3 diagnostics/large_crossing.py` for the finite reverse check.
It starts at `(2*e-1,3*e+1)` and enumerates exact gcd predecessors with
the necessary cap, horizon, and `D(n) ≤ 2*n` conditions. The 9637 odd
values `729 ≤ e ≤ 20001` exhaust all such predecessors before any
possible canonical origin index. For a separate local control, take
`M=1321` and the synthetic state `(2317,3510)`. Its exact local gcd
replay reaches `(2518,5036)` with final increments 5 and 1259 and passes
200 indices before the crossing. The original sequence has
`D(2317)=2658`, so this is a local suffix rather than an actual
canonical-origin replay. The reverse scan and the control are integer
diagnostics. The three remaining forms have no universal reachability
exclusion yet.

`lake build A166944.Attempt` passed on Lean 4.33.1. The exported
crossing theorems were audited with `#print axioms`.
