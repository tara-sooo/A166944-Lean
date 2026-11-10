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

## Canonical growth with a bounded number of exceptional increments

`A166944/CanonicalGrowth.lean` uses the whole prefix from the canonical
origin. At a first hit, the increment divides the parity-specific
difference of twice the index and the horizon term. This difference
is nonzero by parity. The elapsed index distance on a prefix is at
most three times its horizon growth. The cofactor of the next increment
also bounds the last gap. These facts give the Lean-checked bound
`e ≤ 7 + 5*(C-(2*M-2)) + Q` if `4*(C+1) ≤ Q*Q`.

For a positive even `P`, every interval of increments dividing `P`
grows by less than `P`. Combining such intervals with the step bound
gives `C < 2*M-2 + 7^k*(P+Q+6)` on any actual canonical prefix whose
increments outside `P` are covered by a list of length `k`. In particular,
a large old crossing with `M ≥ 65536` needs at least two preceding
increments that do not divide 210. For any old first crossing, if the
exception list includes the crossing index, set `A=7^k`. Then necessarily
`M < max (128*A*A) (2*A*(P+6))`. This also applies to the small final
increment case.

The diagnostic reproduces a limitation of a single choice of `P`. The
actual replay for `M=355723` reaches its fundamental return at `C=713832`
after 57 old nonunit increments. Even with the smallest square bound
for that horizon, every even `P ≤ M+7` gives a list budget larger than
`M+7`. This finite check concerns the budget formula, while the
three large-crossing forms still require a general reachability proof.

There is also a direct target on the original recurrence.
`half_index_increment_iff` proves `d(2*e)=e` iff `D(2*e-1)=3*e+1`
for `e ≥ 5`. For `e ≥ 20`, `half_index_increment_predecessor` gives the
same three preceding forms even without a canonical-origin assumption.
A direct integer scan through index 30,000,000 found only the half-index
increments at indices 6, 18, and 66. This scan updates `a` from 2 by
the exact gcd in the recurrence at each index and tests `2*d(n)=n`
at even indices. The exclusion at arbitrary large indices is open.

Verified with `lake build A166944.Attempt` on Lean 4.33.1 and
`#print axioms` for the exported theorems. The reported dependencies
are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## First-hit travel and the verified finite prefix, 2026-11-10

Codex continued from `f65e07b`. For an event with increment `e` and
cofactor `v`, the gap is at most both `2*e` and `2*v`. Thus its square
is at most `4*(C+1)`. A first crossing of `3*M+4` needs index
displacement greater than `M/2` from the canonical start, because
`D(r) ≤ 2*r`. With `k` first hits through the crossing, this proves
`M ≤ 48*k*k+1` for either size of final old increment. In particular, an actual capped
replay with `p` events and `48*p*p+1 < M` satisfies the horizon bound. The
travel cover also allows different positive even multiples on contiguous
segments. Within a run supported on `P` the travel is at most
`3*(P-1)`, and an exceptional event costs at most the square-root
gap bound. A large crossing after a cover of cost `B` requires
`M < 2*B+13`.

`diagnostics/generate_record_replays.py` proposes 20 segments from record
7 to record 22933441. The table contains 622 old nonunit indices, the
terminal horizons, and integer root bounds. `RecordReplay.lean` checks
the exact gcd at each hit and every intervening shorter gap. For each
long final quiet interval it checks divisors up to the supplied root
bound for both horizon terms, and verifies the root bound itself.
The soundness theorem propagates the actual previous maximum and the
next strict record from the starting value. No numerical search output
is assumed in the theorem. The finite table is accepted by kernel
`decide`, with the segments checked separately.

- `records_verified_through_22933443` proves that every strict record
  above 5 through that index occurs at `R+2` and both twin candidates
  have no proper factors. `target_for_records_le_22933441` proves the
  exact twin-primality predicate for all strict record values in that
  range, without assuming an index bound.
- `canonical_horizon_bound_before_22933441` proves `D(s)≤3*M+4`
  for actual capped states with canonical `968≤M<22933441`.
  `record_index_of_horizon_bound_from_22933441` reduces the universal
  index theorem to the same bound from `M=22933441` onward.

Verified with `lake build A166944.Attempt A166944.VerifiedTwinPrimePrefix`
on Lean 4.33.1 and `#print axioms` for the exported results. The proof
dependencies are subsets of `propext`, `Classical.choice`, and
`Quot.sound`. The universal index and twin-primality targets are open.

## A travel hypothesis for both unrestricted targets, 2026-11-10

Codex continued from `65d36ca`. On a genuine quiet return, a divisor
`f≥2` of `C-1` would force an even hit at `C-1-f`. A divisor of `C+1`
would force an odd hit at `C+3-2*f`. If `C-s > 2*sqrt(C+1)`, both
indices are inside the quiet interval for every such divisor up to
the square root. `quiet_return_no_proper_factors` proves both factor
certificates in the recurrence-side environment.

For a capped canonical prefix, `2*(s-(M+2)) ≤ M` gives `C ≤ 2*s ≤ 3*M+4`.
This excludes the inside-horizon larger-hit exit. At the quiet exit
`C ≥ 2*M-2`, so the same travel bound gives enough quiet length for
the factor theorem. The next record is `C+1` at `C+3`.

`TravelTarget.lean` discharges the finite initial range with the
verified prefix. From `M≥22933441`, a joint induction proves both full
conclusions assuming travel only from a genuine canonical previous
record `M` whose twin-primality is already known. The existing count
criterion `48*p*p+1 < M` implies short travel as well. These are exact
reductions, with the uniform travel bound still open.

Verified with `lake build A166944.Attempt A166944.TravelTarget` and
`#print axioms` on Lean 4.33.1. The dependencies are subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

## One more verified interval and a residue-sensitive travel bound, 2026-11-10

Codex continued from `84ce964`. A complete replay bounds the travel of
every actual capped prefix by the travel to the last listed nonunit
event (`canonical_replay_travel_bound`). The certificate in
`VerifiedTravelExtension.lean` starts at the canonical record
`M=22933441`, checks 209 old nonunit events, and ends those events at
index 22947786, just 14343 indices after the start. The quiet horizon is
45895572. The next strict record is 45895573 at index 45895575. The
record-index and twin-prime theorems now cover all strict record values
`5 < R ≤ 45895573`. The same certificate discharges short travel for
every actual capped prefix with canonical `22933441 ≤ M < 45895573`.

`moving_horizon_gap_le_six_of_six_not_dvd` uses the divisor 3 of one
horizon term whenever `6 ∤ C`. For `p` events and a cover of length `k`
of the starts with `6 ∣ C`, the sufficient short-travel inequality is
`2*(6*p + k*(sqrt(4*(3*M+4))-6)) ≤ M`. The proof tests the first index
that would exceed short travel. All event starts through that crossing
still satisfy the horizon bound used in the square root. The joint
conditional theorem in `TravelTarget.lean` now requires either short
travel or this sufficient budget only from actual canonical greater twin
records with `M ≥ 45895573`.

Run `python3 diagnostics/travel_residue_probe.py` to reproduce the
integer comparison. The actual interval has `p=209`, `k=125`. The two
synthetic canonical-coordinate starts `M=23613589` and `M=23619049`
both have `M` and `M-2` prime. They fail `48*p*p+1 < M` with `p=740`
and `p=721`, respectively. Their travel is 55779 and 50319, and the
weighted budgets pass with `k=445` and `k=432`. The two starts lie
between consecutive certified records and are not actual recurrence
histories. Regenerate the extension data with
`record_segments(45895575)[1][-1]` from `diagnostics/generate_record_replays.py`.

Verified with `lake build A166944.Attempt A166944.TravelTarget` on Lean
4.33.1. `#print axioms` on the replay, finite-prefix, residue-bound, and
joint conditional results reports only `propext`, `Classical.choice`,
and `Quot.sound`.

The unconditional index theorem and the universal exclusions of the
two quotient branches are open.
