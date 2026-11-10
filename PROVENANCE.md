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

## Long composite gaps and reuse of an increment factor, 2026-11-10

Codex continued from `b6b2288`. Any nonunit divisor `f` of an increment
`e` bounds the preceding first-hit gap `g` by `2*f`. If `g>10` and
`e` is composite, take a factor with `f*f≤e`. The first-hit bound and
oddness give `f≥7`, hence `3*g≤6*f≤e-1`. The exact sum `T` of gaps of
length at most ten and long gaps ending in primes satisfies
`3*(s-s0)≤3*T+(C-C0)` on a path from `(s0,C0)` to `(s,C)`.

`canonical_first_travel_crossing_residual` takes the first step `s→r`
across `2*(s-s0)≤M`, with canonical start `(s0,C0)=(M+2,2*M-2)`.
It proves `3*M<6*(T+(r-s))+2*(C-C0)`. At that start, `C-C0≤M+5` and
the crossing gap is at most `Q=sqrt(4*(3*M+4))`, giving
`M<6*(T+Q)+10`. `record_index_and_twin_prime_of_residual_travel_from_45895573`
therefore reduces the joint theorem to `6*(T+Q)+10≤M` on actual capped
prefixes with short travel from already canonical greater twin records
`M≥45895573`.

For any factor `f≥5` used at two ordered events, the growth from the
first end to the second start is at least `f-1`. The first end is zero
or minus two modulo `f`, while the second start is plus or minus one.
Evenness rules out smaller growth. Including the first jump, the second
gap is at most the growth between the two starts plus two. These are
`moving_horizon_factor_reuse_growth` and `moving_horizon_factor_reuse_gap`.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_factor_probe.py`
for the exact integer diagnostics. A prime is first-used when it divides
no earlier increment in that replay, including increments at short gaps.

| Previous record or synthetic start | Short | Long, first-used prime | Long, reused prime | Long, composite |
| --- | ---: | ---: | ---: | ---: |
| 22933441, certified replay | 565 | 13107 | 671 | 0 |
| 45895573, replay from a certified start | 99 | 858 | 0 | 0 |
| 23613589, synthetic | 2114 | 49215 | 4385 | 65 |
| 23619049, synthetic | 2046 | 44201 | 4007 | 65 |

In the first actual replay the last `f-1` units of required growth before
reuse overlap for factors 7 and 31. The two horizon windows are
`[45883362,45883368]` and `[45883350,45883380]`. Summing these windows
requires controlling overlap across different primes. The second actual
row is an integer replay from a certified starting state. A direct
recurrence scan to index 91793061 agrees on the event lists in both actual
rows. It can be reproduced with `record_segments(91793061)` from
`diagnostics/generate_record_replays.py`.

Verified with `lake build A166944.Attempt A166944.TravelTarget` on Lean
4.33.1 and `#print axioms` on the factor, residual-travel, and joint
conditional results. The dependencies are subsets of `propext`,
`Classical.choice`, and `Quot.sound`. The uniform residual budget is open.

## Uniformly sublinear travel at first-used primes, 2026-11-10

Codex continued from `10b0aff`. `HasMovingHorizonFirstUseTravel` records
the exact distance `F` from long gaps ending in a prime that has not
divided any earlier nonunit increment in the replay. The history includes
short and composite events. The ledger is obtained from the same path
as the residual distance `T`, with `F≤T`. Thus `T-F` measures short gaps
and long gaps ending in reused primes.

At any cutoff `L>0`, each prime at most `L` is charged at most once, by
twice that prime. Above `L`, a step ending at increment `e` has
`g*e≤2*(C+1)` by the cofactor bound and grows the horizon by `e-1`.
On a short canonical prefix with horizon growth `G`, the result is
`F≤2*sum(primesLE L)+2*(3*M+4)*G/(L*(L+1))`, with natural division.
This is `canonical_first_use_travel_bound`.

For any natural `j`, the primes at least `4^j` have product at most the
primorial, which Mathlib bounds by `4^L`. Comparing exponents and adding
the smaller primes proves `j*primeCounting L≤L+j*4^j`. With
`A=32*k`, `j=A^3`, and `L=A*(sqrt M+1)`, the small and large terms each
contribute at most `M/(2*k)` for sufficiently large `M`. This gives
`canonical_first_use_travel_sublinear`: for every positive `k`, one
threshold works for `k*F≤M` on every short canonical prefix. The proof
uses natural-number arithmetic and the primorial bound. Its threshold
`max 6 ((j*4^j)^2)` is an explicit, coarse asymptotic threshold.

`canonical_travel_crossing_requires_short_or_reused` uses `k=48` and
the square-root bound for the crossing step. For sufficiently large `M`,
a first travel crossing would require `M<12*(T-F)` immediately before
that step. The uniform bound on this remaining travel and the range
between the verified finite prefix and the asymptotic threshold are open.

The two actual rows from `diagnostics/travel_factor_probe.py` have
`G=28692` and `G=1914`, respectively. Substituting `L=2332` and `L=1422`
into the finite formula gives bounds `1456866` and `543823` for the
observed first-use distances `13107` and `858`. These are evaluations
of the bound on the two specific replays.

Verified on Lean 4.33.1 with `lake build A166944.Attempt` (14 jobs),
`lake build A166944.TravelTarget A166944.TravelFirstUse`, and `#print axioms`
on the first-use ledger, finite bound, and asymptotic results. The axiom
dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## Excess travel and overlap of reuse windows, 2026-11-11 JST

Codex continued from `472ca2d`. For a step contributing to short gaps
or long gaps ending at reused primes, charge `max(0, 24*g-(e-1))`
to excess `E`. The exact ledger for the remaining distance `R=T-F`
proves `24*R≤G+E`, where `G` is the horizon growth of the prefix.
For short gaps an excess requires `e≤240`. For a long gap an excess
requires a reused prime increment `p` with `p*(p-1)<48*(U+1)` when
the starting horizon is at most `U`. On a block whose increments
all divide a fixed positive even `P`, the common-multiple travel
theorem gives `E≤72*(P-1)`.

At a first crossing of `M/2`, let `g` be the crossing step's gap and
let `F`, `G`, and `E` refer to the prefix immediately before it.
`canonical_first_travel_crossing_excess` proves the finite inequality
`12*M<24*(F+g)+9*G+E`, with `G≤M+5` and
`g≤Q=sqrt(4*(3*M+4))`. This uses the earlier sharper first-crossing
inequality `3*M<6*(T+g)+2*G`, retaining actual growth.
`record_index_and_twin_prime_of_excess_budget_from_45895573` connects
`24*(F+Q)+9*G+E≤12*M` on short capped actual prefixes from canonical
greater twin records to both unrestricted targets. The sufficient
budget uses no asymptotic threshold. For sufficiently large `M`,
`canonical_travel_crossing_requires_excess` also proves
`2*M<G+E`, `M-5<E`, and `2*M<E+45` at a first crossing, using the
uniform bounds `48*F≤M` and `48*Q≤M`. The uniform budget remains open.

The minimum reuse window is `[C-(p-1),C)` immediately before the later
use of a factor `p≥5`. It lies after the previous event's end by the
reuse growth bound. If the first and third windows of ordered events
contain a common point, the third width exceeds the sum of the first
two widths. Thus any width band `[B,2*B)` has overlap at most two.
This holds for actual ordered steps even without requiring each window
to be a prime reuse.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_excess_probe.py`
for the integer diagnostics. Short runs below consist of consecutive
short events with positive excess. `P=210` runs consist of consecutive
events whose increments divide 210. Reported maxima are over each replay.

| Previous record or synthetic start | Growth | Short excess | Reuse excess | Max short run | Max `P=210` run | Max window overlap |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 22933441, certified replay | 28692 | 12312 | 15590 | 1212 | 694 | 2 |
| 45895573, replay from a certified start | 1914 | 2140 | 0 | 1012 | 352 | 0 |
| 23613589, synthetic | 97614 | 46322 | 101078 | 1542 | 1030 | 3 |
| 23619049, synthetic | 86694 | 44836 | 92258 | 1542 | 1030 | 3 |

Both synthetic replays have three reuse windows containing 47279388,
for factors 13, 101, and 241. Their widths are 12, 100, and 240, so
this is a control against a global overlap-two bound. The two actual
replays agree on all event indices with a direct recurrence scan to
91793061. Their finite scores `24*(F+Q)+9*G+E` are 998834 and 603166,
respectively. These scores use the exact integer replays, with `F` from
`diagnostics/travel_factor_probe.py`.

Verified with Lean 4.33.1, `lake build A166944.Attempt`,
`lake build A166944.TravelTarget A166944.TravelFirstUse`, and `#print axioms`.
The new results use only subsets of `propext`, `Classical.choice`, and
`Quot.sound`.

## Residue budgets for blocks of increments dividing 210, 2026-11-11 JST

Codex continued from `2e3ec8b`. For a supported event, `d(r)∣210`.
There is then a divisor of the increment between 2 and 7, so its
first-hit gap is at most 14. Clipping the parity-specific gcd to 210
preserves the supported increment and every unit increment in the gap.
It depends only on the index and horizon modulo 210. This proves that
the clipped search finds the exact step on every supported block.

`TravelMod210Data.lean` contains 105 rows of periodic tables for the
22,050 pairs of index residue and even horizon residue. A row stores
its period and the entries for one period, packing the block excess
cap and potential in two 11-bit fields per entry. `TravelMod210.lean`
checks both caps and both one-step inequalities for every state in
seven bands using kernel `decide`. Each supported step is charged
`max(0,24*g-(e-1))` in the table, an upper bound on its actual excess.
The block cap is at most 1316 and the potential `V` is at most 1260;
both table values attain these caps at residues `(23,110)`. The result
`moving_horizon_supported210_block_excess_le_1316` bounds actual block
excess. To regenerate and compare the data, run:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_mod210_probe.py --lean-data \
  | cmp - A166944/TravelMod210Data.lean
```

For a separating event `e∤210`, the charge is the positive part of
`E_i+V(after)-V(before)-2*(e-1)`. Supported steps have nonpositive net
cost and zero charge. `moving_horizon_excess_by_separator_charges210`
proves `E+V(end)≤2*G+V(start)+B` with `B` the exact sum of separating
charges. A positive charge requires `e≤630` or a long gap at a reused
prime within the earlier cofactor range. At a first crossing,
`canonical_first_crossing_requires_separator_charges210` gives
`12*M+V(end)<24*(F+g)+11*G+V(start)+B`, hence
`M<24*(F+g)+1315+B`. The uniform upper bound on `B` remains open.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_mod210_probe.py`
for the exact integer diagnostics, including independent generation by
scanning one entire period at each residue state. At `M=22933441`,
there are 93 separating events, with `B=23736`. Long reused-prime gaps
contribute 16308 and short gaps contribute 6792. At `M=45895573`,
the integer replay from the certified start gives 16 separators and
`B=1550`, of which 664 is short and zero is long reused-prime charge.
The two synthetic starts `23613589` and `23619049` give `B=138180`
and `128714`, respectively.

Verified with Lean 4.33.1, `lake build A166944.TravelMod210`, and
`#print axioms` on the block, potential, separator, and crossing results.
The dependencies are subsets of `propext`, `Classical.choice`, and
`Quot.sound`.

## Signed separating balances and factor reuse congruences, 2026-11-11 JST

Codex continued from `2e11eb1`. The integer balance of a step is
`E_i+V(after)-V(before)-2*(e-1)`. The previous separating charge is
the positive part of this balance at a separator. If `E_i=0`, the
balance is at most `1260-2*(e-1)`. On a genuine path the signed
supported sum `A` and signed separating sum `S` satisfy the exact
identity `E+V(end)=2*G+V(start)+A+S`, with `A≤0`. Thus the new finite
first-crossing theorem gives `M<24*(F+g)+1315+S` using the signed sum on
the prefix before the crossing. The necessary estimate concerns every
such prefix.

For any factor `p>2` of a genuine increment, the pre-event horizon
and hit have fixed residues modulo `2*p`. In hit and horizon order,
the pair is `(0,p+1)` at an even hit and `(p+2,p-1)` at an odd hit.
For two ordered uses, the elapsed index and horizon growth residues
are `(0,0)` for equal parity, `(p+2,2*p-2)` for even to odd, and
`(p-2,2)` for odd to even. If the earlier increment is exactly `p≥5`
and there is one intervening event with increment below `3*p`, that
increment is `p+2` for equal parity or `p+4` for odd to even.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_signed_reuse_probe.py`
to reproduce the integer comparisons. Each positive long reused-prime
balance is assigned unused negative separator balances strictly between
the preceding use and the current event, taking the earliest eligible
credit first. The independent total ignores overlapping claims on the
same credit. The assigned total uses each credit at most once.

| Previous record or synthetic start | Final signed sum | Peak signed prefix | Long reuse charge | Independent credit | Assigned credit |
| --- | ---: | ---: | ---: | ---: | ---: |
| 22933441, certified replay | -29464 | 60 | 16308 | 10766 | 10766 |
| 45895573, replay from a certified start | -1742 | 582 | 0 | 0 | 0 |
| 23613589, synthetic | -47864 | 1272 | 109074 | 88060 | 80208 |
| 23619049, synthetic | -36378 | 12758 | 99672 | 78940 | 76808 |

For the actual replay from 22933441, the increment 19 at index 22940203
reuses 19 from index 22940182. The index and horizon drifts are 21 and
36. The four intervening balances are 138, 0, 0, and 0, including the
supported events. The reuse incurs a positive balance of 738, with
zero negative credit strictly between its two uses. This rules out
paying every positive reuse solely within its own interval. The signed
prefix bound at arbitrary canonical records is open.

Verified on Lean 4.33.1 with `lake build A166944.Attempt
A166944.ReuseCongruences A166944.TravelSigned210` and `#print axioms` on
the congruence, signed-balance and crossing results. The dependencies
are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The unconditional index theorem and the universal exclusions of the
two quotient branches are open.

## First long gaps by phase and intervening credit, 2026-11-11 JST

Codex continued from `e25f5e0`. `TravelPhases210.lean` moves the first
long gap for each `(prime, phase)` into a separate distance `F_phase`.
The phase can be any fixed finite labeling of the pre-event horizon and
the hit index. For a labeling with `k` values, the small-prime part of
the finite budget is at most `2*k*sum(primesLE L)` and the large-prime
part still uses the cofactor bound against total horizon growth.
`canonical_first_prime_phase_travel_sublinear` proves uniform
sublinearity for every fixed labeling size. The new signed separator
sum `S_phase` uses zero excess at a first long gap of a phase.
`canonical_first_crossing_requires_phase_balances210` proves
`M<24*(F_phase+g)+1315+S_phase` before a first crossing.
`canonical_travel_bound_of_prime_phase_budget210` gives the reverse
sufficient budget with the square-root upper bound on `g`.

`moving_horizon_same_phase_reuse_requires_separator` shows that two
uses of a factor `p>2` with the same hit parity and the same pre-event
horizon residue modulo `P` have positive horizon drift divisible by
`lcm(P,2*p)`. If the earlier increment equals `p`, an intervening
increment must fail to divide that modulus. In the modulo-210 case,
for `p≥11` coprime to 210 and exactly one intervening increment `e`
outside the divisors of 210, `moving_horizon_prime_phase_pair_budget210`
proves `209*p≤e+416`. If the middle event has zero excess, its signed
balance plus the later balance is at most `3357-373*p<0`. In the
separator subsequence the credited event immediately precedes the
target, so two positive targets of this form cannot use the same
credit. The general multiple-separator case is open.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_phase_probe.py`
to reproduce the integer checks. The direct scan from the initial
recurrence confirms the `M=355723` replay. The chain beginning with
`M=22933441` uses the Lean-certified start and exact first-hit replay;
an independent term-by-term scan to index 91793061 agrees on the first
two intervals (209 and 37 nonunit hits). The later intervals are integer
diagnostics from this chain. The synthetic starts are not recurrence
certificates.

| Previous record or synthetic start | Old peak | Phase peak | Phase final sum | Positive same-phase reuse charge | Assigned credit |
|---|---:|---:|---:|---:|---:|
| 355723, direct recurrence | 3066 | 862 | -748 | 0 | 0 |
| 22933441, certified replay | 60 | 60 | -44088 | 0 | 0 |
| 45895573, replay from a certified start | 582 | 582 | -1742 | 0 | 0 |
| 367232911, exact replay chain | 212 | 212 | -23014 | 1386 | 1386 |
| 1786441, synthetic | 3640 | 1288 | -11194 | 666 | 666 |
| 23613589, synthetic | 1272 | 978 | -137528 | 7542 | 7542 |
| 23619049, synthetic | 12758 | 6944 | -117482 | 6978 | 6978 |

The earlier `p=19` example at 22940203 loses 294 in gap excess, so
its balance falls from 738 to 444. In the replay from 367232911 the
positive same-phase balances 558 and 828 for 11 and 13 have 13 and
9 intervening separators. The positive use of 11 at 367241820 itself
breaks divisibility by 2730 in the reuse interval for 13. The synthetic
start 1786441 exercises the single-separator theorem with `p=11`,
`e=2293` and middle and final balances -4584 and 666.

Verified with `lake build A166944.Attempt A166944.TravelTarget
A166944.TravelPhases210` and `#print axioms` on Lean 4.33.1. The
dependencies of the new theorems are subsets of `propext`,
`Classical.choice`, and `Quot.sound`. The uniform signed-prefix bound,
including small positive separator balances and repeated phases with
several intervening separators, remains open.

## Several separating events and disjoint credit blocks, 2026-11-11 JST

Codex continued from `00c42b6`. `SeparatorBlocks210.lean` records the
exact separator excesses and signed balances in chronological lists.
The supported-step identity
`(C'-C)+(C-1)%210=(C'-1)%210` keeps track of growth below the next
multiple of 210. If a path has `k` separators with total excess `A`
and signed sum `S`, the resulting block inequality is
`S≤A+1678*k+418-2*G`, where `G` is its horizon growth.

For two equal prime phases modulo any fixed positive `P`, let
`L=lcm(P,2*p)`. The signed sum `B` from strictly after the earlier
increment `p` through the later increment `p` satisfies
`B≤A+1678*k+1679+47*p-2*L`. Here `A` and `k` concern the strictly
intervening separators. For `P=210` and `p` coprime to 210 this gives
`B≤A+1678*k+1679-373*p`. In particular, `A=0` and `5*(k+1)≤p`
suffice for `B≤0`, for any number of intervening separators.

`HasPhaseSeparatorCreditCover210` partitions a separator list into
contiguous nonpositive blocks and uncredited single events.
`phase_separator_credit_cover_bound210` proves that the complete signed
sum is at most the sum of the uncredited positive parts. Concatenation
ensures that these credited blocks do not share any event. A universal
cover with a sufficiently small residual budget remains open.

Run `PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_block_probe.py`
for the block inequalities and disjoint covers. The synthetic canonical
start `M=15609199` has two long uses of 23 at 15609389 and 15611827,
with three intervening separators and zero intervening separator
excess. Their balances total -8970 and the final balance is 774, giving
`B=-8196≤-1866`. This is an abstract replay from a synthetic start,
not an initial-sequence certificate. In the exact recurrence replay
from `M=367232911`, the disjoint cover using numerically checked
nonpositive reuse blocks leaves a positive-part budget 5348. The
general block upper bound is too coarse to certify those particular
blocks automatically. The synthetic 23613589 and 23619049 controls
leave budgets 6094 and 5474 under the same numeric cover algorithm.

`diagnostics/travel_credit_search.cpp` implements an independent exact
bounded search. Compile and run with

```sh
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000
```

It examines every twin-prime-shaped canonical start `13≤M≤100000000`,
using exact small-factor sieving and first-hit jumps. For each positive
same-phase long-prime balance it assigns the oldest eligible unused
negative separator balance strictly between its two long uses.
All 36616 such demands from 440310 synthetic starts were assigned.
Two paths stop at their first failure of the cap or short-travel
condition; their later events are outside this diagnostic. No path
reached the imposed 3000-event limit. The native `--table` output
matches all 22050 independently computed Python potential entries.
An independent Python trial-factorization search through 2000000
also agrees on all 14869 starts, 194 paid demands and two cutoff stops.
This finite computation establishes neither the universal allocation
claim nor the remaining small-positive-budget estimate.

Changing a fixed phase modulus preserves the sublinear first-phase
theorem. In the sample replay at 367232911, modulus 840 removes the
remaining long same-phase demands but increases the first-phase
distance from 13781 to 13832. Enlarging the phase modulus can increase
the finite combined budget `24*F_phase+S_phase`; its benefit here is
the stronger structural constraint on subsequent repeated phases.

Verified on Lean 4.33.1 with `lake build A166944.Attempt
A166944.TravelTarget A166944.SeparatorBlocks210`, the sample probes,
the independent table comparison and native bounded search.
`#print axioms` on the new theorems uses only subsets of `propext`,
`Classical.choice` and `Quot.sound`. The main A166944 theorem and the
uniform signed-prefix estimate remain open.
