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

## Small positive costs and first-phase funding, 2026-11-11 JST

Codex continued from `e979b55`. Extending the negative-only allocation
to repeated positive costs from small increments has a counterexample
at the synthetic canonical start `M=4394191`. The positive increment 9
at 4394988 repeats the same phase from 4394232. Its balance is 378;
the total strictly intervening negative separator capacity is 90, so
288 cannot be allocated within that interval. This is an abstract
first-hit replay, not an initial-sequence counterexample. Even adding
one unit of first-phase-gap funding per unit of gap is insufficient
at synthetic `M=7874413`: the corresponding increment 9 has demand
1062 and eligible total capacity 1027, leaving 35.

`FundedPhaseCredits210.lean` proves the pointwise bound
`balance≤45*e+1263`, hence positive balance at most 29613 for an
increment `e≤630`. Charging at most once for each small increment and
the 420-valued horizon/parity phase gives the conservative fixed bound
`B=(631*420)*29613=7848037260`.

`FundedPhaseCreditAllocation210` explicitly records startup events,
distinct startup keys, eligible sources, allocation amounts, source
capacities and the total funding bound. Row bounds pay the remaining
positive costs; column bounds prevent spending a unit twice. If source
funding is bounded by negative balances plus `c*F_phase`, Lean proves
`S_phase≤B+c*F_phase`. It then proves uniform sublinearity of
`S_phase.toNat` for fixed `c` and fixed phase-label count, conditional
on this certificate. `canonical_travel_of_funded_prefix_allocations210`
proves short travel on capped replays at all sufficiently large canonical
starts if every short capped prefix has such a certificate. The existence hypothesis
is explicit and remains unproved. Current recurrence diagnostics use
the actual separator balances and startup keys from those replays.

The native search keeps its original mode. The additional funded mode
also pays repeated positive small-increment costs. A first positive
cost without an earlier eligible use becomes a small startup charge.
Eligible ordinary negative credit must lie strictly after the chosen
earlier use. Extra funding from a first long phase can be used at its
own event or later. The coefficient 24 matches the travel coefficient
already present in the crossing budget.

```sh
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 24
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_funded_probe.py
```

The funded native search through `M=100000000` checks 440310 synthetic
twin-prime-shaped starts and pays 131257 demands, with maximum observed
startup 39118. There are two cap/travel cutoff stops and no 3000-event
stops. The original negative-only long-reuse mode still reports 36616
paid demands. Independent Python trial-factorization comparison through
2000000 agrees on 14869 starts, 1064 funded demands, two cutoff stops
and maximum startup 18920. `travel_funded_probe.py` independently checks
the row amounts, source capacities, source eligibility and startup
uniqueness for actual-replay controls and the synthetic failures above.

Verified on Lean 4.33.1 with `lake build A166944.Attempt
A166944.TravelTarget A166944.FundedPhaseCredits210`, the standard-axiom
audit and the diagnostics above. Conditional balance and short-travel
theorems depend only on subsets of `propext`, `Classical.choice` and
`Quot.sound`. Universal construction of the funded allocation and the
bridge from the verified finite record range to the eventual threshold
remain open.

## Weighted Hall and endpoint-window obligations, 2026-11-11 JST

Codex continued from `93cdbcf`. `CreditHall210.lean` expands each
integer demand and capacity into individual units and applies the
existing finite Hall theorem in the pinned Mathlib, then counts the
matching by rows and columns. This is an application of Hall's theorem,
not a new combinatorial principle. The imported theorem is
`Finset.all_card_le_biUnion_card_iff_existsInjective'` from
`Mathlib/Combinatorics/Hall/Finite.lean` in Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

`credit_hall_iff_allocation210` proves that a natural-number allocation
with exact row payments and bounded column use exists if and only if
every set of requests has total demand at most the total capacity of
the union of its eligible sources. It includes competition between
requests; checking each request separately does not suffice.
`funded_phase_credit_allocation_of_hall210` constructs the previously
defined funded certificate from these inequalities, the startup bounds
and the total funding bound.

For requests with closed timestamp windows `[left_i,right_i]`,
`CreditWindows210.lean` proves an equivalent criterion: for every
contiguous window `[a,b]`, sum the demands of requests whose entire
eligible interval is contained in `[a,b]`; this must not exceed the
capacity of sources timestamped in `[a,b]`. Source timestamps may
repeat, capacities may vanish, and each request must have a nonempty
window. In the proof, an uncovered source timestamp splits a request
family into two smaller families with disjoint source sets. Otherwise
the hull itself is covered and its window inequality applies.

Only request endpoints need testing. The theorem
`credit_endpoint_windows_iff_allocation210` makes the at most `n*n`
endpoint inequalities equivalent to allocation existence.
`funded_phase_balance_of_endpoint_windows210` consequently proves
`S_phase<=B+c*F_phase` directly from those inequalities and the startup
and funding assumptions. These results supply a finite, explicit
criterion; they do not establish the inequalities on all actual
canonical recurrence prefixes. That recurrence estimate and the
finite-range bridge to the eventual threshold remain open.

The diagnostic `travel_credit_windows.py` reconstructs complete finite
integer replay ledgers without consuming sources. For each endpoint
window it records demand `D`, negative supply `N` and first-phase-gap
mass `F`; if `F>0`, that window requires coefficient at least
`ceil(max(0,D-N)/F)`. Positive deficiency with `F=0` rules out all
coefficients for that fixed eligibility policy. Its result agrees with
the existing chronological allocation probe on seven actual/replayed
or synthetic controls and four coefficients. A separate exhaustive
small-instance comparison with direct subset Hall enumeration passes
2187 checks, including duplicate timestamps and zero demands/capacities.

At the synthetic canonical start `M=56837371`, increment 9 at 56837844
repeats its positive phase from 56837484. The timestamp window `[17,93]`
has demand 1062, negative supply 470 and first-phase-gap mass 234.
Coefficient 2 leaves `1062-470-2*234=124` unpaid; coefficient 3 suffices
on that complete replay. This is not an initial-sequence counterexample.
The native exhaustive run with coefficient 3 through 100000000 pays
131257 demands from 440310 synthetic starts, maximum startup39118,
with two cap/travel cutoff stops and no 3000-event stops. Events after
those cutoffs are not tested by the native run.

```sh
lake build A166944.Attempt A166944.TravelTarget A166944.CreditWindows210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_windows.py
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 3
```

Lean 4.33.1 accepts the new equivalences, allocation constructors and
signed-balance corollary. `#print axioms` on all twelve new theorems
and the existing eventual-short-travel theorem reports only subsets
of `propext`, `Classical.choice` and `Quot.sound`. The ordinary Attempt
import boundary and original A166944 target are unchanged. No new
unconditional infinite-recurrence estimate or twin-prime theorem is
claimed by this checkpoint.

## Composite-gap savings and four-growth balances, 2026-11-11 JST

Codex continued from `2bf0ed3`. The recurrence-side theorem
`moving_horizon_long_composite_seven_growth` strengthens the long
composite-gap estimate to `24*g≤7*G`, for gap `g>10` and event growth
`G=e-1`. A nonunit small factor `f` satisfies `g≤2*f` and `f*f≤e`;
oddness and `g>10` force `f≥7`. Then `48*f≤7*(f*f-1)`. The previous
theorem `3*g≤G` is retained with the same statement as a corollary.

The previous travel estimate reserved nine growth units for those
gaps. The stronger estimate needs seven, leaving two more units for
separating-event credits. `TravelCharged210.lean` defines
`b4=E_phase+V(after)-V(before)-4*(e-1)` at a separator and zero at a
supported event. At every separator this is exactly `b2-2*(e-1)`.
The total coefficient in the checked path budget remains `7+4=11`:

`24*T+V(end)≤24*F_phase+11*G+V(start)+S4`.

The new ledger retains the identical first-phase-gap mass; its
projection into the earlier ledger is proved. The resulting first
crossing still needs `M<24*(F_phase+g)+1315+S4`, now with the smaller
signed balance. Its pointwise bound is `b4≤43*e+1265`. A positive
balance above e315 must be a reused long-prime phase. A positive event
whose phase key is not yet seen has e at most315 and positive part
at most14810. The existing funded certificate, including its
conservative fixed startup bound, is reused without changing its
fields or weakening the original target.

`ChargedPhaseCredits210.lean` proves eventual short travel from
allocation existence on every short capped prefix using these
improved balances. This includes multiplier0: all nonstartup demand
can then be paid only from ordinary negative balances. The original
`24*F_phase` travel term is still present and is handled by the proved
first-phase sublinearity theorem; multiplier0 removes only additional
funding from that term. Allocation existence on all actual prefixes
and the finite-range/eventual-threshold bridge remain open.

The native diagnostic preserves its original default growth charge2
and accepts the additional `--growth-charge 4` option. For this new
cost and zero additional funding, exhaustive replay through100000000
pays127504 requests from440310 synthetic twin-shaped starts, with
maximum startup32580, two cap/travel cutoff stops and no3000-event
stops. The three former small-e9 shortage controls at M4394191,
M7874413 and M56837371 all admit zero-funded interval allocations
under the new costs. Their shortages for the old costs remain valid.
These starts are not original-sequence certificates, and events after
the two cutoffs are outside the native test.

The Python interval checker now tests both growth coefficients and
agrees with the row/column allocation probe on seven controls at four
funding coefficients. Its2187 direct-subset Hall checks still pass.
`travel_credit_prefix.py` independently chooses starts and first hits
by trial division, checks quiet indices, and checks all row, column,
eligibility and startup conditions. Through2000000 its totals agree
exactly with the native sieve:14869 starts,1049 requests, two cutoff
stops, zero event-limit stops, maximum startup15688. The unchanged
default native mode with funding3 retains the previous2000000 totals
of1064 requests and maximum startup18920.

There is a further local refinement available for subsequent work:
`residualPhaseSeparatorBalance210` uses
`24*(g-first_gap)+V(after)-V(before)-11*G` at unsupported events.
Lean proves it is at most b4 and that it supports the same one-step
travel budget. Its complete path ledger and allocation experiment are
not yet implemented; the current exhaustive allocation result uses b4.

```sh
lake build A166944.Attempt A166944.TravelTarget A166944.CreditWindows210 A166944.ChargedPhaseCredits210
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 0 --growth-charge 4
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_windows.py
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_prefix.py 2000000 --native /tmp/travel_credit_search
```

On Lean4.33.1, the twelve new public theorems and the retained
one-third composite bound pass the axiom audit using only propext,
Classical.choice and Quot.sound. The existing endpoint-Hall equivalence
also passes. Attempt retains its prior imports and the canonical
A166944 theorem remains open.

## Residual path budgets, smaller startup costs and unused credit, 2026-11-11 JST

Codex continued from `de97718`. `ResidualPhaseCredits210.lean`
integrates the residual step balance into an exact ordered ledger.
Its first-phase-gap sum is identical to that in the previous ledger,
and its signed sum is no larger than the four-growth signed sum.
Lean proves the full path budget, the necessary first-crossing
condition, and short travel conditional on the finite net inequality
`24*(F_phase+Q(M))+1315+S_res≤M`, where
`Q(M)=sqrt(4*(3*M+4))` is the natural square root. This leaves the
negative signed sum available to cancel first-phase travel.

`ResidualStartup210.lean` proves a sharper event-level startup bound.
A positive event that is not a reused long-prime phase has increment
at most169 and positive part at most1478. For a short gap, the bound
comes from `24*g≤240` and the eleven-growth charge. A first long prime
has no residual gap. A long composite uses a factor f≥7 with
g≤2*f and f*f≤e. Positivity forces f≤13 and e≤172; oddness and the
factor3 first-hit bound exclude e171, leaving e≤169. Its charge is
also bounded using `24*g≤7*G`.

An admissible startup increment is an odd unsupported value between3
and169. There are77 such values, kernel-checked on the170-element
range. The pre-event horizon is even, so its residue modulo210 has105
possible values, and the hit has two parities. The encoding
`420*e+4*h+parity` is injective on those inputs, giving16170 admissible
keys. Positive startup events have keys in this set. Distinct keys and
the1478 pointwise cap yield the fixed total
`B_res=16170*1478=23899260`, replacing the old7848037260 bound in the
new allocation corollaries.

`ResidualAllocation210.lean` defines unused credit U as total supply
minus total allocation. Source capacities show this subtraction is
nonnegative. Instead of discarding U, Lean proves
`S+U≤startupBound+c*F_phase`, and in particular
`S+U≤B_res+c*F_phase` for the admissible startup keys. Thus the finite
inequality

`(24+c)*F_phase+B_res+24*Q(M)+1315≤M+U`

suffices for the net crossing budget. The general theorem also accepts
the exact startup sum in place of B_res. No asymptotic threshold is
needed for this implication. A uniform bound on the net expression is
still required to apply it to all actual prefixes.

`CreditDeficits210.lean` proves that failure of weighted interval Hall
has a deficient window of least timestamp length; every strictly
smaller contained window has enough capacity. The diagnostic now
extracts such minimum-length endpoint windows. The remaining
recurrence-specific task is to exclude their existence on the actual
capped canonical prefixes. No such exclusion is asserted here.

The native residual mode preserves the earlier default and four-growth
modes. Through100000000, zero additional funding pays107076 requests
from440310 synthetic twin-shaped starts, maximum startup20096, with
two cap/travel cutoff stops and no3000-event stops. Python trial
division agrees through2000000:14869 starts,927 requests,two cutoff
stops, maximum startup10740. The interval checker tests all three
balance modes on seven controls at four funding coefficients and
retains2187 direct-subset Hall comparisons. The earlier default and
four-growth prefix totals remain1064 and1049 requests, respectively.
The synthetic origins are distinct from original-sequence certificates;
the native run does not inspect events after its two cutoffs.

The optional allocation trace checks the exact identity
`S+U=startup+c*F_phase` on every paid prefix of these integer replays.
`travel_residual_net.py` checks cancellation and finite margins using
both the actual startup sum and B_res. For the replay from45895573,
the minimum fixed-startup net margin is21418714; from367232911 it is
341577624. These are integer diagnostics, not new Lean-certified
record-range extensions. The certified prefix still ends at45895573.

```sh
lake build A166944.Attempt A166944.TravelTarget A166944.ResidualAllocation210
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 0 --residual
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_prefix.py 2000000 --residual --native /tmp/travel_credit_search
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_windows.py
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_residual_net.py
```

Lean4.33.1 accepts the fifteen new public results. Their axiom audit,
and that of the existing implication to unbounded twin primes, uses
only propext, Classical.choice and Quot.sound. Attempt's imports and
the original target remain unchanged. Universal allocation existence,
the uniform net bound, a usable threshold and the finite-range bridge
remain open.

## The fifty-million bridge and minimal deficient windows, 2026-11-11 JST

Codex continued from `bea9fc28b2038c0cd442b6d5c604b56f74d24f11`.
`VerifiedTravelExtension.lean` exposes the already checked record and
previous maximum at index 45895575. `VerifiedFiftyMillionBridge.lean`
checks 37 capped events from that record, starting with horizon 91791144
and ending at index 45896532 with horizon 91793058. The event travel is
957. The kernel checks the replay and the quiet return with square root
9580. The next strict record is 91793059 at index 91793061. This proves
the index and twin-primality results for every strict record
`5 < R ≤ 91793059`, and short travel for actual capped canonical starts
`45895573 ≤ M < 50000000`. It closes the finite bridge for this route.
`generate_fifty_million_bridge.py` regenerates the replay by integer trial
division. The range theorem uses the Lean checks.

`ResidualThreshold210.lean` proves the explicit arithmetic implication
from `2*(24+c)*F_phase ≤ M+2*U` at `M ≥ 50000000` to the previous
net crossing budget. For `Q(M)=sqrt(4*(3*M+4))`, it proves
`1536*Q(M) ≤ M` and uses `64*(23899260+1315) ≤ 31*M`.
A `ResidualReserveCertificate210` contains the exact signed sum,
the funded allocation, admissible startup keys with individual cost at
most 1478, and the reserve inequality. Such a certificate on every
short capped prefix rules out the first crossing.
`TwinReserveTarget210.lean` combines that implication with the finite
bridge: for any fixed funding multiplier `c`,
`ResidualReserveCondition210 c` implies the unrestricted record index,
the original A166944 `Target`, and unbounded greater twin primes.
The reserve condition itself is open. In particular, a threshold for the
implication does not establish existence of the certificates.

`CreditDeficitStructure210.lean` proves two consequences of minimality:
both endpoints are attained by positive requests, and each interior cut
is crossed by a positive request confined to the window. The cut proof
splits supply and, if no positive request crosses, splits all demand
between two proper subwindows. `RecurrenceDeficit210.lean` uses actual
hit timestamps `2*r+1` and `2*u+1` for an annotated same-phase reuse of
increment `e`. The cut witness satisfies `2*e ∣ u-r`, and the horizon
drift is a positive multiple of `L=lcm(210,2*e)`. An intervening increment
does not divide `L`. The endpoint witnesses are also actual hit times
under this annotation hypothesis. The uniform construction of the
annotated residual interval problem and exclusion of deficient windows
on arbitrary actual prefixes remain open.

The native `--residual-reserve` run at multiplier zero covered 440310
synthetic canonical-shaped starts through 100000000. It paid 107076
requests, with maximum startup 20096, two cap/travel cutoff stops, and
no event-limit stops. For starts at or above 50000000 it checked 12139762
prefixes and found minimum half-reserve margin 48558783, at start
50026063 and hit 50079773. The Python trial replay independently checks
the reported witness and the balances along that start, not the minimum
over all starts. The smaller through-2000000 regression retains the
1064 default, 1049 four-growth, and 927 residual requests. These runs
use synthetic origins and stop at the configured cutoff.

`travel_relaxed_cycle_probe.py` checks a separate obstruction in the
clipped modulo-210 model. Its 25-event cycle has travel 210, horizon
growth 420 and repeated full residual balance +420. It cannot be an
actual recurrence cycle: the two same-phase uses of increment 77 have
horizon drift 210, below their required period 2310. The cycle shows
why the clipped transition table alone cannot imply a uniform reserve.

```sh
lake build A166944.Attempt A166944.TwinReserveTarget210 A166944.RecurrenceDeficit210
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 0 --residual-reserve > /tmp/travel_reserve.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/generate_fifty_million_bridge.py
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_half_reserve_probe.py /tmp/travel_reserve.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_relaxed_cycle_probe.py
```

Lean 4.33.1 accepts the 23 new public theorems. Their `#print axioms`
results are contained in `propext`, `Classical.choice`, and `Quot.sound`.
The original target and the imports of `A166944.Attempt` are unchanged.

## Actual residual intervals and a direct signed reserve, 2026-11-11 JST

Codex continued from `78c87b2a2a60cccf40812836ddcb52b797891f00`.
`ResidualEventTrace210.lean` extracts a finite ordered array from an
actual residual ledger. Each row retains its first-hit proof, prior
long-prime phase keys, first-phase gap and residual cost. The sums
equal the input ledger's `F_phase` and `S`. Consecutive rows meet at
the same recurrence state, and earlier rows account for every
previously seen phase in an initially empty ledger.

`ResidualIntervals210.lean` uses the latest earlier long-prime event
of the same key for a reused long prime. Other positive requests use
the latest positive event of the same key. Positive events without an
anchor are startups. Their codes are distinct and admissible, and
each costs at most 1478. Sources are the negative parts of the event
costs. At zero additional funding, hit timestamps implement exactly
the eligible ordinal range `anchor < source ≤ request`.
`ResidualIntervalBudget210.lean` constructs an exact Hall allocation
if the window inequalities hold. It proves `S+U=startupCost` for the
resulting certificate and recovers the previous reserve certificate
from the signed inequality with this exact startup cost.

`ResidualDeficitBounds210.lean` instantiates minimal deficient windows
on these actual rows. The endpoints are actual hits. Across each
interior cut there is a positive same-phase request with the full
index and horizon congruences. Such a request requires at least 630
horizon drift, since a positive multiple of 210 below 630 would force
its increment to divide 210. It cannot connect consecutive events.
For a request with just one intermediate event, the middle increment
is at least 463 and exceeds the request increment. If the middle is
short, composite or the first long prime of its phase, its negative
balance pays the entire request. The composite proof reuses the small
divisor lemma and charges at most four times its growth to travel.
Hence a deficient window spanning at most three events needs a
reused long prime in the middle. Its earlier occurrence is strictly
before the window, with horizon drift at least `210*463 = 97230` to
the middle. Longer windows and that remaining repeated-prime case
are open.

`ResidualThreshold210.lean` isolates the crossing overhead inequality
`2*(23899260+24*Q(M)+1315)≤M` for `M≥50000000`. Thus
`2*(24*F_phase+S)≤M+47798520` alone suffices for the crossing budget.
`TwinSignedReserveTarget210.lean` checks its implication from the older
allocation and half-reserve condition for any fixed funding multiplier,
and its implication to unrestricted index, the exact `Target`, and
unbounded greater twin primes. The signed inequality is still open on
arbitrary actual short capped prefixes from canonical greater twin
prime records at or above the threshold.

The bounded native search through 100000000 checks 12139762 relevant
prefixes from synthetic canonical-shaped starts at or above 50000000.
The minimum stronger signed margin `M-2*(24*F_phase+S)` is 48546931
at start 50026063 and hit 50079773. Across all 440310 synthetic starts,
14 requests have one intervening event, and none of those intermediate
events is a reused long prime. The least one-middle payment margin is
29862 at start 62782879 and hit 62787155. Trial division reproduces both
reported witnesses and their margins over the corresponding individual
traces. The latter request has endpoint increment 13, middle increment
2719, demand 36 and negative supply 29898. The previous reserve witness,
2187 direct subset comparisons, and old mode totals through 2000000
also agree. These are bounded synthetic replay diagnostics.

```sh
lake build A166944.Attempt A166944.TwinSignedReserveTarget210 A166944.ResidualDeficitBounds210 A166944.ResidualIntervalBudget210
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 0 --residual-reserve > /tmp/travel_reserve.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_half_reserve_probe.py /tmp/travel_reserve.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_windows.py
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_prefix.py 2000000 --residual --native /tmp/travel_credit_search
```

The Lean 4.33.1 build and audit of 40 declarations pass, using only
`propext`, `Classical.choice`, and `Quot.sound`.

## Overlapping prime reuse intervals and a two-thirds growth budget, 2026-11-11 JST

Codex continued from `e34d06bc3377df1f88b8b1a0467fa6048414332d`.
`ResidualNetContributions210.lean` defines each event's net cost as
its signed residual cost plus 24 times its first-phase gap. The sum
is exactly `W=24*F_phase+S`. Outside the increments dividing 210, the
first-phase term cancels, leaving `24*g+ΔV-11*(e-1)`. The positive
part is at most `37*e+1326`. The strengthened three-event deficit
witness retains the right request and gives a preceding reuse of its
middle prime `f≥463` with drift at least `210*f`. Since the right
increment is smaller than `f`, twice their combined positive net
cost is at most that drift.

`ResidualReuseOverlap210.lean` uses half-open intervals of horizon
growth. The union of crossing intervals counts the shared portion
once. Two reuse costs fit in half their union if the larger
increment is at least 86. Distinct primes `p,q` with equal drift
force that drift to be a multiple of `210*p*q`, which pays the two
costs even at small primes. This also pays more events if their
increments are bounded by `max(p,q)` and twice their number is at
most `min(p,q)`. The drifts are equal when the two flank widths
differ by less than 210, in particular for consecutive matching
flanks. With two thirds of the growth, an individual prime of at
least 13 or two primes with maximum at least 41 fit by the pointwise
cost and reuse-period bounds.

`ResidualGrowthAllocation210.lean` checks the load from all active
windows at each left endpoint and sums capacities with no duplicate
growth units. It also sums signed costs over disjoint growth blocks.
A block `[left,right)` can select any costs with pre-event horizons
in `(left,right]`, so a negative contribution belongs to at most one
block. The unselected costs stay in the signed remainder.
`TwinCrossingBudget210.lean` uses the actual gap `g` and the cap through
the candidate crossing event. Its open condition asks only for
`W+24*g+1315 ≤ M` at such crossings and implies the original target
and unbounded twin primes. The prior signed reserve implies this
condition. For `G=C-(2*M-2)≤M+6` and `M≥50000000`, the arithmetic
bound `3*W≤2*G+47652293` suffices using `1536*Q(M)≤M`. Thus the
two-thirds block bounds can be combined with a bound of 47652293
on three times the remaining signed sum. These uniform bounds on
actual prefixes are open.

The bounded native search through 100000000 had 36065 positive
long-prime reuse windows, 11340 overlapping pairs and 6577 crossings
from 440310 synthetic canonical-shaped starts. Three overlapping
pairs have distinct primes and equal widths. Half of the union width
fails to cover the two positive costs in 83 pairs. The lowest
margin is -2132 at M69921739, using increments 11 and 13, costs 1276
and 1260 and union width 2940. Negative net costs inside that interval
sum to -17940, giving a margin of 33748 when included. The maximum
uniform load at this start is exactly 34556/15015, with rounded
scaled load 2301433/1000000. There are 452 overloaded starts and a
maximum depth of 11.

Merging overlapping windows on each complete capped trace gives
27846 blocks. Charging every signed event in each block to half its
growth fails 23780 times. Selecting the positive long-prime reuse
costs and all negative net costs within each block leaves one
failure, a single increment 13 at M41453053. Its width is 2730 and
its positive cost 1380 with no negative net cost inside, giving
margin -30. That start is below the 50M threshold.
Rechecking the blocks every time a reuse window arrives gives 38115
component checks at the two-thirds rate, all nonnegative with
minimum 1200 at M89666641 and horizon 179336112. The block selection
stays fixed between these arrivals. For all 12139762 tested prefixes
from M≥50M, three times the signed remainder is at most 3770442,
attained at M86278501 and hit 86353653. Trial division independently
reproduces these reported witnesses on their own traces. The runs
retain the two cutoff stops and no event-limit stops. These are
finite tests on synthetic starts.

```sh
lake build A166944.Attempt A166944.ResidualGrowthAllocation210 A166944.TwinCrossingBudget210 A166944.ResidualIntervalBudget210
g++ -O2 -Wall -Wextra -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search 100000000 --funded 0 --residual-reserve > /tmp/travel_overlap.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_reuse_overlap_probe.py /tmp/travel_overlap.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_half_reserve_probe.py /tmp/travel_overlap.log
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_credit_prefix.py 2000000 --residual --native /tmp/travel_credit_search
```

Lean 4.33.1 builds the selected modules and the audit of 35
declarations uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Refined startup and scaled reuse costs, 2026-11-11 JST

Codex continued from `da7953780f66c0664cfe8e994ecfbe1596240201`.
`ResidualStartupWeights210.lean` bounds the positive startup cost
at increment `e` by `min(1478, 1326 + K(e) - 11*e)`, with natural
subtraction. Here `K(e)=48*f` for the first proper divisor in
`[3,5,7,11,13]`, or 240 if there is no such divisor. In the latter
case the eligible odd increment at most 169 is prime, so a first
long gap is already deducted and the remaining gap is at most 10.
For `gcd(e,210)=h`, the parity of the hit fixes the pre-event horizon
modulo `2*h`, including the even-horizon constraint when `h=1`.
Each increment therefore has at most `2*(210/(2*h))` startup keys.
The weighted finite sum is 6,181,254, checked with `decide +kernel`.
For the original ledger this yields the sufficient bound
`3*(24*F_phase + S_nonstartup) ≤ 2*G + 29108531`, with all first
gaps and all signed non-startup costs included.

`ResidualScaledPotential210.lean` uses `V'=floor(8*V/9)≤1120`.
For supported events the full gap satisfies
`24*g + V'(after) ≤ 11*(e-1) + V'(before)`. For other events keep the
signed cost `w'=24*g+ΔV'-11*(e-1)` with positive part at most
`37*e+1131`. A reused unsupported prime of increment `e` has at least
`210*e` growth, and its whole positive cost fits in two thirds of
that interval. In particular the bound for 11 is 1538 against 1540.
Latest-long-anchor windows of the same key are disjoint, so the
bound also covers an arbitrary selected set of those reuses together.
Two reuses with maximum increment at least 35 fit in two thirds of
their union. The bound `k*(37*e+1131)≤140*e+credit` also works for
`k` selected events of increments at most the largest reuse `e`
using the negative credit in the union. For two costs, 1536 of
enclosed negative credit always suffices. One short-gap event of
increment at least 265, or a composite event of increment at least
665, supplies that much credit.

The exact ordered trace telescopes `V'` together with travel and
horizon growth. The scaled signed sum `W'` only needs to obey
`W'+24*g+1175≤M` at actual capped first crossings. Lean verifies that
this condition implies the original target and unbounded greater
twin primes. `signed_budget_iff_block_slack` works with either
ledger. For the scaled condition, if `A` is the sum of selected
disjoint block widths, `D` their total slack `2*width-3*cost`,
and `R` the remaining signed sum, the budget is equivalent to
`3*R≤3*M-72*g-3525-2*A+D`. The unrestricted mixed-key overlap and
signed remainder bounds on actual crossing prefixes are open.

The trial-division diagnostic checks 14,877 capped synthetic replays
through 2,000,000 and at eight controls, with 222 positive scaled
reuse windows and 394 endpoint-window checks. With growth alone one
window fails. At synthetic `M=69921739`, its width is 2940 and it
contains costs 1170, 306, 1169 for increments 11, 11, 13. The
margin `2*width-3*demand` is -2055. Including negative costs of
-17794 gives margin 51327. These include a gap of 26 with composite
increment 1157, whose scaled cost is -11532. With enclosed negative
credit all 394 checks pass, with minimum margin 1464 at
`M=89666641` on `[179333802,179336112)`. These are bounded tests on
canonical-shaped starts.

```sh
lake build A166944.Attempt A166944.ResidualStartupWeights210 A166944.ResidualScaledPotential210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_reuse_overlap_probe.py --scaled-limit 2000000 \
  --control 22933441 --control 23613589 --control 23619049 --control 41453053 \
  --control 45895573 --control 69921739 --control 86278501 --control 89666641
```

The original native/Python overlap comparison through 2,000,000 also
agrees. The Lean 4.33.1 build and audit of 34 declarations pass with
only `propext`, `Classical.choice`, and `Quot.sound`.

## Adjusted costs and first-hit deficit bounds, 2026-11-11 JST

Codex continued from `b91ad42e262113912e5714dd337fce0ed01ba517`.
`ResidualAdjustedCosts210.lean` splits `W'=24*F+sum(u)` exactly, where
`F` sums the first long gap of each unsupported prime phase and
`u=w'-24*f` at the corresponding event. A long reuse uses its latest
long anchor and the other repeated positive costs use their latest
positive predecessor of the same key. `ResidualStartupWeights210.lean`
uses the existing reachable-phase count and travel cap `K(e)` to
bound each adjusted startup by `max(0,1131+K(e)-11*e)`. A positive
adjusted cost outside the long reuses requires `e≤159`. The weighted
finite sum is 4,651,452. Both the original and adjusted sums share the
phase counting proof.

`ResidualGrowthWindows210.lean` applies the existing interval Hall
and minimal-deficit results to capacity `2*(b-a)+3*N(a,b)`, where
`N` counts the negative cost parts at pre-horizons in `(a,b]`. The
integer sources are `[a,b-1]`, with a negative cost at `H-1`. Positive
requests attain both endpoints of a minimal deficit and cross every
interior cut. The deficit at a cut is at most three times the demands
of requests crossing it, since both proper subwindows pay their own
requests.

`ResidualSmallReusePairs210.lean` verifies the coarse list of 19
possible prime pairs and maximum width 6,833. An actual first-hit
gap above 14 rules out factors 3, 5 and 7 on both sides of the even
horizon, leaving 15 horizon residues modulo 210. The resulting
pointwise scaled cost caps for increments 11, 13, 17, 19, 23, 29, 31
are 1522, 1537, 1722, 1759, 1704, 1809, 1744. The refined list has
15 pairs, all with maximum prime at most 23 and window width at
most 5,276. This applies to any deficient growth window with exactly
two positive requests in the long-prime-only system.

`ResidualSmallAdjusted210.lean` checks the event and horizon residues
for the four composite increments 9, 25, 45, 63. The resulting cost
caps are 979, 739, 84, 108. The last two fit in two thirds of their
same-phase drift. A single adjusted request can be deficient only
for increment 9 at width 630 or 1260, or increment 25 at width 1050.
For a minimal single-request deficit these are the actual window
widths, and the enclosed negative credit in unscaled units is at
most 558, 138, or 38 respectively.

If every adjusted window fits, then `3*W'≤72*F+13954356+2*G`.
For `M≥50000000`, the uniform sufficient first-travel inequality
is `64*(72*F+13957891)≤61*M`; the actual gap also gives a sharper
per-prefix condition. The existing sublinear first-phase theorem
gives the first-travel inequality at sufficiently large `M`, with
an existential threshold. The cofactor bound also proves that a
single scaled cost is nonpositive when
`48*(C+1)+1120*e≤11*(e-1)*e`. The adjusted window inequalities on
actual prefixes and the first-travel inequality between the finite
bridge and the asymptotic threshold remain open.

The trial-division comparator with the adjusted costs independently
reproduces the 2,000,000 scan plus eight controls with 14,877 starts,
956 requests and 1,981 window tests, of which 26 fail with growth
alone and none with negative credit. Extending the scan to 10,000,000
plus the same controls gives 58,986 starts, 6,566 requests, 10,719
window tests, 59 growth-only failures and zero signed failures. The
least signed margin is 9,321 at synthetic `M=3893863` on
`[7788016,7788646)`, with increment 9, cost 35 and negative credit
2,722. The previous native/Python overlap comparator through 2,000,000
still agrees. The scans are on capped canonical-shaped synthetic starts.

```sh
lake build A166944.Attempt A166944.ResidualGrowthWindows210 A166944.ResidualSmallAdjusted210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_reuse_overlap_probe.py --scaled-limit 10000000 --adjusted \
  --control 22933441 --control 23613589 --control 23619049 --control 41453053 \
  --control 45895573 --control 69921739 --control 86278501 --control 89666641
```

Lean 4.33.1 builds the selected modules. The audit of 40 declarations
uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Rebalanced costs and capped first payments, 2026-11-12 JST

Codex continued from `618462ef55111b485da358f16f939cdf7262c846`.
`TravelClip210.lean` proves that an actual event with
`gcd(e,210)>1` gives a first clipped hit at the same gap with
increment `gcd(e,210)`. `TravelRebalanced210.lean` checks the
generated potential on all 22,050 residue states with even horizon.
The cap is 1,036. The supported steps obey the usual inequality
`24*g + V_after ≤ 11*(e-1) + V_before`. For increments
9, 25, 45 and 63 the corresponding allowances are 315, 525,
315 and 315, half of their respective minimum same-phase drifts.
The original scaled-cost bounds remain available.

`ResidualRebalancedCosts210.lean` splits the signed net cost
`w` into the first payment `phi=min(24*f,max(0,w))` and the
remainder `u=w-phi`. Here `f` is the first long gap of the
unsupported prime phase, or zero at other events. The cap
preserves negative net costs and limits the separate payment
to positive net cost. The startup sum for `u` is at most 4,054,512.
`rebalanced_request_fits210` proves `3*d≤2*width` for every
positive reuse request, so `rebalanced_deficit_has_multiple_requests210`
requires at least two requests in any deficit. This covers the
previous single-request exceptions at increments 9 and 25
without using enclosed negative cost.

For an event of increment `e` and pre-horizon `C`, put
`g*=min(2*e, floor(2*(C+1)/e))`. The first payment is at most
`min(24*g*, max(0,24*g*+1036-11*(e-1)))`. It vanishes when
`48*(C+1)+1036*e≤11*(e-1)*e`. For a prefix with total horizon
growth `G` and all pre-horizons at most `U`, a positive cutoff
`L` gives the following bound on the sum `Phi` of first payments:

```text
W = L*(L+1)
Phi ≤ 210*sum_{prime p≤L} min(48*p,37*p+1047)
      + floor(max(0,48*(U+1)+1036*(L+1)-11*W)*G/W).
```

`ResidualFirstPayment210.lean` counts low prime payments once per
reachable phase and bounds the tail after subtracting the event's
own growth. If every window fits, the signed sum satisfies
`3*sum(w)≤3*Phi+12163536+2*G`. The uniform sufficient first
budget is `64*(3*Phi+12166819)≤61*M` for `M≥50000000`.
There is also an actual-gap version with overhead 1,091 and an
eventual bound from the existing sublinear first-phase theorem.
The window inequalities for overlapping requests and an explicit
first-payment budget down to the finite bridge are open.

On synthetic canonical-shaped starts through 10,000,000 plus eight
controls, the trial-division scan checks 58,986 starts, 6,357
requests and 10,210 intervals. Six intervals are deficient with
growth alone. All 10,210 fit with enclosed negative credit, with
least signed margin 315 at `M=6874213` on `[13752100,13752730)`.
The earlier adjusted scan and native/Python comparator through
2,000,000 also pass.

```sh
lake build A166944.Attempt A166944.ResidualFirstPayment210 A166944.ResidualSmallAdjusted210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/rebalanced_potential_probe.py --lean-data \
  | cmp - A166944/TravelRebalanced210Data.lean
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_reuse_overlap_probe.py --scaled-limit 10000000 --rebalanced \
  --control 22933441 --control 23613589 --control 23619049 --control 41453053 \
  --control 45895573 --control 69921739 --control 86278501 --control 89666641
```

Lean 4.33.1 builds the selected modules. The audit of 42 declarations
uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Two rebalanced requests and endpoint offsets, 2026-11-12 JST

Codex continued from `cd5acc84ace0924aec1a11411106ccc92d02e7e6`.
Every positive request fits within two thirds of its minimum
phase period `lcm(210,2*e)`. Right endpoints with one phase key
are separated by at least that period. Their terminal periods
are disjoint and lie inside the respective requests, so any
collection of requests of one key fits its containing window.
This applies to long, short, and composite requests.

`ResidualRebalancedPairCaps210.lean` restricts a long reuse in
a two-request deficit to increment at most 31. Other positive
requests have increment at most 159 and cost at most 1,166.
These bounds leave 23 increments to test and 72 coarse pairs.
The extended clipped checker bounds costs for 13 composite
increments. The post-event potential for each of seven small
primes is bounded using the 15 horizon residues required by gaps
above 14. The refined caps give 35 unordered increment pairs,
width at most 5,093, and negative credit at most 1,363 for any
two-request deficit. A single enclosed composite increment
of at least 295 contributes at least 1,364 credit and pays
the possible shortfall.

For requests in event order with pre-horizons `C<H`, the
containing width is at least `lcm(210,2*e)+H-C`, where `e`
is the earlier increment, and `H-C≥e-1`. The increment-23
checks combine the two horizon-specific caps with the minimum
offset modulo 210. Two requests at increment 23 always fit
from growth alone. A positive increment-63 cost requires
pre-horizon 22 modulo 210. For a potentially deficient pair
with 9 earlier, the offset must be between 8 and 34, where
the first-hit table caps the increment-9 cost by 266. If 63
is earlier, its own growth gives an offset of at least 62.
Both orders of (9,63) therefore fit. The resulting list has
33 pairs, including pairs with equal increments and different
phase keys. The general signed bound on those pairs and on
overlaps of three or more requests remains open.

The independent Python calculation reproduces the counts and
caps. On the synthetic start `M=7163911`, the interval
`[14342410,14343058)` contains two increment-9 requests of
234 and 231. Its growth-only margin is −99. Enclosed negative
cost gives margin 7,731. Through 10,000,000 plus the same eight
controls, all 10,210 synthetic intervals fit with signed
credit. Five growth-only failures share that pair and those
endpoints. The sixth is the three-request control at
`M=69921739`.

```sh
lake build A166944.Attempt A166944.ResidualFirstPayment210 A166944.ResidualRebalancedPairOffsets210 A166944.ResidualSmallAdjusted210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/rebalanced_pair_probe.py
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/travel_reuse_overlap_probe.py --scaled-limit 10000000 --rebalanced \
  --control 22933441 --control 23613589 --control 23619049 --control 41453053 \
  --control 45895573 --control 69921739 --control 86278501 --control 89666641
```

Lean 4.33.1 builds the selected modules. The audit of 34 declarations
uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Two further certified record replays, 2026-11-12 JST

Starting from `3682029d1e486f0485ed843b79e9edfee71b4aa7`, the first
replay has 53 nonunit events after `M=91793059`. Its terminal horizon
is 183616422 and its next record is 183616423 at index 183616425.
The second replay has five nonunit events. It ends at horizon
367232910 and reaches record 367232911 at index 367232913.
`record_index_and_twin_prime_of_le_367232911` proves the position and
twin-primality statements for every strict record `5 < R ≤ 367232911`.
`twin_travel_from_367232911` transports the remaining travel hypothesis
from the last certified record to the existing unrestricted reduction.

The independent recurrence in `diagnostics/generate_record_replays.py`
through index 367232913 reproduces both terminal horizons and all 58
nonunit indices. `lake build A166944.VerifiedRecordExtension` and the
audit of the six added declarations pass on Lean 4.33.1 with only
`propext`, `Classical.choice`, and `Quot.sound`.

## Crossing budget for small actual horizon growth, 2026-11-12 JST

`rebalanced_net_cost_le_growth210` bounds each signed net cost by
`146*(e-1)`, using the existing cost cap for `e ≥ 11`, the cap 315 at
`e=9`, and zero cost at `e=3,5,7`. Summation gives `W ≤ 146*G` with
the first payments included in `W`. For `M ≥ 50000000` and `150*G ≤ M`,
`rebalanced_crossing_budget_of_small_growth210` combines this estimate
with the square-root gap bound to prove `W+24*g+1091 ≤ M`.

Lean 4.33.1 checks the new proofs and the existing pair-offset module.

```sh
lake build A166944.TravelMod210 A166944.VerifiedRecordExtension A166944.Attempt
lake build A166944.Attempt A166944.ResidualFirstPayment210 A166944.VerifiedRecordExtension A166944.ResidualRebalancedPairOffsets210
```

The audit of all nine declarations from the two changes uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## Growth constraints at the first travel crossing, 2026-11-12 JST

From `c72443c4dbd4319d56c2d0d709a05e24a5a8bb79`, a potential `U`
takes value two at `(s mod 6, C mod 6) = (2,0), (5,2), (0,4)` and zero
elsewhere. The parity and divisibility of increments three and five
give `2*g+U_after ≤ 5*(e-1)+U_before` at every actual first hit. For
`e ≥ 7` the bound follows from `g ≤ 2*e` and `U ≤ 2`.

Let `H` be the sum of `e-1` at events with `e-1 < 3*(gap+1)`. At all
other events `6*gap+3*U_after-3*U_before ≤ 2*(e-1)`. The telescoped
bound `6*t ≤ 2*G+13*H+6` gives the two necessary growth inequalities
for an actual first crossing. Only gaps at most ten with `e ≤ 33`,
or longer gaps ending at a prime with `(e-4)*e < 6*(C+1)`, contribute
to `H`. `growth_at_large_gaps_le_count` also bounds `H` by their count
times an increment cutoff. The square-root gap bound gives
`100*M < 501*G` and `M < 14*H`.

The exact signed lower bound at a first crossing retains both endpoint
potentials and the actual `11*G` charge. Its strict reverse on the
remaining crossings above the finite prefix implies the full target.
The reverse inequality remains open.

The bounded native scan over synthetic twin-shaped starts in
`[367232911,377232911]` checks 33,855 starts, 2,420,497 prefixes and
2,386,642 legal next hits. Every start stops at a quiet return and no
prefix has `150*G > M`. The largest `G/M` is `307236/375243109` and
the largest `H/M` is `184602/375243163`. Independent trial division
with `travel_residue_probe.py` reproduces both extremal traces and
the synthetic crossing controls at `M=13` and `M=43`. The existing
residual-reserve diagnostic through 20,000 gives identical output
before and after the native change.

```sh
lake build A166944.Attempt A166944.ResidualFirstPayment210 A166944.VerifiedRecordExtension A166944.ResidualRebalancedPairOffsets210 A166944.RebalancedCrossingGrowth210
c++ -O2 -Wall -Wextra -Werror -std=c++17 diagnostics/travel_credit_search.cpp -o /tmp/travel_credit_search
/tmp/travel_credit_search --crossing-growth 13 100000
/tmp/travel_credit_search --crossing-growth 367232911 377232911
```

Lean 4.33.1 accepts the eight added theorems. The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. The composition
with the existing position, primality and unboundedness theorems is
also checked.

## First-payment phases and duplicate demand width, 2026-11-12 JST

From `7b35561133bfc0d24c05709a39772780d191f1a8`,
`RebalancedFirstPaymentBudget210.lean` counts positive first-payment
keys. A gap longer than ten excludes the two residues ±1 modulo 3 and 5
for the even horizon. For increments at least 127, positive net cost
forces a gap longer than fourteen and excludes ±1 modulo 7 as well.
This gives 21 or 15 horizon residues, each with two hit parities.
At increments at least 339, positive first payments require
`e-1 < 3*(gap+1)`. The cutoff at `L ≥ 338` uses the resulting 42 or 30
phase counts below the cutoff and the growth `H` for the tail.

For every positive repeat demand `P_i`, the interval of width
`ceil(3*P_i/2)` ending at its event horizon lies in its original
request interval. The intervals on the same key are disjoint. Let
`U` be the union, `O` the sum of widths minus `|U|`, and
`Q = sum (P_i mod 2)`. Then `3*sum P_i + Q = 2*(|U|+O)`.
`rebalanced_overlap_width_le_prior_different` bounds `O` by the
sum of each interval's length before the latest earlier positive
request of another key.

Let `N_in` be the negative residual costs at coordinates `C_i-1`
inside `U`. At an outside event with `e ≥ 339` and
`3*(gap+1) ≤ e-1`, the cost is at most `1012-3*(e-1)`.
Sum that guaranteed credit as `N_out`. For the same gap condition
and `e ≥ 507`, the credit from either location covers at least the
event's growth. With `E = 2*O-2*(G-|U|)-Q-3*(N_in+N_out)`, the
verified bound is `3*W ≤ 3*Phi+12163536+2*G+E`. The exact sufficient
prefix budget is
`3*Phi_upper+12163536+35*G+72*g+3*V_start+E < 36*(M+1)+3*V_end`.
The uniform sufficient estimate is
`64*(3*Phi_upper+12166819+E) ≤ 61*M` under the existing short-prefix
and crossing-gap bounds. `target_of_rebalanced_overlap_crossings210`
uses the exact prefix budget on actual crossing candidates. Its
universal hypothesis remains open.

Trial division with the independently generated rebalanced potential
reproduced all 22,050 packed potential values and checked the terminal
width and credit identities on eight synthetic controls. The scans on
`[7163911,7263911]` and `[367232911,367332911]` used 533 and 328
twin-shaped starts and inspected 7 and 29 prefixes with overlapping
terminal intervals. The synthetic prefix at `M=367264309` ending
after the request at horizon `734547102` has `O=45`, `|U|=1017`,
`G=18502`, and `Q=N_in=N_out=0`. Its terminal union alone is short
by 90 budget units, while unused growth contributes 34,970.

```sh
lake build A166944.Attempt A166944.RebalancedOverlapBudget210 A166944.ResidualRebalancedPairOffsets210
python3 diagnostics/rebalanced_pair_probe.py
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=diagnostics python3 - <<'PY'
from rebalanced_potential_probe import rebalanced_potential
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at
from travel_reuse_overlap_probe import replay

M, cut = 367264309, 734547102
windows, costs = replay(M, residue_tables(), rebalanced=rebalanced_potential())
requests = [w for w in windows if w.right <= cut]
assert [(w.increment, w.cost) for w in requests] == [(29, 30), (17, 678)]
widths = [(3*w.cost + 1)//2 for w in requests]
U = set().union(*(range(w.right - length, w.right) for w, length in zip(requests, widths)))
assert (len(U), sum(widths) - len(U)) == (1017, 45)
assert sum(max(0, -cost) for C, cost in costs if C - 1 in U) == 0
assert cut + increment_at(367273576, cut) - 1 - (2*M - 2) == 18502
print("Synthetic overlap witness checked")
PY
```

Lean 4.33.1 accepts the new proofs, including the composition with
the verified finite prefix and the unbounded greater-twin-prime
theorem. The audit of 21 public theorems uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Cumulative credit intervals and a signed allowance, 2026-11-12 JST

From `dc75d68338b83ada388d0cd79a6c0691d964ec51`,
`RebalancedCreditIntervals210.lean` uses the coordinate
`B_i = 2*(C_i^+-C_0)+3*sum_{k≤i} max(0,-u_k)` after event `i`.
The interval of length `3*P_i` ending there fits between its anchor
and its own endpoint. Same-key intervals are disjoint, and a request
covered by its own growth is disjoint from all earlier intervals.

Telescoping on the clamped interval between two hits gives
`B_j-B_i = sum_{i<k≤j} (2*(e_k-1)+3*max(0,-u_k))`.
For selected intervening events with `e_k≥339` and
`3*(gap_k+1)≤e_k-1`, this is at least
`11*sum(e_k-1)-3036*count`. In particular, one such event with
`e_k≥595` separates a later request outside long prime phase reuse
from every interval before that event. This uses the existing cost
cap 1166 for those requests.

For `i<j`, the pair intersection has width
`min(3*P_i, max(0,3*P_j-(B_j-B_i)))`. A demand's duplicate width is
the intersection with the union of all earlier intervals. It is
bounded by both the sum of the pair widths and the part reaching
before the latest earlier different key. Let `E` be the sum of
these upper bounds minus all cumulative credit outside the union.
Lean gives `3*W ≤ 3*Phi+3*A+2*G+E`, using the actual startup cost
`A`. An enclosing band can supply a lower bound on unused credit
through its length.

`rebalanced_crossing_signed_of_credit_allowance210` checks that
`10*(3*Phi_upper+E)≤9*M` suffices for the signed crossing bound
at `M≥367232911` under the existing short-prefix and gap hypotheses.
For example, `E≤0` and `10*Phi_upper≤3*M` imply this allowance.
For sufficiently large `M`, the existing sublinear first-phase
result suffices when `80*E≤27*M`. The uniform allowance on actual
crossing candidates remains open.

Independent trial division checked seven synthetic controls and
533 and 684 twin-shaped starts in `[7163911,7263911]` and
`[367232911,367432911]`. At the 69 and 292 demand arrivals, the
union and enclosing-band adjustments were nonpositive. Counting
growth through the requests gives 7 and 30 overlapping pairs.
Including negative costs leaves 6 and 8. All three pairs on the
`M=69921739` control separate after negative costs are included.
On the `M=367264309` control at horizon `734547102`, the pair
cap reduces the duplicate-width upper bound from 1974 to 90.
There are 43,547 unused units at that prefix, giving `E=-43457`.

```sh
lake build A166944.Attempt A166944.RebalancedCreditIntervals210 A166944.ResidualRebalancedPairOffsets210
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=diagnostics python3 - <<'PY'
from itertools import combinations
from rebalanced_potential_probe import rebalanced_potential
from travel_credit_prefix import capped_hits
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at
from travel_reuse_overlap_probe import replay

table, potential = residue_tables(), rebalanced_potential()

def demand_intervals(M, cutoff):
    requests, costs = replay(M, table, rebalanced=potential)
    hits, _ = capped_hits(M)
    growth_ends, credit_ends, negative = {}, {}, 0
    for (C, cost), hit in zip(costs, hits, strict=True):
        growth_ends[C] = 2 * (C + increment_at(hit, C) - 1 - (2*M - 2))
        negative += max(0, -cost)
        credit_ends[C] = growth_ends[C] + 3 * negative
    return [[(ends[w.right] - 3*w.cost, ends[w.right])
             for w in requests if w.right <= cutoff]
            for ends in (growth_ends, credit_ends)]

def overlap_width(a, b):
    return max(0, min(a[1], b[1]) - max(a[0], b[0]))

growth, signed = demand_intervals(69921739, 139856952)
assert len(growth) == 3
assert all(overlap_width(a, b) > 0 for a, b in combinations(growth, 2))
assert all(overlap_width(a, b) == 0 for a, b in combinations(signed, 2))
_, signed = demand_intervals(367264309, 734547102)
assert len(signed) == 2
assert overlap_width(*signed) == 90
assert signed[-1][1] == 45581
assert len(set().union(*(range(a, b) for a, b in signed))) == 2034
print("Cumulative credit witnesses checked")
PY
```

Lean 4.33.1 accepts the new proofs. The audit of 24 public theorems
uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Anchored placement and weighted phase periods, 2026-11-12 JST

From `575f73529f4105d1494b5309b4683b5ce0df8d34`,
`RebalancedAnchorWindows210.lean` lets demand `3*P_i` use any unit
between the cumulative credit just after its anchor and just after
its endpoint. The closed-interval Hall theorem gives the exact
equivalence between the window inequalities and a feasible
allocation. A deficient window can be shrunk to positive request
endpoints while preserving every contained positive request.

Full terminal periods are disjoint within each key. For long reuses,
the full intervals back to their latest long anchors are disjoint
within that key as well. A rate bound compares the sum of the
fractions of the containing window needed by the keys with one.
At most three keys of long prime increments `e≥109` fit for
arbitrarily many requests, since `3*(111*e+3141)≤420*e`.
Four long keys fit when each request has negative cost at least
`8*e+4188` between its own anchor and endpoint. Its full width is
twice the horizon drift plus three times that negative cost.

A deficit with at most four long keys of increments `e≥32` forces
one request with width below `12*P_i`. Its horizon drift is a positive
multiple of `210*e`. Two periods would already pay this width, so
the drift is exactly `210*e` and the negative cost is below
`8*e+4188`. In any deficit with at most two requests the long
increments are at most 31. With at most three requests the long
increments are at most 107, all request increments are at most 159,
and the credit width is at most 45,053. Between actual event
endpoints of such a window, every increment is at most 22,527
and every gap at most 45,054. An increment at least 339 with a small
relative gap is at most 4,371 there.

The exact repeat credit debt is `3*sum P_i - B_total`. It is bounded
above by the previous terminal-interval adjustment, and
`3*W = 3*Phi+3*A+2*G+debt`. The signed allowance accepts this exact
debt. A first crossing with `10*Phi≤3*M` has positive debt, hence a
deficit at positive anchored endpoints containing at least two
keys. The universal bound on actual crossings remains open.

Trial division on 533 and 684 synthetic starts in
`[7163911,7263911]` and `[367232911,367432911]` checks 116 and 723
positive endpoint windows. All pass and an independent placement
of each request in the earliest available units succeeds. The
minimum slack in the two ranges is 3,735 and 1,575 credit units.
On the `M=367264309` control, the terminal intervals overlap by
90 units. The full intervals `[3779,45521)` and `[9881,45581)`
admit the disjoint placements `[3779,3869)` and `[9881,11915)`.

```sh
lake build A166944.Attempt A166944.RebalancedAnchorWindows210 A166944.ResidualRebalancedPairOffsets210
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=diagnostics python3 - <<'PY'
from rebalanced_potential_probe import rebalanced_potential
from travel_credit_prefix import capped_hits
from travel_mod210_probe import residue_tables
from travel_residue_probe import increment_at
from travel_reuse_overlap_probe import replay

M, cut = 367264309, 734547102
requests, costs = replay(M, residue_tables(), rebalanced=rebalanced_potential())
hits, _ = capped_hits(M)
credit, negative = {}, 0
for (C, cost), hit in zip(costs, hits, strict=True):
    negative += max(0, -cost)
    credit[C] = 2 * (C + increment_at(hit, C) - 1 - (2*M - 2)) + 3 * negative
rows = [(credit[w.left], credit[w.right], 3*w.cost)
        for w in requests if w.right <= cut]
assert rows == [(3779, 45521, 90), (9881, 45581, 2034)]
assert min(rows[0][1], rows[1][1]) - max(r-p for _, r, p in rows) == 90
assert all(left + size <= right for left, right, size in rows)
assert rows[0][0] + rows[0][2] <= rows[1][0]
print("Anchored allocation witness checked")
PY
```

Lean 4.33.1 checks the new module and its composition with the
existing first-crossing reduction. The audit of 51 public
theorems in the two credit modules and the reused demand cap
uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Ordered small deficits and disjoint anchor components, 2026-11-12 JST

From `c6c5e648f9221f4936036530e447fc26b7663ec3`, a deficit with up
to three requests has at most 47 eligible increments. The
window contains the full phase period of each request and the
horizon growth from its endpoint through the last request. Between consecutive
requests of increments `e,f`, the growth is at least `f-1`,
and at least `2*f-2` when `e=f` by the factor reuse residues.
The finite checks in `RebalancedSmallAnchorData210.lean` use
the maximum over the ordered requests of twice the period and
the subsequent growth. Independent enumeration leaves 59 pairs
and 4,400 triples whose summed cost caps can exceed that floor.

For actual event endpoints, the credit width also includes three
times the sum `N_w` of negative cost magnitudes between them.
With two requests the width is at most 10,187, `N_w ≤ 1350`,
the deficit plus `3*N_w` is at most 4,052, and all increments are
at most 77. The corresponding bounds with three requests are
43,277, 2,789, 8,368, and 119.

The union of positive anchored intervals is a disjoint union of
windows with original endpoints. Every request belongs to one
window. The exact repeat credit debt is the sum of the signed
window debts minus the unused credit outside the union. The
component allowance uses `4052-3*N_w` or `8368-3*N_w` on positive
two- or three-request debts and the positive part of the actual
debt elsewhere. The signed crossing theorem accepts the sum of
these allowances minus unused credit in place of the exact debt.
The uniform bound with first payments on actual first crossings
remains open.

Trial division at the full capped synthetic prefixes in the two
preceding scan ranges gives 44 and 147 components with no positive
debt, from 69 and 292 requests. On the `M=367264309` control through
horizon `734547102`, the component is `[3779,45581)` and its total
demand is 2,124. Its debt is −39,678 and there are 3,779 unused
units, giving exact repeat credit debt −43,457.

```sh
lake build A166944.Attempt A166944.RebalancedAnchorComponents210 A166944.ResidualRebalancedPairOffsets210
```

Lean 4.33.1 checks the new modules and the composition of their
crossing allowance with `target_of_rebalanced_remaining_crossings210`.
The audit of 12 new public theorems uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Growth rates and a joint first-payment budget, 2026-11-12 JST

From `27acad17132541b1ef8117b90dcbda91992d7b84`, disjoint
anchor components have disjoint event ranges. Their horizon
growths `G_w` sum to at most prefix growth `G`. With scaled
repeat demand `Q_w`, define the growth debt as `Q_w-2*G_w`.
The exact repeat credit debt is the sum of these growth debts
minus twice the unused growth and three times the prefix's total
negative cost. The signed identity counts negative costs once.

The finite pair and triple checks also apply to positive growth
debt before any negative costs are credited. They give the
respective bounds `min(4052, floor(7*G_w/4))` and
`min(8368, floor(18*G_w/5))`. Such windows have growth at most
5,093 and 21,638 respectively. Independent enumeration of the
same ordered tuples gives maximum demand-to-twice-growth ratios
of 2178/1165 and 3267/1175.

The terminal phase periods fit in raw horizon growth on each key.
For at most four long keys, all increments at least 109, the
growth debt is at most `floor(2*G_w/3)`. For at most five long keys,
all increments at least 393, it is at most `floor(5*G_w/6)`. Both
allow arbitrarily many requests. The prefix allowance uses these
rates and the positive part of the actual growth debt for other
windows.

The refined first-payment bound uses the smaller of the cofactor
and linear increment weights above cutoff `L`. The tail counts
only positive first-payment events with increment greater than
`L`. Such events cannot lie inside windows with growth below
`L`, so the growth in those deficient windows can be subtracted
before evaluating the tail. At `L=338`, the finite low-prime sum
is 13,887,360 and `Phi ≤ 13887360 + 41*H_first`. Hence
`10*debt + 1230*H_first + 416620800 ≤ 9*M` suffices to rule out
the first crossing. At threshold 367,232,911,
nonpositive debt and `H_first ≤ 2348353` suffice. The joint bound
on all actual crossing candidates remains open.

Trial division with the existing capped replay and rebalanced
potential gives one positive growth debt among 44 components at
the 533 synthetic starts in `[7163911,7263911]`. At `M=7166563`,
the post-horizon interval `[14342418,14343066)` has two requests
with scaled total 1,395 and growth debt 99. For the 684 synthetic
starts in `[367232911,367432911]`, all 147 components have
nonpositive growth debt, and the maximum `H_first` at cutoff
338 is 77,474. The minimum slack in the displayed numeric
budget is 2,797,229,001 at `M=367418929`. The control
`M=367264309` through horizon 734,547,102 has growth 18,502,
unused growth 202, negative cost 2,859, repeat debt −43,457,
and first payment 20,394. These are synthetic prefix checks.

```sh
lake build A166944.Attempt A166944.RebalancedComponentGrowth210 A166944.ResidualRebalancedPairOffsets210
```

Lean 4.33.1 checks the new modules and the composition of
`rebalanced_crossing_signed_of_joint_growth_budget210` with
`target_of_rebalanced_remaining_crossings_from_1468965061`.
The audit of 42 new or revised public theorems uses only `propext`,
`Classical.choice`, and `Quot.sound`.

### Two further actual record transitions

`VerifiedLaterRecordExtension.lean` checks 109 nonunit events
from record 367,232,911 with total travel 14,181, and a quiet
return to record 734,482,123 at index 734,482,125. The next replay
has six events with travel 1,209 and returns to record
1,468,965,061 at index 1,468,965,063. The prefix certificates
give the index and twin-primality statements for every strict
record `5 < R ≤ 1468965061`. They also bound travel on every
capped prefix in each of these two segments. The remaining
signed crossing condition now starts at `M ≥ 1468965061`,
where nonpositive debt and `H_first ≤ 10409808` suffice for
the numeric cutoff-338 bound.

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=diagnostics python3 - <<'PY'
from travel_credit_prefix import capped_hits, is_prime
from travel_residue_probe import increment_at

for M, next_M, count, travel in (
    (367232911, 734482123, 109, 14181),
    (734482123, 1468965061, 6, 1209),
):
    hits, stop = capped_hits(M)
    assert (stop, len(hits), hits[-1] - (M + 2)) == ("quiet", count, travel)
    C = 2*M - 2
    for hit in hits:
        C += increment_at(hit, C) - 1
    assert C + 1 == next_M and is_prime(C - 1) and is_prime(C + 1)
print("Both later record segments checked")
PY
```

## Weighted period overlaps and first-payment runs, 2026-11-12 JST

From `a66ec90cf5450c3e072e3ae1bfbae3751d1e817d`, put each scaled
request `3*P_i` on its terminal phase period of width `L_i` at
integer weight `ceil(60*3*P_i/L_i)` per unit. Periods of one key
are disjoint. Summing the point loads counts each weight times
its period width. The load at any occupied point is at most the
load at the latest start of its covering periods.

The weights for long requests of increment at least 109, 143,
or 393 are at most 20, 19, or 17 respectively. The nonlong
weight is at most 46 by the checked cost caps for odd increments
below 160. A window can use any number of keys with no load
above 85 if at most five large long periods cover each point.
The mixed criterion permits two long periods of increments at
least 143 and one nonlong period at each point.

Let `E_w` be the sum of `max(0,load-85)` over the doubled
horizon range of a window. For the disjoint cover, Lean checks
`60*debt ≤ 50*G + sum(E_w) - 170*G_unused - 180*N`, where
`N` is the total negative cost magnitude. The joint allowance
uses the smaller of the prior growth allowance and the signed
period load minus capacity in each window. This retains surplus
in paid windows. For sufficiently large records, the sublinear
first-payment estimate and `sum(E_w)+300 ≤ 2*M` suffice for the
signed crossing bound.

Above cutoff 338, let `H` be the growth at positive first
payments, `k` their count, `b` their number of consecutive runs,
and `F=sum(2*e-gap)` their gap shortfall. The potential differences
cancel between consecutive selected events, giving
`Phi + 24*F ≤ 13887360 + 37*H + 48*k + 1036*b`.
This estimate and the signed period allowance compose with the
reduction to `Target` above record 1,468,965,061. The combined
uniform estimate on actual crossing candidates remains open.

The endpoint sweep in the diagnostic treats adjacent half-open
windows as separate when they only share a boundary. Trial
division on 684 twin-shaped synthetic starts in
`[367232911,367432911]` gives 160 components with maximum
point load 76. At 579 synthetic starts in
`[1468965061,1469165061]`, there are 119 components.
The `M=1468999771` window has 20 requests on 16 keys, maximum
depth four, and peak load 77. The `M=1469100181` window has
seven requests on six keys, peak load 100, and excess 13,920.
The maximum saving in the first-payment upper bound is 5,745,336
at `M=1469113729`. All new joint-budget comparisons pass in
both bounded synthetic ranges.

```sh
lake build A166944.Attempt A166944.RebalancedPeriodLoad210 A166944.ResidualRebalancedPairOffsets210
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/rebalanced_period_load_probe.py 367232911 367432911
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/rebalanced_period_load_probe.py 1468965061 1469165061
```

Lean 4.33.1 checks the new modules and the composition with
`target_of_rebalanced_remaining_crossings_from_1468965061`.
The audit of 27 new or revised public theorems uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## Cofactor bound for the index and horizon, 2026-11-12 JST

From `b7fd35a1af1b4b1832ea0815a6f68ad1271bb6de`, let
`Y(s,C) = 432*s - 215*C + 18*V(s,C)`, where `V` is the rebalanced
potential. For a nonunit hit of increment `e`, its cofactor `v` satisfies
`3 ≤ v`, `|C-e*v| = 1` in the corresponding parity branch, and
`gap ≤ 2*v`. For `e > 5` the gcd divisibilities also give
`C+e ≤ 2*r+1` at the hit `r`. Combining these estimates yields
`219*e - 2809 ≤ Y(s,C)` for `e ≥ 864`. Thus below `219*M - 2400`
an inside hit cannot exceed an odd record `M ≥ 863`.

The increment of `Y` is bounded by `18*w-17*(e-1)`, where `w` is the
signed rebalanced event cost. An increasing step has `e ∤ 210`.
For gaps at most ten it has `e ≤ 107`. For larger gaps the composite
possibilities are `49, 77, 121`. The finite factor check uses
`f² ≤ e`, `gap ≤ 2*f`, and excludes factors three and five. The clipped
cost cap at increment 91 rules out the fourth numerical candidate.

For a prefix let `G` be its horizon growth, `Phi` its capped first
payments, and `D_credit` its signed rebalanced credit debt. Put
`B = 180*Phi + 60*D_credit - 50*G`. The change of `10*Y` is at
most `B + 729812160`, using the existing startup cap. The period
bound gives `B ≤ 180*Phi + E - 170*U - 180*N`, with period excess
`E`, unused growth `U`, and negative cost magnitude `N`.
At the new finite threshold, every boundary crossing needs `M < 4*H`
in the prefix, where `H` counts growth at large relative gaps. The
crossing's own increase is at most `325*gap+18863` and its gap obeys
`3600*gap ≤ M`. The sufficient budget `B ≤ 2169*M` on these actual
prefixes excludes the crossing. This implies a long quiet interval at
the capped exit, so the existing factor and return theorems give the
record index and twin primality. The uniform budget remains open.

The finite certificate extends from 1,468,965,061 through the next
three actual records, with 4, 52 and 26 nonunit events respectively.

| Previous record | Next record | Horizon growth | Growth at large relative gaps |
| ---: | ---: | ---: | ---: |
| 1,468,965,061 | 2,937,930,211 | 90 | 90 |
| 2,937,930,211 | 5,875,882,249 | 21,828 | 13,298 |
| 5,875,882,249 | 11,751,795,061 | 30,564 | 30,370 |

The replay diagnostic uses trial factorization to propose first hits
and checks each proposed gap against the original gcd recurrence.
In the bounded range `[11751795061,11751995061]` plus four controls,
483 twin-shaped starts produce 43,908 transitions and all reach
quiet exits. The maximum observed prefix budget is 954,242,160 at
`M=11751931201`. Each replay runs to a quiet exit, a new record inside
the horizon, a boundary crossing, or 3,000 nonunit events.

```sh
lake build A166944.TravelRebalanced210
lake build A166944.VerifiedBoundaryRecordExtension
lake build A166944.RebalancedBoundary210 A166944.Attempt
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/rebalanced_boundary_probe.py --synthetic 11751795061 11751995061
```

The mod-210 check uses the same seven 15-row kernel certificates in
separate declarations to reduce the peak memory of its build.
Lean 4.33.1 builds both new modules and `A166944.Attempt`. The
`#print axioms` audit of 21 declarations, including the finite result,
the boundary reduction to `Target`, and the inherited twin-prime
implication, reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Index offset returns and continuations, 2026-11-12 JST

Rowland's recurrence returns to `a(n)=3*n` at its nonunit hits. This
comes from the recurring-structure lemma, whose first-hit distance
uses the smallest prime factor of a single fixed term.
[Rowland, arXiv:0710.3217v3, Section 3](https://arxiv.org/pdf/0710.3217v3)

For the A166944 recurrence, Shevelev's observation 6 and Theorem 1
use a quiet interval of square-root length near a fundamental point
as a sufficient condition. Proposition 1 records the parity-dependent
upper bounds on `a(n)/n`. These suggest tracking the offset from
`3*n` at intermediate events.
[Shevelev, arXiv:0911.5478v11, Sections 1 and 4](https://arxiv.org/pdf/0911.5478v11)

Write `X=2*s-C`, `g=r-s`, and `e=d(r)`. At any genuine event with
`e≥5`, the offset after the hit is `2*e*k` at an even hit or
`2*e*k+6` at an odd hit, with `k≥0`. Using
`X'+(e-1)=X+2*g` and `g*e≤2*(C+1)` shows that
`3*e²>e*(X+1)+4*(C+1)` forces `k=0`.

For a suffix starting at `X≤6`, its large-gap growth `H` alone
bounds the terminal offset by `X≤4*H+8`. The stronger estimate
retains all the growth `G` as `3*X_end+G≤3*X_start+13*H+6`.
Just before a crossing of the cofactor boundary, the current
horizon `C` and final gap `g` therefore satisfy
`219*M < C+864*H+325*g+41639` with `H` taken on that suffix.
For `M≥11751795061` and `C≤8*M` this gives `6*M<25*H`.
The horizon itself still increases across a return.

The exact supported-hit map modulo 210 gives a finite certificate
from offset at most six. Start at each of the 210 index residues
and four even offsets. The initial horizon residue follows from
`C=2*s-X`. A supported path from any such state has at most nine
events, offset at most 76, and horizon growth at most 32. Lean
checks the four sets of starting residues and transfers the result
to genuine recurrence paths via `first_clipped_hit210_of_supported`.

The separate C++ clipped enumeration at modulus 90090 considers
all 360,360 initial residue/offset pairs for increments at most 15.
It finds 1,426,261 transitions, at most 30 events per path, offset
at most 220, and horizon growth at most 170. These larger-table
values are computational checks. The same enumeration independently
matches the three mod-210 bounds.

In 14,869 twin-shaped synthetic starts through 2M, the 491,514
transitions include a run of six successive gaps above ten each
increasing `X` at `M=733333`. At `M=1461853`, increment 8297
with gap 179 forces `X` from 7944 to 6. The near-threshold scan
of 478 starts in `[11751795067,11751995061]` gives 42,708 events.
Of 27,087,276 total units of large-gap growth, 14,797,746 occur
on steps ending at `X≤6`. At `M=11751887509`, one stretch has
473 successive post-event offsets above six. Fourteen consecutive
events in that replay increase both `s` and `C` by 420, increasing
`X` by 420 and the boundary value by 91,140 while restoring both
residues modulo 210. An arbitrary local first-hit state gives a
single positive step returning to the same residues modulo 30030.
Both witnesses are checked with the original gcd recurrence.

A second sufficient condition uses `2*X≤M` and `8*(C+1)≤M²`
at every capped endpoint. An inside increment above `M` would need
`M≤4*g` and therefore `M²<8*(C+1)`. At a quiet exit, the small
offset gives enough distance for both horizon terms to be prime.
`canonical_next_record_factors_of_index_offset_bounds` proves the
resulting conditional next-record theorem for `M≥33`. The uniform
endpoint estimates remain open.

```sh
lake build A166944.ReplayOffset210 A166944.Attempt
g++ -O3 -std=c++17 -Wall -Wextra -o /tmp/replay_offset_clipped diagnostics/replay_offset_clipped.cpp
/tmp/replay_offset_clipped
PYTHONDONTWRITEBYTECODE=1 python3 diagnostics/replay_offset_probe.py --scan
```

The replay scan uses SymPy 1.14.0 for factorization and cross-checks
the selected witnesses and six actual segments by direct gcd iteration.
Lean 4.33.1 builds both targets. The axiom audit of 13 declarations
reports only `propext`, `Classical.choice`, and `Quot.sound`.
