# Local crossing support: research plan

2026-11-26 JST. User-directed sixth exploratory branch, cut from
`5aef6a4ed635b40666a045663f4fa439ce74243d` of `research/min-simple-crossing-2026-11-26`.
This commit records a research direction only. It introduces no
implementation, executed audit, Lean theorem, novelty claim, or proof of
twin infinitude. Preserve the parent branch's results and formal targets.

## 1. Goal and inherited facts

Replace the full-history stable-carrier / merger-mass problem by a local,
single-origin crossing problem. Seek a sufficiently good unbounded
subsequence of integer resets, not a uniform upper bound for every
trajectory. A density or average result may be useful but is optional.

Use the ordinary uncut offset MIN, without changing the earliest-clock
and least-label tie rules. Start at a positive multiple of 6, X>=6,
with (u,v)=(X,X/2+3). An event (w,p) sends (u,v) to
(u+p-1,v+w), with u/2<=v<=u+1. A twin center is an even u for
which u-1 and u+1 are prime. The crossing is stopped at the first
post-offset reaching the chosen boundary. Include the final crossing
event in the wait and support counts.

Inherited references at the pinned base:

- [Record-free crossing](2026-11-26-min-simple-crossing.md):
  arbitrary integer resets, envelope, finite exit, and crossing
  potential.
- [Local label diversity](2026-11-26-min-simple-crossing-local-label-diversity.md),
  sections 1--2: uniform per-label capacity, primorial wall,
  support-gap lemma and robust small/high-label decomposition.
- [Three-point roughness and clock CRT](2026-11-26-min-simple-crossing-triple-clock-sieve.md):
  optional short-return and triple bounds. They are not required
  for the initial reduction.

These are inherited paper results; no independent full proof audit or
Lean verification is performed by this planning commit.

## 2. Primary local reduction (derived from inherited results)

Fix 0<delta<1 and D=ceil(X^(3/4)). Stop at the first U>=X+D.
Let P(X) be the set of DISTINCT selected odd prime labels of all
events through that exit, and K(X)=|P(X)|. If any pre-offset of this
crossing is a twin center, the desired local conclusion already holds.

Otherwise all source offsets lie in [X,X+D), and the total wait W
satisfies, by the envelope at exit,

    W = v_exit - (X/2+3) >= D/2-3.

The inherited uniform local support lemma, with R=X, gives

    K(X) <= floor((1-delta) log_2 log X)
       ==> W <<_delta D/log log X = o(D)

for a non-twin crossing. These bounds contradict each other for all
sufficiently large X. Consequently the following is a sufficient
condition for twin infinitude:

    There exist a FIXED delta in (0,1) and unbounded X with 6|X
    whose actual local crossing has
    K(X) <= floor((1-delta) log_2 log X).

The reduction is not a proof that such a sequence exists. In
particular, selecting X to be a twin center would be circular as
a construction of an unbounded good subsequence. Use the inherited
uniformity of constants, including the final crossing event. A
shorter D=X^(1/2+epsilon) for fixed epsilon>0 is a secondary
direction requiring the corresponding local estimates to be checked.

### Weaker weighted-support targets

Do not insist on the raw cardinality condition. For the labels
actually used, split P into a small-label initial segment A and its
complement. Set Q=2 product_(p in A) p, with empty product 1, and
let p_* be the least remaining label, when one exists. The inherited
support-gap estimate on a non-twin crossing is

    W <= 3Q(D/(p_*-1)+2) + C D sum_(p in P minus A) 1/log^2 p.

If A=P, the bound is W<=3Q. It is enough to find an unbounded sequence
and cuts with Q/D -> 0, Q/(p_*-1) -> 0 and the displayed reciprocal
log-square sum -> 0 (or an explicit upper bound strictly below the
required wait after normalization). The all-small case needs only
Q/D -> 0. The cutoff may depend on the actual trajectory. The
robust small/high-label version of the inherited lemma is another
option. Keep quantified constants and endpoint costs explicit.

## 3. Alternative: few difficult blocks, not zero difficult blocks

Use the common-boundary setup: R large, reset X in [R,3R/2],
6|X, and stop at first U>=2R. Partition [R,2R) into half-open blocks
of width D=ceil(R^(3/4)), truncating the last block. A block is bad
for one chosen trajectory if its visited pre-event states have more
than floor((1-delta) log_2 log R) distinct labels. Empty blocks are
not bad. Under the twin-free premise every block's visited states
form a consecutive path segment, with the exit event included.

The inherited local bound makes the total wait in good blocks
O_delta(R/log log R)=o(R). In a bad block, all gains except the
last telescope to at most D; using w<=3(p-1) and the non-twin bound
w<=2 sqrt(2R+1) on the last wait yields

    W_block <= 3D+2 sqrt(2R+1).

The envelope requires W>=R/4-3 on a twin-free full crossing.
Therefore it suffices to show, for unbounded R, the existence of
one reset in the slab with

    J_bad <= R/(16D).

Indeed its bad-block wait is <=3R/16+o(R), and its good-block
wait is o(R), giving a contradiction for sufficiently large R.
More generally any fixed coefficient strictly below 1/12 works
in place of 1/16 with these bounds. A weighted or average bad-block
count could give the required existence by averaging over resets.
This is a separate sufficient condition, not an established bound
on J_bad.

## 4. Research priorities

1. Seek a deterministic arithmetic construction of good resets.
   Explore residue classes and small-alphabet terminal maps, including
   the first departure from a restricted alphabet. A fixed finite
   CRT prefix is not an unbounded crossing of length D; account for
   modulus growth versus the resulting X, and all possible competing
   clocks.
2. Test the weakest useful weighted-support criterion, rather than
   optimizing the cardinality bound alone. Look for an adaptive
   cut Q/p_* or mixed-scale estimate that allows many labels with
   small total capacity.
3. Explore the few-bad-block alternative, aiming for a bound on
   frequency or total wait of difficult blocks along at least one
   reset, without controlling global coalescence or exact-state mass.
4. If the local cardinality criterion is too restrictive, seek a
   more permissive local obstruction (actual significant waits,
   short return words, exact clock congruences, weighted label
   capacity). Use the triple sieve only when its stated hypotheses
   hold; no independent multiplication of arithmetic and clock
   probabilities.
5. Compare against the fifth branch's event-count and full-history
   targets. Prefer a direct existence proof for a short crossing
   or a density bound that implies existence, and avoid recreating
   the entire merger-energy problem in different notation.

## 5. Proposed first diagnostic (not executed)

Use exact modular first-clock MIN, cross-checked by literal GCD
ticks on small controls. Enumerate all multiples of 6 in moderate
slabs, record local exit, total actual wait, first twin index,
distinct label support, low/high support, adaptive-cut score,
and bad-block frequency. Separate twin-at-start, twin reached
later, and twin-free exits. Record the final event and the
seed-to-scale relation explicitly. Search for candidate residue
patterns among non-twin starting seeds. Report finite observations,
counterexamples, and the exact domain, not inferred asymptotic
bounds. Do not treat correlated or coalescing paths as independent
samples.

## 6. Completion criteria and limitations

A substantive breakthrough on this branch is an unconditional
proof of the existence of an unbounded sequence satisfying one
of the sufficient conditions above, or another rigorously
equivalent local contradiction. The current work has not proved
that existence. A simple reduction is not by itself progress
toward an upper bound unless the residual existence problem
becomes tractable. Keep all proof dependencies, exact quantifiers,
and any unresolved hypotheses visible. No Lean target, other
branch, or canonical proof status is changed by this plan.
