# Paired RESET support, long canonical-age deletion, and inherited heavy ancestry

2026-11-26 JST. Continues [e25fb0b8f7a3](https://github.com/tara-sooo/A166944-Lean/blob/e25fb0b8f7a37771d04ef5593eae0ffd08478153/research/2026-11-26-min-unified-low-phase-slot-halos.md). Integrates the exact canonical bridge from the [stable-heavy canonical renewal map](https://github.com/tara-sooo/A166944-Lean/blob/e1ad9e2b434c652699e1bc9a0797887631e0ea6d/research/2026-11-25-min-clock-canonical-renewal.md), the [four-form rough landing sieve](https://github.com/tara-sooo/A166944-Lean/blob/0fda077cd533a8f0cfddb8104e683e1c1ef549e2/research/2026-11-25-min-unified-rough-pair-isolation.md), and the [true-tick entropy window](https://github.com/tara-sooo/A166944-Lean/blob/3fe50cf6378294cdaa25cacc0e9f9cda16a2174c/research/2026-11-25-min-unified-stable-strand-clock.md). Independent branch heads verified unchanged: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New all-mass deletion of high RESET waits ending long canonical-age intervals, stronger paired-RESET actual cohort and all-event halo threshold using simultaneous roughness, and a quantitative origin-age/inherited-cohort consequence. Not a bound on all high RESET clock or all renewal arcs; twin-prime infinitude remains open. No Lean compilation.

## 1. Original ensemble and exact canonical ages

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Keep every original prime-root gain-stopped MIN prefix, including terminal snapshots. Natural HIGH means selected p>=Q, r(C)>p/sqrt(log p). Actual event gain p-1 and wait w<=2r<=3(p-1), total gain <H, total elapsed <=3H, nonnegative deficit d=2t-C. The initial state for every root M is canonical (C,t)=(2M-2,M+2). A canonical point is any actual physical state with C=0 mod4 and t=C/2+3, including virtual points within completed waits and actual terminal snapshots if canonical. No point after the original stop is introduced.

A high RESET-ending event at prehorizon C, departure v, posthorizon D=C+p-1 has adjusted phase phi=2v-D-6s=0, where s=v mod2. By the exact bridge lemma, odd RESET is immediately canonical; even RESET reaches a canonical point within seven clock units and eight gain unless the actual path stops first. The only completed jumps before that canonical point are selected 3 or 5. Thus if a later HIGH RESET-ending event exists on this original path, the requisite bridge is contained in the actual prefix and occurs before that later high departure (Q>5 eventually).

For each high RESET-ending event define its age a=v-t_c, with t_c the time of the last actual canonical point STRICTLY before v. It always exists from the root, and can lie inside the high event's own wait. The half-open time intervals [t_c,v) for successive high RESET events on one original tag are disjoint: the previous departure is no later than the current t_c by the bridge. Hence the sum of ages on a tag is <=3H. This is not a partition into all renewal arcs and does not count a canonical point at the current v as its own predecessor.

Put Z=B sqrt(u). Pay the WHOLE original high RESET wait if a>Z. There are <=3H/Z such events per tag; each costs <=2B. Therefore
    W_long <= 6 NH B/Z=O(NT/sqrt(u))=o(NT).                 (1)
No cohort-size restriction, no number-of-ancestors assumption and no new cutoff. This applies to the endpoint high RESET wait, NOT to the whole long canonical arc. Any surviving high RESET event has an actual preceding canonical point at age <=Z. If its horizon is C_c, then D-C_c=2a+6-6s<=2Z+6 by the two deficits. Its actual most recent canonical predecessor is therefore within O(Z) gain of its posthorizon.

## 2. Paired RESET keys and uniform four-form support

Consider two CONSECUTIVE original natural HIGH events on a tag, both RESET-ending, at C and A=C+p-1+e with selected labels p,q respectively and intervening total gain e even, 0<=e<=L=floor(u^.75). The intermediate events may have arbitrary labels, but none is natural HIGH by consecutiveness. For each original tag there is a unique next high event if it exists. At this small offset q!=p: if equal, the two divisibilities imply p divides p-1+e+tau-sigma, which is p plus a nonzero odd integer of magnitude <p for large X. The argument applies to all signs sigma,tau of the eligibility of p,q.

For fixed p>=Q and sigma with p|(C+sigma), write C=p a-sigma, a odd. Both horizons being natural HIGH force all four forms
    a, p a-2 sigma, p a+p+e-sigma-2, p a+p+e-sigma
to avoid every odd prime below R=B^(1/8), for sufficiently large X. The fourth and third are A+1 and A-1. The four-form Selberg upper bound of 0fda077 is uniform in p,sigma,e and applies to the present L (indeed smaller than its original exploration width): the exceptional product of pairwise offset differences and p is nonzero and has log O(u). It gives O(X ell^4/(p u^4)) possible C for each fixed p,sigma,e. At a high horizon A, at most four distinct primes q>=Q divide A-1 or A+1, since Q³>7X+O(B). Thus summing over e, the two signs and the reciprocal prime bound sum_(p>=Q)1/p=O(ell/u), the number of relaxed keys (C,p,e,q) is
    S_pair << X (L+1) ell^5/u^5.                          (2)
No dependence on ancestor multiplicities, arrival times or number of intermediate events. The exact high RESET departure formula v=(C+p-1+6s)/2 makes each endpoint time unique once the key is fixed. In particular no additional multiplicity for possible original pairs of exit times, unlike an unrestricted physical pair census.

For each key define the ACTUAL paired cohort P(C,p,e,q) to be all original tags that complete the indicated two consecutive natural HIGH RESET events on their original paths. Freeze its mass n_pair and membership before any accounting deletion. It is a subset of each endpoint's full original exit-slot tag set (last occupied tick mass). This is an actual one-path sequence cohort, NOT the Cartesian product of two tag sets or a count of root pairs. Determinism of the future from the first exit fixes the intermediate path; source-specific stops only remove tags from this cohort. Count every key even if its cohort is empty.

## 3. Stronger mass cap and all-event halos

Put kappa=max(2,floor(u^.25)), and
    m_pair(p,q)=H u^4/[kappa (p+q)(L+1) ell^6].            (3)
For every key with 0<n_pair<=m_pair, mark on every tag of its actual paired cohort all completed events whose ENTIRE gain intervals are contained in
    [C-kappa p, A+q-1+kappa q].
This includes both endpoint high waits, every intervening nonhigh wait, and additional nearby events on the same original tag. Do not mark an uncompleted event or extend a terminal. The interval length is <=(kappa+1)(p+q)+e=O(kappa(p+q)), using e<=L=o(Q). Per-tag total marked gain is at most the union of these lengths, and actual waits <=3 times gain. Consequently by (2)-(3),
    W_pair << sum_(eligible keys) kappa(p+q)n_pair
            <= O(S_pair * H u^4/[(L+1)ell^6])
            = O(NT/ell)=o(NT).                            (4)
All overlaps are paid by priority only once, also with the previous low-phase and other masks. There is no factor for the number of ancestor pairs or actual merge nodes. This sharper cap uses two simultaneous rough horizons, rather than the earlier single RESET support. It can pay the entire sequence even if one endpoint has a much larger total slot mass than the cohort, because it only marks tags that actually complete both endpoints. The comparison is between different accounting sets; do not equate pair mass with the full slot mass.

If EITHER actual endpoint incidence of such a short pair survives the new halo deletion, its paired cohort satisfies n_pair>m_pair. In particular for p,q in [Q,B], uniformly
    n_pair > m_min := H u^4/[2 kappa B (L+1)ell^6]
                   = Theta(B u^(11/4)/ell^6).             (5)
Both endpoint full slot masses are at least n_pair. At p,q~B this new paired-cohort threshold is larger than the previous single-RESET halo threshold of order B u^(3/2)/ell² by order u^(5/4)/ell^4, tending to infinity. The stronger result only covers short paired RESETs, not isolated RESETs. The same argument permits kappa=1 for a larger mass threshold and smaller neighborhood, or smaller L for a larger cap on the narrower class.

## 4. Quantitative root-age restriction

At any actual paired cohort's initial prehorizon C, each tag has a prime root M in [X,2X) with origin horizon C_M=2M-2<=C and C-C_M<T. For a window of gain length z, the uniform prime interval upper bound gives at most O(z/log z) such roots in C-z<C_M<=C, uniformly as z tends to infinity. Let
    z=c u m_min = Theta(B u^(15/4)/ell^6),
where c>0 is an absolute sufficiently small constant from this prime upper bound. Since log z=Theta(u), at most m_min/2 distinct roots in this recent window are possible, for all sufficiently large X. By (5), at least half the actual paired-cohort tags have original start horizons <=C-z, and all lie in C-T<C_M<=C. In particular its original root span is at least z in horizon units up to the recent-window formulation; a safer direct span statement follows separately from the same uniform prime interval bound on ANY interval of length z: such an interval cannot contain the full cohort. These statements use root primes, not the distribution of arbitrary canonical indices. They do not assert that the older tags had already physically coalesced just because their origins are old.

## 5. Actual inherited common state using the existing entropy trim

Now take an original surviving focal tag at either endpoint of a short paired RESET. Require that this focal event also survives the earlier true-tick entropy-window deletion and endpoint trims of 3fe50cf. Recall D_window=floor(T/(u ell²)), eps=1/ell. Its original path begins at least D_window gain before its focal prehorizon, continues at least D_window beyond it, and the sum of original true-tick variation tokens within this window is <=eps. The parent lemma says that for any segment of that path contained in the window, and any full group of size n at a state of that segment, at least (1-exp(eps)eps)n of its members are present at every state of the segment. This lemma includes root injections and terminal expiry; no monotonic full mass assumption.

Here z+B+p+q+L=o(D_window), while z/Z -> infinity. On the focal original path choose the last recorded vertex whose horizon is <=C-z before the first paired event; its horizon is in [C-z-B,C-z], since gains <=B and the original endpoint trim guarantees it exists. Include the full actual tick segment from that earlier vertex through the second RESET poststate. Every transition's prehorizon is within the focal window, whether the retained focal event is first or second. At the first endpoint's last occupied tick the full visiting group has size >=n_pair. Use that group as the reference in the entropy intersection lemma on the chosen entire segment. At least
    (1-exp(eps)eps)n_pair = (1-o(1)) n_pair                 (6)
tags are present at EVERY state of the segment, in particular at the earlier vertex and both high jump transitions (both poststates included, so a tag expiring at a last occupied tick cannot be counted as executing the jump). These tags themselves belong to the actual paired cohort, by determinism and the absence of intervening HIGH on the focal path. Thus almost all of the huge paired cohort already shares the same actual physical state at least z gain before the first high prehorizon. This is stronger than a root-age statement; it uses the actual entropy deletion, not an assumption of independent root positions.

If the first high RESET incidence of that focal tag also survives (1), its last preceding canonical point is within 2Z+6 gain of its posthorizon. Since z>>Z+B, the earlier common state established in (6) lies strictly BEFORE that preceding canonical point. The entire large cohort is therefore inherited from well before the current short canonical return, rather than having formed during that return, up to the explicit o(1) fraction in (6). If only the second endpoint survives the long-age mask, its own prior canonical point obeys the analogous proximity bound and the earlier common state precedes it as well. No claim is made that every paired tag survives every prior mask or that the earlier common state is itself canonical.

This does not bound the number or total clock of such old inherited cohorts. In particular the entropy budget permits a huge already-formed cohort to persist for a long time. It does establish a new lower bound on both paired mass and actual common ancestral span for short RESETs in the residual, together with an independent all-mass deletion of high RESET waits with long canonical ages. A route to further reduction is to estimate the occupation of these old inherited cohorts rather than repeatedly accounting for their recent local formation.

## 6. Residual ledger

Apply the two fixed new linear masks (1),(4) by priority to the original ledger. The original no-twin lower bound W_all>=N(T-6)/2 and the earlier sufficient condition liminf (A_rem+L_rem)/(NT)<1/2 hold on the smaller residual; A_rem and L_rem are exact remaining non-HIGH and HIGH actual clocks. No added quadratic pair-energy condition. The new restrictions do not cover all RESETs: pairs with larger intervening gain, RESET followed by nonRESET or no later high, very heavy inherited paired cohorts, and the remaining nonHIGH and nonRESET clock are not evaluated fully. No external novelty claim or Lean verification. Main and independent branches unchanged.

## 7. Finite diagnostic audit

Source [min_unified_paired_reset_ancestry_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/c005f4ad74f22ddf962569577d0475f2278988c5/research/min_unified_paired_reset_ancestry_audit.mjs), commit c005f4ad74f22ddf962569577d0475f2278988c5, exact remote readback. Executed the audit function in available ECMAScript tool runtime (not a separate Node process). Reproduce:
    node research/min_unified_paired_reset_ancestry_audit.mjs 256 1024 4096 16384 65536

Five normal diagnostics and one stress, all passed. Finite T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), high r>3 and 2r>p; normal L16,kappa2, cap8B/(p+q), Z=ceil(B/2); stress at X65536 L32,kappa3, cap24B/(p+q), Z=B. Restrict initial p>L+3 in pair test for finite geometry. These are substitutes for analytic thresholds. Literal per-tick gcd comparisons on X256 and X1024 (431 and1239); exact virtual canonical points in completed waits, actual RESET predecessor age, bridge between consecutive high RESETs, disjoint age intervals and elapsed-time budget; exact actual paired cohorts, both endpoint masses, unique endpoint times, relaxed four-form rough support on observed paired centres, exact CRT residues, complete interval coverage, halo union budget and disjoint addition of long age mask. The support enumeration is restricted to actual paired initial centres, not an exhaustive arithmetic support census. Heavy root span checks use the elementary odd-root separation only, not the analytic prime-interval constant. The older ancestry/entropy intersection implication (6) is a paper deduction using the inherited proven entropy lemma, NOT implemented in the new audit. No cumulative earlier masks.

| X/mode | paired groups | eligible | heavy | pair halo all clock | pair halo HIGH | long-age additional HIGH | remaining HIGH |
|---:|---:|---:|---:|---:|---:|---:|---:|
|256|1|1|0|44|29|6|1718|
|1024|8|8|0|1084|621|16|3271|
|4096|26|26|0|5769|3323|442|33693|
|16384|42|42|0|24222|13455|1156|180863|
|65536|79|71|8|92874|62416|8501|1309632|
|65536 stress|115|115|0|211606|140247|0|1240302|

Largest normal: 5709 roots,140255 completed events,2395330 full actual clock, raw high1380549, raw high RESET257778. 3046 exact canonical age checks,6544 virtual canonical points,1045 between-high-RESET bridge checks. 92 long-age high RESET incidences cost8706, of which8501 disjoint after pair halos. 322 actual paired-cohort incidences,79 groups,126 relaxed keys,2587 individual small-prime rough checks,126 spatial CRT checks, maximum group mass29. Eligible71 groups with209 tag incidences and full sublist coverage,8 heavy groups with113 tag incidences. Pair halo union4775 events,92874 clock including62416 HIGH and30458 nonHIGH, of which45725 high RESET. Stress 454 incidences/115 eligible groups and all-event halo211606 (140247 HIGH,71359 nonHIGH), zero long-age incidences at larger Z. These finite counts are diagnostic, not asymptotic estimates.
