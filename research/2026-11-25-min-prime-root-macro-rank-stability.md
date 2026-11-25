# Descending-rank stable macroblocks: linear synchronization deletion and full-log high-label diversity

2026-11-25 JST. Continuation of 9db807e00aba8bfc0f59aa818d5698e871024f09 on the selected prime-root branch. A new absolute LINEAR clock mask replaces the preceding short-shared-age and terminal-pair exclusions: every remaining synchronous pair at every recorded high hit actually shares the same much earlier macrogrid crossing, and both endpoints really complete a much later one. The macrogrid is on scale T/u^1.5 instead of B u^2.5. This also improves the local distinct-high-label lower bound from powers of log u to powers of u, using the inherited uniform two-form quotient sieve. No assumptions about independent clock phases or source density of individual merger fibres. Paper deductions plus reproducible finite audit; no Lean compilation or twin-prime proof.

## 1. Setup and original descending rank

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, T=floor(X/u^.25), H=T+B, N=Theta(X/u), F=T² B u, Q=ceil(B/u). Original MIN prime roots M in [X,2X), original gain-stopped prefixes include terminal snapshot. Every selected p<=B gives gain g=p-1, wait w<=2r(C)<=3g, so original proxy R_all<=1.5 NH. Natural high p>=Q, r>p/sqrt(log p). The actual-clock criterion and high Cauchy support sum_C r(C)=O(XB/u³) are unchanged.

At any actual recorded vertex v=(C,t) of source M let
    d_M(v)=#{original tags M' >= M visiting exactly v}.
Count M itself; count actual terminal snapshots too, no extension after them. This is the descending larger-source rank already present in physical-cover and birth-entropy, now used as a source-wise stability mask. The original stop order implies d_M is nondecreasing along M's full original recorded list, including terminal. Indeed every larger tag that has met M continues through all actual recorded vertices up to M's stop. If M completes an outgoing edge at v, all the d_M(v) counted tags also complete that edge. In particular d_M(v)<=n_v, the full original COMPLETED mass at v. Original prime injections are singletons (incoming selected p would divide prime M>B), so d_M at its own root is 1. The argument would also work starting at a larger rank with fewer future thresholds.

Choose delta=u^(-1/8). For each source define the integer bin j(v) by
    (1+delta)^j <= d_M(v) < (1+delta)^(j+1).
Every positive threshold (1+delta)^j is first attained at most once per source. The number of attained thresholds is <=log N/log(1+delta)=O(u/delta)=O(u^(9/8)). Multiple thresholds attained in a single actual jump may be counted separately, which only increases the upper bound. If two actual vertices a<=b on the source list are in the same bin, then
    d_M(b)-d_M(a) < delta d_M(a).                   (1)

## 2. Wide macrogrid and three absolute linear masks

Let P0 be the largest even primorial <= B u^1.5, z its largest prime. As in persistent-blocks, elementary Chebyshev and Bertrand give P0=Omega(B sqrt u), P0>B eventually and z=Theta(u). Use a NEW macrogrid width and age
    S=P0 floor(T/(P0 u^1.5)),   D=S.
For sufficiently large X the floor is positive, S=Theta(T/u^1.5)=Theta(B²/u^1.75), S/B->infinity, S/P0->infinity, S=o(T). Analytic finite audit uses max(1,floor(...)) for small scales. In comparison to the previous D_old=Theta(Bu^2.5), D/D_old=Theta(B/u^4.25)->infinity. The macrogrid is nested in the base primorial grid; S need not itself be a primorial. Every strict crossing of a multiple of P0 is an actual edge with p>z; since p-1<B<P0, distinct base grid crossings are distinct completed edges. This remains true at macrogrid boundaries.

For a high completed hit at C on ANY currently retained incidence list choose its unique macro K=S floor((C-1)/S), K<C<=K+S. Test in this priority, with ranks on FULL original lists:
(i) If its original source has no completed strict crossing of K-D, remove the hit. Since current C>K-D, the only reason is initial horizon >K-D. Its gain age is <D+S, so total proxy removed per root <=1.5(D+S+B).
(ii) If no completed strict crossing of K+D, remove the hit. The actual terminal horizon <=K+D (including equality), so this hit lies in the last D gain of its original prefix; total proxy per root <=1.5D.
(iii) Otherwise let a be its own actual prevertex of the strict crossing of K-D; compare the actual original descending-rank bins at a and the present hit v. If different, remove the hit. The source attained some positive threshold strictly after a and no later than v. Since K-D-B<C_a<=K-D and K<C<=K+S, the hit's prehorizon is within D+S+B of that actual first-attainment vertex. All these hits for one threshold cost <=1.5(D+S+2B), including the possible last gain overshoot. A union bound over threshold attainments is valid even if intervals overlap.

Hence total removed proxy (and actual waits by w<=2r) is
    R_end = O(N(S+B)) = O(NT/u^1.5),
    R_rank = O(N(S+B) u/delta)=O(NT/u^(3/8)).       (2)
These are absolute linear bounds, not claims that the corresponding quadratic pair energy is small. No dependence on the number of partners, on birth fibre mass, or on local high mask. These tests are implementable by actual original crossing lookup and bins; they need not remove all events in the bounding windows. At every surviving hit both real crossings exist, and (1) holds from a to v.

## 3. Single old cohort selection at each physical high fibre

Fix any actual physical completed high vertex v=(C,t), and the set V of tags that remain there after the three masks and ANY previous incidence deletions. If V is empty do nothing. Otherwise let M0 be its smallest retained source and a0 its own actual crossing prevertex of K-D. Keep all tags of V that also visited a0 (equivalently have the SAME physical completed crossing of K-D); remove the other tags at this hit ONLY.

Proof of the budget: every tag of V is >=M0. Any larger visiting tag counted in d_M0(a0) still visits v, and all those tags follow the same actual deterministic crossing edge. Thus among all larger original tags at v, the number that did NOT visit a0 is exactly d_M0(v)-d_M0(a0). The number removed from V is at most this, strictly <delta d_M0(a0)<=delta n_v by the rank bin equality of M0. This is true regardless of which larger tags survived earlier incidence masks; no density-of-retained-tags hypothesis, no pairwise average, no mass cap on n_v. It is not necessary that the retained tags are contiguous in original source order. One may alternatively select the largest actual earlier-crossing cohort within V, since it retains at least as many tags.

Sum with the common physical weight r(C):
    R_foreign <= delta sum_v r(C) n_v
              <= delta R_all = O(NT/u^(1/8))=o(NT). (3)
This extra mask is linear proxy, hence also linear actual clock. It removes all cross-cohort synchronous pairs exactly: every two remaining tags at a physical high hit share a0, their actual completed crossing of K-D, and both complete K+D. In particular every surviving synchronous pair belongs to a genuine original through cohort with shared actual history across the two macro boundaries. A pair need not be kept at every high hit of that cohort; the mask can change at each physical vertex. No claim that the removed pair energy itself is o(F). Apply the mask to source incidences BEFORE using pair energy as a sufficient bound for their remaining linear clock. It can be combined with previously paid linear incidence masks by priority. Previously proved absolute energy deletions and quota eligibility restrict to the remaining pair pieces (do not reallocate previously paid scalar residuals). The new mask cannot increase any async pair demand; it does not by itself estimate async residual.

This is the main new synchronization result: no near-origin/local-prime-pair counting is needed to extend the shared-age window to S. A naive absolute quadratic payment for such a long age could exceed F. Instead the new actual rank proof pays the removal in the objective's LINEAR clock units.

## 4. Full-log local high diversity on macroblocks

Independently apply the density construction of persistent-density at the NEW block width S (not the old small grid P0). Work from the original natural high predicate, with its own deterministic masks identical for any source sharing the complete block. Use
    eps=eta=u^(-1/8), k0=floor(u^1.5), s=ceil(B^1.5).
First delete high hits with w<=eps(p-1) at total actual cost <=eps NH. At every original source macroblock rank the remaining high selected labels by block sum 2r (tie by p) and delete the first k0 (or all if fewer).

Here is the strengthened sieve scale check. For any actual vertex-endpoint interval of length L>=s, the high p>=Q quotient coordinate k defined by (C+sigma)/p=2k+1 is strictly increasing on the p list. Its candidate interval has length Hq=ceil(L/(2p))+O(1), which can be enlarged to an interval with Hq>=c sqrt B. Also p>=B/u. Therefore log(2+min(p,Hq))>>u, uniformly. Apply the previously proved short-quotient two-form bound in gain-prefix/quotient-blocks (sieve level floor(min(p,Hq)^1/8), high least-factor predicate). For any fixed selected p:
    sum_(high p hits in I) 2r <= 2p O(Hq/u²) << L/u². (4)
For a short first/last partial source block, use an enlarged interval of length S+B, since S>>s. Each source has <=G_M/S+2 actual prehorizon blocks. All choices of k0 labels per block, even adapted to original histories, therefore cost
    R_localrank << N(H/S+2) k0 (S+B)/u²
                = O(NT/u^.5)=o(NT).                (5)
Compare to the old bound L/(log u)² and old rank cutoff (log u)^1.5. No independence of p labels is required.

Next freeze the post-cheap/post-rank actual high wait measure mu on each actual macroblock's disjoint gain intervals, zero on other events. Mark the union of ALL actual endpoint intervals I contained in that block with length >=s and mu(I)<=eta |I|. The existing same-union depth-two interval lemma bounds actual marked wait <=2eta sum G_M, so another O(NT/u^1/8) deletion. The same earliest-start prefix-max algorithm and its literal finite oracle apply. This is a frozen one-pass mask, not a repeated fixed point.

Any surviving high hit has, in EVERY eligible actual endpoint interval of length L>=s containing its full selected gain interval,
    mu(I)>eta L,
    # distinct contributing high selected labels >> eta u²=u^(15/8),
    # contributing high events >=eta L/(2B),
    contributing high selected gain >=eta L/3.       (6)
Use (4) for the label count and w<=2B, w<=3g for the other inequalities. The witnesses in (6) are the frozen post-rank PRE-sparse high list; they need not survive the sparse or descending-rank masks themselves. All witnesses have actual waits >eps(p-1) and actual high selected primes. A complete through block has gain interval length at least S-B>>s. Hence every nonzero post-mask natural through block has at least order u^15/8 distinct actual high labels in its full central block. This is stronger than the preceding log-log diversity. The use of a local adaptive rank cutoff is justified by the new larger interval quotient sieve, not by increasing a finite quota.

The masks of this section can be performed before the rank-stability and single-old-cohort masks. The previous local-mask construction at P0 can be used additionally at its already established linear cost, but is not needed for this new sufficient route. All original high-attached LOW costs remain negligible by the earlier total count of original high selected hits. Total new actual linear deletions, combining (2), (3), (5), cheap and sparse, are O(NT/u^1/8).

## 5. Reduced synchronous high target on very long actual corridors

Define original macro through cohort A_(K,e) as all tags completing the same actual strict crossing edge e of K-D and a strict crossing of K+D. They share the whole central block and all base-grid crossings in between. Each positive group shares at least 2 floor(S/P0)+1 distinct completed edges with p>z; this is Omega(B/u^(13/4)) crossings. At most one group membership per original tag per K. Thus sum n<=NH/S+N. For the deterministic macro local high mask of section 4, define
    A_new(K,e)=sum of 2r over its full common central block surviving that mask.
Same local masks for every original group member, natural pair graph uniform with weight A_new per pair. In particular 0<=A_new<=3(S+B), sum n A_new<=3NH. The source-specific rank and single-cohort masks of sections 2-3 need not preserve a complete graph; actual surviving pair loads are <=A_new for every pair and eligible only at its actual old through group. No uniform equality asserted after source-specific masks.

As before pay groups with n<=m=floor(Bu^13/8) by at most 1.5mNH=O(F/u^1/8)=o(F). Remaining number of nonzero thick through groups is now
    <= (NH/S+N)/m = O(N/(B u^1/8))
                    = O(B/u^9/8),                  (7)
rather than the much larger earlier bound with denominator P0. This counts original ACTUAL macroblock crossing cohorts, not candidate words. Does not bound their squared masses. Each is a long common corridor of many original primorial crossings, containing the full-log diversity witness (6). There is no requirement of distinct crossing labels (only distinct edges); high label diversity is separately ensured for the central block, not necessarily for the crossing labels.

Use endpoint keys (K,M) cap c=S L_H, L_H=Bu^1.5. Total capacity <=L_H(NH+NS)=O(F/u^.25). This is an ALTERNATIVE to previous boundary keys, not cumulative. Same convex complete natural envelope and old eligibility yield the new sufficient synchronous estimate
    sum_(K,e:n>m) [ A_new(K,e) choose(n,2) - S L_H n ]_+ = o(F). (8)
The residual actual incidence energy is covered by (8) plus the o(F) small group and joint capacities and existing applicable absolute pair payments; the rank masks remove the entire short/late sector of the remaining synchronous ledger at o(NT) LINEAR cost, so no additional short/late pair-energy estimate is necessary. For a sharper actual local Hall objective use retained tag sets U_v at each central high vertex of a group:
    max_(L subset of A_(K,e)) (sum_v 2r(C_v) choose(|L intersect U_v|,2) - c|L|).
This is bounded by the natural complete envelope (8), but not necessarily attained by all members; earlier arithmetic keys may reduce it further.

The main remaining estimate (8) is OPEN. The new reduction combines very long actual synchronization, O(B/u^9/8) thick macrocohorts, and full-log local distinct-high-label constraints. Next try bounding occupancy-weighted formation and persistence of these few very large cohorts, using their earlier recorded merge forest and the actual two-clock prime congruences of the many high witnesses; no inference from merely counting possible labels or hypothetical words. Async-only high residual o(F) and medium actual residual o(NT) remain separate on a common unbounded dyadic sequence; then the actual-clock contradiction. No proof of twin infinitude or Lean compilation.

## 6. Reproducible finite audit

Source research/min_prime_root_macro_rank_audit.mjs at source commit d2e37c4f93f30b73abb3cbd49c322097e35eed4c, blob 3eca103446de9abc1d4909962358cc5f68a766ca, exact remote readback. Actual 16 runs in available ECMAScript runtime, not separate Node process. Reproduce:
    node research/min_prime_root_macro_rank_audit.mjs raw 30 2 256 1024 4096 16384 65536 262144
    node research/min_prime_root_macro_rank_audit.mjs diagnostic 210 1 16384 65536 262144
    node research/min_prime_root_macro_rank_audit.mjs wide 0 1 65536 262144
    node research/min_prime_root_macro_rank_audit.mjs wideRaw 0 1 65536 262144
    node research/min_prime_root_macro_rank_audit.mjs analytic 0 1 16384 65536 262144

All 16 passed. Retain earlier exact arithmetic MIN reconstruction, literal per-tick small controls, quotient candidate enumeration, all-interval oracle and common natural graph checks. Original descending rank independently constructed by visiting roots in decreasing order; each actual recorded state counts all visiting tags incl terminal, separate full completed mass. Check monotonic ranks, total threshold budget, actual last threshold witness inside window for each failed rank test, per-root endpoint and threshold clock caps, same-bin growth inequality, literal earlier physical membership of every kept candidate, foreign count <=rank growth<delta n_v, complete actual cohort membership for surviving tags and all surviving pairs, pair-wise accumulated load <=natural uniform graph and exact priority partitions of BOTH actual wait and proxy. Finite bin boundary comparisons have numerical tolerance. No arithmetic proof of asymptotic constants by finite tests.

Raw modes deliberately disable cheap/local rank/sparse actual deletions (eps=eta=0,k0=0) so many nonempty rank-stability and foreign masks exercise the new lemma; delta=.5. Diagnostic/wide local mask retains earlier finite settings (.15,.25,rank1), delta=.25. Raw and filtered are different diagnostic masks, not added. Analytic parameters from sections 1-4, including larger macro S; all three analytic runs have zero post-local-rank high residual, hence rank tests on high hits vacuous there. Finite local rank threshold does not establish limiting smallness.

| X/mode | S | D | input actual high after local mask | origin removed actual | terminal removed actual | rank removed actual | foreign removed actual | retained actual | retained synchronous energy |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|256/raw|30|60|1464|1165|187|36|0|76|0|
|1024/raw|30|60|3908|2957|387|422|0|142|22|
|4096/raw|30|60|32485|13949|1203|7664|38|9631|37400|
|16384/raw|30|60|176121|63502|0|51180|1351|60088|396264|
|65536/raw|30|60|1292149|298079|0|424370|13570|556130|5789812|
|262144/raw|30|60|7958300|1689170|0|2241717|57818|3969595|65663746|
|16384/diagnostic|210|210|11627|7344|223|2698|0|1362|3098|
|65536/diagnostic|210|210|26610|14374|0|9701|0|2535|7276|
|262144/diagnostic|210|210|265|265|0|0|0|0|0|
|65536/wide|2310|2310|254522|254522|0|0|0|0|0|
|262144/wide|2310|2310|1278706|1169408|40669|57375|0|11254|55036|
|65536/wideRaw|2310|2310|1298487|1294205|4282|0|0|0|0|
|262144/wideRaw|2310|2310|8001428|7576188|225786|148509|0|50945|921098|

Largest raw P30: 633075 actual rank monotonic checks, 58179 attained thresholds, max rank101, max bin11. 6945 rank-failed hits with actual threshold witness, 10992 per-root bounds, 12313 eligible tags and earlier membership checks across 2952 physical fibres. 155 fibres have foreign deletions (max9), actual foreign57818, proxy78978. Before dominant selection 903 young/different-crossing pair hits and 80336 same-crossing pair hits; afterward all 80243 surviving pair hits share same actual earlier crossing (all 903 young and 93 additional old pair hits removed by the tag mask). Actual retained synchronous energy65663746 versus same previous raw natural through93888770, but the deleted energy is NOT claimed an asymptotic small quadratic payment. Input actual high7958300 ->3969595. Largest wide filtered P2310>B1355 retains 11254 actual high wait, proxy9116, 20 eligible tags across4 fibres, 58 actual pair hits /52 pair-block keys, energy55036 versus previous same local-mask natural through858890. No foreign cases in this wide run; raw P30 exercises that theorem nonvacuously. Largest wideRaw retains actual50945, energy921098. For analytic largest X, P0=2310,S=6930, raw actual7971454, cheap2729278, local rank5242176, remaining zero, rank checks636506, thresholds39817; no positive analytic-scale corridor claim. Full natural earlier Hall envelope fields are retained as controls; the new post-rank pair energy is not a computed post-rank joint max-flow residual. No medium or async finite calculation in this auditor.

Main and other branches not edited. Paper proof and actual ECMAScript audits; Lean and twin infinitude remain open.
