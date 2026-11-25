# Actual high-clock local diversity and sparse-interval deletion on persistent blocks

2026-11-25 JST. Continuation of 51740a88e00bf1cc236ed7d7ecc2ffc2ee72a0c7 on the selected prime-root branch. Use the existing actual-clock sufficient target to remove high hits with small actual waits, local per-block selected-label concentration, and every hit contained in a low-density actual-clock interval. These three are absolute LINEAR clock deletions, not estimates of their deleted quadratic energy. The new deterministic mask is identical on the full shared central block of a persistent cohort, so the exact uniform graph and local Hall formula survive with a smaller occupation. No claim of general closure, no Lean compilation.

## 1. Setup and actual cheap high hits

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, v=log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, F=T²Bu, Q=ceil(B/u). Work asymptotically at v>1. All original gain-stopped prime-source paths unchanged, including actual terminal snapshots. Per-event selected gain g=p-1, actual wait w<=2r<=3g. Original natural high predicate p>=Q, r>p/sqrt(log p), weight h=r. The preceding actual-clock lower bound on no-twin windows and all existing LOW attachments remain valid.

Take eps=v^(-1/4). Among the full original natural high hits remove those with w<=eps g, with their actual cost
    W_cheap <= eps sum_M G_M <= eps NH=o(NT).
No assertion about their proxy r-cost (which can be larger). The remaining high actual wait is still bounded by 2r; on such events r>eps g/2. All later masks only delete incidences, not rerun dynamics. High-attached LOW is still handled by the earlier bound for ALL original high selected hits; no new LOW accounting needed.

## 2. Local same-label capacity at a wide grid

Use the preceding largest even primorial P<=B u^1.5, P=Omega(B sqrt u), P>B eventually; j=floor(Bu^2.5/P), D=jP. Put each completed event into its unique K=P floor((C-1)/P), i.e. K<C<=K+P. On each original source the consecutive event blocks indexed by K partition ALL its completed gain intervals. A nonempty block's actual first prehorizon and last posthorizon give a half-open interval of length <=P+B; these intervals are disjoint and exactly partition its completed gain range (some K can be absent). The number of blocks <=G_M/P+2 since the prehorizons lie in its gain range.

A high hit of selected p at even C has unique sign sigma in {-1,1} with p|(C+sigma), quotient (C+sigma)/p=2k+1. The exact same-label recharge identity in quotient-blocks proves k strictly increases on a source's p list. For an interval of horizon length L>=s=ceil(B u^1/4), all its possible high p prehorizons have k in an interval of at most ceil(L/(2p))+O(1) consecutive integers. Enlarge to a fixed interval of that length with sufficiently large absolute additive constant. Apply the already proved two-form upper-bound sieve in research/2026-11-25-min-prime-root-quotient-blocks.md and the uniform short-quotient form in gain-prefix: for Hq consecutive quotients the union over two signs has size O(Hq/log²(2+min(p,Hq))), using r>p/sqrt(log p), sieve level floor(min(p,Hq)^1/8). Here p>=Q and Hq>>u^1/4 since p<=B, so log(2+min(p,Hq))>>v, uniformly. Consequently for each fixed selected high p, in any such interval,
    sum_(p hits) 2r <= 2p #hits << L/v².             (1)
This is a per-source deterministic capacity, not a statement about how often a p is chosen. It applies to arbitrary retained subsets and also bounds their actual waits. For all hits whose gain intervals are contained in an interval [a,b), use their prehorizons in [a,b). For partial overlap with a gain interval one could enlarge by B, which would not change the estimate since s/B->infinity; no partial intervals are needed below.

Use (1) with an enlarged horizon window of length P+B even for initial or terminal partial source blocks. On each original source and central K, after cheap actual removal, rank the remaining high selected labels by their summed 2r weight in that block (ties by p), and remove the first k0=floor(v^1.5) distinct labels, or all if fewer. In fact any choice of <=k0 labels works. The deleted proxy and actual cost satisfies
    W_rank <= sum_(rank hits)2r
            << N(H/P+2) k0 (P+B)/v²
            = O(NT/sqrt v)=o(NT).                 (2)
Here P=o(T). This is local, per gain block; the earlier global per-source logarithmic-band concentration bound did not permit a new choice of top labels in every such short block. No summation over crossing-word candidates. In particular each surviving label's block 2r weight is at most the original post-cheap block 2r mass divided by k0+1, since the k0 removed labels each have at least its weight. This rank statement concerns the frozen pre-rank measure.

## 3. All low-density intervals at once, no repeated overlap payment

Inside each source block freeze the actual high-clock measure after cheap and rank deletion but BEFORE sparse deletion. Give the actual wait w of a remaining high event uniformly to its own selected gain interval, and zero to other intervals. Denote the resulting absolutely continuous measure by mu; at actual visited vertex endpoints [a,b) its value is exactly the sum of remaining actual waits in that sublist. Take eta=v^(-1/4), min length s above. Call every actual vertex-endpoint interval contained in this same block with length >=s and mu(I)<=eta |I| sparse. Mark all high events contained in the union U of ALL sparse intervals (finite family, arbitrary overlaps). This is a one-pass mask defined using frozen mu. Because all endpoints are actual vertices, every marked event has its entire gain interval in U and no ambiguity at boundaries.

Any finite interval family has a subfamily with same union and multiplicity at most two a.e. (existing actual-clock-cover lemma). Its selected lengths sum to <=2|U|, so
    mu(U) <= sum_selected mu(I) <= eta sum_selected |I|
           <= 2 eta |U|.
Sum over disjoint blocks of all original sources:
    W_sparse <= 2 eta sum_M G_M <=2 eta NH=o(NT).  (3)
No multiplier for number of candidate intervals, label bands, partner pairs or overlaps. This is an actual clock bound; no claim of small removed 2r proxy. The union can be computed in O(n log n) for n events in one block: for endpoints C_i and prefix actual mass M_i put S_i=M_i-eta(C_i-C_0). At each right endpoint b the earliest a<b with S_a>=S_b is obtained from the monotone prefix maxima by binary search. If its length is <s then no earlier qualifying endpoint exists; otherwise its interval contains every sparse interval with right endpoint b. Thus at most n intervals generate the exact union, followed by the same-union depth-two cover. This is also a useful independent way to audit all candidate sparse intervals.

For ANY retained hit after these three masks, EVERY actual vertex interval I in its own block containing the hit's full gain interval and having length L>=s obeys
    mu(I)>eta L.                                    (4)
This property is in the frozen POST-CHEAP/POST-RANK, PRE-SPARSE measure mu, NOT a claim that the final masked occupation of every such interval remains dense. It is a necessary witness constraint on actual paths: by (1) each distinct contributing high selected label in I has actual wait <=C L/v²; hence (4) forces
    # distinct contributing high p in I >> eta v² = v^(7/4).       (5)
Also at least eta L/(2B) actual contributing high events, since each waits <=2B. Their total selected gain is at least eta L/3, since w<=3g. Each counted event has w>eps(p-1) and a selected label not among the top k0 of its own block. These conditions all concern ORIGINAL recorded events of that common path. No assumed distribution of clock phases and no new occurrence probability. Low density elsewhere in a block is permitted; every witness interval must contain a surviving hit. Initial/terminal blocks shorter than s have no such interval, which is harmless.

The total actual high cost deleted by the three priority masks is O(NT/v^.25)=o(NT). For the high actual objective, remove these tag incidences from the high ledger BEFORE bounding the remaining proxy by energy. Earlier arbitrary-subset upper bounds remain valid; old arithmetic and origin eligibility remain attached to retained pieces. It is not legitimate to subtract their proxy from an old scalar energy as though it were an absolute quadratic payment. The async retained mask can only reduce its earlier residual; medium unchanged.

## 4. Persistent uniform block identity is preserved

Recall the actual persistent cohort (K,e) of original tags which traverse the same strict crossing e at K-D and actually complete the crossing of K+D. Its full central block is identical for every member, including actual first prehorizon >K and last posthorizon after the last prehorizon <=K+P, even when D=P. In analytic regime P>B so no missing central block if through; empty or no-high blocks can be ignored. The cheap filter depends only on the actual recorded event; block rank and sparse cover depend only on that common complete block, with a deterministic tie rule. All masks are therefore identical on the central block for every member, independent of what happened before K-D or after K+D. Define A_new(K,e)=sum 2r over the remaining high hits in that full block. The natural post-mask persistent graph is EXACTLY a uniform complete graph, with every unordered pair weight A_new, as in 51740a88e00b. For arbitrary additional retained holes it is an upper envelope.

A_new<=A_old; sum n A_new<=3NH. Previous short shared-age, terminal-age and thin persistent bounds unchanged. With the unchanged (K,M) capacity c=P L_H, L_H=Bu^1.5, and m=floor(Bu^13/8), the new sufficient synchronous condition is
    sum_(K,e:n>m) [A_new(K,e) choose(n,2)-c n]_+ = o(F).          (6)
This is weaker than the preceding (8) in persistent-blocks. It now restricts every positive term to an actual thick shared cohort with at least one high hit satisfying (4)-(5) on every eligible interval. For P>B the complete central block has length at least P-B (first prehorizon <=K+B, last post >K+P), and P-B>>s eventually. Thus a positive term's full common block has at least order v^1.75 different actual selected high labels, at least eta(P-B)/(2B) high events, and at least eta(P-B)/3 selected gain in the frozen post-rank high list. They occur on the same actual common physical suffix, not just in a set of possible arithmetic labels. Each event waits >eps(p-1). The high hit at a given C may be absent from the final mask; the frozen witnesses remain valid. Do not infer that all distinct labels are present after sparse deletion.

The remaining estimate (6) is OPEN: the local constraints do not yet bound the occupancy-weighted mass of such thick cohorts. A next step is to exploit the dense actual high-label words inside these shared wide blocks, their true parity-clock CRT conditions, and first thick-rank formation/representative covers, rather than increasing finite quotas. Async-only old Hall and actual medium residual remain open on the same unbounded dyadic sequence, then the previous exact contradiction. No new Lean claim.

## 5. Finite audit

Source research/min_prime_root_persistent_density_audit.mjs, committed and exact readback at 8c0b6af59129e9b9d860c93917b8e0c2dd88fcaa, blob 921dda41f98f7c94e505bbd02d20b392bd0ed4a7. Derived from previous independent audit; actual 14 runs in available ECMAScript runtime, not a separate Node process. Reproduce:
    node research/min_prime_root_persistent_density_audit.mjs diagnostic 30 2 256 1024 4096 16384 65536 262144
    node research/min_prime_root_persistent_density_audit.mjs diagnostic 210 1 16384 65536 262144
    node research/min_prime_root_persistent_density_audit.mjs wide 0 1 65536 262144
    node research/min_prime_root_persistent_density_audit.mjs analytic 0 1 16384 65536 262144

All 14 passed. Diagnostics use eps=.15, eta=.25, minLen=max(2,floor(P/4)), rank1, inherited finite high r>p/2 and original diagnostic T,Q,c,m. Analytic uses actual eps=eta=max(1,log u)^(-.25), minLen=ceil(Bu^.25), rank=max(1,floor(max(1,log u)^1.5)), inherited analytic high predicate. The independent integer quotient enumeration checks each actual original post-cheap p list's distinct quotient coordinate and weight against the literal relaxed arithmetic candidates in its block; this is NOT a numerical validation of the asymptotic constant in (1). Per-tick literal clock checks at X256/1024 inherited. Exact actual/2r priority partition, cheap bound, all endpoint prefix-max witnesses, depth-two cover equality and cost, literal all-interval union on every nonempty small-X block and 128 sampled eligible blocks per larger run, complete shared-mask event-sequence identity, original stop order, pair-by-pair postmask uniform graph, natural Hall maximum and nonuniform masked small subset checks passed. Floating comparisons at finite eps/eta have stated numerical tolerance.

| X/mode | raw actual high | cheap actual | rank actual | sparse actual | retained actual | retained persistent energy | heavy excess |
|--:|--:|--:|--:|--:|--:|--:|--:|
|256 / P30|1464|36|1132|43|253|0|0|
|1024 / P30|3908|29|3670|82|127|0|0|
|4096 / P30|32485|473|32012|0|0|0|0|
|16384 / P30|176121|1893|174228|0|0|0|0|
|65536 / P30|1292149|10161|1281988|0|0|0|0|
|262144 / P30|7958300|47892|7910408|0|0|0|0|
|16384 / P210|176121|1893|157401|5200|11627|9784|0|
|65536 / P210|1292149|10161|1248303|7075|26610|37278|23360.375|
|262144 / P210|7958300|47892|7909995|148|265|0|0|
|65536 / wide|1298487|10222|837469|196274|254522|0|0|
|262144 / wide|8001428|48020|5679931|994771|1278706|858890|780921.875|
|16384 / analytic|161263|47721|108965|4577|0|0|0|
|65536 / analytic|1223324|371317|827027|20942|4038|0|0|
|262144 / analytic|7971454|2814767|5047792|63906|44989|0|0|

Largest wide P2310>B1355 uses EXACTLY the previous wide control paths, original high R9751372, raw actual high8001428. Retained actual1278706, proxy R931911 (different units), 2783 hits, 2183 blocks. 22633 distinct quotient checks, 136144 literal candidate loop checks, 160314 earliest witnesses, 10946 cover intervals, union gain13586882, cover length13648666, actual covered sum996293 vs sparse actual994771. 18194 literal interval checks in 128 sampled blocks, 1504 non-sparse sampled intervals with a surviving event; finite minimum distinct labels1, not evidence for asymptotic v^1.75. 88 shared mask-sequence checks across23 nonzero persistent cohorts, max n41, 870 exact pair-block loads, 1 heavy group; persistent natural energy3018206 ->858890 and heavy excess2539095.5 ->780921.875 relative to the EXACT same prior natural wide control. Thin60210, heavy798680; ten positive local Hall excesses, masked small subset168 checks. The analytic finite through residual is vacuous (as in previous note); analytic high remaining actual44989 at largest X does not establish o(NT). P30 larger scales rank1 removes all because these narrow finite blocks contain at most one surviving label; not an analytic conclusion. No cumulative async or MED audit in this script.

Main and independent branches unchanged. Paper deduction, not Lean compilation; twin-prime infinitude still open.
