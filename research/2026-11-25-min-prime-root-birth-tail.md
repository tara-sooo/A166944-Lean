# Arithmetic first-contact tail quotas and joint physical/projected cutsets

2026-11-25 JST. Continuation of 7e53c0f869b45f3cf8ff2e865713b224e10da151 on the user-selected branch. The previous stable ancestry reduction leaves long synchronous backbones. Assign each pair's actual remaining cost to its first physical merger, or to its first projected contact, regardless of the current horizon, age, or depth of the original histories. Extend the parallel true waiting-birth arithmetic (a31a2f7872d58) from short all-odd deficit debit to long prime-root shared-tail energy and the actual medium quota ledger. In addition, joint max-flow/min-cut gives an exact obstruction-subset formulation for the TWO quota families, rather than independent greedy masks. This is a partial absolute deletion and a new finite sufficient target, not a proof of the unrestricted pair masses. No Lean compilation or twin-prime proof.

## 1. Original paths and pair ledgers

Use the inherited dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime starts M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu. The initial state is (M+2,2M-2); actual original cutoff and gain stop are unchanged. All vertices include the original terminal snapshot, no extensions beyond it. The total gain is <H, actual waits <=2r<=3(p-1), and all actual physical vertices have even horizon C in [2X-2,7X], deficit d=2t-C in [0,6+5H]. Set Dmax=6+5H.

For each unordered pair of distinct original roots, aggregate arbitrary remaining actual medium quota charges in BOTH directions into w_med>=0. These are fractional focal block charges, not proxy pair products; original allocations unchanged. Aggregate retained ordered high energy products in BOTH directions into w_high>=0, using the full frozen natural high list I as reference (p>=Q, r>p/sqrt(log p), Q=ceil(B/u)). Accounting masks and linear deletions may have removed arbitrary incidences. Each pair's entire natural ordered shared high energy is <=3H. If it first meets physically at v, its natural synchronous part is exactly twice the smaller root's remaining natural high tail at v, by ordered persistence. The retained synchronous part is no larger. The pair's pre-meeting asynchronous products can be included in the same quota without charging a pair twice. Similarly medium charges may occur before, at, or after a first meeting; no identification of a later charged E with the birth state is needed. We apply all earlier absolute and linear masks before the new quotas in the finite audit, but the bounds here hold for any such nonnegative retained weights.

Each pair carrying positive w_med or w_high has a common projected horizon, since each medium charge has a common later E and each high product a common C. It may have no common physical selected vertex. The first projected contact and first physical contact (if any) are fixed by FULL original vertex lists including all earlier deleted hits, not by residual incidence lists.

Use the two global budget bases
    A_med = NT/(X u^.25),
    A_high = F/(X u^.25).
All weights below refer to either metric separately; write A for its base. A per-key quota is an actual cost/energy amount, not a bound on the number of original roots. No comparability of focal and partner actual waits is assumed.

## 2. All projected first-contact keys, with arbitrary incoming primes

At the first common horizon C of two original roots, either one is at its own root horizon (at most one such root), or both have incoming labels p,q>0. If p=q, the predecessor horizon C-p+1 would be common earlier, contradiction. Thus p!=q and each divides C(C+2). For fixed unordered positive distinct primes p,q, there are four choices of sides; CRT leaves one residue class modulo pq for each. Since pq<=B²=O(X), the number of candidate C in the full horizon interval is O(X/(pq)), uniformly including the additive one. These are keys (C,min(p,q),max(p,q)), NOT root pairs. Arbitrary masses, physical times and all future recontacts are permitted.

Take Y=max(5,ceil(B^(1/8))). For positive labels let
    h1(q)=1 if q>=Y, else ell;
    h2(p,q)=1 if both >=Y, else ell².
The standard elementary reciprocal-prime estimates used in the preceding research give sum_{3<=q<=B}1/q=O(ell), sum_{Y<=q<=B}1/q=O(1). Thus sum_p<q 1/(pq h2(p,q))=O(1), and sum_q 1/(q h1(q))=O(1).

Give a projected mixed key the quota A/h2(p,q). A root-contact key is the actual original root M at which the first contact occurs, with quota A X/N; there are at most N keys. The sum of all projected quotas (even on the relaxed arithmetic key set) is O(X A). For any remaining actual pair weights, pay at each key at most its quota, e.g. uniform fraction min(1,quota/key total). This bound includes NEVER physically meeting pairs and arbitrarily long projected shared histories. In particular it does not use a first waiting meeting or a small relative rank.

For high energy, dividing the mixed quota by 3H shows the normalized full-tail product threshold is of order B sqrt(u)/h2; for medium the analogous reference whole-pair scale is H/m_g from the inherited endpoint density and sum of disjoint blocks, yielding a normalized threshold of order m_g/u^1.25/h2. These are interpretations, not an assumption that each pair attains its maximal budget. A quota can cover the full retained weight even if the full natural pair envelope is much larger. The root quota is independent of the other branch's mass.

## 3. Mixed physical births including all lower labels

A distinct root cannot visit another original prime root's starting physical state: at that odd tick t=M+2, every noninitial incoming prime would divide t-2=M>B. Thus a first shared physical vertex of distinct original roots has two positive incoming labels. If either predecessor is an initial root state, assign the pair to that original root-child key, breaking a tie by smaller root; there are at most N such keys, with quota A X/N. All pairs in this key are associated with the same root's first completed event. They may have huge opposite branch mass. This rule is not the assertion that the first shared vertex itself is a root.

Otherwise suppose the two incoming labels are distinct p,q. Write s=t mod2, d=2t-C. Actual MIN clock congruences give
    pq | C+2s,   2pq | d-6s.
For d<=6 use a low/reset key (C,t,p,q), with quota A/h2. In fact d=6s for two distinct labels because 2pq>=30, but the more general finite low-strip counting convention also works. For fixed p,q and parity, the horizon choices number O(X/(pq)); d has O(1) low-strip possibilities.

For d>6 define j by D_j/2<d<=D_j, D_j=Dmax/2^j. Then 0<d-6s=2pq k, k>=1, so pq<=D_j/2. For fixed p,q,j there are O(D_j/(pq)) possible positive deficit values for each parity, and O(X/(pq)) possible horizons. Since t=(C+d)/2, this bounds the full relaxed key count by
    O(X D_j/(p²q²)).
Additional parity or actual MIN eligibility can only decrease the count. Give each such key quota
    A pq/[D_j (j+1)² h2(p,q)].
Summing gives O(X A), using both the reciprocal-prime estimates and the summability of (j+1)^(-2). The low/reset key quotas sum to O(X A) separately. No requirement that either incoming label be high, or that both incoming masses be thin. No use of the short-clock deficit bound of the parallel branch; the long strip Dmax=6+5H is essential here.

## 4. Same-label true waiting births and rough arithmetic support

If the two distinct physical predecessor states of the first common recorded vertex have the same selected label p, both have the same pre-horizon C0=C-p+1 and distinct physical entry ticks a<b<t. They have the same deterministic scheduled exit (t,p). The actual first common waiting-state tick is (b,C0), because both original half-open waits cover that tick; any earlier common waiting tick would force an earlier common physical vertex or would already be in this same waiting interval. The proof uses actual completed events and terminal snapshots only. Conversely for different incoming labels the first waiting meeting of such a physically meeting pair is the recorded vertex. This is the parallel true-birth lemma, applied to the long original gain prefixes.

If neither predecessor is a root, let q be the actual incoming selected label of the LATER predecessor (b,C0), and q0 that of the earlier predecessor. These can depend on the original root tag even when the physical predecessor state has many incoming labels. Define lag h=b-a>0, r0=r(C0), d*=2b-C0, s=b mod2. Then
    h<t-a<=2r0, q|C0+2s, 2q|d*-6s.
If q=q0 the two arrival ticks are in the same progression of period 2q (one side at fixed C0), so h>=2q and r0>q. This is a deterministic restriction on their true birth, irrespective of their eventual suffix length.

Classify as rough if h>=Y, plain otherwise. Rough implies r0>Y/2, so both C0±1 avoid all odd primes <=z=floor(B^(1/64)) eventually. The key is (C0,b,q,rough/plain); we do NOT include earlier arrival tick a, earlier incoming label, or outgoing p as extra key multiplicities. The scheduled exit is determined by (b,C0); many distinct earlier branches can be assigned to the same key. This reduces to a count of candidate later-arrival states with one incoming label. The partition is frozen per original pair, not per charged endpoint.

For each q and each parity, the relaxed number of candidate C0 in the q congruence is O(X/q). In the rough class this improves to O(X/(q u²)): write C0=-2s+q k on an interval of O(X/q) consecutive integers, and use the established two-linear-form Selberg upper bound (32d4185 and the two-form argument in the prior prime-root exit-phase paper). For every odd sieve prime l<=z except q, C0-1,C0+1 exclude exactly two distinct residues of k. If q itself is a sieve prime and one form is identically divisible by q, no rough candidate is possible; otherwise omit q, which changes the product by at most an absolute constant. The previously established O(z^6) remainder is uniformly absorbed by X/(q u²) because X/q>=cB and z^6<=B^(3/32). This is a local sieve on the quotient k, with no independence assumption between C0 and the arrival phases. The parallel a31a2f7872d58 paper proves the same rough support for short prefixes; only the horizon interval and deficit range are used, so the longer strip here does not change this sieve.

For d*<=6 (call this LOW, not necessarily reset; q=3 admits exceptions), each parity has at most four admissible even deficits, so the plain key count per q is O(X/q), rough O(X/(q u²)). For d*>6 in D_j/2<d*<=D_j, there are O(D_j/q) admissible positive phases per parity, since q<=D_j/2. Therefore plain support O(X D_j/q²), rough O(X D_j/(q² u²)). The count may overinclude times outside the original cutoffs, impossible parity combinations, or nonrealizable inverse histories, all safely.

Let amp=1 for plain, u² for rough. Give each LOW true-birth key quota
    A amp/h1(q)
and each positive-band key quota
    A amp q/[D_j (j+1)² h1(q)].
For each class the amp cancels the rough sieve improvement. Summing q and j gives O(X A). In the rough class the normalized high full-tail budget can be of order B u^2.5 when q is comparable to d*, before the label-fee and j factors. This can cover many pairs with thick original ancestry; it does not impose a pointwise bound on their group products. In general small q/d* gives smaller quota. Roots in either predecessor were already handled by the root-child key; no q=0 is used in a reciprocal sum.

The full physical quota family including sections 3-4 has total O(X A). It pays pair weights of any physically meeting pair, even its earlier asynchronous products or earlier medium charges. Together with projected quotas the total permitted absolute payments are
    W_birth=O(NT/u^.25)=o(NT),
    E_birth=O(F/u^.25)=O(T²Bu^.75)=o(F).
They are not a linear deletion of all the sources meeting in one key. Fractional payments are algebraic removal of specified cost/energy portions and do not rerun MIN.

## 5. Joint allocation and exact excess cutset theorem

A pair has exactly one projected key and either one physical key or no physical key. Freeze the keys on full original histories. A pair with positive residual weight w_e can allocate any amount <=w_e across its eligible keys, as long as each key k receives total at most its quota b_k. The medium and high allocation problems are separate; do not identify their weights or optimize one metric at the expense of the other. These are bookkeeping payments, not new original medium partner choices.

Aggregate pairs with the same eligible key set into one weighted intersection e. Form a directed flow network:
    source -> e, capacity w_e;
    e -> each eligible k, capacity greater than the total weight W;
    k -> sink, capacity b_k.
Each feasible payment is a feasible flow and conversely; intersection flow may be distributed proportionally among its actual pairs. The best paid weight is the maximum flow M*. For any subset S of the keys, let
    W(S)=sum_{e: all eligible keys of e lie in S} w_e,
    b(S)=sum_{k in S} b_k.
A pair with no physical key has just its projected key in this test; no fictitious capacity is added.

The exact min-cut characterization is
    U* := W-M* = max_{S subset of keys} [W(S)-b(S)].            (1)
The empty S gives zero. Proof: a minimum cut never crosses an edge e->k of capacity >W, since cutting all source arcs costs W. For a fixed set S of source-side key nodes, every source-side intersection has all its keys in S. Conversely all such intersections can be put on the source side to minimize cut cost. The cut capacity is W-W(S)+b(S). Minimize over S and subtract from W. Thus this is an exact weighted Hall-type deficit, not just the largest isolated key excess. It exposes groups of original pair intersections that overload ALL available arithmetic keys jointly. A sequential uniform quota pass is feasible but need not maximize total paid; any additional flow uses only the already bounded combined quota budget.

In particular after the earlier medium and high reductions, the joint OPEN sufficient conditions can be written
    max_S [W_med(S)-b_med(S)]=o(NT),
    max_S [W_high(S)-b_high(S)]=o(F)
on the same unbounded dyadic windows. Relative error absorption from 7e53c0f and 4e8c7db remains a relative O(u^-1/8)E_J term, not an absolute deletion. The arithmetic quota allocation acts on the actual remaining nonnegative pair products after those classifiers, with no double subtraction. A bound on all excess subsets would close these remaining sufficient estimates; (1) alone does not give such a bound. The two global quota sums are themselves small, so this is not a magical route to bounding large total residual energy. It is useful as an exact localization of which original early histories must be controlled.

For example, if a maximal-excess S is found from the reachable vertices after max flow, every intersection with unpaid positive weight has all eligible keys in S. All other intersections are fully paid. Separate components of the incidence graph may be analyzed independently, since both the weight and quota terms add. A large individual projected key need not itself be an obstruction if its pairs spread across many physical keys with enough capacity; conversely a connected group of overloaded keys with few alternate neighbors is a genuine cut obstruction. No general estimate of W(S) from b(S) is proved.

## 6. Reproducible finite verification

Standalone research/min_prime_root_birth_tail_audit.mjs. Final code commit 18a1b6bfa58d0119e28e095a9fd6d3cc7081f71d, blob 40e2b930ed373e54a188dee9a7c920cad144e8a8, exact remote readback. Commands:
    node research/min_prime_root_birth_tail_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_birth_tail_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress 256 1024 4096 16384 65536 262144

Executed actual audit function in available ECMAScript runtime, not Node process. Initial version14 runs (analytic/concurrent four X256..16384, analytic/concurrent/combined stress at X65536,262144). Final version incorporates joint flow, separate full natural control pairs and low-deficit q=3 exceptions; all18 final runs (analytic, concurrent, combined six stress flags at six X) passed. Other final-version modes not rerun. Independently merge original full vertex lists to determine projected/physical first contacts; verify first projected labels, physical phase, true same-label lag and same incoming progression, ordered natural birth tail, total shared gain cap, and independent first waiting interval oracle on up to64 pairs (all checked until limit, including controls). Enumerate relaxed CRT phase/horizon support independently for all observed key TYPES, not all possible types, and exact finite rough-horizon count for up to32 observed rough types. Extra up to128 largest natural shared pairs exercise the classifier independently of residuals (analytic retained quota/pair residuals empty). Explicitly count all original low-deficit phase exceptions to the exact reset-line condition; use the LOW d<=6 class for same-label births, not a false assertion d=6s. Sequential payment and joint flow both checked for quota conservation, no double subtraction, and max-flow/min-cut excess equality; floating fractional weights and flows use tolerances. No Lean compilation or external novelty claim.

Analytic A_med=N H/(X u^.25), A_high=H² B u^.75/X (H~T), Y=B^.125. Normal diagnostic A_med=2, A_high=2H, Y=max(5,ceil(B^.125)); stress A_med=8,A_high=8H,Y=max(5,ceil(B^.1)). These are finite diagnostic choices, not asymptotic prevalence estimates. Prior natural high ledger includes only previous direct rank, local window, reverse, age and ancestry stability/density/recent-sync masks (NOT all cumulative hybrid masks). High linear deletion effects from previous turn are unchanged; this turn's additional quota payments are absolute pair-cost bounds. The two joint optimizations maximize TOTAL medium or high payment, not never-meeting or asynchronous payment separately; these subcomponents may differ between equally good or improved allocations.

| X | preceding normal medium | joint medium remainder | preceding never | joint never remainder | preceding isolated high | joint isolated high remainder |
|--:|--:|--:|--:|--:|--:|--:|
|4096|1.166667|0|1.166667|0|962|0|
|16384|42.553030|36.554588|42.553030|36.554588|11363|486.497465|
|65536|55.266667|45.191324|2.333333|.257991|608688|300930.683935|
|262144|67.714339|39.372628|25.314815|19.263192|8818550|5268893.691558|

Largest normal X262144: 8582 residual unordered pairs, 8433 physical,149 without physical contact. Of physical:509 root-child,708 mixed,7216 same-label. For same-label nonroot births 6441 rough,3898 same incoming q, lag range1..1120. 128 independent natural control pairs all physical. 43894 original noninitial low-deficit phase exceptions (tag occurrences, NOT necessarily births); 307 support-type checks including control types,32 exact finite rough-type checks. Sequential physical paid12.962426 medium,1282617.324475 high; projected extra15.377795 medium (never6.051623),2247967.896650 high. Joint improves by .001489938 medium and19071.087316 high. Total joint high payment3549656.308442, async residual79999.850923 (sequential74373.493941, so do not claim the joint total optimization improved this subcomponent). The final high residual is predominantly synchronous; both metrics' payment fractions are finite diagnostics.

Largest normal high joint graph1452 keys,995 intersections, mincut475 keys,5539 internal unordered pairs, internal weight6434790, quota1165896.308442, excess5268893.691558. Cut keys:254 projected-mixed,185 same-nonreset-rough,23 same-nonreset-plain,9 mixed-reset,3 same-low-plain,1 mixed-nonreset. Largest projected keys with unpaid intersection weight in this allocation:
    (C,p,q)=(787212,3,31):349718.577579 (298 pairs in unpaid intersections)
    (786508,5,971):266385 (248)
    (962872,11,23):231553 (117)
    (952470,3,19):213146.554174 (108)
    (710064,3,757):193134.283550 (67)
These are projected first-contact keys, NOT current high horizons; the labels are INCOMING at the first contact, not current natural high selections. The exact cut, not the ranking of these five keys, determines the unavoidable excess for the specified quotas.

Largest normal medium mincut23 keys,326 internal pairs, weight52.426190476, quota13.053562859, excess39.372627617. Largest remaining projected-key allocated excess10.010931882 at (991584,3,313), then8.477834963 at (760704,3,283). The graph shows small incoming labels may be crucial even for later high energy.

Combined six-stress largest medium37.179312->joint9.547318, never1.074074->0, high3611702->1532727.192363, async residual0. High joint extra8270.094378 beyond sequential, cut73 keys/1611 pairs, internal weight2161056, quota628328.807637. These are stronger thresholds, not an asymptotic bound or a cross-mode convergence claim.

## 7. Remaining proof task

The previous stable-backbone approach localizes old synchronous mass but cannot bound the origin basin. The new cutsets locate which pairs of early physical and projected histories jointly exhaust arithmetic budgets. In particular many largest observed projected keys have a small incoming label (3,5,11), and the remaining physical cut includes numerous same-label rough true births. One can now examine actual incoming source sets at those early keys, compare their intersections under the two fixed partitions, and seek a sieve/reverse-history bound on W(S) for arbitrary cutsets, rather than assuming thinness at every large current high state. The generic arithmetic key envelope alone only bounds b(S); it does not bound W(S). No proof of the joint medium and high little-o residual estimates, no proof of twin-prime infinitude. Main unchanged.
