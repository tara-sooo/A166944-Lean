# Twin-prime closure roadmap and wide-primorial persistent block cohorts

2026-11-25 JST. Selected branch research/min-prime-root-repeat-energy-2026-11-25, starting checkpoint 1ccfb6af1957dcada4ee3286d01206288664e135 (fixed-age boundary Hall). This is an alternative boundary allocation for the same actual retained synchronous high weights, not an additional payment of the previous boundary capacities. New paper theorem: exact complete uniform natural pair graph on cohorts that actually share a wide block and both a preceding and following span of grid crossings; absolute payment of short shared age, terminal age and small persistent cohorts. The grid can exceed the maximum event gain, yet every surviving cohort shares at least order log B distinct strict crossings. Independent finite audit. Twin-prime infinitude and the remaining asymptotic bounds are OPEN; no Lean compilation.

## 1. Closure roadmap (direct twin-prime route, not the stronger record conjecture)

Use the existing prime-source MIN ensemble: dyadic X, B=ceil(sqrt(7X)), u=log B, N=#primes M in [X,2X)=Theta(X/u), T=floor(X/u^.25), H=T+B, F=T^2 B u. Original gain-stopped prefixes start (t,C)=(M+2,2M-2), include the crossing event and terminal snapshot, and keep the original time cutoff. Every completed edge selects p<=B, increases C by p-1, and waits w<=2r<=3(p-1). Here r is the least eligible odd prime at the actual prehorizon. Natural high h_M=r for completed p>=ceil(B/u), r>p/sqrt(log p), otherwise zero. Physical successor deterministic and stop order holds. Sum 2h_M<=3G_M, G_M<H.

The existing actual-clock reduction (research/2026-11-25-min-prime-root-actual-clock-cover.md) gives 2 sum w=G_M+d_end-6, d=2t-C>=0. On sufficiently large windows without a twin terminal every root crosses T, hence W_all>=N(T-6)/2. It suffices to establish W_all=o(NT) on a common unbounded sequence of dyadic X. The stronger least-factor support sieve (research/2026-11-25-min-prime-root-minfactor-support.md) gives sum_C r(C)=O(XB/u^3), so energy o(F) pays the corresponding high proxy via Cauchy. The actual medium target is o(NT), with the frozen focal-edge allocations and the earlier absolute payments. Low blocks, first uses, relative cheap hits and all earlier linear/energy payments retain their established bounds; no dynamics are rerun.

Concrete remaining sufficient tasks for the existing selected approach:
1. Synchronous high: establish the persistent block excess estimate (8) below for the actual original ensemble, or a bound on the smaller jointly retained synchronous demand. This note removes short shared age, proximity to actual terminal, and small persistent block cohorts unconditionally.
2. Asynchronous high: prove the old-key asynchronous-only Hall residual is o(F), or a direct actual clock bound compatible with the earlier high accounting. Do not transfer synchronous birth or suffix identities to different arrival ticks.
3. Medium: prove the remaining actual focal quota clock o(NT) using the actual fast interval cover and slow-edge arithmetic constraints of actual-clock-cover; do not substitute the stronger proxy or the unrelated squarefree-GCD label moments without proof.
4. Assemble all estimates on the SAME unbounded dyadic sequence, with exact disjoint accounting (or a verified joint allocation). Check hypotheses of the no-twin lower bound and derive contradiction. Formalize the resulting unconditional proof in Lean, including any imported analytic estimates and their axioms. Existing paper reductions and finite tests are not that proof.

The current result is task 1's new reduction. No claim that the three residuals have comparable difficulty or that finite residual size predicts completion.

## 2. A wide grid and a genuinely persistent segment

Let P be the largest even primorial <= B u^(3/2) and z its largest prime factor. Use standard elementary Chebyshev bounds for theta(x) and Bertrand's postulate. If q is the next prime, P q > B u^(3/2), q=O(u) (theta(z)<=log(B u^(3/2)) and q<=2z), and z=Theta(u) (theta(q)>log(B u^(3/2)) and q<=2z). Therefore
    B << B sqrt(u) <= O(P),  P<=B u^(3/2),  P>B eventually.
In particular all selected primes are <P. Set
    j=floor(B u^(5/2)/P), D=jP.
Eventually j>=u-1, D=Theta(B u^(5/2)), D=o(T). Every strict grid crossing C_a<=L<C_b at L multiple P has p>z: if p<=z then p|L; if C_a=L neither side is divisible by p, and otherwise the positive even distance L-C_a is congruent to +/-1 modulo p and is at least p-1, contrary to strict crossing. Since p-1<B<P, each completed edge crosses at most one grid boundary. Thus the actual crossing labels are in z<p<P (and p<=B).

For a natural unordered synchronous high pair hit at C, assign the WHOLE ordered pair weight 2h to the UNIQUE K multiple P with K<C<=K+P, i.e. K=P floor((C-1)/P). Retained pair weights may be arbitrary nonnegative <=2h with arbitrary holes or layer density; the entire retained density is assigned to this same K. There is no n_P(C) divisor and no fractional grid duplication. Let C_birth be the first actual recorded physical meeting of this pair, and C_end be the smaller source's actual terminal horizon (including gain crossing, twin or cutoff). Use disjoint priority:
- short: C_birth>K-D;
- late: not short and C_end<=K+D;
- persistent: neither.

For a short hit C-C_birth<D+P. The total natural ordered pair weight on all such hits is <=3(D+P+B), using increasing prehorizons and the possible last gain overshoot B. For a late hit C_end-C<D. All contributing completed gain intervals lie in the last D units up to the actual terminal, so total ordered pair weight <=3D. This includes terminal landing exactly at K+D in the late sector; no fictitious completed edge after a terminal.

Every pair that ever has a common completed hit has |M-M'|<T/2 since both pre-gains are <T. By the uniform elementary upper bound on primes in intervals of length T/2 (as used in gain-prefix), there are O(NT/log T)=O(NT/u) possible unordered pairs, regardless of physical mergers. Hence, for the full natural high synchronous ledger and any retained subledger,
    E_short+E_late << (NT/u)(D+P+B)
                   = O(F/u^.25)=o(F).                  (1)
This use of origin locality permits the larger shared age D, rather than bounding the number of pairs by choose(N,2). It is an absolute partial-hit energy estimate, not removal of an entire future shared suffix. No assumption about the arithmetic or frequency of the intervening primes.

## 3. Exact original persistent cohorts and common occupation

For every central K and ACTUAL physical completed crossing edge e of K-D, define A_(K,e) to be all ORIGINAL tags that traverse e and also actually complete a strict crossing of K+D. Write n=|A_(K,e)|. At each K an original tag belongs to at most one such cohort. By determinism, all cohort tags share the original recorded path from e through the strict crossing of K+D; no artificial extension. They share the actual strict crossings of every grid level from K-D to K+D, at least 2j+1 distinct completed edges with p>z in the analytic regime. This is a statement about common trajectories, not merely the number of visits at one horizon. Other sources may join or stop inside the span but are not members of this original cohort.

For any member define the common natural block occupation
    A(K,e)=sum_(x on its completed natural high suffix, K<C_x<=K+P) 2h(x).
It is EXACTLY identical for all n tags: all have crossed K+D strictly, D>=P, and share the full central block, including a completed hit at K+P if present. The selected gain bound gives
    0<=A(K,e)<=3(P+B).                                 (2)
Empty cohorts and zero occupation groups may be omitted.

Every persistent pair hit is assigned to its actual earlier crossing e at K-D and both endpoints belong to A_(K,e). Indeed the pair is already shared by K-D, and the smaller terminal exceeds K+D, so both complete the strict crossings. Conversely every two distinct tags of this cohort were already shared at the prevertex of e (C_e<=K-D) and their terminals exceed K+D. Every one of their common completed natural high hits in the central block passes both short and late tests. Therefore the FULL original natural synchronous high graph, after exactly those two deletions, is a disjoint family of complete uniform pair graphs at the boundary keys:
    E_persistent = sum_(K,e) A(K,e) choose(n_(K,e),2).  (3)
This is equality, not the previous top-suffix upper envelope: each unordered pair in this block has precisely A weight. For a retained ledger each corresponding pair has weight <=A, with eligibility to all earlier keys preserved. Each source's central high hits belong to a single K, so
    sum_(K,e) n A(K,e)<=2R_high<=3NH,                  (4)
and the total membership sum n <= sum_M(G_M/P+1)<=NH/P+N. These two budgets use the actual original source ledger, not a count of possible predecessor states.

## 4. Thin persistent blocks: an unconditional additional payment

Set m=floor(B u^(13/8)) for large X. Using (4), all through-group pieces with n<=m cost at most
    E_thin<= (m-1)/2 sum_(K,e) n A(K,e)
          <= 1.5 m NH = O(F/u^(1/8))=o(F).            (5)
No Hall capacity is increased to obtain this payment. The remaining groups have n>m, number at most (NH/P+N)/m=O(NH/(P m)). The same payment is valid for arbitrary retained layer weights. This removes a wider class than simply applying the previous minimal-Hall internal-degree threshold of order B u^1.5; the price is paid with the actual single-block membership/occupation budget, not an assumption of thin original fibres.

## 5. Exact local Hall excess and joint reduction

Replace the previous boundary allocation by keys (K,M) of capacity c=P L_H with L_H=B u^1.5, eligible at BOTH actual endpoints of each persistent block demand. At each K each such key belongs to a unique persistent group. Old arithmetic and integrated origin eligibility is unchanged. The total new capacity is at most
    c (NH/P+N)=O(NH L_H)=O(F/u^.25)=o(F).              (6)
The old boundary keys are not charged a second time. If a key has no eligible retained demand, it can be omitted. No change in the previous arithmetic/origin capacities.

For any selected set of k endpoint keys of a single group, the internal demand is bounded by A choose(k,2). Since this is a convex quadratic minus linear capacity c k, its maximum on integers 0<=k<=n is at an endpoint:
    H_persist(K,e)=[A(K,e) choose(n,2)-c n]_+.          (7)
For the full natural graph with only these new endpoint keys, the local Hall residual is EXACTLY (7); for arbitrary retained pair masks and joint old-key constraints, it is an upper bound. Unlike the earlier nonuniform natural suffix envelope, no interior top-k optimization is required. With a=A/P in [0,3(1+B/P)], a positive term requires a(n-1)>2L_H. Thus a thick group still must have sufficient actual central high occupation. Source-ordered stops have already been handled by the absolute late payment, not ignored in (7).

The same weighted Hall objective argument as boundary-hall now yields for the current joint high ledger with the alternative block allocation
    R_joint <= E_short+E_late+E_thin + R_async,old
                + sum_(K,e:n>m) H_persist(K,e).
Subtract the new included endpoint capacities only against the persistent group demand; subtract the included old pair capacities against async-only demand; ignore remaining nonnegative capacities for this upper bound. The removed thin pieces are bounded directly, with no duplicated old payment. In particular a new explicit sufficient synchronous condition is
    sum_(K,e:n>m) P n [ a(K,e)(n-1)/2 - L_H ]_+ = o(F). (8)
This is the analytic remaining estimate, NOT proved here. It concerns original actual cohorts that persist across order u distinct completed primorial crossings, with a single common full-block occupation, rather than arbitrary recent births, differing stop truncations, or large-p>=P boundary edges. A possible next approach is to use the common crossing word's true phase constraints (each crossing p>z=Theta(u)) and the actual thick-cohort representative cover across these spans to bound the occupancy-weighted tail in (8), separating rare large rank formations from inherited cohorts. The membership count and gain budget alone do not give (8). For example an abstract large long-lived cohort can make the complete graph contribution quadratic despite satisfying the membership count. One may alternatively bound the smaller actual joint residual, not the full natural envelope.

The async-only old Hall estimate and actual medium residual remain independent. The derivation concerns the current synchronous high ledger; it must be combined with the cumulative hybrid's exact layer density/accounting, not with a scalar from an old flow.

## 6. Independent finite audit

Source research/min_prime_root_persistent_block_audit.mjs, commit 741f2aaf52abdd045062938f106a345e400d7079, blob 6a6fd3e0d3b2299802bb2008490a22823f8f3225, exact committed source read back. Executed the exact audit function in available ECMAScript runtime, not a separate Node process. Reproduce:
    node research/min_prime_root_persistent_block_audit.mjs diagnostic 30 2 256 1024 4096 16384 65536 262144
    node research/min_prime_root_persistent_block_audit.mjs diagnostic 210 1 16384 65536 262144
    node research/min_prime_root_persistent_block_audit.mjs wide 0 1 65536 262144
    node research/min_prime_root_persistent_block_audit.mjs analytic 0 1 16384 65536 262144

All 14 runs passed. Independent reconstruction of canonical MIN prime-source paths from factorized parity clocks; literal per-tick gcd oracle X256/1024 (1707 checks), linear first-birth oracle through X4096. Actual strict crossing existence, forbidden small selected prime, one crossing per edge when P>B, exact membership count, common middle and future crossing, full span on every member, common natural occupation, per-pair short/late caps, stop order and origin localization, disjoint full natural graph partition, exact pair-by-pair common block loads, global thin bound, convex local Hall formula, exhaustive subsets for n<=10 with independent nonuniform pair masks all checked. No dependence on the previous flow scalar. The finite graph is the FULL natural high synchronous ledger, not the cumulatively retained joint ledger; its values are not comparable to the previous scaled flow residual. Diagnostic T=4B, Q=ceil(B/8) (min5), r>p/2, c=3P/16 and m=8; wide T=max(4B,4P) and P smallest primorial>B; analytic parameters from sections 2-5. The deliberately nonanalytic smaller caps are diagnostic only, not a new quota increase. No finite medium or async calculation in this auditor.

| X / mode | P | D | full natural sync | short | late | persistent | heavy excess |
|---|---:|---:|---:|---:|---:|---:|---:|
| 256 / diagnostic |30|60|4768|3768|966|34|0|
| 1024 / diagnostic |30|60|11788|10398|384|1006|0|
| 4096 / diagnostic |30|60|134658|64336|7532|62790|0|
| 16384 / diagnostic |30|60|1141674|391062|0|750612|525388.875|
| 65536 / diagnostic |30|60|12715542|3830752|0|8884790|6882968.625|
| 262144 / diagnostic |30|60|116767336|22878566|0|93888770|84802207.5|
| 16384 / diagnostic |210|210|1141674|803846|86300|251528|153356.125|
| 65536 / diagnostic |210|210|12715542|7128008|196040|5391494|4132168.25|
| 262144 / diagnostic |210|210|116767336|44055684|18684|72692968|65507399.875|
| 65536 / wide |2310|2310|12847478|12830798|16680|0|0|
| 262144 / wide |2310|2310|120272202|114010722|3243274|3018206|2539095.5|

Largest P30: 20390 original roots, 612685 completed events, 144798 natural pair-hit checks, 68675 first physical births, 633315 grid crossings. 5323 nonzero natural through groups, 19258 tag-block occupation checks, max n71, 550 thick groups, 116141 exact pair-block loads. Thin energy9032270; heavy84856500; 2561 positive full natural local excesses. 2133 small-group exhaustive masked oracles, 147704 subsets. Largest P210: 3945 groups, 14630 tags, 89014 exact pair-block loads, 429 thick groups, thin6891870. Largest wide P2310>B1355: 8159 actual strict one-edge crossings, 41 nonzero through groups, 174 tag-block checks, max n41, 3 thick groups, 1189 exact pair-block loads, positive groups26, thin449658, 24 masked oracles/1520 subsets. This exercises nonempty actual through cohorts with P>B. Analytic X16384/65536/262144: D exceeds T or the observed shared spans; all synchronous weight is classified short, no persistent group. This is a vacuous finite test of the analytic persistent residual, not evidence for (8).

Main and independent research branches were not edited by this checkpoint. The paper proof and source persistence are separate from Lean formalization; no twin-prime proof.
