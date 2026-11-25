# Direct leaf allocation and boundary-only flux certificate

2026-11-26 JST. Continues [6058ade75882](https://github.com/tara-sooo/A166944-Lean/blob/6058ade758820e99e02047b031c2ecaef0ff4698/research/2026-11-26-min-unified-laminar-inner-flux.md), with original independent heads unchanged at preflight: prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. Three results: disjoint source/sink gain packing gives a boundary-only sufficient condition at threshold 1/6; direct Hall transport of all long matched charge into short matched atoms and admissible crossings with capacity tending to 5, independent of nesting depth; and direct source-cell attribution of every remaining targeted pair to an admissible boundary after the old disparate-label deletion. No full upper contraction or Lean verification.

## 1. Setting and disjoint two-endpoint packing

Retain dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u), original completed MIN paths through first gain crossing T or original stop. Every selected odd p<=B has gain g=p-1, wait w<=2r<=3g and deficit increment delta=2w-g, with deficit d>=0 starting at 6. Total gain G<H on each tag. Use P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1) from 26afc6c. An admissible crossing is one on p<kappa P or r>=g/u; all other events are bad sinks, necessarily negative drift. At a bad sink j, gamma_j=P n_j/(-delta_j)<=cstar, where n_j is its strict grid crossing count; other negative sinks have gamma=0. F is admissible boundary flux, R=R_target the exact noninitial matched charge of 2d1f1cf. Each original positive source i pushes levels (d_pre,d_post], and each negative sink pops from the highest remaining levels. For any original (i,j), c_ij=gamma_j times length of the popped interval born at i; use the frozen original matching. For any subset of pair charges or fractions, the sum associated to one source is <=cstar delta_i<=5cstar g_i; to one sink <=cstar (-delta_j)<=cstar g_j. Positive sources and negative sinks are disjoint actual events, even when a particular event is shared as an endpoint by many pairs.

Let C be the total of ANY such pair subset whose source and sink gain intervals are all contained in a gain interval of length L. Sum over distinct source events and distinct sink events. The disjoint gain packing gives
    C/(5cstar) + C/cstar <= L,
    C <= a cstar L,   a=5/6.                             (1)
In particular R<=a cstar G for the full path, with no assumption about lifetime, phase, mass, or ultimate deficit. All statements use original tag-event multiplicity, not independence.

## 2. Boundary-only sufficient criterion

Parent exact identity F+R=P n_all-I_initial, 0<=I_initial<=6cstar, and P n_all>=G-P, imply
    F >= (1-a cstar)G-P-6cstar.                          (2)
Since cstar->1, eventual coefficient is positive and tends to 1/6. Under finitely many twins, all original tags reach T eventually by the original reachability argument, so sum F >= (1/6-o(1))NT. Retain old projected admissible boundary cap masks only, or any other independently proved o(NT) payment of actual boundary flux. In particular the short-label and rough boundary caps of 26afc6c cost O(NT/ell); do not count a source-tick payment as a boundary payment without proof. Then the following suffices for infinitely many twin primes:
    liminf_(dyadic X->infinity) F_rem/(NT) < 1/6.          (3)
This is a separate sufficient route requiring no direct bound on ANY matched charge, no canonical exposure parameter, and no estimate of terminal persistent deficit. It does not claim that (3) follows from the prior F_rem+R_rem<NT criterion: (3) has a smaller objective but a stricter threshold. Keep their disjunction. The raw lower bound under no twins is not an upper bound or proof of (3).

Optional refinement, not included in the finite audit: for each positive source define E_i=(delta_i-3g_i)_+; E_i<=4 by w<=2p. Let E=sum E_i over positive events on original tags. Then R/cstar<=3 G_source+E and R/cstar<=G_sink with disjoint gains, so R<=cstar(3G+E)/4. Consequently under no twins
    F_rem + cstar E/4 >= (1/4-o(1))NT.
One may restrict E to p<Y for Y->infinity at extra o(NT), since p>=Y contributes <=4G/(Y-1). This yields an additional weighted sufficient criterion with threshold 1/4, if the small-label positive drift excess and boundary flux can be controlled together. It is not claimed E=o(NT). The unconditional 1/6 route does not require E.

## 3. Direct leaf Hall allocation, avoiding repeated transport

For each matched pair i<j write e=C_pre,j-C_post,i, and let W_ij be the raw interior witness atoms of 6058ade: all admissible boundary flux of events i<k<j plus all targeted pairs i<k<l<j. By the local flux identity
    e-B0 <= weight(W_ij) <= e+P,  B0=P+5cstar B.          (4)
Matched intervening gain intervals are laminar per original tag, and their interior witness sets are nested or disjoint. Choose D=B ell² (round up), or any D/B->infinity and D<=H eventually. Call pairs long if e>=D, short otherwise. A LEAF destination is an original admissible boundary atom or an original short pair atom. No long pair is a destination, so no iteration is needed.

All strictly internal long pair endpoints of a fixed interval lie within its actual intervening gain segment of length e. By (1), their total RAW charge is <=a cstar e. Hence the total raw leaf weight W_leaf inside a long pair interval satisfies
    W_leaf >= (1-a cstar)e-B0.                            (5)
In particular for all large X this is at least (1/6-o(1))e, even if the interval contains arbitrarily many nested long matches.

Consider any selection of remaining long source charge portions. In a maximal distinct selected interval [C_post,i,C_pre,j] of length e, ALL endpoints of contained selected pairs (including shared births and sinks and outer endpoints) have gain intervals contained in [C_post,i-B,C_pre,j+B]. Apply (1) to that interval of length e+2B. The total selected demand there is <=a cstar(e+2B). Maximal selected intervals have disjoint interiors by laminarity, and their leaf witnesses are disjoint. Thus every subset of chosen long sources satisfies the weighted Hall condition for destinations strictly inside those sources with capacity
    K_leaf(D) = a cstar(1+2B/D)/(1-a cstar-B0/D).          (6)
The denominator is positive eventually, and K_leaf(D)->5. By finite max-flow/min-cut there exists a direct fractional allocation of ALL chosen long charge to leaf atoms, with total load <=K_leaf times raw leaf weight per original tag atom. The capacities are not replenished at different nesting levels. One can also use innermost-first greedy allocation because allowed witness sets are laminar (ties in interval size can be processed arbitrarily). Original boundary atoms and short pairs are not duplicated. This is a transport of long charge, not itself a deletion or claim that the leaf witnesses are small.

For any fixed previously paid leaf portions of total U_X=o(NT), allocate using raw capacities (split paid and unpaid portions); at most K_leaf U_X of transported charge is sent to paid leaf portions, and all remaining transported charge goes to unpaid leaves. Since K_leaf=5+o(1), there is no cumulative depth-dependent loss. Alternatively any subset of source intervals for which the paid leaf weight is >=eps e can be paid at cost <=a cstar(1+2B/D)U_X/eps by the maximal-interval argument. For a fixed finite old budget O(NT/ell), eps=ell^-1/2 gives o(NT). One must not then automatically declare every destination paid by repeating the mask.

Globally F+R_long+R_short <= (1+K_leaf)(F+R_short) by this direct allocation. This gives a sufficient bound on remaining leaf flux with threshold 1/6 after justified leaf payments, but the boundary-only result (3) is a smaller objective at the same threshold. The independent merit of (6) is local attribution to strictly interior short witnesses, not another stronger numerical threshold.

## 4. Direct source-cell transport of ALL surviving targeted pairs to admissible crossings

A further alternative eliminates the short/long distinction for transport. Let a positive source i with selected p, prehorizon C and posthorizon J supply positive targeted charge to bad sink j with selected q. The sink crosses at least one grid boundary because gamma_j>0. Let k be the first strict crossing event at or after source i on that original tag (including i if it crosses). It exists and k<=j.

If i crosses, its positive delta implies w>g/2, r>g/4, hence it is admissible for u>4. In this case k=i. Otherwise all events from i through the prehorizon A_k of k remain in the same closed grid cell, with C>=K-P and A_k<=K for K the first boundary crossed by k. Thus p-1<=P, A_k-C<=P and cumulative positive drift from source prestate to that crossing prestate <=5P.

If k is a bad sink, its deficit loss is at least (1-4/u)(q_k-1)>5P for sufficiently large X, since q_k>=kappa P, kappa->infinity. Its post-deficit is therefore strictly below the original source pre-deficit. ALL levels born at i have been popped no later than k. As j>=k, a positive L_ij forces j=k. For this pair e=A_k-J<=P and p<=P+1, q_k>=kappa P. With rho=ell from 2d1f1cf, eventually q_k>=rho p and e<=q_k/rho. Thus the earlier disparate-label mask pays this entire matched charge at total O(NT/ell), regardless of depth or mass. There is no other bad-first-crossing case for large X. Every pair remaining after that mask has an admissible first crossing k strictly before j, and this crossing is uniquely determined by the source and original tag. No use of arbitrary projected path extension.

Assign all remaining target charge to this admissible crossing event. It may be the source event itself. To bound congestion, fix one such original crossing event k, with label p_k, gain g, n>=1 crossed boundaries, first boundary K and offset a0=K-A_k>=0. All other source events assigned to k are noncrossing within the preceding grid cell; their full gain intervals are disjoint, and their summed gain l satisfies l<=P-a0. Also l+g<=(n+1)P, because the posthorizon is <=K+nP. By source drift capacity, their total assigned charge is <=5cstar l. The own-source contribution at k (zero if not positive) is <=cstar(3g+4), since w<=2p_k. Hence total assigned charge at k is <=
    cstar (5l+3g+4)
        <= cstar ((3n+5)P+4)
        <= cstar (8+4/P) Pn.
Distribute uniformly to its n individual original boundary atoms. Each atom has load at most K_cell P, where K_cell=cstar(8+4/P)=8+o(1). This does not multiply by nesting depth or count how many sinks consume a source. It is a one-step map, not a claim that the boundary is strictly interior to every assigned source. In particular the source may be the crossing event itself.

For ANY previously justified paid boundary set of weight U_X (e.g. short/rough projected caps), pay the remaining targeted charge assigned to those atoms, including partial charge when only some of a source's atoms are paid. The added cost <=K_cell U_X=o(NT). Every leftover charge unit is now supported on an unpaid admissible boundary atom (at that source cell). Thus the targeted residual can be localized entirely to old heavy boundary keys using only old disparate and boundary payments. The resulting bound R_remaining<=K_cell F_remaining would yield a threshold 1/9 via the total score, weaker than the unconditional 1/6 boundary-only result. Its distinct benefit is explicit support, not a stronger threshold. The direct leaf result (6) supplies internal rather than source-cell witnesses. No claim that these two different transports can be added without a partition.

## 5. Status

All extra payments above are either charge payments or boundary payments with independent bounds, not actual MIN path deletions. The two-endpoint global bound and the direct allocations use no independence or control of giant coalesced masses. The new boundary-only criterion (3) leaves precisely an arithmetic upper estimate for heavy admissible projected crossings. The short/rough boundary support sieve of 26afc6c and earlier phase/ancestry/Hall methods remain available, but no upper contraction to 1/6 has been established. The previous full targeted flux criterion can still succeed even when the boundary-only condition fails. No twin-prime proof, external novelty claim, or Lean verification. Main and independent branches unchanged.

## 6. Finite audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/39e0452d0d1d68101914a1f1758463973519c5f9/research/min_unified_direct_leaf_flux_audit.mjs), commit 39e0452d0d1d68101914a1f1758463973519c5f9, exact remote content readback. Eight runs in available ECMAScript runtime passed, five normal, three focus. Reproduce with node research/min_unified_direct_leaf_flux_audit.mjs 256 1024 4096 16384 65536. Derived from parent laminar audit; same finite P,T,kappa=2,alpha=1/8,cstar=4,D=floor(B/8) (minimum4). Uses actual per-tag gammaMax to check (1),(2) and interior/nested two-endpoint packing, not limiting cstar. For direct leaf routing, only long intervals with actual leaf weight >=e/8 are eligible: the finite valid Hall bound is KLeaf=8*(5/6)*cstar*(1+2B/D), not analytic limiting 5, since cstar=4. Tests direct innermost-first allocation to boundary or short pair only, no long destination. Tests source-cell map, first-bad-sink geometry, finite exception if preceding bad drop <=5P or finite rho=3 disparity fails, per-cell source gain packing, exact partition and bounded transfer to diagnostic paid boundary keys. These finite exceptions are not claimed payable by the analytic theorem with finite parameters. In fact no earlier-bad survival was observed, and finite disparity failures occur only in two focus runs. No analytic sieve, optional E refinement, cumulative historical mask, or literal gcd oracle tested. Initial code-generation attempt had a syntax error before execution; corrected source passed all eight and was saved/read back.

| X/mode | leaf-eligible long charge routed | long charge skipped at finite leaf threshold | charge mapped to admissible first crossing | charge at first bad crossing (same sink) |
|---:|---:|---:|---:|---:|
|256|0|0|0|0|
|1024|174.222222|0|213|0|
|4096|678.278308|0|3165.278074|37.530896|
|16384|14747.810004|0|35101.948960|467.590504|
|65536|88675.508428|1062.433195|200137.874566|2591.111478|
|4096 focus|188.186823|41.142857|330.934301|135.629405|
|16384 focus|476.249577|0|3178.544626|549.389761|
|65536 focus|15500.451330|0|49944.536754|4755.786957|

Largest normal: 5709 roots,140255 completed events, no full T reaches, actual G3088970,F2873142,R202728.986045. 5709 boundary-only packing checks,2444 long interval two-endpoint checks,2439 eligible leaf sources and allocation edges, all eligible demand routed exactly. 5756 per-tag source-cell keys and capacity checks, observed maximum load/F6.153846 (finite bound34.666667); entire first-bad charge2591.111478 meets finite disparity. 6119.262671 charge attributed to diagnostic paid boundary keys. Largest focus: 2886 roots reach T; on these actual G1271316,F1220310, sum of per-tag finite (2) lower bounds1054517.498724. All 768 long sources eligible and routed15500.451330. 864 source-cell keys, 2212.121131 target charge at paid boundary keys. First-bad charge4755.786957, of which4749.120290 meets finite disparity and6.666667 remains a finite exception. Max observed leaf load/weight normal83.991045, focus15.276498 (finite bound457.142857), not a test of analytic near-5 coefficient. Many original paths stop before T; these finite data do not establish (3) or the previous sufficient upper inequality.
