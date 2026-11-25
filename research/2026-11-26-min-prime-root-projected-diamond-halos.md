# Primitive projected divergence diamonds, shared-label packing, and close-label all-event halos

2026-11-26 JST. Continuation of fa872d9c5c94d683b41081b886a7e58903c0f4fe on research/min-prime-root-repeat-energy-2026-11-25. Target the actual projected witness mismatch sector from lag-witness-crt. A deterministic packing inequality on primitive projected divergence-return intervals, together with a uniform shifted two-prime CRT support count, pays all original events in every one-high-per-side diamond with small background gain, without any partner multiplicity charge. The result is a LINEAR incidence deletion before energy accounting, not a general bound on far asynchronous energy. Paper deductions and finite audit; no Lean compilation, twins OPEN.

## 1. Original paths and primitive projected intervals

Retain dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, F=T²Bu, Q=ceil(B/u). Original prime-root gain-stopped MIN paths (including their original terminal snapshots) are unchanged. A completed event of selected odd p<=B increases even horizon C by g=p-1, actual wait w<=2r(C)<=3g, where r(C)<=p is the least eligible odd prime. Total gain G_M<H. Natural high p>=Q, r>p/sqrt(log p) implies r>3 eventually; explicitly impose r>3 in the spacing lemma and the centre selection below, including finite tests. In the analytic regime this is automatic. At a completed prehorizon C there are O(T/u) possible original prime-root tags, because C-T<2M-2<=C and the uniform prime interval upper bound applies. This is an upper bound on the full actual incidence set, not an independence hypothesis.

For any two distinct original roots, intersect their FULL projected vertex lists (including terminals) in increasing horizon. For two consecutive shared projected vertices A<D, the corresponding actual completed event sublists from A inclusive to D exclusive have the same total gain L=D-A. If their outgoing selected primes at A coincide, their next projected vertex is the same and D is exactly that next vertex. Otherwise call the interval a primitive projected diamond. Its two lists have disjoint internal projected vertices; their outgoing labels at A differ and their final incoming labels at D differ (equal final incoming label would imply a shared previous horizon D-p+1). No synchronization of physical times is required; if the two paths physically meet before a completed common suffix, there are no later primitive diamonds between their subsequent common projected vertices. A divergence with no later common vertex is NOT a completed diamond. All definitions are on original lists, not on thinned high lists.

## 2. Packing a shared high label inside a primitive diamond

At any high prehorizon C with r>3, C is even and C=0 mod3, hence C=0 mod6. For a selected odd prime p>=5, one has p|(C+sigma), sigma in {-1,1}. Two DISTINCT such horizons C,E with the same selected p obey
    E-C = 0, +2, or -2 mod 2p.
Indeed E-C+sigma_E-sigma_C is an even multiple of p. The only positive possibility below 2p-2 is 2, which is impossible because both horizons are multiples of 6. Therefore
    |E-C| >= 2(p-1).                                  (1)
This holds globally across different roots, even at different physical times. It counts distinct projected horizons, not physical buckets.

In a primitive diamond, any high occurrences of the same p in the two sublists have DISTINCT prehorizons: the only possibly common prehorizon is A, and the outgoing labels at A differ. If there are k>=1 occurrences of this label in the two combined sublists, list their prehorizons in increasing order. All lie in [A,D-(p-1)]. Consecutive ones are separated by at least 2(p-1) by (1). Thus
    L >= (2k-1)(p-1).                                 (2)
In particular a label used on BOTH paths forces L>=3(p-1). For L<3(Q-1), the high selected-label sets of the two lists are disjoint. For any common high label p, the sum of all OTHER gain on each side must be at least 2(p-1) if that side has exactly one p. If two high multisets are equal and contain at most two high events on each side, write P for their largest high label. The total gain is at least 3(P-1), so their nonhigh background gain on either side must be >=P-1 (if one high, >=2(P-1)). More generally, if a largest common high label P occurs once on either side and the rest of that side's gain is <2(P-1), the diamond is impossible. These are consequences of (2), not a probability statement about shared labels or a bound on all divergence counts.

For an actual pair with a same-label shared high edge, any subsequent unmatched high witness with its label present in the opposite sublist of a primitive diamond must be in a diamond of gain >=3(p-1). If its label appears only outside that diamond, or the two paths never rejoin, this local restriction does not apply. This addresses a subset of the preceding witness-mismatch problem, not all unmatched witnesses.

## 3. Global shifted close-label CRT support

Take integer J>=1 with J=o(Q); later J=floor(u^1/8), min1. A centre is an original natural high (C,p) key with r(C)>3 (at least one actual original tag selects p there). Call it bad if another such centre (E,q) satisfies
    p != q, |C-E|<=J, |p-q|<=J.
The reference support is the FULL original natural high ensemble, before any masks. We upper bound its bad centre weight by counting a relaxed arithmetic envelope, so actual tag multiplicity is not involved yet.

For fixed distinct p,q in [Q,B], fixed integer h=E-C in [-J,J], and signs sigma,tau, the congruences
    C+sigma=0 mod p, C+h+tau=0 mod q
give one residue modulo pq. Original horizons are in [2X-2,7X]; pq<=B²=O(X), so O(X/(pq)) solutions including the additive one, uniformly. Count all integer horizons (even/rough restrictions can only reduce the count). Count each unordered bad centre via ordered conflicting pairs with weight p+q; if a centre has many partners this overcounts it. With J=o(Q), p,q comparable, each p has at most 2J possible distinct q even ignoring primality, and there are <=2J+1 shifts. The elementary upper bound for reciprocal primes in [Q,B] gives sum 1/p=O(ell/u). Consequently
    sum_(distinct bad centres) p
      <= sum_(conflicting pairs) (p+q)
      << X (J+1)^2 sum_(Q<=p<=B, prime) 1/p
      = O(X (J+1)^2 ell/u).                          (3)
No external twin-prime or prime-gap estimate needed. This is a weighted arithmetic key bound; counting p,q both prime by the trivial short-interval bound is sufficient.

## 4. All-event gain halos and their absolute cost

For each original tag M, take every actual natural high centre (C,p) of that path whose key is bad in section 3. Around it put the horizon interval [C-kappa p,C+kappa p], integer kappa>=2. Mark every original completed event of M whose ENTIRE gain interval is contained in at least one such halo. This includes high, medium and LOW events, even if their own label is not involved in a conflict. Do not mark uncompleted events or extend a terminal. Define the mask simultaneously from original centres, no rerun of MIN or recursive propagation.

For each path marked gain intervals are disjoint; their total length is <= the length of the union of the halos, in turn <=2kappa sum of its bad-centre selected p. There is no extra B overshoot because only full contained event intervals are marked. Use r<=1.5g and w<=3g for the corresponding proxy and actual cost. Summing with the original source tag cap O(T/u) per centre and (3),
    W_halo, R_halo << kappa (T/u) X (J+1)^2 ell/u
                  = O(NT kappa (J+1)^2 ell/u).       (4)
With J=max(1,floor(u^1/8)), kappa=max(2,floor(u^1/4)), this is O(NT ell/sqrt u)=o(NT). In general any J=o(Q), kappa>=2 with kappa(J+1)^2 ell=o(u) works; the two exponents may be traded against each other. This is an all-event absolute LINEAR deletion. No factor for the number of root pairs, number of primitive diamonds, or repeated halo overlap. It is also valid if only high incidences in the halo are deleted, or after any previous incidence masks. For the actual-clock objective the all-event mask may pay actual waits directly; do not automatically delete an entire medium-plus-LOW quota block from its existing ledger if only some constituent waits have been paid. The high-only mask is sufficient for the immediate high-energy application.

## 5. Every small-background one-high-per-side diamond is fully covered

Suppose a primitive diamond contains exactly one natural high hit (with r>3) on each path, selected p,q>=Q. The total OTHER completed selected gain on the two sides is b_a,b_b<=J. Then
    L=p-1+b_a=q-1+b_b,
    |p-q|=|b_b-b_a|<=J.
The high prehorizons C,E lie in [A,A+J] because only background gain precedes them. If p=q then (2) would imply L>=3(p-1), contrary to L<=p-1+J<2(p-1) for J<p-1. Thus p!=q, |C-E|<=J, and both keys are bad centres. In fact each entire diamond [A,D] is contained in its own high centre's halo for kappa>=2: the left distance <=J<p-1, the right distance <=p-1+J<2p. Hence EVERY original completed event of both sublists is marked in the all-event mask. This holds simultaneously for every actual original root pair; there is no need to count the pairs. A preceding or following high incidence whose full gain interval lies inside its own centre's halo is also paid. In particular a shared high hit lying in the two respective halos is deleted on both endpoints. If a representative's diamond lies beyond a smaller tag's stop, no claim of coverage on that smaller tag follows; the proof is per actual original root pair.

Consequently after this mask all actual high hits in these diamonds and all sufficiently nearby high hits are removed from the remaining high ledger at cost (4). It is NOT legitimate to subtract the entire quadratic energy of any pair which has such a diamond somewhere in its future. For the residual far same-label sector, short primitive diamonds containing a high event on both sides must either have disjoint high labels (automatic for L<3(Q-1)) with substantial other gain on at least one side or more than one high hit on a side, or lie too far from the current retained common high hit for the halo to apply. Diamonds with no high or only one high side, divergences that never rejoin, and long primitive diamonds remain separate. The macroblock future-room mask ensures many actual future high labels on each surviving individual path, but does not force the two paths to share them. No proof of a global lower bound on witness agreement is obtained here.

## 6. Reproducible finite audit

Source research/min_prime_root_projected_diamond_audit.mjs at dd640a8968c52ecd96d24cd12726de39eb59189a, blob 4e77aa97e6786a6f07df9de6a06f05f8b318866f, exact remote readback. Initial source 19206e997a2252d2f58cae8cbafbf0652f6b5596 then all-event and independent global spacing extension. Final 18 actual ECMAScript runs, not a separate Node process, all passed. Reproduce:
    node research/min_prime_root_projected_diamond_audit.mjs diagnostic 256 1024 4096 16384 65536 262144
    node research/min_prime_root_projected_diamond_audit.mjs stress 256 1024 4096 16384 65536 262144
    node research/min_prime_root_projected_diamond_audit.mjs analytic 256 1024 4096 16384 65536 262144

Inherit original MIN reconstruction, literal small per-tick clock checks, exit-rank mask and far K=1 energy controls exactly from exit-rank-far-lag. Independently enumerate ACTUAL natural rough high distinct centres, sort by horizon, check all centre pairs with |h|<=J and near distinct labels, exact shifted CRT divisibilities, unique weight <= conflicting-pair weight. Check global sorted same-label spacing (1) even if the diamond common-label case is vacuous. Mark original full-contained gain intervals (all events and high subset), exact per-root and global length/proxy/wait budgets. At each original post-exit-rank retained physical bucket choose largest retained root representative. For every far same-p bucket pair at common C, merge its two actual original projected suffix vertex lists and identify consecutive shared vertices, primitive diamonds and unmatched terminal divergence. Check disjoint interiors, different outgoing/incoming labels, gain sums, shared-label packing where present, short disjoint alphabets, equal multiset restriction where present, small-background close-centre and whole-diamond halo coverage, and current hit halo membership when applicable. These are representative diamond OCCURRENCES per current bucket-pair hit, not necessarily unique root pairs/diamonds, and the weighted presence statistics overlap. The high energy after halo is computed on actual remaining tag counts at each bucket, not representative weights. Do not equate representative presence with all tag coverage.

Diagnostic J8,kappa2, stress J32,kappa4; original diagnostics T=4B, Q=max(5,ceil(B/8)), r>p/2, exit-rank delta .2/.5. Analytic T,Q,natural high predicate, capped delta as before, J=max(2,floor(u^.125)), kappa=max(2,floor(u^.25)). Finite integer parameters need not satisfy J<Q-1 at small X; for the one-high lemma explicitly require J<min(p,q)-1. The arithmetic asymptotic support (3) is a paper bound, not numerically verified as a constant bound by actual support counts. No cumulative macro density or lag-witness masks, and no medium quota recomputation.

| X/mode | bad centres | all-event halo actual | high-only halo actual | far K1 before -> after | diamond occurrences | short |
|---:|---:|---:|---:|---:|---:|---:|
|256/diag|20|1155|744|300 -> 116|3|0|
|4096/diag|12|4649|2127|13580 -> 13396|34|34|
|16384/diag|10|26982|13104|68614 -> 55316|34|28|
|65536/diag|6|12425|7775|357516 -> 357298|72|64|
|262144/diag|4|13925|6143|2818904 -> 2812378|244|223|
|16384/stress|130|165355|84512|87906 -> 51238|34|28|
|262144/stress|132|781521|476532|3703692 -> 3339482|254|231|
|16384/analytic|4|12094|7041|72546 -> 72546|22|19|
|262144/analytic|0|0|0|2874168 -> 2874168|219|203|

A nonvacuous small-background diamond at X16384 stress: current common high C=52848, divergence A=52890, first projected return D=53128, L238, p227/q233, background12/6; both high prehorizons52890, distinct close primes gap6. Both complete original sublists are halo-covered (combined gain476) and both prior current high incidences are marked on their actual representatives; associated full original bucket-pair energy1640 is a presence statistic, not a claim of that exact energy payment via only those representative marks. Largest stress 3338 distinct high centres,67 conflicting pairs,132 bad centres, bad key weight42854, bad original tag weight280173, all-event gain1041498 <= halo bound2241384, all-event actual781521, proxy932107,33113 marked events. Global same-label spacing3169 checks. Far energy3703692 ->3339482 (actual high tag counts). Largest analytic 3203 centres,3030 independent global spacing checks, no bad centres. 139 far bucket pair hits,219 completed primitive diamonds on their representative future suffixes,203 of gain <3(Q-1),18 with high on both sides,11 exactly one high on each side, none with small background. No shared high label within any examined primitive diamond in all 18 runs, so that particular positive packing case and equal high multiset case are vacuous; global spacing is nonvacuous. Largest analytic far energy2874168: representative has some completed diamond2297900, short diamond2297900, one-high-each120192, unreturned divergence850622; categories overlap. No halo change at this largest analytic finite scale. The small-background mechanism is exercised positively by the above stress example, not by analytic parameters. No finite claim of asymptotic decay.

## 7. Remaining proof task

The new exact inequality (2) restricts primitive returns, and the all-event halo removes a concrete class of short divergences unconditionally in linear clock units. Largest analytic sampled diamonds are mostly short with no shared high label; they need not contain any high on either side. A useful next task is to treat short LOW/medium-only diamonds by their actual phase congruences, including same-small-phase partitions and actual clock expenditure before/after their divergence, then address longer returns and no-return witness mismatches. Continue the earlier synchronous macro Hall o(F), far same-label async o(F), and actual medium o(NT) on a common unbounded dyadic sequence. Main and independent branches untouched; Lean and twin-prime infinitude remain open.
