# Polynomial stopped HIGH transport, clock-refined separation, and record-label ladders

2026-11-28 JST, Issue #10. Base 3d2b22d83187f893a097d85d5821ff58c9e91629. User requests continued research toward M85 and eventual twin infinitude. This checkpoint changes the stopping rule from a prescribed number of events to a polynomial displacement threshold, sharpens the physical-state collision count using the exact clock relation, and derives a large-record-label alternative and a high-strip spatial-cut flux bound. It reuses the previous common-time theorem rather than replacing it. These are paper deductions and finite checks, not new Lean or independent specialist verification. M85 remains open; no new height exponent or common polynomial elapsed interval is proved.

## 1. Source and target

Let L=log R and fix 0<a<c<1/2. Use a density-scale family of distinct actual canonical roots A in [R,2R], whose first HIGH firing has anchor
    x0=r(u-1)+c0, h0=r+b0, n0=h0-x0/2,
where r is prime in [R^a,R^c], u is odd, x0 is even, ru is comparable to R, A=x0+r-1, and either (c0,b0)=(0,0) for HIGH plus or (2,3) for HIGH minus. Assume at least c_* R/L² such roots, c_*>0 fixed. The statement below counts arbitrary anchor pairs r,u for an upper, so it does not require a fresh lower-sieve theorem.

Existing input: the HIGH plus family at [.2855,.2856] from c20b70c, and the HIGH minus alternative at [.300,.3128] (or a fixed band approaching 5/16 from below) from e66355d. The latter remains a dichotomy with the static improvement alternative, and inherits the earlier Pascadi two-factor specialization review item. The present theorem is independent of that analytic input once a source family is supplied.

We retain the same M85: at H=floor(R^.4), Omega(R/L²) distinct actual FIRST-H sites with total gain<=4H. The stopped connectors below preserve the existing HIGH anchor height; they do not attain that target.

## 2. Order-free dyadic shell bound with a polynomial time horizon

Let T,D be positive integer horizons (T elapsed ticks after HIGH anchor, D cumulative suffix gain). Set M=ceil(T L^6), E=(M+1)(D+1). Assume
    T>=1, D>=1, E=o(R^a), (E+1)(T+1)=o(R^a/L²).             (1)
These imply T=o(R^a), D=o(R^a). In applications D and T grow and have fixed power margins in (1). The following estimates hold uniformly over the indicated horizons, without enumerating event histories.

At relative tick w, let g be pre-tick displacement and s=+1 for even absolute clock, -1 for odd, b_s=0 or3. The exact eligibility pins are
    q | F=2(r+b0)+2w-g+1-2b_s,
    q | r(u-1)+c0-g+s.                                      (2)
Conversely these imply eligibility when the clock parity corresponds to s. For all 0<=g<D even and 1<=w<=T the integer F is positive O(r), by (1). Also q=r cannot be eligible: g would equal c0+s modulo r; the possible residues are -1,1 (plus anchor) or 1,3 (minus anchor), impossible for even g with 0<=g<r-3. Thus every eligible q in this region differs from r and satisfies q=O(r).

Partition g+1 into dyadic shells 2^j<=g+1<2^(j+1). Declare a root exceptional if ANY g,w,s in such a shell admits an eligible prime q>=M 2^j in (2), even if the state is never visited by its actual trajectory. For fixed r,g,w,s the number of prime divisors of F is O(L), and the sum of reciprocals of those q>=M 2^j is O(L/(M 2^j)). For each q the spatial pin fixes one u residue modulo q, since q!=r and r is prime. The available u interval has length O(R/r), with q=O(r) and r²<=R^(2c)=o(R), so the u count is O(R/(r q)), with no extra additive term. Sum over g (O(2^j) values), w<=T, both signs and prime r (sum 1/r=O_{a,c}(1) by Mertens). The bad anchor count in each shell is
    O(R T L/M).
There are O(L) shells since D=o(R^a). The number of exceptional roots in the whole source is therefore
    O(R T L²/M)=O(R/L^4)=o(R/L²).                           (3)
No assumption that the intermediate state distribution is uniform; no source roughness, priority, or previous transcript used in this upper. Allowing both signs only overcounts.

For every nonexceptional root every actual winner in this region obeys
    q < M(g+1).                                             (4)
Follow the TRUE trajectory, including the final landing, until the earlier of T ticks and the first time the suffix gain is >=D. In case of equality at T classify it as the time branch. At any tick before the stop, gain<D; at the last moving tick (4) gives gain<=E. Hence the whole stopped connector lies in x0-E<=x<=x0, relative time 0..T. Its height is exactly
    h=r+b0+w-g/2.
By (1) uniformly over the whole connector h/r=1+o(1). In particular there is no reset to low height on these connectors. We have not asserted that the height increases over the anchor or over the earlier prefire record.

This differs from the prior shell theorem (research/2026-11-28-min-negative-high-height-shell-growth-and-second-quiet.md): the old stopping rule was T or a prescribed depth, with T polylogarithmic and a polynomial bound on gain after that depth. Here T can be polynomial and the stopping alternative guarantees either that actual elapsed time or actual polynomial gain. It is still a stopped alternative, not common polynomial time for all roots.

## 3. Clock-refined near-anchor packing

An improvement on the earlier O(R^(1-a) E(E+T)) estimate is available when T is much smaller than E. Two distinct same-sign-family connectors can meet only if, writing d=x0'-x0,
    |d|<=E,  |n0'-n0|<=T.
But n0'-n0=r'-r-d/2 (same b0), so the exact condition is
    |r'-r-d/2|<=T.                                         (5)
For FIXED r and even d there are O(T+1) integer candidates r', not O(E+T). They are comparable to r by (1). If r'=r then x0 and x0' are both c0 modulo r and |d|<=E<r, so d=0 and the root is identical. For different primes r,r', the congruences x0=c0 mod r and x0+d=c0 mod r' determine one residue modulo rr'. Since rr'=o(R), there are O(R/r²) candidate anchor positions in the slab enlarged by O(R^c). Sum over d, r' (even over integers), and r>=R^a (even over integers):
    # near pairs << R^(1-a)(E+1)(T+1)=o(R/L²).              (6)
Delete both endpoints of these pairs. The surviving >=c' R/L² connectors are pairwise disjoint in actual physical states, INCLUDING different relative ticks, with each connector itself having distinct clocks. The condition (5) is necessary for meetings, not sufficient; this deliberately discards all near pairs. If a mixed-sign source is available choose a single sign subfamily with positive lower before applying the argument. No disjointness of spatial positions alone is claimed.

## 4. Polynomial and stretched-exponential consequences

For fixed 0<t<delta and delta+2t<a, take T=floor(R^t), D=floor(R^delta). Then E=R^(delta+t+o(1)), (E+1)(T+1)=R^(delta+2t+o(1)), so (1) holds with power slack. Every retained actual connector reaches time T with gain<=E or reaches gain>=D earlier, and throughout h/r=1+o(1). All visited states are physically separated. Concrete examples (not optimization):
    HIGH minus a=.300: t=.040, delta=.210, delta+2t=.290;
    HIGH plus a=.2855: t=.040, delta=.195, delta+2t=.275.
These give actual polynomial-scale stopped alternatives, not a lower on the fraction of time stops.

For any fixed 0<gamma<1 and 0<delta<a, take T=floor(exp(L^gamma)), D=floor(R^delta). Then E=R^(delta+o(1)) and (1) holds. This variant gives a sharper structural alternative in the gain branch, as follows.

Let p_1,...,p_k denote the strict successive record winners among suffix events (not including the anchor r), in chronological order. If gain>=D occurs before T, its largest label is at least D/T, since each of at most T events contributes p-1. The first record has p_1<M by (4). Before a new record p_i, cumulative gain<=T p_(i-1), hence
    p_i < M(T p_(i-1)+1) <= M(T+1) p_(i-1).
Consequently
    k >= log(D/T)/log(M(T+1)).                              (7)
For the stretched-exponential horizons, log(M(T+1))=(2+o(1))L^gamma and log(D/T)=(delta+o(1))L. Thus the gain branch has
    k >= (delta/2-o(1)) L^(1-gamma)
distinct actual record labels, all less than the original r for large R. Their logarithmic exponent gaps are at most (2+o(1))L^(gamma-1), starting with log_R p_1=o(1), and ending at exponent >=delta-o(1). In particular every fixed open exponent interval strictly inside (0,delta) contains at least one actual suffix winner on every such gain-branch connector for large R. This is not a support count of possible labels in a relaxed graph: the labels are actual winners of the true path.

The previous common-time theorem (3d2b22d8) can be combined with this one. Start with its positive density-scale HIGH cohort, whose common initial T0=Theta(L²) suffix has gain O(L³/log L) and a growing number of actual events. Apply the deletion of (3),(6) to that cohort; it loses only o(R/L²). For either type of horizon in this section, D exceeds the earlier polylog gain bound and T exceeds T0 for large R. Thus every retained stopped connector actually contains the entire earlier common T0 suffix, including the earlier roughness and event-depth conclusions on the shorter subinterval where those were proved. We do not restart the dynamics or assume old pins can be forgotten. This is a genuine composition of established short common time with the new polynomial-gain/time stopping theorem.

## 5. Two distinct aggregate consequences: actual states and horizontal flux

At least a fixed fraction of the retained population must be of one of the two types for each sufficiently large R (the type may vary with R). If the TIME branch has positive density scale, its pairwise disjoint actual states number Omega(R T/L²) at high height. The common elapsed suffix T itself then holds for that subfamily.

If the GAIN branch has positive density scale, total suffix displacement of its distinct trajectories is Omega(R D/L²). More precisely restrict to moving edges with p-1>=D/(2T): the other at most T edges contribute <D/2, so at least D/2 gain per gain-stopping trajectory comes from those large actual winners. This is a lower on large-label gain from actual high histories, not an inference from the number of candidate pins.

There is an exact geometric bound on overlap of these moving edges. A moving edge with source x, destination x-p+1 and posttick clock n crosses (p-1)/2 even spatial cuts z with x-p+1<z<=x. Index each cut by (z,n). All edge keys of the disjoint trajectories are distinct, because equality of physical source and preclock would be a meeting. At a fixed n and fixed p the sign is fixed and eligible even source centers are one residue modulo 2p. Their intervals of length p-1 are disjoint. Across different p, each p divides n if n even or n-2 if n odd, by the exact calendar. Both relevant integers have absolute size O(R) and are nonzero throughout these connectors. For T=R^t,D=R^delta with delta>t, or the stretched-exponential T and fixed delta>0, the large-label condition implies p>=R^xi for a fixed xi>0 (e.g. half the positive limiting exponent of D/T). Thus at most O_xi(1) such distinct p divide the clock integer. Each cut (z,n) is counted O_xi(1) times. It follows that the gain branch, when of positive density scale, supplies
    Omega(R D/L²) distinct horizontal cut-clock coordinates
crossed by actual large moving edges in the high strip. The associated interpolated height z/2+n lies between the landing height and preheight+1, so remains (1+o(1))r for its corresponding connector. These cuts can be skipped by an actual jump and are NOT actual visited states. This distinction matters for M85 and for comparison with the time branch.

In the gain branch with D/T tending to infinity the net height change at the stop is w-g/2<=T-D/2, a polynomial downward change. The height nevertheless remains high relative to r because E=o(r). This makes clear that the new alternative does not by itself furnish upward record growth. It provides a distinct scale constraint on the downward behavior that a future height-section transport must handle.

## 6. Remaining analytic problem

The decisive open issue in this approach is controlling the gain branch or converting its record-label structure into actual upward height growth. The existing order-free pin count (3) cannot exclude the large winners required in section 5: its argument for a uniform threshold Q on g<D,w<=T gives at best O(R T D L/Q) by the crude divisor count, whereas the necessary labels can start as low as D/(2T). This upper is larger than the full density-scale population. Similarly, charging q-1 gain to every eligible candidate before any reachability test gives O(R T D L) total weight by the same fixed-r divisor bound; that is far above the required Omega(R D/L²). Even replacing the divisor-count L by a constant for polynomial-size q leaves the power of T. No claim that these relaxed upper bounds exclude actual gain stopping. The global positive-pin transcript method of 3d2b22d8 was limited by its modulus budget, and does not establish the necessary chronological correlations across the record-label ladder.

One possible next specific target is a bound on the weight of large eligible keys that are ACTUALLY reachable at g<D,w<=T, rather than summing all offset/tick possibilities. Any upper o(RD/L²) for the actual large-label gain of the separated source population would force the time branch to be density-scale. But even that would be a high-occupation result, not M85, unless accompanied by a sufficient bound on gain relative to time enabling positive height increments. Another next route is a reverse-first-use counting bound conditioned on several widely separated actual record labels. No estimate of either kind is proved here. M85 remains unmet.

## 7. Verification and provenance

- Reopened base 3d2b22d83187f893a097d85d5821ff58c9e91629, research/2026-11-28-min-negative-adaptive-high-transcript-and-quadratic-time.md (prior HIGH common-time result).
- Reopened previous phase-split source e66355d7718f684f05a780d9213603f8ddf46133, research/2026-11-28-min-negative-phase-split-absolute-bv-and-high-arrival.md; earlier shell note research/2026-11-28-min-negative-high-height-shell-growth-and-second-quiet.md and min-plus/height-section notes at base, 2026-11-28 JST. No new external theorem beyond the standard prime reciprocal bound used in the previous papers. No new use of Pascadi beyond the inherited source dichotomy.
- Audit research/lean/negative_min_polynomial_stopped_high_audit.mjs @0b2833c5a7b3008403af3da995e07672d992ed22, expanded synthetic controls @275aea1309d990bdf0c87cee7cd20435e979190d, final blob eaaaaba007171c63d2cdc18bebc2e50490e372e6. Actual finite proxy R=100000,400000,1000000; 868 isolated actual HIGH minus anchors, wider source band and deliberately small finite proxy M independent of T L^6. Tested 555520 hypothetical offset/tick cases for exact pin equivalence (109961 actual eligible-prime incidences), 493 retained anchor/budget cases, 6800 stopped ticks, 448 time stops, 45 gain stops, 337 record inequalities; 374 large-cut incidences (374 distinct). No actual meetings or near pairs in these small samples, so those checks were vacuous there. Independent synthetic (not canonical trajectory) geometry controls: 20880 anchor pairs, 908 nontrivial near-clock windows and CRT classes, 908 overlapping envelopes, 1180 cut incidences, 334 cuts of multiplicity>1, maximum multiplicity 3. Both programs executed with passing assertions, exact pinned and branch content verified. Synthetic examples test the geometry and necessary conditions only; they are not evidence of asymptotic collision probability.
- No new Lean run or independent specialist review. Core unchanged at blob b0e26798535b2c997f1383c1dc37bbe560aac938. Main/sibling branches untouched. No M85, unconditional twin proof or new static exponent claim.
