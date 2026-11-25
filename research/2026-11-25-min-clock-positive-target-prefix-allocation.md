# Positive rough targets: adaptive common-prefix strips and capacity-two upstream allocation

2026-11-25 JST. Continues 1ce40c101e84d8dcf8771a689f0a83c2629c8201. New paper results: exact classification by distance from first COMMON RECORDED state, an adaptive backwards gain-strip length depending on both r and anchor deficit, constant-capacity allocation of overlapping predecessor strips WITHOUT a dyadic log factor, and recent-birth transport with a coefficient proportional to the upper target r cutoff. No full energy estimate, no Lean compilation, twin infinitude OPEN.

## 1. Actual ensemble and pair/target charge

Retain dyadic X, odd roots M in [X,2X), B=ceil(sqrt(7X)), u=log B, H=4B, original starts (M+2,2M-2), gate K(M)=floor((7M-1)/4). Fixed-cap MIN, actual completed original waits including crossing event, endpoints <=s+6B or earlier twin. Actual d=2t-C in [0,12B+6], total gain <=12B+6. At any completed wait w<=2r<=2p<=3(p-1). No new occupation. Use actual long-age LOW nonreset donor anchors g of 24bfe41 and 01297e9, unique rough recipient target, row weights x_i(g) in [0,1]. Write D=d_g-6>0, r=r_g, x=x_i(g)x_j(g). Internal unordered donor pair/anchor contribution to S^sharp+I^sharp is
    c=(r/B)xD, D<=12B.
Both tags share the same recorded target arrival b, horizon C and completed departure v. Focus on POSITIVE target net drift 2(v-b)-(p-1)>0. This defines M_pos, the same sector as 1ce40c1. Each pair/target key counted once, and all targets for a fixed pair are actual completed slots on the same recorded suffix. Internal pairs share an anchor, so |M_i-M_j|<=6B and there are O(XB) possible pairs. Pair gain budget sum r/B<=27. This is donor-square weight, not original old cross W_g.

Let (t_*,J_*) be the pair's first common RECORDED state, not necessarily its first physical meeting. Backwards matching actual full recorded waits locates it exactly. If first physical meeting is a jump-stationary meeting inside a waiting slot, the first common recorded state is its next completed departure; if the first meeting is a root or simultaneous jumps, it is already a common recorded state. The target anchor is itself a common recorded state (same labeled post-event), hence J_*<=C_g<C. Define d_*=2t_*-J_* and G=C-J_*. The actual shared gain to anchor G_g=C_g-J_*<=G. Actual common elapsed clock to anchor <=3G_g by the wait bound, so
    d_g-d_* <=5G_g <=5G.                          (1)
The earliest common recorded state is fixed for the pair, irrespective of which subsequent target is under consideration. The pair-specific future support may be shorter than either full path; no fictitious reference.

## 2. Adaptive predecessor strips

For each positive target choose integer
    h=ceil(min(r/2,D/10)).
It satisfies 1<=h<=ceil(r/2)<=r-1 (r odd >=3). Define OLD if G>=h; otherwise RECENT. The terms are disjoint. OLD strip I=[C-h,C) is completely covered by actual shared recorded edge gain intervals STRICTLY BEFORE this target, starting at or after J_*. An edge ending at C is permitted but the target's own outgoing wait is not. Density of charge satisfies
    c/h <= max(2D/B,10r/B) x <=24.                (2)
In particular there is no inverse small-deficit or small-strip parameter in (2). In the recent case, integer G<h implies G<min(r/2,D/10), even when the ceiling rounds upwards. By (1), D<=d_*+5G-6<d_*+D/2, hence
    D<2d_*, c<=2(r/B)x d_*.                      (3)
This detects already high recorded births if D is large. If desired first pay small anchor deficits D<=m=u^11/4: per pair sum charges <=27m, total O(XBm)=o(XBu³). Then recent d_*>m/2. That optional small-D priority is paper only; the adaptive audit retains all positive targets. An earlier fixed eta comparison was tested separately: low D<=eta B transfers <=18 eta E_target,pos; the remaining old strips h=ceil(eta r/16) have density <=192/eta and dyadic log reuse. The adaptive version improves those constants and covers the whole positive sector without that low-deficit split.

## 3. NEW capacity-two allocation, with proof

Fix one actual donor pair and the finite collection of its OLD target strips. Their reflected forward intervals F=[C,C+h) are pairwise disjoint, because h<=r-1<=p-1 and the selected target outgoing gain intervals are disjoint on the common recorded suffix. The forward intervals are used only for this geometric argument, never charged as old ancestry.

For ANY subset of the backwards strips, take a connected component of their union with endpoints a,b. All strips in this component have lengths <=b-a, and their right endpoints C lie in [a,b]. Their forward reflected intervals are disjoint and contained in [a,b+(b-a)], of length 2(b-a). Thus the sum of lengths of strips in that component is <=2(b-a). Summing components proves the subset inequality
    sum_(I in family) |I| <=2 |union I|             (4)
for EVERY subfamily, not just the whole collection.

All endpoints and lengths are integers. Make h unit demand copies for strip I, and two unit capacity copies of each unit gain interval [k,k+1) in the union. A demand copy can be matched only to gain units inside its own strip. For an arbitrary subset of demand copies, its neighborhood is the union of the strips having at least one copy in the subset, with capacity twice its length. Inequality (4) verifies Hall's condition, since the subset has at most the sum of full demands of those strips. Thus there exists an allocation of every strip's h units into its own interval, with at most TWO allocations per gain unit. This may also be found by processing strips in order of increasing right endpoint and using the earliest still available capacity units inside the strip. Exchange proof: in any feasible allocation after previously fixed strips, if the current strip uses a later unit instead of an earlier available one inside it, exchange with that unit's owner (or use a free unit); the owner is a later-deadline strip, its release is no later than the earlier unit, so it can use the later one. Iterate to obtain greedy allocation. Multiple copies at one gain unit are identical capacity slots; no issue with ties.

Assign c/h weight to each allocated unit of its strip. By (2) at most 48 total weight per gain unit for this pair. Hence every old charge is assigned only to strictly prior ACTUAL shared recorded edges, with total assigned mass <=48(p'-1) at a fixed pair/upstream edge. NO number-of-targets or log(B/R) factor. This is stronger than separately summing per dyadic r band (the old geometric overlap may be large across bands). The allocation preserves each target's own admissible predecessor interval; it does not move its charge to an edge after that target. For actual normalized x<=1, the displayed uniform density bound applies; the audit uses actual c/h. The two independent LOW classifications L30 and L6 must not be added as one graph.

## 4. Strictly upstream energy comparison

At an upstream actual common recorded wait of gain a=p'-1, duration w', least r', define
    e'=(w')²/(2r'), delta'=(a-2w')_+.
Since r'<=p'<=1.5a,
    a <=12e'+2delta'.                             (5)
Proof: let t=w'/a>=0. Then 12e'>=4a t². If t>=1/2 the first term is >=a; otherwise 4a t²+2a(1-2t)=a(1+(2t-1)²)>=a. This is a gain (p'-1) bound, not merely the earlier r bound.

Let E_pre and D_pre sum e' and delta' over DISTINCT actual supporting unordered pair/upstream recorded edges in the allocation (unweighted, includes all selected labels). By (2),(4),(5),
    M_pos,old <=48 sum_(pair,edge in support)(p'-1)
              <=576 E_pre +96 D_pre.              (6)
Can split the allocation according to upstream net drift or selected label relative to target r. These are exact portions of the allocated mass; a separate bound for the small-label moments would be required. Equation (6) transfers every old charge to earlier edges at an absolute constant, not a small coefficient. It does not prove global contraction because the upstream moments can themselves include rough positive targets of other charges. E_pre may contain nonpositive waits too, and is not bounded by E_+^full alone. Do not add this transport to the direct target bound on the same weight. Its merit is the earlier physical support and bounded reuse, not numerical dominance of the RHS.

## 5. Recent-birth packing and sub-top gain coefficient

For a fixed pair all RECENT target starts C satisfy J_*<=C<J_*+r/2. For any cutoff 3<=T<=B, restrict recent targets to r<=T. Their starts are within gain T/2 of J_*. Except the last target in this subset, each outgoing selected gain interval ends no later than the last start, even if other targets or ordinary events intervene. Their total gains <=T/2. Using r<=1.5(p-1) for those except last, and r<=T for last,
    sum_(recent,r<=T) r <= (7/4) T.
By (3) and x<=1,
    M_pos,recent,r<=T <= (7/2)(T/B) F_rec,          (7)
where F_rec sums d_* ONCE per distinct supporting unordered pair with a recent target in the chosen band; it is a subset of recorded birth deficit moment. No r-band or target-count multiplier. For T=B, coefficient <=3.5. For T=B/u^alpha (any fixed alpha>0 with T>=R eventually, e.g. alpha=1/4), coefficient O(u^-alpha) tends to zero. The remaining near-top r>T recent target sector can be retained separately, or use the T=B bound without small coefficient. No claim that F_rec or near-top raw mass is small. If one chooses to pay D<=m first, every remaining recent birth satisfies d_*>m/2; its actual recorded birth deficit is the relevant one, not the true earlier first contact deficit unless independently compared.

Together the new route gives for any T in [R,B]
    M_pos <=576 E_pre+96 D_pre
             +(7T/(2B)) F_rec + M_pos,recent,r>T
(with optional O(XBm) small-deficit payment). The earlier reset/strong/neutral classification remains unchanged. This replaces the positive part of 1ce40c1 by a different upstream support. It is not an unconditional little-o estimate, nor a proof of the original cross linkage or twin infinitude.

## 6. Finite audit

Standalone research/min_clock_positive_target_prefix_audit.mjs. Source commits 0fe2795147fd8ed0a233f53921dcc54aefbb5304 (fixed strips), dfa36ed375419c5102e0a851a43b5787f1ad18d4 (adaptive allocation), final 944ee49b6c30eba58f2702bd0216f583ec9743e8, verified exact final blob bd51a870121940d0958422d3a5f96e1c0709b796. Two intermediate tool scripts had a syntax error (extra closing parenthesis), corrected before successful execution; neither failed attempt committed. Final JS executed in available runtime, not separate Node. Retains previous literal MIN, sampled anchors, exact phase, exit checks. New checks: actual earliest common recorded state by backwards scan and consistency with true first contact, unique pair/target, adaptive h, exact old strip coverage by shared earlier edges, recent inequality and actual per-pair gain packing, interval union bound and integer capacity-two allocation, assigned edge strictly earlier, gain coercivity, exact allocated charge and positive/nonpositive/label partitions. Final density test 24 and total bound 48(12E_pre+2D_pre) passed. Synthetic eight expanding intervals (geometry only, not prime events) have total length32776, union24577, max allocated multiplicity2; verifies nontrivial overlapping allocation. Actual sampled strips happen to have disjoint unions per pair; synthetic test exercises overlap separately. No asymptotic claim from finite checks.

Run:
    node research/min_clock_positive_target_prefix_audit.mjs 4096 16384 65536
12 original modes, three prefix comparisons per mode (fixed eta1/4,eta1/2 and adaptive), same 12 sampled rough origin levels per X, two original occupations, independent LOW L30/y5 and L6/y3. Only X65536 full-positive modes have positive target charge. The adaptive comparisons do not add the fixed-eta transfers; allocation is independent of earlier exit and phase payments. Finite non-top cutoff B/2. Optional small-D absolute payment not executed.

| X65536 LOW | M_pos | adaptive OLD | adaptive RECENT | distinct pair/target OLD/RECENT |
|---|---:|---:|---:|---:|
|L30|1156101.58112|1156101.58112|0|4186/0|
|L6|1496831.75811|1449696.53687|47135.22124|29927/3110|

Largest target C203040,b101862,v102215,r=p277,w353, all 4186 internal pairs (92 donors) OLD. Actual first common recorded deficit 0..140, gain distance702..1532, same earlier anchor d682. Adaptive h=68, total strip length284648; all allocated upstream labels <r/4, positive/nonpositive allocated charge680059.75360/476041.82752. All-strip natural moment270539.03743, selected allocated E_pre197213.36471, D_pre25116. These are unweighted supporting pair/edge energies, not target raw and not full original census. Fixed short strips h5/9 had all positive small-label support; the longer adaptive strip exposes actual nonpositive earlier edges too. Fixed eta1/4 and1/2 both put L6's other two target cohorts in low anchor deficit sector340730.17699. Do not infer all old paths are positive.

L6 adaptive: target C165480,b82794,v82933,r127,w139 raw292931.68142, OLD248155.75221, RECENT44775.92920; target C165420,b82746,v82777,r43,w31 raw47798.49558, OLD45439.20354, RECENT2359.29204. These two cohorts have first recorded birth deficit0..116, gain distances2..1364 /2..1304. Recent 3110 distinct pairs, F_rec294900, all r<=B/2, max observed recent sum r/B=.18731563. No recent top in this sample, not a theorem. All old total strip length494294=union length, max allocated2, allocation positive/nonpositive973654.70935/476041.82752; labels below target r/4 carry1404257.33334 and >=r/4 carry45439.20354. E_pre293103.19626,D_pre25116. Sampled allocation not a numerical contraction at the proved constants. Main and independent prime-root branch unchanged.

## 7. Next

The largest cohort's backward allocation is entirely on smaller selected labels, with substantial actual negative as well as positive earlier drift. Investigate a longer actual shared prefix and classify predecessor strips by scale relative to target r, especially small-label nonpositive shared gain and the source of its earlier high deficit. For recent births, exploit actual birth phase/label and small coefficient T/B in (7); near-top birth sector remains open. Full positive energy, recorded descent, cross-to-donor coefficient chi, recipient reuse and original remaining terminal/other sectors are not closed. No Lean proof or twin infinitude claim.
