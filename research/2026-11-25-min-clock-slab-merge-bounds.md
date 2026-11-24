# Short-clock middle pairs: unconditional deletions, large-incoming mixed mergers and exact mass audit

2026-11-25 JST. Continues the relative-clock slab at 25473614cf384cff0d8af534e34404cd774ae053 and the earlier full-horizon first-meeting ledger at b0b17927de404b5d2a5d0f74cf9c93b4d8b18ddf and 9450ea5e3ebd0909bffb775093330e2d37cd968e. New unconditional bounds for parts of the actual short-clock energy and clock budget; the dominant early shared-state source mass remains OPEN. Paper arguments, not Lean-compiled.

## 1. Setup and exact five-way partition

Retain ALL original odd M in [X,2X), canonical start s=M+2,C0=2M-2, original K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). Write H=4B,a=2B,h=H-a=2B,N=X/2. Assume X sufficiently large that H+2B<=min_M(K(M)-s), as holds eventually. Use actual waits starting before s+H, including the next actual event even if it occurs after s+H. If r(C)>0, that event exists before K, because the wait is <=2r(C)<=2B. If r=0 the state is a twin and we stop. Let ell_M(C) be the integer wait duration intersected with the relative slab [a,H), w_M(C)=ell_M(C)/(2r(C)), U=sum w_M, R=sum rU, E=sum rU^2. Per root the linear slab cost is <=B. The target E=o(XB log^2 B) suffices by the preceding clock certificate and the horizon sieve. All pair sums below are ORDERED, and nonnegative unless stated.

At a common occupied C classify a pair by actual arrivals t,t', next events u,u', selected primes p,p'. If t=t', the states are identical; if u=u' then p=p' (same eligible set and tie rule at that clock). The five disjoint categories are:

    SAME_STATE: t=t';
    MERGE: t!=t', u=u';
    PARALLEL: t!=t', p=p', u!=u', |u-u'|=|t-t'|;
    CHANGE: t!=t', p=p', u!=u', |u-u'|!=|t-t'|;
    DIFFERENT: p!=p'.

Each pair contribution is r w_M w_M'. Common horizons require |M-M'|<=H+3. The near part |M-M'|<=d=floor(4 log B) including diagonal is <=(d+1)R=O(XB log B). Thus this section concerns the remaining middle pairs. The previous unweighted full-horizon five-way partition alone does not give a small bound on the entire short-slab MERGE term.

## 2. NEW uniform removal of fast high events and adjacent LOW blocks

Let Q=ceil(B/sqrt(log B)), z=max(1,floor(sqrt(log B))). Choose the largest even primorial L=2 product_{3<=p<=y}p <=6 sqrt(log B); LOW means p<=y. For sufficiently large B, Q>y. The exact canonical invariant C<=2t and monotone C give the sum of selected gains p-1 over the prefix of events whose waits start before s+H at most 2H+B+6 (the last event may extend beyond H, but its gain <=B-1). Thus the count n_Q of selected p>=Q per root is at most (2H+B+6)/(Q-1)=O(sqrt(log B)).

Remove the following original-tag incidences, WITHOUT rerunning the dynamics:
- selected p>=Q whose clipped slab duration ell<=2z (includes all such r<=z);
- maximal contiguous LOW-only blocks at the beginning/end of the prefix, or immediately adjacent to a selected p>=Q.

For a LOW-only block the gain is <L: no LOW event can cross an even multiple of L, and all LOW primes are inactive at that multiple. Its total r cost is <=3L/2 by r<=p<=3(p-1)/2. The number of selected LOW blocks is at most 2n_Q+2. The removed linear cost per root is at most

    z n_Q + (3/2)L(2n_Q+2) = O(log B).

Hence R_del=O(X log B). At a fixed horizon all possible roots lie in an interval of length H+3, so U<=m_H=floor((H+3)/2)+1. If U_del is the deleted occupation, exactly

    E-E_kept = sum_C r (2 U U_del-U_del^2)
               <=2m_H R_del=O(XB log B)=o(XB log^2 B).   (1)

This is an unconditional removal at the required ENERGY scale, including all source weights after arbitrary mergers. More generally Q=B/log^b B up to rounding and z,L=O(log^c B) work for fixed b,c>0 with b+c<2. The remaining LOW blocks between medium events are not bounded by this argument.

## 3. NEW partial merger and lag deletions

Let Z=floor(log^(3/2) B). Each pair can occur in MERGE at most once: it has its first common physical state at the next vertex, and its forward choices thereafter agree whenever both still run. If one clipped wait <=2Z, then

    r w_M w_M' <= min(ell_M,ell_M')/2 <= Z.

There are O(XB) supported ordered distinct pairs, so the entire short-wait MERGE part is O(XB Z)=o(XB log^2 B). Long-wait MERGE is still open. Likewise, for SAME_STATE pairs whose FIRST physical meeting occurs at relative time >=H-2Z for the earlier root (smaller M), the earlier root has at most 2Z slab ticks left after the meeting. Its total fractional cost on that common suffix is <=Z, and multiplication by the other weights <=1 does not increase it. All such late-first-meeting common suffix energy is O(XB Z). This does not remove early first meetings that still have long common suffixes.

For the same-label lag rounding, if two common-horizon states choose p and have positive lag k, their next lag is either 2p floor(k/(2p)) or 2p ceil(k/(2p)). This is exact periodic-clock arithmetic and |k'-k|<=2r-1. In particular, a positive OUTPUT lag <=2y requires p<=y.

For each MERGE pair, examine the contiguous matching-horizon suffix immediately BEFORE the final merger step, going backwards while the output lag is positive and <=2y and the two predecessor horizons agree. Every step in this suffix has a shared selected label p<=y, since its positive output lag is a multiple of 2p. Its gain is <L by the LOW barrier, and its weighted pair cost is <=3L/2, even if it begins outside the slab. Each pair has at most one such pre-first-meeting suffix. Its total contribution over supported pairs is O(XB L)=o(XB log^2 B). The final merger event is not part of this bound. A constant positive lag run also has gain below 2 times the product of its distinct selected labels, which divides the lag, as in the earlier full-horizon note; this is not a bound on the number of runs.

The bounds in this section may overlap (1); use a union upper bound, not subtraction as though disjoint.

## 4. NEW short deficit strip: ALL large-incoming distinct-label mergers

A post-event physical vertex (t,C) in the short prefix has delta=2t-C in [0,2(H+2B)+6], since its root s=M+2 and C>=2M-2. Put epsilon=0 at even t, 6 at odd t. Incoming selected p satisfies p|t,C on the even side, p|(t-2),(C+2) on the odd side. Distinct incoming p,q thus satisfy

    2 p q | (delta-epsilon).

For a NONRESET vertex (delta!=epsilon) with at least one large incoming prime p>=Q, necessarily pq=O(B), hence q=O(B/Q). For fixed p,q the number of possible nonzero deficits is O(B/(pq)); for each deficit the t range has O(X/(pq)) possible t, since t or t-2 is divisible by pq. Each t determines C. Therefore the total number of (vertex,distinct unordered incoming label pair) instances with at least one p>=Q off the reset line is

    O(X B sum_{p>=Q}1/p^2 sum_{q>=3}1/q^2)
      = O(X B/(Q log Q)).                               (2)

For RESET vertices delta=epsilon, each fixed pair has O(1+X/(pq)) possible t. Counting both parities and allowing overcount yields

    O(X (sum_{Q<=p<=B}1/p)(sum_{q<=B}1/q) + pi(B)^2)
      = O(X (loglog B)^2/log B + X/log^2 B).             (3)

All sums are over primes (except that using integer sums for the convergent q square sum is also valid). The prime counting estimates use Chebyshev and partial summation; for the narrow large band, split dyadically, giving sum_{Q<=p<=B}1/p=O((1+log(B/Q))/log Q). For Q=B/sqrt(log B), (2) is O(X/sqrt(log B)) and (2)+(3)=o(X).

In the original-source maximal-M representative ledger on the truncated prefix, first retain one maximal-M representative per incoming label after combining predecessor-time classes (SAME demotions), then combine distinct labels (MIXED demotions), then a possible injected root (ROOT demotion). The monotonicity of both original cutoff K(M) and relative horizon cutoff s+H ensures the representative survives whenever any smaller tag continues. Include the last actual post-event vertex even when it is beyond the slab. At a vertex with k>=2 distinct incoming labels and at least one large label, there are at least k-1 large-involving label pairs. Thus at most the count (2)+(3) of representative tags can be demoted by the distinct-label combination at such vertices, including when the other labels are small. Each original tag's entire slab cost is <=B. Consequently the sum of their POST-demotion costs is

    R_mixed,large = o(XB).                               (4)

The same is true of ROOT demotions at vertices with at least one incoming large label: a root (M+2,2M-2) on the odd reset line implies p|M, so the count is <=sum_{Q<=p<=B} O(X/p+1)=o(X); each tag costs <=B. This counts the old maximal representative even if its own incoming label was small. These removals are disjoint ledger categories. Unlike the previous full-horizon BIG estimate, (4) covers every distinct-label merger involving at least one large label, not only large-large.

This is a LINEAR clock-budget removal, not an unconditional negligible ENERGY removal. Under a no-twin window R=NB=XB/2, so one may remove these o(XB) tag costs and apply Cauchy to the remaining occupation, still with the same leading lower bound. One must not multiply the sparse vertex count by an assumed uniform ancestor weight. SAME demotions (even with a large incoming label) and previously demoted tags' continuing suffix costs are not bounded by (4).

## 5. NEW label-group-surviving high representative events

An event carrying the representative from its predecessor is called a label-group winner at the target if it survives the SAME combination there, regardless of later MIXED or ROOT demotion at that vertex. For each possible target (t,C) and selected p there is at most one such winner. Write D=C-p+1 for the pre-horizon. Fix p and divisibility side. As in 9450ea5, the sum of r(D) over eligible D in the full horizon window is O(X/log^2 p): split at p^(1/4), use the elementary contribution O(X p^(1/4)/p), and for the rough part use the uniform two-dimensional upper-bound sieve for h and ph+-2 where D+-1=ph, multiplying the count O(X/(p log^2 p)) by r<=p. The interval length X/p is at least a constant times p, sufficient for the stated sieve error.

For fixed D,p the target deficit strip of section 4 confines t to an interval of length O(B), and the eligible clock has period 2p. Thus there are O(1+B/p)=O(B/p) candidate event times. The sum of r-cost, and hence of fractional slab costs, of all label-group winners with p>=Y is

    O(X B sum_{p>=Y}1/(p log^2 p)) = O(XB/log^2 Y).       (5)

For any growing Y<=B this is o(XB). This improves the full-horizon representative bound at the short scale; it does not need an O(XB) term for demotions into a target, because SAME losers are explicitly kept separate. Each event entering a SAME demotion whose selected p<Y costs <=Y; there are at most N such events, hence O(XY)=o(XB) if Y=o(B). Still unbounded are the group-winning LOW events and the entering events of SAME demotions with p>=Y, as well as post-demotion suffix costs (unless separately removed by (4) or other valid bounds). All these are linear-budget statements, not the full energy bound.

## 6. Finite audits and actual dominant terms

Two standalone ECMAScript files; exact remote readback verified:
- research/min_clock_slab_pair_audit.mjs at d426b8615ff1139ae3191c692f2a20cbe1616ed2, blob 008dbc73acc50f9a41c567194e6de106a7521af7.
- research/min_clock_slab_merge_ledger.mjs at 43f921168e22f1eedaec0b173dbf78bb58b08d84, blob ebff4a95c2ab263e7eded59994839b13c1844f4a.

Run each using node with arguments 1024 4096 16384 65536 262144. Actual JS audit functions executed in available JS runtime, not separate local Node runs. Prefix cutoff gate excludes X256. First script computes weighted pair categories by horizon, with a source-index sliding aggregate for |M-M'|>d and maps keyed by arrival time, next time, prime and (prime,unclipped wait); checks partition, (1), short-wait MERGE bound. Explicit pair oracle at X1024 and X4096 checks five categories and lag identities, and backtracks first physical meeting and bounded-lag premerge suffix. Diagnostic [0,4B),d=0 at X1024/4096 exercises 2266/15154 unordered MERGE pairs, bounded-lag premerge ordered weights 170/1143.67; late-first-meeting shared weight zero (not a nonvacuous test of that class). Literal parity-GCD comparisons 4658 per X1024 mode. Floating point energy checks use tolerances. Ledger uses exact half-integer slab costs, verifies all representative/demotion accounts, high-label pair divisibility, count domination and tag costs; diagnostic threshold Q=11 exercises nonreset instances.

Normal slab [2B,4B), d=floor(4 log B), weighted ordered middle pair results rounded:

| X | SAME_STATE | MERGE | PARALLEL | CHANGE | DIFFERENT |
|--:|--:|--:|--:|--:|--:|
|1024|46|0|36|0|0|
|4096|168379|0|5611|26234|8488|
|16384|1270707|0|4579|25093|5291|
|65536|15789961|79900|534|107615|3245|
|262144|161224810|1143863|33698|1227343|35148|

At X262144 B1355, Q505,y3,L6,z2 (fast threshold z=2, merger threshold Z=19), 3941922 prefix events, 138829 slab incidences. E=184229117.19, middle=163664861.47, SAME_STATE=161224809.74 (98.51% of middle), R=2373997.5. Fast/LOW removal linear costs 229.5 and 11900, E_kept=182840348.32, middle_kept=162409236.79. Short-wait MERGE ordered weight 518.69. Thus the unconditional energy deletions do not account for the dominant finite mass.

Ledger at X262144: 466351 physical vertices, R_rep=29759, R_same=1501338 (74456 demotions), R_mixed=184795.5 (9934), R_root=658105 (35065). These are actual source-tag suffix costs, not pair energy. At Q505, 421 large-involving label pairs (all reset), 376 vertices, 421 distinct-label demotions with suffix cost 17896; 525 large-incoming ROOT demotions cost 15050.5. At diagnostic Q11, 9721 pairs including 7 nonreset, 9012 mixed demotions cost 164695. For Y=ceil(log^2 B)=53, representative high entering cost 24207 splits into label-group winners 22873.5 and SAME losers 1333.5; 16912 group-winner events. All counts preserve original source tags and cutoffs. No statistical extrapolation; the late slab has only 279 roots surviving to H at this scale, so finite trajectories are already mostly terminated.

## 7. Next task

The actual middle-energy audit changes the practical emphasis: in the earlier full-horizon far-pair data asynchronous CHANGE was prominent, but in the short late slab SAME_STATE dominates. For an ordered middle pair, its shared-state energy is exactly the common suffix occupation product after its first physical meeting, with each root's own relative-time slab. The open part is early first-meeting original-source mass, particularly SAME and ROOT at small/medium labels, and the amount of their common suffix still in the slab. The new high-mixed/reset and group-winner bounds remove o(XB) linear budget; the fast/LOW and small merger-tail bounds remove o(XB log^2 B) energy. Neither proves the remaining middle estimate. Next target actual weighted first-meeting products rather than counting more rare vertices alone; use cutoff-tagged reverse ancestry and distinguish early merging from rare late first meetings. Main untouched, no Lean proof, twin-prime conjecture OPEN.
