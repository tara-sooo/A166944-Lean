# Complete thick-segment covers, hysteresis excursions and tail-weighted deficit transport

2026-11-25 JST. Continuation of 9ce7d27b168663311ad931850e3a341ab21b79ef on the selected prime-root branch. Strengthen the preceding representative state cover to a simultaneous cover of every actual physical segment with at least K traversing original roots. Apply it to canonical large-deficit up/down excursions, obtaining absolute pair budgets and a sparse exceptional younger-root set without assuming independent arithmetic labels. Derive a separate exact tail-weighted deficit transport identity for all natural synchronous high pairs, with additive dyadic deficit bands. The new finite near-endpoint mask pays no additional positive residual in the tested configurations. The new transport identities are nontrivially verified on the full original histories. Neither supplies a general little-o estimate for the inherited tail weights; no Lean compilation or twin-prime proof.

## 1. Ensemble and complete segment cover

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime starts M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, m_g=u^(19/4)/ell^4. The original gain-stopped MIN paths, including actual terminal recorded vertices, are unchanged. Completed gains p-1<=B and waits W<=2r<=3(p-1); total original gain <H. Deficit d=2t-C is nonnegative, starts at 6 and changes by 2W-(p-1) on a completed edge. Thus positive deficit variation along a path is at most 5G_M and negative variation at most G_M. At a shared physical vertex, every larger source follows all subsequent recorded vertices of a smaller source until its actual stop, because its gain threshold and absolute time cutoff are no earlier. All source sets in this note are full actual original source sets unless explicitly called an unpaid ledger.

A physical segment is a directed interval from one actual recorded vertex v to a later actual recorded vertex w along the common deterministic continuation (a singleton is allowed). Its traversing cohort consists of the original sources visiting v and reaching w on that continuation. It is a largest-source suffix of the original visiting fibre A_v. Fix integer K>=1. For each v with |A_v|>=K, let k_v be its Kth largest source. We claim there exists a single set of at most floor(N/K) original representative paths such that EVERY segment with at least K actual traversers is contained in one of these representative paths, including both endpoints and all intermediate completed edges.

Process actual physical vertices in increasing horizon C, breaking ties by time. Mark each covered vertex with the largest representative source whose marked original suffix reaches it. If at v with |A_v|>=K this maximum is absent or smaller than k_v, select the largest source of A_v as a new representative and mark its actual suffix starting at v. Use the K largest members of A_v as its seed population. These K-element seed populations are pairwise disjoint: if a tag occurs in an earlier seed and a new seed, it visits the earlier seed vertex before the new one. The earlier representative was at least as large as that tag, and therefore reaches the new vertex by ordered persistence. Its source is at least k_v, contradicting the selection criterion. The same source cannot be selected twice. Hence at most floor(N/K) representatives are selected, with total original suffix gain <=NH/K.

For any segment with >=K actual traversers starting at v, k_v itself traverses it by suffix ordering. Some representative of source >=k_v reaches v on its marked suffix, so it traverses the entire segment as well. Unlike the preceding state cover, this stronger cover guarantees that a completed edge with >=K continuing tags is actually traversed by a representative, with no terminal-edge exception. It does NOT remove the terminal exception for a prevertex with >=K visiting tags but fewer than K continuing tags. The cover simultaneously handles arbitrary collections of complete thick segments, even with many different thresholds/predicates on the intervening states. It does not bound an individual fibre's mass by K.

## 2. Canonical two-level deficit excursions and their weighted counting bounds

For D>6, call a recorded state low when d<=D and high when d>=2D. Ignore intermediate states for switching between low and high. On an original path, start in low at its root. At every switch from low to high, record the segment from the LAST low recorded state before the switch to the FIRST high state of the switch. At every high-to-low switch, record analogously from the last high to the first low. These are the canonical up and down excursions at threshold D. Their interiors contain no low or high recorded vertex, by construction. A segment's canonical status depends only on its endpoints and interior; every original path traversing that segment has the same canonical excursion. Incomplete terminal excursions that never reach the opposite band are not counted.

For fixed D, excursions on a given original path have disjoint edge interiors (endpoints may coincide). Each upward excursion has net increase >=D and gain >=D/5; each downward excursion has net decrease >=D and gain >=D. It follows that
    D * #up_M(D) <=5G_M,
    D * #down_M(D) <=G_M,
    sum_(excursions on M at D) gain <=G_M.             (1)
These inequalities also hold after summing over actual source memberships. For a distinct physical excursion segment s let a_s be its number of actual original traversers. Then
    sum_(up s) a_s <=5NH/D,
    sum_(down s) a_s <=NH/D,
    sum_s a_s gain(s)<=NH.
By the complete segment cover, all canonical excursions with a_s>=K appear among at most N/K actual representative paths. Consequently
    #distinct up segments with a_s>=K <=5NH/(KD),
    #distinct down segments with a_s>=K <=NH/(KD).      (2)
The same representative set can be used at all D. For the actual number of endpoints, use the number of segments as an upper bound. Equations (1)-(2) retain actual multiplicities, not a bound on relaxed reverse paths. They do not bound sum a_s² by a small order; old very thick segments can still occur.

## 3. Summable whole-pair near-endpoint payment (high) and rare thick-excursion support

Use dyadic D_j=2^j D_0, D_0=ceil(B/u^.5) (min8), up to 5H+6; j starts at zero. For an unordered original pair M<M' sharing any projected horizon, write C0'=2M'-2 and Dland for the actual older landing at the cut x=C0'-1 of c6bf00ef. Do not confuse Dland with the deficit level D_j. Use the previous whole-pair high bound U_H=3H, valid on arbitrary nonnegative retained pair subsets and feasible fractional payments.

Pay the entire remaining high pair weight if the older original path, at or before its landing Dland, has ANY complete canonical up or down excursion at D_j with end horizon C_e satisfying
    |C_e-C0'|<=2W_j,
    W_j=floor((D_j/B)u^1.5/(j+1)^2).
For each fixed excursion occurrence on a fixed older path, at most 2W_j+1 younger integer roots can qualify (prime count could only improve this). By (1) the total high payment over all levels is
    O(U_H N H sum_j (W_j+1)/D_j)
    = O(U_H N H (u^1.5/B + 1/D_0))
    = O(F/u^.5).
Here N=O(B²/u), H~T, and the squared-index weights and inverse dyadic scales are summable. The mask applies to all actual pair contacts, not just physical mergers or thick fibres. It is a whole-pair absolute bound without a gate recomputation. It does not bound all long excursions or all pairs landing inside an excursion. The width is on the initial horizon of the younger root, not on its first contact horizon. For medium at these parameters the same argument does not yield the required small cost, so no analogous medium payment is made.

There is also a different linear support result that exploits (2). Put K=floor(Bu^(9/8)) (min1), and W'_j=floor((D_j/B)u/(j+1)^2). Let R be the set of original prime roots whose initial horizon lies within 2W'_j of the endpoint of ANY canonical excursion at D_j with >=K actual traversers. The excursion can be on any original path; there is no requirement that the root itself belongs to the excursion cohort. Then
    |R| <= O((NH/K) sum_j (W'_j+1)/D_j)
         = O(NH/K * (u/B+1/D_0))
         = O(N/u^(3/8)) = o(N).                       (3)
This upper bound uses only integer root counts; no prime-progression independence. The first term H u/(K B)=O(u^(-3/8)) and the rounding term H/(K D_0)=O(u^(-7/8)). Thus the entire original high incidence history of these exceptional roots may be discarded at linear proxy/clock cost o(NT), with the final density gate applied to the resulting ensemble as in earlier notes. This is NOT a bound of o(F) on their removed quadratic products. For actual medium it pays only the exceptional focal roots' own charges, not other focal directions. No such linear deletion is applied in this finite audit. In particular the finite count of roots in R is not presumed asymptotically small at the diagnostic sizes.

For any high survivor after the absolute mask, no complete canonical excursion endpoint on its actual older prefix through Dland can lie within the corresponding window of its younger initial horizon. After the optional high linear deletion, no remaining younger root can lie near a complete excursion with >=K actual traversers at the smaller width. This supplies a restriction on the location of large-amplitude changes in an inherited group, without merely capping its size. It still permits a thick high-deficit path segment that has no such endpoint near the younger origin.

## 4. Exact physical deficit flux at actual pair births and exits

For the full original physical DAG let n_v count all visiting original tags, b_v those continuing on a completed edge. Write P(n)=choose(n,2). Physical first-meeting pair count at v is
    B_v=P(n_v)-sum_(w->v) P(b_w),
and pair exit count (smaller source stops at v) is L_v=P(n_v)-P(b_v). Both nonnegative. For any function f on nonnegative deficits, summing over actual completed edges gives the signed identity
    sum_v B_v f(d_v) + sum_(v->w) P(b_v) [f(d_w)-f(d_v)]_+
      = sum_v L_v f(d_v) + sum_(v->w) P(b_v) [f(d_v)-f(d_w)]_+.
This is the exact birth/transport/exit telescoping on original unordered physically synchronized pairs, even if a pair's earlier projected contact was much earlier. Replace P by the threshold excess (n-m)_+ to obtain the same identity for actual source tags after first PHYSICAL descending-rank attainment >m, with the birth and loss definitions in 9ce7d27. Neither identity needs monotonic deficit. For f=min(d,D) it retains just the clipped variation up to D. No claim of smallness of the right side or of natural high occupation from the unweighted flux alone.

## 5. Tail-weighted deficit transport: an upper bound on actual synchronous high occupation

The key additional identity weights deficit increments by FUTURE high tail, not merely by current visiting mass. For original source M let h_M(v) be the natural high weight r(C) at its completed high event (p>=Q, r>p/sqrt(log p)), zero otherwise including terminal. Write R_M(v)=sum of these h over its original suffix starting at v. At a recorded vertex on source M define n_M(v)=1+# larger original source tags at v, and
    a_M(v)=n_M(v)-n_M(prev(v)),
with a=0 at the singleton prime root. This is exactly the number of larger sources having their FIRST common recorded physical vertex with M at v, because original larger companions persist and no earlier common vertex can be followed by separation before M stops. A smaller source's entire physical suffix after first meeting is shared by the larger source. These facts justify using its own natural tail for every such natural synchronous pair.

For a nonnegative function f of deficit define ordered (twice unordered) quantities
    B_f = 2 sum_(M,v) a_M(v) f(d_v) R_M(v),
    U_f = 2 sum_(M,v->w) (n_M(v)-1)
                            [f(d_w)-f(d_v)]_+ R_M(w),
    D_f = 2 sum_(M,v->w) (n_M(v)-1)
                            [f(d_v)-f(d_w)]_+ R_M(w),
    Z_f = 2 sum_(M,v) (n_M(v)-1) f(d_v) h_M(v).
Then
    Z_f = B_f + U_f - D_f.                            (4)
Indeed on each smaller-source shared suffix beginning at its actual pair birth b,
    f(d_v)R_M(v)-f(d_w)R_M(w)
       = f(d_v)h_M(v) - (f(d_w)-f(d_v)) R_M(w).
Telescoping, with terminal natural tail zero, gives (4) for that pair. Summing births and shared edges using their exact multiplicities gives the displayed formulas, without enumerating pairs. This is also valid for arbitrary pair-specific nonnegative frozen weights on their actual shared physical hits if R is replaced by that pair's own remaining tail and sums are kept pair-specific. For arbitrary retained masks or unpaid fractions, one must not factor them using the FULL n_M and a single-source tail as if equality still held. The full natural nonnegative upper bound B_f+U_f remains available. The identity applies to synchronous physical recorded-event energy, not asynchronous projected hits or medium charges with no physical meeting.

For a deficit band D_j..2D_j take f_j(d)=min(D_j,max(0,d-D_j)). Let E_sync,>=2D_j be the full ordered natural offdiagonal synchronous high energy at physical recorded hits with d>=2D_j. Then
    D_j E_sync,>=2D_j <= Z_(f_j) <= B_(f_j)+U_(f_j).    (5)
In particular a sufficient estimate for this high-deficit sector of size o(F) is B_(f_j)+U_(f_j)=o(D_j F). For the residual synchronous sector the same pair-specific identity can be used with its actual frozen weights. Equation (5) identifies two terms: the high-deficit value already present at actual first meeting, multiplied by its later high tail; and positive band drift on the shared suffix, multiplied by the remaining high tail at the target. Negative band drift reduces the exact moment and is not treated as a new payment. The source-cover count (2) alone does not bound either weighted term, since it gives no upper bound on old mass or remaining tail at a segment.

For the consecutive dyadic bands from D_0 through all possible deficits, sum_j f_j(d)=(d-D_0)_+ exactly. Because each f_j is nondecreasing, all band increments on a fixed edge have the same sign as the edge's deficit change. Consequently B,U,D,Z separately sum to their respective values for f(d)=(d-D_0)_+, with no logarithmic overlap in this additive partition. This avoids counting a single large increase once in full in every threshold band. Dividing by different D_j in (5) is a different operation; no uniform logarithm-free bound for a sum of those normalized inequalities is asserted. The total natural synchronous energy itself is the f=1 case, and it includes both before-first-common-reset and after-common-reset sectors of 9c62b7. Diagonal and async energy are not included.

This gives a genuine exact weighted reduction of the high-deficit synchronous occupation to birth and future-tail-weighted drift. It is not a proof that the positive weighted drift is negligible, and neither the unweighted excursion count nor the representative cover justifies dropping the multiplicities in (4).

## 6. Verification and finite results

Standalone research/min_prime_root_excursion_cover_audit.mjs, final source commit 276fe89fb4d6b910ab8285a0e1e139306ecfb560, blob ce1a0a30f818ff5b750adb955d6f887aedbc79be, exact remote readback.
    node research/min_prime_root_excursion_cover_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_excursion_cover_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress --grid-stress --star-stress --prefix-stress --reset-stress --threshold-stress --cover-stress --excursion-stress 256 1024 4096 16384 65536 262144
Actual audit function executed in available ECMAScript runtime, not separate Node process. Initial8 successful runs (analytic/concurrent X256..16384), then6 larger runs (three configurations at X65536,262144); final18 successful runs (analytic/concurrent/combined sixteen stress flags across all six X), after adding the tail-weighted identities. Other final modes not rerun. Previous canonical and accounting assertions retained. Complete segment cover is constructed independently at thresholds2,8 and chosen K, verifying disjoint exact K-element seed sets, maximum source dominance at every thick state and membership of the representative in EVERY complete thick excursion cohort (all levels, both directions), plus independent original endpoint lookup. Canonical excursions and per-source disjoint gain budgets checked. Exact integer pair and rank-weighted clipped deficit flux checked on the full physical graph. Tail-weighted identities, independent dyadic partition at every original vertex, and full separate actual pair/shared-suffix enumeration at X<=16384 checked. Counts and reported natural energy moments are exact integer computations at tested sizes. Fractional unpaid payments and maximum flows use tolerances. No Lean compilation.

Finite nonanalytic configurations use inherited T=4B and diagnostic masks, rather than analytic T=floor(X/u^.25). Normal K=3, D_0=max(8,ceil(B/16)), W_j=max(1,floor(B/(32(j+1)))), rare W'_j=max(1,floor(B/(64(j+1)))); stress K=4,D_0=max(8,ceil(B/32)), widths B/(8(j+1)) and B/(16(j+1)). Analytic uses the stated asymptotic settings; previous analytic residuals empty and chosen asymptotic K exceeds actual fibre max at tested X, hence the independent K=2/8 covers exercise nonempty controls. Rare root support only measured, not removed. The high residual is the inherited isolated natural high diagnostic, NOT the full cumulative hybrid. The new near-endpoint mask has NO additional positive unpaid payments in any tested configuration. Thus X65536 normal high remains zero to floating precision, MED1.272782249835; X262144 normal high remains57314.68775612349, MED0 to floating precision, never/async0. Combined stress prior both zero stays zero. The new results concern structural bounds and exact full-natural moments, not a numerical residual reduction.

Largest normal X262144: N20390, maximum deficit6110. Nine tested levels85,170,340,680,1360,2720,5440,10880,21760. 11645 distinct complete canonical excursion segments over these levels, counted with their level and direction. K3 simultaneous complete segment cover selects3853 reps,11559 disjoint seed tags, suffix gain3596006;55166 thick vertex dominance checks. 3251 complete thick segments, 2727 up and524 down, all representative memberships and endpoints verified. At K2:6996 reps/13992 seed tags/83427 thick states/5265 thick segments (4549 up,716 down); K8:906/7248/19086/977 (781 up,196 down). These complete segment covers are different from the smaller state-only cover of 9ce7d27. At level85 all distinct up/down4896/688, actual source occurrences12997/3583; K3 thick distinct1121/345, representative occurrences2815/785. At170:3155/268 distinct,8869/1588 tags,K3 thick818/137. At340:1779/77 distinct,5392/451 tags,K3 thick512/42. At680 K3 thick225 up/0 down; at1360 50/0; at2720 1/0. Rare-root diagnostic set4594 roots,7145 nearby incidences; includes26 of133 positive unpaid pairs with aggregate11549.198529 high weight, NOT paid or subtracted. No near-endpoint absolute mask matches positive high unpaid weights. This distinction matters because R can be induced by a different original path from the older pair source.

Full natural ordinary pair-weighted deficit flux at X262144:
    birth31598112 + upward76365724 = exit79848974 + downward28114862.
Full tail-weighted deficit transport (4) at the same size:
    birth27528174672 + upward72958636356
       = moment72541596736 + downward27945214292.
Natural ordered synchronous high energy116767336,126505 distinct physical first-meeting pairs.633075 original recorded vertex checks of the exact dyadic band partition. For f=(d-85)_+, B=23013191902,U=63279252010,D=20958004622,Z=65334439290, exactly the sum of the nine band quantities. For f_85, B=3145718678,U=6139294410,D=3484429142,Z=5800583946; actual sync high energy with d>=170 is64674252, times85 is <=Z. For f_170, B=5126774544,U=9438111104,D=4711970360,Z=9852915288; actual energy with d>=340 is53442924, times170<=Z. All these quantities refer to the full natural histories, not the 57314.687756 residual; units include deficit times energy in the tail-weighted moments. At X16384 normal the separate explicit pair oracle verifies5309 distinct first-meeting pairs and55 numerical band/moment comparisons. Analytic X262144 full natural sync120546712,126660 first physical pairs, tail birth28419150568/up80762102608/down30728724552/moment78452528624. K2 analytic cover6996 reps/746 segments,K8 906/167, chosen K12508 empty. No finite zero or numerical trend is used as an asymptotic theorem.

## 7. Remaining proof target

The complete-segment cover strengthens the earlier representative-state count and handles both upward and downward shared excursions simultaneously. The near-origin large-deficit endpoint estimates are unconditional absolute/linear bounds for their specified classes. The exact tail-weighted identity reduces the high-deficit synchronous sector to actual birth-tail and shared positive-drift-tail terms, with additive nonoverlapping bands. The main remaining task is to bound these actual terms (on the retained pair weights, not just all natural candidate states) or to use the earlier rank, age and source-cell constraints to control them. In particular very old thick excursions and low-deficit sectors can remain, and the asynchronous and actual medium estimates are separate. The two joint little-o targets on a common unbounded dyadic sequence remain OPEN; no proof of twin-prime infinitude. Main and independent branches unchanged.
