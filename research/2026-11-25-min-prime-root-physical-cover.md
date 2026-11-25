# Physical threshold formation, representative covers and bounded-deficit nonreset runs

2026-11-25 JST. Continuation of 59b9bc56627b48bd1be51d2f8fd09a7694a47f0c. Extend the reset formation potential to every actual recorded physical vertex, including nonreset vertices and terminal snapshots. A greedy largest-source representative cover controls the number of deterministic paths needed to cover large physical fibres, and their large selected edges, allowing for terminal exceptions. An arithmetic count of low-deficit landing slots at younger prime starts permits a whole-pair thin-rank exclusion for shallow physical births. Together with the full physical branching exclusion, this gives a nonvacuous thick-ancestry restriction even when the reset strip contains no reset. A primorial barrier bounds the gain of a consecutive bounded-deficit nonreset run. No general o(F) or o(NT) residual estimate, no Lean compilation.

## 1. Original ensemble and all-physical formation potential

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime starts M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, m_g=u^(19/4)/ell^4. Each original path has completed gains p-1, positive waits <=2r<=3(p-1), total gain <H, includes actual terminal snapshot. Original prime injection is a singleton physical fibre; an arriving selected q would have to divide 2M at odd time, impossible. The deterministic stop order proved in 9c62b7 ensures every larger source at a common physical vertex continues through every subsequent recorded vertex of the smaller source up to its own stop. No artificial extension.

Build the DAG of ALL physical recorded vertices v=(C,t), with A_v its full original source set, n_v=|A_v|, B_v the subset continuing on a completed edge, b_v=|B_v|. The continuation set is the largest-source suffix of A_v and has a unique successor if nonempty. Original terminal snapshots can coexist with continuing tags at the same vertex. At each v the incoming continuation cohorts partition A_v apart from singleton injection. Define f_m(n)=(n-m)_+ for integer m>=1 and
    Delta_m(v)=f_m(n_v)-sum_(w->v) f_m(b_w),
    Loss_m(v)=f_m(n_v)-f_m(b_v).
The proof of 59b9bc5 applies word for word to the actual physical graph, rather than the compressed reset graph:
    sum_v Delta_m(v)=sum_v Loss_m(v)<=N.
More strongly Delta_m(v) equals the number of source tags FIRST attaining descending larger-companion rank >m at this PHYSICAL vertex. Loss_m(v) counts exiting tags with such rank at their actual terminal vertex. Each is counted once. This holds on nonreset vertices, not just first reset attainment.

At n_v>=2m classify type A (no incoming cohort with size>=m), B (at least two such cohorts), C (exactly one). If k thick incoming cohorts and k>=1 then Delta=(k-1)m+sum small incoming masses. For A, Delta=n_v-m>=n_v/2>=m. Thus
    #A + sum_B(k-1)<=N/m,
    sum_A n_v<=2N,
    sum_(n_v>=2m) sum_(incoming size<m) size <=2N.       (1)
These are upper bounds for actual full physical formation states and inflow tag counts, independent of the number or length of reset-free intervals.

## 2. A representative cover of all thick physical states

For integer K>=1 scan all original physical vertices in increasing C, breaking ties by t. Whenever an as yet uncovered vertex has n_v>=K, select its largest source M_v and mark every original recorded vertex on that source's suffix from v to its terminal snapshot. Call A_v the seed population. The seed populations of different selections are disjoint. Indeed if a source from an earlier seed population visits the new v, it does so after its earlier seed state (strictly increasing C; no two vertices on one path at the same C). The earlier representative, being the largest source in that earlier population, also visits v by deterministic persistence, so v would have been marked. This contradiction applies even if an earlier representative has already reached its stop. Consequently the number of representative paths is <=floor(N/K), and every physical vertex with n_v>=K is covered.

For any selected label threshold P>1, let J(K,P) be the set of distinct physical prevertices with n_v>=K and some actually completed outgoing edge of label p>=P. On each representative path there are <=H/(P-1) such completed edges by gain. There is a subtle terminal exception: if a covering representative stops at a vertex and another, larger tag continues, the representative's suffix covers that state but not the outgoing edge. Every such exceptional state is a representative terminal, hence at most one per representative. Therefore
    |J(K,P)| <= (N/K)(H/(P-1)+1).                     (2)
No claim that every representative traverses all covered edges. Alternatively cover only edges with >=K continuing tags by the same greedy algorithm on the continuing cohorts, which has no terminal exception. Equation (2) covers the larger class using full fibre size. The cover is on actual physical states, not projected horizons; it does not require reset events or impose an upper bound on the size of individual old fibres. The selected representatives are original paths, not virtual continuations.

A general consequence: any predicate on physical prevertices with at most D qualifying completed events on each original path, plus terminal states if needed, has <=(N/K)(D+1) qualifying distinct heavy prevertices. This is useful for counting rare events on large inherited groups even without arithmetic independence.

For example let S=floor(u^.25) (min1), K=floor(Bu^(9/8)) (min1), P=ceil(B/u). The original younger prime roots whose initial horizon C0 lies within 2S of any prevertex in J(K,P) number at most
    (2S+1)|J(K,P)| = O(N u^(-1/8))=o(N),             (3)
since H=O(B²/u^.25). This holds even counting possible younger integer roots before prime restriction. This particular example can also be bounded by an arithmetic upper sieve on the outgoing label; the advantage of the representative cover is its general actual path predicate version. If desired the exceptional roots can be removed at linear high proxy cost O(H * o(N))=o(NT), before the final density gate or with it reapplied. It is NOT an absolute quadratic payment; medium only permits removing charges with exceptional focal source. The finite audit measures the set, not a rare-root deletion.

## 3. Low-deficit physical landing slots at younger prime starts

For every M<M' with first projected contact, use the older crossing landing v=(D,t) of x=2M'-3. Put C0=2M'-2, i=(D-C0)/2 and d=2t-D. Then 0<=i, 2i<=p-2 for its actual incoming p<=B. If first common recorded physical vertex is J=C0+2g, g>=i, the earlier cone of 9bb7547 gives d<=6+12g-2i. In particular shallow physical birth g<=S implies
    0<=i<=S, 0<=d<=6+12S.
Use this necessary arithmetic class without requiring a later meeting. Put s=t mod2. The necessary incoming conditions are
    p|(M'+i-1+s), d=6s mod 2p.
All physical slots have even D and d, and the parity of (D+d)/2 must be s. There are at most two genuine reset keys per offset i. For nonreset keys p>=5 implies d>=2p, so p=O(S); p=3 is included separately, including the exceptional odd low phase d=0. Each p and side gives at most O(1+S/p) deficit values. For a fixed p and i, Brun--Titchmarsh as used in c6bf00ef bounds possible younger prime M' by O(N/p), the zero residue having no primes >B. There are O(min(S+1,p)) offsets i. Summing over nonreset p<=C(S+1) gives
    #nonreset keys (M',D,t) <=
    O(N sum_p min(S+1,p)(1+S/p)/p)
    = O(N(S+1)(1+log log(3+S))).
Indeed for p=O(S+1) the summand is O(1+S/p); prime harmonic upper bound suffices. Deduplicating physical keys with several possible incoming labels can only reduce the count. Add O(N(S+1)) reset keys. With S=floor(u^.25) use the looser O(NS ell) upper bound for all keys. This is an upper bound on the number of physical slots, not the number of older origins in them.

At fixed (M',D,t), n_M(v)=1+# larger companions in the full original fibre is exactly descending source rank, so at most k old sources have rank<=k. Use whole unordered pair bounds U_H=3H and U_M=C_med H/m_g (both actual medium directions). Pay the entire remaining pair in this landing class if n_M(v)<=2K for high, or <=floor(L_M/(S ell)) for medium, with L_M=m_g/u^.25. The costs are
    O(N U_H K S ell)=O(F ell/u^(3/8))=o(F/u^.25),
    O(N U_M L_M)=O(NT/u^.25).
There is no inverse-grid-spacing cost, and no assumption that all shallow births are synchronizations before the older landing. Both bounds apply to the larger arithmetic landing class and therefore to every actual shallow recorded physical first meeting. There is no restriction on later shared tail length. They are absolute whole-pair costs, not linear rare-root deletion.

## 4. Thick physical ancestry strip (high)

Use the previous near-reset threshold m=Theta(Bu^(5/6)), as in 59b9bc5, and half-horizon strip A'=ceil(u²). For a first-contact pair pay the remaining high weight if the older original history up to D visits any actual physical vertex v within |C(v)-C0|<=2A', n_v>=2m, and type A or B of section 1. By (1) at most N/m such states exist, each at most N old tags and O(A') possible younger integer roots. Thus payment
    O(U_H N² A'/m)=O(F/u^(19/12)).
Also pay an actual small-incoming member at any type C in that strip; cost <=O(U_H N A')=o(F/u^.25). No analogous full physical branch payment for medium at its smaller threshold. This is the all-physical extension of the reset strip exclusion, with the same budget, independent of incoming prime or reset.

For high survivors from section 3 with shallow physical birth, n_M(D)>2K. Previous fresh-rank exclusion ensures the first attainment of the current dyadic rank predates the entire strip (the gain age >B u^1.25 whereas D-C0<=B and A'=polylog). That rank is >=K and, eventually, >=2m. Every old visited physical vertex inside the strip up to D therefore has rank>=2m, exactly one thick incoming cohort and the focal old source belongs to it. Because D itself belongs to the strip for shallow birth, this assertion is nonvacuous even when there is no genuine reset in the strip. The unique thick predecessor can extend outside the strip; smaller incoming cohorts may enter but cannot contain the surviving focal. More generally the same condition applies to any high survivor with dyadic rank >=2m attained before the strip; if no actual vertices are in the strip it is vacuous. No lower bound on physical rank for all older crossings outside the shallow class is asserted.

This bounds formation and selects an inherited physical chain, not its unrestricted incoming mass. The representative cover in section 2 is available for all such thick physical states. Neither statement directly supplies the necessary small high tail mass.

## 5. Bounded-deficit nonreset runs

For z>=3 let L_z=2 product_(odd prime p<=z) p. Consider a consecutive sequence of completed original steps whose TARGET vertices are nonreset and all have d<=2z. All incoming p<=z: for p>=5 use d>=2p; p=3 trivially. For any even prehorizon C and such a selected p, p|C-1 or p|C+1. If C is at a multiple of L_z no such p is possible. Otherwise the distance to the next multiple of L_z is even positive and congruent to +1 or -1 mod p, hence at least p-1. A step of gain p-1 cannot cross this boundary. Reaching it ends the run because no following small-label step can start there. Thus total gain from the first prevertex of the run to any target is <L_z.

In a maximal such run, the immediately preceding physical vertex (the first prevertex) is an original root, a genuine reset, or a nonreset state with d_pre>2z. In the last case the first step has p<=z and positive wait, so d_pre-d_post<=p-3, giving
    2z<d_pre<=3z.
Consequently an arbitrarily long nonreset interval cannot have uniformly bounded deficit at all its targets. Tracing backwards from a bounded-deficit nonreset target stops at a root, a reset, or a downcross from this narrow higher deficit range within gain <L_z, time <=3L_z. This is a gain-axis barrier, not a bound on time spent in arbitrary high-deficit portions or the origin mass at the frontier. Chebyshev's upper bound implies L_z<=exp(O(z)), so z=c log u with sufficiently small c has L_z bounded by a fixed small power of u. For the larger shallow deficit scale z~u^.25 the length bound is subexponential in u but not necessarily polylogarithmic. The finite audit uses z=5 normal, 7 stress, 3 analytic at tested sizes; observed runs do not exercise the higher-deficit predecessor alternative. No further residual payment is attributed to this barrier.

## 6. Audit and results

Standalone research/min_prime_root_physical_cover_audit.mjs, final source commit 1265b7019bde952b9c5ae467d9f40c486bb2862e, blob 04afff13a916875f69a4ff58cec5057fb2d1521d, exact remote readback.
    node research/min_prime_root_physical_cover_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_physical_cover_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress --grid-stress --star-stress --prefix-stress --reset-stress --threshold-stress --cover-stress 256 1024 4096 16384 65536 262144
Actual execution in available ECMAScript runtime. Preliminary duplicate identifier fixed before first successful version; initial 8 successful runs (analytic/concurrent at X256..16384), 6 larger tests after adding terminal exception accounting, final18 successful runs across six X and three configurations. Other final modes not rerun. Full physical DAG ordered continuation and first threshold attainment checked at each distinct state. Greedy original seed disjointness, cover of all heavy states, representative gain and large-edge bounds; independent cover controls at thresholds2 and8 even when asymptotic threshold has empty fibres. Independent state-first low-deficit slot oracle on first128 roots (or fewer), actual consecutive low-deficit run frontier and barrier, actual physical strip and unique thick input checks, unpaid-only absolute pair payments and feasible reoptimization. Counts integer, fractional flows use tolerances. No Lean compilation.

Normal finite diagnostic K=3, m=2, S=8, strip A'=ceil(B/4), P=ceil(B/4), shallow rank caps4 high/3 MED. Stress K=4,m=3,S=16, A'=ceil(B/2), P=ceil(B/8), caps8/5. Analytic asymptotic settings of sections2-4 with finite min2 thresholds. At all tested analytic sizes previous residuals empty and chosen K exceeds actual fibre max, so independent smaller-threshold cover controls are essential. Rare-root support computed but not subtracted; no fresh linear deletion or density gate. High residual is the inherited isolated natural high diagnostic, NOT full cumulative hybrid.

|X|prior normal MED|final MED|prior normal high|final high|
|--:|--:|--:|--:|--:|
|16384|0|0|0|0|
|65536|1.272782|1.272782|14151.916041|0|
|262144|0|0|62161.837452|57314.687756|

Largest normal X262144:145 positive unpaid pairs,12 paid and133 remain. High additional4847.149696 (11 physical branch pairs4447.427676, one small-inflow pair399.722021), no shallow landing matches, MED unchanged zero to tolerance, never/async0. 4485 actual strip visits checked before masks; 2585 actual unique thick physical input checks on survivors with qualifying prior rank activation. These are visit occurrences, not distinct physical states or 2585 pairs. At X65536 all16 remaining high pairs paid by physical branch strip (14151.916041; final -5.82e-11 rounding); MED remains1.272782. Combined stress already zero, remains zero; no new stress reduction. No shallow rank payment exercised in positive residuals at these sizes.

Full largest normal physical controls: N20390,191361 distinct states, physical threshold m2 Delta=Loss=12040, A42,B1954, small-incoming total5607. K3 representative cover 2731 representatives, disjoint seed populations totaling9022 roots, covers55166 heavy states; representative full original gain2852556;1308 distinct heavy large prevertices,2220 representative large-event occurrences,0 terminal exceptions (allowed and checked). Independent K2 cover4972 representatives/10419 seed tags/83427 heavy states/1984 large keys; K8 cover723/6811/19086/493. Nearby heavy large support1143 distinct younger prime roots,1614 incidence count, not deleted. Low-deficit slot support421771 keys (116502 reset,305269 nonreset), max43 per younger root;128 independent state-first oracles. Nonreset low-deficit runs43894, steps47720, maximum gain6 with L=30; all preceded by reset, no downcross or root frontier in normal finite run sample. Stress low runs54821, steps70118,max10,L210;7985 root/46836 reset/0 downcross. Largest analytic controls physical states191396, m chosen threshold Delta169; K=12508 empty, independent K2 cover4971/10413/83456/3387 and K8 cover720/6742/19185/815. Shallow arithmetic keys33369, all counts finite.

## 7. Remaining proof target

The near-start thick ancestry restriction now acts on actual physical vertices even in nonreset strips, and representative covers give a global count of paths required to contain all high-rank physical fibres. A nonreset bounded-deficit run is short in its own primorial scale. Neither property gives a bound on mass inherited through arbitrary high-deficit excursions. A useful next step is to estimate long inherited physical paths of the representative cover by the actual high-deficit excursion occupation or upward/downward level crossing budgets (cf. independent donor-ascent partitions), retaining their multiplicities rather than assuming all heavy paths contribute small tails. Joint medium o(NT) and high o(F) on an unbounded common sequence remain OPEN. Main and independent branches unchanged.
