# Absorbing younger-prefix reverse graph and bounded nonreset physical birth cone

2026-11-25 JST. Continuation of c6bf00ef5af6fe32651855ac7a4a5c8851ae0b67 on the selected prime-root branch. The one-sided younger-root cut now uses a reverse arithmetic first-hit graph excluding every earlier younger vertex, followed by the exact original older-path first-hit cohort. This gives an upper bound on the actual older source sets in each shallow contact band, as a subset of the full crossing population, and a more selective rank deletion. Separately, a physical first-meeting deficit cone restricts the older entry phase and its backward nonreset ancestry. A short backward path reaching its original root has a quantitative source-distance bound, and a nearby reset with a very large incoming label lies over a negligible exceptional set of younger prime roots. These are partial structural and absolute estimates, not an upper bound on all deep ancestor masses. No Lean compilation; twin-prime infinitude remains open.

## 1. Setup and actual first-contact bands

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime starts M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, m_g=u^4.75/ell^4. Original gain-stopped MIN paths are unchanged. A completed selection p increases the even projected horizon by p-1, with positive wait <=2r<=3(p-1); total original gain <H. The initial state is (M+2,2M-2), deficit d=2t-C=6, and all physical vertices have nonnegative deficit. The uniform whole-pair bounds are U_high=3H and U_med=C_med H/m_g, using the full natural high list and inherited actual directed medium allocation respectively (C_med a sufficiently large absolute constant, both directions included). Nonnegative remaining pair weights may have arbitrary earlier mask holes and feasible quota fractions.

For M<M' let C* be their first common original projected horizon, C0=2M'-2, x=C0-1. The unique older crossing of x has prevertex A<=x and postvertex D=A+p-1>x, D<=C*. Write C*=C0+2a and D=C0+2i. Then 0<=i<=a, 2i<=p-2, and p divides M'+i-1 or M'+i. All old vertices from landing i up to the first hit a, excluding a, avoid EVERY younger original vertex. This condition uses original histories, not residual-only incidence lists. Age bands j=0 for a<=1, j>=1 for 2^(j-1)<a<=2^j, and theta_j=(j+1)^(-2), as in the preceding root-star paper.

## 2. Absorbing arithmetic DAG and exact first-hit cohorts

For fixed younger root M' and integer age ceiling S, put V={0,...,S}. Mark the set P of offsets of all original younger vertices in this range, including its root and terminal if present. For 0<=h<k<=S insert an edge h->k when
    q=2(k-h)+1 is an odd prime <=B,
    q | M'+k-1  or  q | M'+k.
This is exactly the necessary projected label congruence at an incoming posthorizon C0+2k. It does NOT impose physical time, earliest MIN selection, or original stop; it is a relaxed arithmetic graph. Make every vertex of P absorbing, so paths cannot leave it before their first younger hit.

Define R(i) as the set of all possible first-hit offsets in P reached from i by a path in this absorbing graph. It is calculated by descending recursion
    R(i)={i} if i in P,
    R(i)=union_(i->k) R(k) otherwise.
The empty union is empty. This is an exact identity for the RELAXED graph. Every actual older prefix from its cut landing i to its first common projected horizon a<=S gives a path in this graph and hence a in R(i). No statement that all relaxed paths are realizable by MIN is needed. The number of possible paths from any i is bounded by 2^S (each positive-increment path is a strictly increasing sequence of offsets), even without arithmetic restrictions. The audit uses a saturating count of paths rather than huge exact integers, and checks the hit sets independently using a forward BFS that stops at the first marked vertex.

At a fixed younger root/age band j truncate at S<=2^j if desired. The full actual older crossing reference list is the one of c6bf00ef5af6 (one tag per older root crossing x). For each landing offset and label let A_(i,p) be its actual older source set. Then the ACTUAL older source set F_j with first projected hit in the chosen age band satisfies
    F_j subset union_(i,p : R(i) intersects age band) A_(i,p).
All A_(i,p) at this cut are disjoint. Thus
    |F_j| <= sum_(compatible i,p) |A_(i,p)|.
The same holds for any subset of older sources and for a sum of any nonnegative older-tag weights. For an upper tail envelope of high pair energy, use the weight 2 min(retained older tail at D, retained younger tail at C0); for medium use the uniform whole-pair bound. One can also require a given target offset rather than an entire band. The arithmetic filter improves the previous all-landing-i<=S envelope; it excludes an entire landing population when there is no allowed route to a first contact in that band.

Compute F_j exactly by scanning the actual original older suffix from D up to S and finding the FIRST younger vertex, if any. It is a fixed subset of the full original reference cohort independent of all quota payment choices. This is not an asymptotic estimate of the masses of A_(i,p); deep old ancestry may still make an allowed slot very large. It gives an explicit one-sided first-hit envelope and a smaller exact ranking population. A pair may share many later horizons but is included at only its first hit.

For each j put L_high=B u^1.5, L_med=m_g/u^.25 and m_j=floor(L_metric theta_j). On the exact full F_j ordered by decreasing older source, admit its first m_j, or its first floor(m_j/b_j) in each of its b_j nonempty actual landing cohorts. One younger source admits <=2m_j distinct older partners, irrespective of the sizes of the relaxed graph or the cohorts. The WHOLE remaining unordered pair weight, including both medium directions, is paid on admission. The total cost is O(N U_metric L_metric)=O(F/u^.25) high or O(NT/u^.25) medium. This is an additional valid rank family; it is more selective toward actual first hits than the previous rank on all older crossing tags. It may admit pairs already covered by prior accounting, so the audit charges only the currently unpaid fraction. Neither the relaxed filter nor the ranking assertion alone implies that all allowed groups are thin.

## 3. Direct absolute bound on short-age large older crossings

This estimate bypasses the rare-root linear deletion and uses total ORIGINAL older gain. Fix S>=0 and P>=5. For a given completed older edge of selected label p>=P, a younger prime root M' with contact age a<=S and this edge crossing its cut must have
    D=2M'-2+2i, 0<=i<=min(S,floor((p-2)/2)).
The edge therefore accounts for at most S+1 distinct possible younger roots (even ignoring primality). The total number of such older edges is <=NH/(P-1). Each unordered pair is assigned to its unique older crossing. Consequently the ENTIRE class of retained high pair weights with a<=S and p>=P costs
    E_short,large <= 3H (S+1) NH/(P-1).
For S=floor(u^.25) and P=ceil(B/u^1.25), this is O(F/u^.5)=o(F). Indeed N=O(B²/u), H~T, and (S+1) B/(P u²)=O(u^(-.5)). This is an absolute energy bound, unlike the previous rare-root linear mask; no physical density gate recomputation is required. The older large selection need not itself be a natural high event, nor the first contact a physical meeting. For medium the corresponding bound U_med (S+1)NH/(P-1) is not generally o(NT), so no analogous whole-class medium deletion is claimed. The earlier stronger-in-label-range rare-root linear deletion remains useful and different. Finite audit verifies the combinatorial count and gain budget; no positive unpaid pair happened to satisfy the finite large-crossing class.

## 4. Physical first-meeting cone and delayed synchronization

If the original pair meets physically, let J be its FIRST common physical recorded vertex horizon (same t and C). This can be later than first projected C*. Write J=C0+2g, with g>=a. Use d=2t-C. Along any original gain segment of size G, elapsed time W lies in [0,3G] and the deficit change is exactly 2W-G, hence -G<=d_end-d_start<=5G. The younger trajectory starts at d=6 and therefore at J,
    d_J<=6+10g.
For the older crossing landing state v=(t_D,D), put d_D=2t_D-D. Nonnegative elapsed time on its subsequent path to J gives
    d_D <= d_J+(J-D) <= 6+12g-2i.                  (1)
At a recorded landing with incoming p and parity s=t_D mod2, phase identity is d_D=6s mod 2p. Call it a genuine reset if d_D=6s. If p>=5 and it is not a reset, nonnegative deficit implies d_D>=2p, since 6s<2p. Thus
    g >= (2p+2i-6)/12                              (2)
for any eventual physical first meeting after a nonreset older crossing with p>=5. This is a lower bound on younger gain-age required before synchronization, valid even when the first projected contact is very early and the old crossing occurs long before that contact. It does not require monotonicity of time lag. Additionally if the original arrival ticks at C* differ by lambda, both elapsed times from C* to J lie in [0,3(J-C*)], so
    lambda <= 3(J-C*).
The two paths need not visit the same intermediate horizons. This lag bound uses actual original waits and a common first recorded physical vertex, not a fabricated time-interpolated state.

In particular for shallow physical first meeting g<=S, every older crossing label p>3+6S must land at a genuine reset. These restrictions are distinct from shallow PROJECTED first contact: a shallow projected hit can be followed by a very late physical merger or never physically merge. Do not apply the physical cone to those without a meeting in the specified age range.

## 5. Backward nonreset cone: quantitative root and reset alternatives

At any nonreset physical poststate v with d_v>=0, write D_v=max(6,d_v). Its actual incoming q satisfies q-1<=D_v/2: for q>=5 use d_v>=2q; q=3 uses D_v>=6, including the odd low-deficit phase exception d_v=0. Its predecessor w has d_w-d_v=(q-1)-2 wait<=q-3 and hence max(6,d_w)<=1.5 D_v. Trace backwards at most k actual completed events, STOPPING at an original root or a genuine reset before reversing its incoming event. For the h<=k nonreset steps actually reversed from landing v, induction gives
    max(6,d_back)<=D_v (3/2)^h,
    gain reversed <= sum_(l=0 to h-1) (D_v/2)(3/2)^l
                   =D_v((3/2)^h-1).               (3)
Every reversed selection label is <=1+D_v(3/2)^k/2. The time distance is also <=3 times the reversed gain. These bounds are actual backward path constraints, not claims of a unique reverse predecessor or an upper bound on all ancestors. The original root is itself a reset; distinguish the two stop types.

For a shallow physical first meeting g<=S0=floor(u^.25), (1) implies D_v<=6+12S0. Choose k=floor(log u) (eventually >=1). By (3), reversed gain and deficit at the frontier are O(u^(.25+log(3/2)))=O(u^(2/3)), since .25+log(3/2)<2/3. The frontier horizon lies within O(u^(2/3)) of the younger initial horizon C0. Thus each such pair is in at least one of the following exact alternatives:
  A. Older ORIGINAL root reached within k nonreset reverse steps: its root horizon is in this short interval, so M'-M=O(u^(2/3)). For each younger root there are at most O(u^(2/3)) such older roots, simply by integer counting. The total whole-pair cost is O(N U_metric u^(2/3)), which is o(N U_metric L_metric) for BOTH metrics. This pays the actual pair even with a very long later shared suffix.
  B. Noninitial genuine reset reached within k steps: its horizon is C0+2i' with signed integer |i'|<=C u^(2/3), for some fixed absolute C. Its incoming label is not covered by the bound on the reversed nonreset steps. If that incoming label is very large, it is handled by the exceptional set below.
  C. Reversed k nonreset steps and still no reset or root: all these actual reversed labels are O(u^(2/3)), and the entire reversed gain and deficit satisfy (3). There may be arbitrarily deep older ancestry before this frontier, so it is not a bound on the full root fibre.

In B, let Y'=B exp(-u^(1/8)). The incoming reset label q divides M'+i'-1 or M'+i'. By the prime progression upper estimate O(N/q) of c6bf00ef5af6, uniform also for signed shifts, the number of younger prime roots admitting ANY such reset label q>=Y' within the above short signed interval is
    O(N u^(2/3) sum_(Y'<=q<=B) 1/q)
      = O(N u^(2/3+1/8-1)) = O(N/u^(5/24)).
Here the narrow-band reciprocal upper bound follows from Chebyshev and partial summation as before. Zero residue cannot contain a prime M'>B. This set of exceptional original younger roots is o(N); their full original high histories have linear proxy/actual cost o(NT). Apply such a deletion before the final retained high density gate (or rerun that gate), never reinterpret it as an absolute quadratic bound. For medium only its focal charges are paid by the linear root deletion. In particular after these high and absolute near-root exclusions, a shallow physical birth must have a nearby reset with incoming q<Y' or a full k-step small-label nonreset reverse suffix. This extends the previous one-edge rare support to a bounded backward physical neighborhood, including resets before the younger start. It does not bound the old mass at the reset or depth frontier.

The asymptotic alternatives and signed-shift exceptional set are paper consequences of the checked cone, NOT additional numerical deletions in this audit. The reverse depth in the finite audit is max(1,floor(log u)), and the finite shallow physical diagnostic uses its own age ceiling.

## 6. Reproducible finite audit

Standalone research/min_prime_root_absorbing_prefix_audit.mjs, source commit 103906ac199cb4bf297e485c009146ec8b1fdc6d, blob 812a4cb3b02deb832898b59c65d9d8569c6dc6ee, exact remote readback.
    node research/min_prime_root_absorbing_prefix_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_absorbing_prefix_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress --grid-stress --star-stress --prefix-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in available ECMAScript runtime, not separate Node process. Initial 14 successful runs (analytic/concurrent four X256..16384 and analytic/concurrent/combined stress at X65536/262144); final18 successful runs (three configurations at six X). Other final modes not rerun. The final version includes eight independent younger-root arithmetic DAG controls even when residual empty, exact hit-set comparison to independent forward BFS, original first-hit cohort scan and rank degree, older edge gain and count, independently merged physical original vertex lists, first-meeting age/deficit/lag cone and actual reverse nonreset cone. In rank application only unpaid fractions of preceding feasible flow are removed, with proportional medium directions and never/async weights; old payments remain feasible and flow is reoptimized. No double payment. Integer state/support counts exact; floating flows use tolerances and relaxed path counts saturate at MAX_SAFE_INTEGER (not exact path counts beyond that value).

Normal finite prefix ceiling floor(B/4), rank caps4/2 (high/medium); stress floor(B/2), caps12/6; analytic ceiling floor(u^.25) and theoretical ranks. Finite large-crossing thresholds normal ceil(B/2), age16; stress ceil(B/4), age32; analytic P=ceil(B/u^1.25), S=floor(u^.25). Prior analytic residuals empty; controls check arithmetic DAG even there. The inherited high ledger is isolated natural high diagnostic with earlier masks, not full cumulative hybrid. Rare-root linear deletions and the new backward root/reset alternatives are not implemented as finite deletions. No Lean compilation.

| X | prior normal high | final normal high | prior medium | final medium |
|--:|--:|--:|--:|--:|
|4096|0|0|0|0|
|16384|0|0|9.252348|9.252348|
|65536|36480.761572|29455.986782|8.320120|8.320120|
|262144|1313263.837279|1097884.517617|10.636373|8.291281|

Largest normal X262144: 1064 positive unpaid queried pairs in both metrics combined,771 in prefix ceiling and293 outside; reference memberships for queried younger age bands4499 before,3150 after relaxed absorbing hit filter,1969 in exact original first-hit cohorts. Occupied slot occurrences608->390. Final DAG20989 nodes,57949 edges including eight additional controls,20989 independent BFS checks. These membership totals count occurrences over distinct younger-root/age-band queries, not distinct original roots. High unpaid rank payment215379.319662, medium2.345091866937, never6.298526033689->3.953434166752, async0. Reopt final high1097884.517617, medium8.291281064262. No positive residual pair qualified for the additional finite large-crossing test; 4195 qualifying original large edges and count upper71315. Physical first meeting exists for1049 pairs,15 never meet physically, max first projected lag906; 545 physical births within finite ceiling. Across the 1049 meeting pairs, reverse cone stopped at743 reset states,306 at depth,0 at original roots (306 actual reversed steps, max reversed gain1216); shallow subgroup410 reset/135 depth. These are pair occurrences, not distinct reset states. Total old crossing landings754 reset/310 nonreset across all1064 queried pairs, not the same statistic as reverse stops. Combined stress already zero under earlier multigrid core and remains zero to floating precision; no additional reduction claimed.

## 7. Remaining proof task

The arithmetic first-hit graph now restricts actual old landing cohorts by the young original prefix, and the nonreset cone identifies concrete backward alternatives in shallow physical births. The deep origin sets at permitted small-label entry slots and at reset/depth frontiers still require a true upper mass or total shared-tail estimate. In particular the backward cone controls where a nonreset ancestor can be, not how many old prime roots can flow into it. Future work can use the actual reverse fibre and the reset ancestry estimates on those frontiers, or extend the first-hit graph with physical-time phase restrictions. The sufficient joint actual medium o(NT) and high o(F) on one unbounded dyadic sequence remain OPEN. Main and independent branches unchanged.
