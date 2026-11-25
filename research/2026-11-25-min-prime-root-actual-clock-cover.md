# Actual-clock target and multiplicity-two covering of fast medium quota segments

2026-11-25 JST. Continuation of 6f46d5e90119b2bfd78caff3ad8d7c847861b008, on research/min-prime-root-repeat-energy-2026-11-25. This changes the sufficient target from total minimum-factor proxy cost to total actual completed waiting time. The earlier gap-adaptive sparse quota and physical formation estimates remain applicable by pointwise domination. A multiplicity-two interval cover now pays every fast focal quota edge in actual clock cost, regardless of its ancestor history. In particular ALL upper-band time-disjoint far charges are paid in the new target, without the earlier short-wait witness restrictions. Residual upper-band far pairs must instead have two almost coincident elapsed-time intervals, each of duration at least a small fraction of the repeat gain. This is a strictly weaker sufficient problem, not a proof of the whole medium or high residual or of twin prime infinitude. No Lean compilation.

## 1. Use the actual clock as the sufficient target

Retain dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) original prime starts, Q=ceil(B/u). For each original gain-stopped MIN prefix, let p_i be the completed selected odd prime, r_i the least eligible prime at its input, and w_i the actual positive wait until selection. Then
    1<=w_i<=2r_i<=3(p_i-1).
Original initial state is (t,C)=(M+2,2M-2), with deficit Delta=2t-C=6. Every actual visited state satisfies Delta>=0, including the terminal vertex. The exact per-step change and telescoped sum are
    Delta_{i+1}-Delta_i = 2 w_i-(p_i-1),
    2 sum_i w_i = G_M + Delta_end - 6,              (1)
where G_M=sum_i(p_i-1)<H is the completed gain. Let W_all=sum_M sum_i w_i. No uncompleted cutoff wait is included.

On a sufficiently large no-twin window, the established gain-prefix argument of a5e1119 gives G_M>=T for every prime root. Indeed a prefix stopping before the gain threshold must be a twin terminal or run out of time before the original cutoff; the latter is impossible at large X since completed elapsed<=3H and the next possible wait<=2B if a positive eligible r exists, while the original cutoff has order-X time remaining (H=o(X)). Thus (1) gives W_all>=N(T-6)/2. It is sufficient to show
    W_all=o(NT)                                     (2)
on unbounded dyadic windows, with the same no-twin contradiction. The old proxy condition R=sum r_i=o(NT) implies (2), but is stronger than necessary. In particular a large r with a very short actual wait is not intrinsically a large contribution to (2). We do not conclude a small R from a small W_all.

## 2. Preserve the established accounting with actual weights

Use the same frozen medium hits y<p<Q, least eligible r, and attached original subsequent LOW blocks of gain <L<=ell^.25. For a retained medium hit E on source M, write a_M(E)=r plus the attached LOW proxy cost (as in 0ce6427); define
    b_M(E)=actual wait at E + actual waits in its attached original LOW block.
Thus 0<b_M(E)<=2a_M(E)<=2(r+1.5L). The initial LOW block and high-attached LOW remain negligible in actual time by the previous proxy bounds. Already-paid root-specific linear deletions remain paid too. No change to paths or selection of events.

Retain exactly the sparse quota k_P, same-r aligned gain cells, and long-edge definition h=E-C>D_r of 8fd0a10, with P the DYADIC LEAST-FACTOR band. Each later hit allocates a_M(E)/k_P in the previous proxy ledger; in the new actual ledger allocate b_M(E)/k_P to the SAME preceding hits. Equivalently multiply each focal edge cost by b_M(E)/a_M(E), independent of partner. Use the same full original source/phase cells, group sizes, and partner rules. Every directed allocated actual charge is at most twice the corresponding original proxy charge. The old first-use, short-gap, sparse-band, thin-source/phase-cell, tiny and close-pool, near-origin and physical first-small exclusions therefore all remain valid in actual time (including their unions with priority). No need to rederive them using b, and no comparison between a focal actual cost and its partner's actual cost is required. In particular do NOT use the old partner-supported argument with b in place of a; b_M(E)/b_M'(E) need not be bounded. The new fast criterion pays focal edges directly.

Use the high proxy estimate unchanged: the previous sufficient condition E_phys,admitbad+E_async,bad=o(T²Bu) yields the required high proxy clock bound with the earlier relative-cheap/LOW exclusions, hence also high actual waits. This note does not prove that high condition. The new medium target only needs to bound actual costs.

## 3. Fast focal edges: a multiplicity-two interval cover

Set rho=u^-1/64. For any FULL frozen long quota edge (M,r,C,E), before any partner or paid-class tests, let F be the original horizon just after the actual selected event at E and its subsequent attached LOW block. Let t_M(F) be its actual time, including a terminal if the block ends there. Define h=E-C>0 and call the focal edge fast in actual clock if
    t_M(F)-t_M(C) <= rho h.                         (3)
This differs from the previous speed-and-witness test: no short-wait support measure, recent anchor, minimum-factor threshold for a witness, or heavy/light history condition is used. No restriction to upper bands is needed in (3). The edge carries only the actual cost of E and its attached LOW, divided by k_P, not the cost of the whole segment.

For a root M define a nonnegative finite gain-axis measure by giving the entire actual wait w_i to the half-open selected gain interval [C_i,C_i+p_i-1), e.g. as constant density w_i/(p_i-1). The measure of any interval from one actual visited horizon to another is exactly the elapsed time between them. All fast edges of M provide extended half-open intervals I=[C,F), each with measure <=rho h<=rho |I|. Their union U lies within the original gain range of length <H. Distinct later nonLOW hits E represented by these edges have disjoint actual selected-plus-LOW gain intervals [E,F) contained in U. This disjointness is of the blocks attached to distinct events, not of the extended repeat intervals. If the same E has several fast preceding hits, their total allocated clock is at most b_M(E) since there are at most k_P choices.

Finite interval lemma: any finite family of positive-length half-open real intervals has a subfamily with the SAME union and multiplicity <=2 away from endpoints (equivalently almost everywhere). For example take an inclusion-minimal subcover; no chosen interval is contained in another, so in increasing left-endpoint order their right endpoints are strictly increasing. If three intervals overlap at an interior point, the middle interval lies in the union of its two neighbors, contradicting minimality. More generally if i and i+2 overlap in interior the middle is redundant. Thus the sum of chosen lengths is <=2|U|. A greedy implementation starts at the leftmost uncovered point, picks the interval extending farthest right among intervals beginning at or before the current covered frontier and extending it, and starts a new component after a gap. It has the same multiplicity property. The measure above is absolutely continuous, so endpoints cause no atom problem.

For each root the measure of U is <=sum of the measures of the chosen intervals <=rho sum lengths<=2rho H. Therefore
    sum of b_M(E)/k_P over ALL fast full quota edges <=2rho H,
    W_fast^quota<=2rho NH=O(NT/u^1/64)=o(NT).        (4)
No multiplicity factor for interval overlap, for the number of label bands, for the number of prior hits, or for the number of partner tags. Every original focal edge distributes exactly its own cost; its total actual charge over all partners is <=its full allocation. Hence after ANY of the inherited paid tests, the entire remaining charge whose FOCAL edge satisfies (3) is paid by (4). This includes already-synchronous, immediate-synchronization, far asynchronous and any other class. Partner fast alone is NOT used. No new partner allocation, no assumption of comparability of actual costs between roots. This is an absolute actual-time bound, not a bound on the old proxy cost of fast intervals.

For an independent additional simple exclusion one can pay all later focal hits with b_M(E)<=rho(p_M(E)-1), by the original gain budget sum(p-1)<=NH. This is valid even if none of their repeat intervals satisfies (3). We leave it optional (not in the finite residual ledger below).

## 4. Upper medium time-disjoint far class is fully paid

From 8fd0a10, for a remaining far asynchronous charge in factor band P, gap band S<=h<2S, the paired roots have both endpoint input lags in absolute value <W_{P,S}=ceil(S u^-1/16 (Q/P)^.75), and both output lags >D_P. In the upper range P>=Q/u^1/24, W_{P,S}/h=O(u^-1/32)=O(rho²). Also h>D_r with D_r of order r u^1.5 sqrt(ell) in this range, so Q/h=O(u^(-1.5+1/24)/sqrt(ell))=o(rho²). The extension from E to F has gain at most Q+L and actual time at most 3(Q+L), since all included events are completed medium/LOW selections. These bounds are uniform in the upper range.

If the two elapsed-time intervals from C to E have disjoint interiors, then BOTH durations are <W_{P,S}. Orient the two intervals by their start times: the earlier duration is bounded by their start gap and the later duration by their end gap. Touching is included. Hence on either root
    t_M(F)-t_M(C) <= W_{P,S}+3(Q+L)
                   =O(h rho²) <= rho h
eventually. Every such focal edge satisfies (3), so (4) pays ALL upper-band far-disjoint charges in actual time. No need for the direct/bridge/elapsed short-wait CRT gain exclusions or long excursion conditions of d8dea6f, 86f67c8 and 6f46d5e in this class. Those results are retained for the stronger proxy target and other future uses, not used to assert the old proxy disjoint charge is negligible. This also pays fast overlapping or fast synchronous focal edges, irrespective of the other root's duration.

In the lower range P<Q/u^1/24, the same exact fast test (3) pays whichever focal edges satisfy it, but a time-disjoint pair need not have fast segments there; W/h need not tend to zero. We do not claim the whole lower-band disjoint class is paid.

## 5. Remaining upper-band far segments have nearly coincident time intervals

Consider any remaining actual far charge in the upper band after (4). Let tau=t_M(E)-t_M(C) on its focal root and tau'=t_M'(E)-t_M'(C) on its partner. The focal failed (3), and the E-to-F extension time is O(Q+L)=o(rho² h). Thus
    tau > rho h-3(Q+L) >= rho h/2
for sufficiently large X. Since both endpoint lags are <W=O(rho² h), |tau'-tau|<2W, and tau'>=rho h/3 eventually. The intersection length I_time of their elapsed-time intervals is at least tau-2W and at least tau'-2W (the possible losses at the two endpoints). In particular
    I_time / max(tau,tau') >= 1-O(rho).
This is stronger than merely requiring positive overlap: both original trajectories are present during almost all of each other's C-to-E elapsed-time segments, and their signed lag drift is <2W=o(tau), while neither shares a physical state before E. No assertion that this forces physical merging, forces the same selected word, or implies any lower bound on the separation of their horizons at a given clock tick. The new remaining async problem is one of concurrent trajectories at upper bands, with the inherited both-endpoint lag, phase density, and origin-separation constraints. A next possible use is to compare their time-indexed horizon difference and CRT selection overlaps during their long shared time interval. No estimate of this overlap class is proved here.

## 6. Joint sufficient conditions

After transferring all previous paid classes from the proxy ledger by domination, and paying fast FOCAL edges as above, define the actual residuals:
    W_already,bad^slow and W_immediate,bad^slow
      = actual charges at large cell-local first physical meetings,
        with focal edge failing (3);
    W_far,lower^slow = lower-band far residual failing (3);
    W_far,upper,overlap^slow = upper-band far residual failing (3),
        with the near-coincident time-interval property of section 5.
Use the same smaller raw source-cell first-formation caps m_a'=floor(u^4.5/ell^4) and m_b'=floor((H/Q)m_a') (min1) as the gap-adaptive allocation, not the stronger previous unrelated cap. The actual synchronous residuals are a subset of the old proxy residuals weighted by at most two. The far residuals retain the old origin cutoff, phase caps and bilateral close tests. The optional later-hit cheap test could further reduce these terms.

The new medium sufficient condition is
    W_already,bad^slow+W_immediate,bad^slow+
    W_far,lower^slow+W_far,upper,overlap^slow = o(NT).
Together with the previous high proxy condition E_phys,admitbad+E_async,bad=o(T²Bu), on the same unbounded windows this implies (2) and contradicts (1) on no-twin windows. Neither residual condition is yet proved. Unlike the previous route there is no separate upper-band disjoint short-wait/anchor/excursion rarity problem. The actual clock objective is sufficient because of the exact original deficit identity, not because the old proxy and actual costs are interchangeable in both directions.

## 7. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_actual_clock_cover_audit.mjs, exact remote readback at fa58419846dc5f01108dd36d9fab93153eb0045f, blob f8e4091f5bf0d2c2be3ea51e08a97b20bed6426f. Run:
    node research/min_prime_root_actual_clock_cover_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node process. All 36 runs (six modes x six windows X256..262144) passed. The audit starts from the gap-phase audit, not the recent-anchor audits, because the new target requires no such short-wait support. It verifies exact original per-root/global deficit identity, terminal nonnegativity, actual LOW attachment and root/medium/high decomposition, pointwise actual <=2 proxy, exact actual quota and focal partner weights; fast extended intervals from actual endpoint/LOW time, greedy union cover, independent coverage of every original interval, multiplicity <=2, disjoint endpoint cost and actual-time sum bound. It retains the original proxy endpoint and first-meeting checks, and partitions actual partner charges before/after fast and first-small exclusions separately. Uses floating tolerances for fractional costs; integer root identities and interval measures exact. No audit of the optional cheap later-hit test or of the asymptotic near-coincident upper overlap property; analytic upper-band retained far checks vacuous. As in 8fd0a10, analytic raw formation caps in inherited code are the older larger ones, but analytic retained residual is empty. Finite diagnostic raw caps differ from the asymptotic caps; do not infer limiting suppression from these checks.

Modes inherited from gap-phase. Analytic rho=u^-1/64; short/wide/phase/stress rho=1; broad rho=2.5 and W=4H, deliberately nonasymptotic to exercise far charges. Fixed finite y3,L6. Analytic mode at largest X262144: N20390, total gain19169594, proxy R16687054, actual completed time14321516, final deficit sum9595778, identity 2*14321516=19169594+9595778-6*20390. None of the roots reaches T at this finite size (twin terminals or cutoff, not a no-twin test). Actual initial LOW34990, high8103930 (including its attached LOW), medium6182596. Medium actual first-use6169252, short728.8333, long12615.1667 all already band-covered. Full fast edges24274, cost9371.4444, 416 source covers with 730 selected intervals, union gain1081428, sum selected lengths1657158, actual selected elapsed1112332, distinct endpoint actual cost12815. Nonvacuous cover test even though retained far residual empty.

Largest diagnostic X262144:
- Short: actual medium4435061, pre-phase surviving actual5578, tiny60, already5518. Fast already1684, small first already1044, residual2790. 1968 full fast edges,1961 selected intervals,11 depth checks.
- Phase: actual pre-allocation126, all paid by fast focal intervals; original proxy residual after first-small278.3441. These are different quantities.
- Stress: actual pre-allocation19635.6667, tiny1.3333, close0, far6 (all overlap), fast far4, remaining far2; already19628.3333, fast already7031.6667, small already7923.7640, large already4672.9027. Final actual4674.9027. Full fast4028 edges/cost9224.6667, 1857 selected intervals, 1655 source covers,13 depth checks. Original proxy final after origin7478.2740 (different units).
- Broad: pre-allocation19971.6667 actual, tiny299, close333.6296, already19152, far187.0370 (disjoint142.9259, overlap44.1111), near-origin1.7778, remaining far185.2593 all fast. Fast already18856, small already53.4214, large already242.5786. Final actual242.5786. Full fast9735 edges cost25563.3333, 3642 selected intervals over2826 roots,126 depth checks and9735 independent coverage checks. Union gain232668, selected gain251102, selected actual time243732, distinct endpoint actual cost31241. Broad X4096,16384,65536 all actual retained residual zero at diagnostic rho2.5. These choices test the partition and interval cover, not the asymptotic fast threshold or upper-band rarity. Wide retained residual zero.

Main and other branches unchanged by this checkpoint.
