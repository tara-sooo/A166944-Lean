# Phase-rank trimming and asynchronous partners at stable two-sided annulus witnesses

2026-11-26 JST. Continues [8689a9918c69](https://github.com/tara-sooo/A166944-Lean/blob/8689a9918c697a8d8941e407dea2bcd32672eeae/research/2026-11-26-min-unified-two-sided-annulus-witnesses.md), combining the actual tick entropy lemma of [3fe50cf63782](https://github.com/tara-sooo/A166944-Lean/blob/3fe50cf6378294cdaa25cacc0e9f9cda16a2174c/research/2026-11-25-min-unified-stable-strand-clock.md). Original source branch heads verified unchanged at preflight, prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New: linear rank deletion inside projected crossing groups, transfer of the full actual cohort stability to all good past/future witnesses, quantitative dichotomy between very massive physical cohorts and abundant smaller-or-equal-mass distant exit slots, and a normalized projected asynchronous-pair sufficient criterion for the complementary clock. No upper contraction, twin-prime proof or Lean compilation.

## 1. Original ensemble and geometric witness masks

Use the original completed gain-stopped prime-root MIN paths, X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. A completed event e of an original tag has prehorizon C, selected odd prime p<=B, arrival t, departure v, gain g=p-1, wait w=v-t<=2r<=3g, and original deficit d=2t-C in [0,6+5H]. Total gain <H. Under finitely many twins eventually all tags reach T and W_all>=N(T-6)/2. No path is rerun.

Use the same M=Theta(u/ell) grids P_j, largest even primorial <= B^(1/8) u^(4j), 0<=j<M=floor(u/(32 log u))+1. P_max<=B^.25, P_min>=B^(1/8)/(C u), and adjacent ratios >=u³/C. Put a=u^.25. In 8689a99 the actual waits of original events with a large fraction of paid grid-local masks were removed at cost O(NT/sqrt(ell)). Here incorporate all those LOCAL masks before averaging, not merely their globally retained events. At an unpaid grid, the left and right actual crossing witnesses of an event exist, and are either the event itself with p>=aP, or are distinct small crossings with labels q_L,q_R<=P/a and focal p<=P/a. In the latter case their prehorizon distances belong to [P/(2 sqrt(a)),2P]. Different grids' nonself annuli are disjoint. Every unpaid crossing key has raw projected tag count n(C,q)>m(q)=H/(q u ell²); stronger applicable graded/rough caps from 8689a99 may be used. The masks are evaluated on frozen original groups.

For each grid and either direction, the entire wait assigned to an actual crossing on one original tag is <=9P n_k, where n_k is the number of strict boundaries crossed by that event. Distribute this over its n_k atoms, with per-tag capacity <=9P. This raw-clock cell bound holds even for bad crossings and after any subsequent restrictions.

## 2. New rank mask inside a projected crossing group

For a fixed projected event (C,q), let n=n(C,q) be its original completed tag count. Partition it by actual departure v. Let b_v be the number of tags executing that departure (the same true tick transition from (v-1,C) to (v,C+q-1)). All possible v for this fixed C,q are in a single residue class modulo 2q, by the eligibility sign. Hence distinct slots have separation at least 2q. The physical departure groups are disjoint and sum b_v=n.

Choose theta=1/ell. Sort the slots by nondecreasing b_v, breaking ties by v. Pay the initial prefix whose cumulative tag count is <=theta n. For every unpaid slot,
    sum_(v': b_v'<=b_v) b_v' > theta n.                     (1)
It is important to use the cumulative rank, not an individual cutoff b_v<=theta n (which could delete the entire projected group). Ties in the ordering cause no problem because the left side includes all equal-sized slots.

For a grid on which (C,q) crosses, the same rank mask applies at every one of its boundary atoms. Transfer the mask to each actual original event whose left or right witness is in a paid slot. In each direction its total cost is at most
    9P sum_(projected boundary keys) sum_(paid slots) b_v
       <=9 theta P sum_(projected boundary keys) n(C,q)
       <=9 theta N(H+P).
The last sum counts every original strict boundary incidence once, and each original path has <=H/P+1 such incidences. Sum two directions for O(theta NT), uniformly in grid size. This budget is independent of total number of exit slots, no prime-pair estimate or mass-independence used. The order and membership are frozen even after other masks. We may apply it on all original crossings before the previous local masks.

Combine the old and rank local masks, then average the union indicators over grids as in 8689a99. Their mean charged wait is O(NT/ell). With epsilon=ell^(-1/2), pay entire waits with bad-grid proportion >epsilon at cost O(NT/sqrt(ell)). Every remaining original event has >=(1-epsilon)M good grids satisfying both the earlier geometric/raw-count conditions and the new rank condition on both witnesses. This is a single average deletion, not M times the cost. It is also compatible with the earlier discounted-grid masks by priority.

## 3. Full actual cohort stability on the witness interval

Apply the independent true-tick entropy mask of 3fe50cf6. For every true tick state V use its full original visiting tag set G_V including terminals, n_V=|G_V|, b_V the continuing mass. Each continuing original tag moves to a unique deterministic next tick state U and contributes token log(n_V/b_V)+log(n_U/b_V). Total over tags and transitions <=N(2+log N), by the merge-entropy and expiry telescoping argument. On a segment of one tag with token sum <=delta, the full group masses differ by at most exp(delta), and for any focal group of size n, its intersection with EVERY full group on the segment has size >=(1-exp(delta)delta)n. This is the original-set lemma, not an independence estimate.

Take D=floor(T/(u ell²)), delta=1/ell. Pay the first/last D gain portions and any completed event whose original token sum for prehorizons within D of its prehorizon exceeds delta. The budget is O(N(D+B)+Nu(D+B)/delta)=O(NT/ell): each token is charged by waits of disjoint gain intervals in a length 2D+B strip, and D>>B. This is a mask on original event incidences and does not alter original group sizes.

For a surviving focal event e let n_e be full true-tick group mass at its actual recorded arrival. All good nonself left/right witness departure states lie within the entropy window of e, as do the entire intervening paths and both witness poststates, because 2P_max+B<<D. Self witnesses lie inside the focal event. Thus every good witness slot on the focal tag has
    (1-exp(delta)delta)n_e <= b_v <= exp(delta)n_e.          (2)
For the lower bound apply the intersection lemma to both the predeparture and postdeparture true states. The common tags continue along the indicated jump, not merely visit a terminal snapshot at its predeparture. More generally all good witnesses share a SINGLE common physical cohort of size >=(1-exp(delta)delta)n_e: take the contiguous segment from the earliest good witness predeparture (or the focal arrival if earlier) to the latest good witness poststate. Its transitions are within the D window. For the whole segment choose a group intersection including the focal arrival. Each indicated witness is executed by all the common members. The left and right paths of this cohort are the same physical tick sequence; different projected groups need not coincide. This strengthens two-sided projected heaviness to an actual common cohort. In particular all distinct nonself witnesses of one focal event use the same stable cohort up to o(n_e) losses or gains, rather than unrelated mass samples.

## 4. Rank plus time spacing forces far smaller-or-equal-mass partners

At an unpaid projected witness slot (C,q,v), define for any R>=q
    f_R(C,q,v) = sum_(v': b_v'<=b_v, |v'-v|>R) b_v'.
This counts original partners in different physical departure slots, including only slots of size no larger than the focal slot. The number of allowed exit slots in [v-R,v+R] is <=floor(R/q)+1<=2R/q. From (1),
    f_R > theta n(C,q) - (floor(R/q)+1)b_v.                 (3)
This is a deterministic lower bound at a single witness, without assuming the partner paths visit another witness. If the right side is negative the useful bound is zero.

Use R_j(q)=16 max(P_j,q) for a good grid's witness, and define the single focal threshold with R_e=16 max(P_max,p_e):
    n_cut(e)=H/(16 R_e u ell³).
For every good witness, R_j(q)<=R_e, since q<=P_j/a in nonself case or q=p_e in self case. For e with n_e<=n_cut(e), (2) gives b_v<=2n_e eventually. Hence the near smaller-or-equal-mass count is <=4 R_e n_e/q<=H/(4q u ell³)<theta n(C,q)/4, using the old plain cap n(C,q)>H/(q u ell²). We obtain uniformly at BOTH good witnesses:
    f_(R_j(q)) >= theta n(C,q)/2
                > H/(2q u ell³).                         (4)
Also the number of DISTINCT far exit slots is at least f_R/b_v>=H/(4q u ell³ n_e). At each witness the corresponding departure time span from v to the farthest such slot is >R_j(q). More quantitatively, because exit slots are separated by 2q, the maximum absolute difference among the smaller-or-equal-mass slots is >=q(theta n/b_v-1), by (1). This is a span bound, not a claim of uniform partner density at intermediate times.

If e is a small focal event, p_e<=P_min/a, then R_e=16P_max, and n_cut=H/(256 P_max u ell³). With P_max<=B^.25, this is at least order B^(7/4)/(u^(5/4) ell³), since H=Theta(B²/u^.25). Thus even VERY large physical groups up to this threshold must have the far-partner alternative at at least 2(1-epsilon)M distinct nonself witnesses, all linked by the common physical cohort in section 3. Above n_cut is the very massive physical cohort sector, not paid. For large self focal p_e, the cutoff becomes H/(256 max(P_max,p_e) u ell³), at least order B/(u^(5/4)ell³). No multiplicity of distinct self jumps is claimed. The result is valid with an optional larger cap m(q,r) by replacing the old plain lower bound in (3) whenever that stronger cap applies.

There is no guarantee that the far partner tag sets of different witnesses are disjoint, or that partners sharing only one witness have a common projected word. Their time shifts may vary between witnesses. In particular (4) is not a claim of a product lower bound on the number of tags. Distinct far slots are distinct actual departures, not a statement that those paths never merge later. These distinctions are essential to using the next energy inequality.

## 5. A normalized rank-restricted asynchronous energy sufficient route

For each grid define a projected quantity depending only on actual exit-slot populations:
    E_P = sum_(K,C,q) P sum_(unpaid rank slots v with
                    (floor(R_P(q)/q)+1)b_v <= theta n(C,q)/2)
                    b_v f_(R_P(q))(C,q,v)/n(C,q),
where K ranges over strict boundaries of that projected event; no term when n=0. Here R_P(q)=16 max(P,q). The rank mask is the frozen one from section 2. Other grid-local masks may be incorporated only if the accounting below still includes every eligible witness tag; the displayed definition deliberately relaxes them. Unlike quadratic energy without normalization, E_P<=P sum_(K,C,q)n(C,q)<=N(H+P), since f<=n. Only far, smaller-or-equal-mass partners and the specified local phase-size bound enter. This is computable from original projected crossing/physical departure populations without reconstructing matching of partner paths across scales.

For a retained e with n_e<=n_cut(e), its good right witness obeys the slot restriction (indeed near bound <=theta n/4) and (4). Consequently w_e <= (2/theta) w_e f_R/n for every good grid. In a fixed grid, assign each such original wait to its right crossing cell. For each original witness tag, the cell total wait <=9P per atom when divided uniformly. Sum over tags in the slot and atoms to deduce
    sum_(eligible retained e good on P) w_e <= (18/theta) E_P.
We could use left instead, with the same global E_P; one must not sum two copies of this bound as separate clock mass. Average over grids; each retained event is good on at least (1-epsilon)M. Therefore if W_mod is the original remaining clock with n_e<=n_cut(e) and W_massive the remaining clock with n_e>n_cut(e), then
    W_mod <= [18/(theta(1-epsilon))] mean_j E_(P_j).        (5)
In particular an independent sufficient condition is
    liminf_(dyadic X) [ W_massive/(NT)
                +18 ell mean_j E_(P_j)/((1-epsilon)NT) ] < 1/2.   (6)
It suffices because all actual masks so far cost o(NT), and under finitely many twins the sum W_mod+W_massive>=NT/2-o(NT). A simpler subroute is mean E=o(NT/ell) together with liminf W_massive/(NT)<1/2 on the same unbounded scales. This is an upper bound by normalized far partner energy plus the massive cohort clock, not a proof of either required estimate. No implication from the old global quadratic-energy criterion to (6) is asserted. In the special case that all projected witness mass lies in a single phase, rank leaves that slot, far energy vanishes, and the surviving clocks must be in the massive sector; this illustrates why an upper bound on far energy alone is insufficient.

The new structure offers two different targets: strong true physical mass bounds in the massive sector, or a far-lag multi-witness estimate in the complementary sector. Previous CRT far-lag arguments for high labels cannot be applied to all small annulus labels without proving further distinct-label/lag constraints. No solution of the final upper contraction, and no claimed external novelty or formal verification. Main and original source branches unchanged.

## 6. Reproducible finite audit

[Standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/122ddd683910a78c8f9d368193ba1c95392391c7/research/min_unified_phase_rank_annulus_audit.mjs), commit 122ddd683910a78c8f9d368193ba1c95392391c7, exact remote content readback verified. Eight finite runs in available ECMAScript runtime, five ordinary and three focus. Reproduce:
    node research/min_unified_phase_rank_annulus_audit.mjs 256 1024 4096 16384 65536
Finite T=min(8B,floor(X/2)) ordinary or floor(B/2) focus, grids [30,210,2310], theta=.5, delta=.5. Reconstructs original completed paths, full true tick counts including terminal snapshots, continuing branch counts, and actual projected exit-slot groups. Checks slot mass equals continuing mass at predeparture, rank prefix payment and cumulative bound, total entropy upper bound, both directional cell capacities and rank union cost. For actual segments whose entropy <=.5 checks upper bound b_v<=exp(.5)n_e at both witnesses; does NOT individually enumerate common cohort intersections. Diagnostic R=q (rather than analytic 16 max(P,q)); checks rank-spacing inequality and positive stable lower bound when applicable, and an auxiliary normalized-energy bound on events where both witnesses actually have far fraction>=theta/2. The finite energy includes all rank-unpaid slots (not the extra analytic slot restriction), uses R=q, and the audit verifies a loose coefficient 36/theta; paper (5) follows with 18/theta from one-direction capacity and analytic slot restriction. The audit does not apply all previous geometric, thin, endpoint and entropy-window masks cumulatively; in particular it tests local segment stability directly, not the analytic global n_cut threshold or (6). Three artificial equally-sized phase lists check spacing arithmetic, not realized trajectories. The eight finite runs are not a proof of analytic entropy, rank, or prime-support estimates. No literal gcd oracle or Lean compilation.

| X/mode | phase groups | stable witness upper-bound checks | far-rank checks | positive rank lower bounds | positive stable lower bounds |
|---:|---:|---:|---:|---:|---:|
|256|213|260|307|0|0|
|1024|626|776|972|0|0|
|4096|3034|8954|9864|26|0|
|16384|11257|50494|56589|20|0|
|65536|43927|255408|281781|226|4|
|4096 focus|2269|2136|2575|0|0|
|16384 focus|9283|13414|15712|0|0|
|65536 focus|38635|85276|113124|85|0|

Largest ordinary: 5709 roots,140255 events, no T reaches,580232 full tick states,31435 projected event keys. Entropy10017.388091<=60799.703381,11792 rank-paid phase groups,123257 actual positive far witness incidences (across grids, repeated tags allowed), max actual far mass22, four positive stable-spacing lower bounds. Rank-paid wait summed across grids536692 (not a single union or asymptotic o(NT) result at theta=.5). The finite auxiliary normalized energy summed across grids650508.778705, qualifying clock summed across grids557855. Largest focus:2886 T reaches,75256 events,498112 tick states,29688 projected keys,38635 phase groups, entropy8950.746766, 8429 rank-paid slots,31935 positive far incidences, max far mass9. No positive stable rank lower bound in this focus diagnostic, although direct far counts occur. The large analytic radius and cutoffs are not validated numerically by these substitute values. No inference of the sufficient upper contraction.
