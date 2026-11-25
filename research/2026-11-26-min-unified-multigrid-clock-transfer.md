# Multi-primorial overshoot averaging and discounted-boundary-to-clock transfer

2026-11-26 JST. Continues [12292f36c699](https://github.com/tara-sooo/A166944-Lean/blob/12292f36c699af543b201c65fbd32c697aa7639d/research/2026-11-26-min-unified-cell-slack-transport.md), using the projected support/caps of [5b562489c22e](https://github.com/tara-sooo/A166944-Lean/blob/5b562489c22e59bf34c2d245342026d340a68437/research/2026-11-26-min-unified-short-boundary-pairs.md) and [8008fbc06831](https://github.com/tara-sooo/A166944-Lean/blob/8008fbc06831c7c4db24a77248cd2e7cde0c60c2/research/2026-11-26-min-unified-discounted-boundary-support.md). Preflight independent source heads unchanged: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New: eliminate the entire overshoot term by selecting or averaging separated primorials, prove an L1 equivalence with half-clock at this averaged scale (so mere carry elimination is not a new asymptotic contraction), transfer discounted boundary deletions back to actual wait incidences, and simultaneously impose heavy boundary witnesses on most primorial scales for every surviving original event. No complete proof or Lean compilation.

## 1. Fixed ensemble, variable grids

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. The original MIN prime-root gain-stopped completed paths are unchanged, G<H and W<=3G per tag. Under finitely many twins all original tags eventually reach T. Each event label p has gain g=p-1 and wait w<=2r<=2p, D=(g-2w)_+, E=(2w-4g)_+. Original deficits nonnegative starting6.

Instead of one P, take
    M=floor(u/(32 log u))+1,
    P_j=largest even primorial <= B^(1/8) u^(4j),
    j=0,...,M-1.
All formulas for sufficiently large X. P_j<=B^(1/4), and P_j>=B^(1/8)/(C u) uniformly for an absolute C, since the largest factor and the next prime factor are O(u), by elementary Chebyshev theta and Bertrand. Their largest prime factors y_j=Theta(u) uniformly. Adjacent P ratio >=u^3/C>u^2, since the underlying size ratio is u^4. Thus the M=Theta(u/ell) middle bands (P_j/u,u P_j) are disjoint. There are no duplicate grids eventually. The selection uses only original ensemble and allowed primorial scales, not a changed path or new root. The old kappa=u^.25,cstar=(1+2/kappa)/(1-4/u)=1+o(1) are common to all grids. Every bound used below is uniform for P in this interval.

For each P, split each original path into cells, each ending at its next strict crossing event k (possibly multiple boundaries), and an uncompleted terminal suffix. A cell is admissible if its last label p<kappa P or r>=g/u. Otherwise it is bad. Define total cell gain G_k, wait W_k, negative variation D_k, excess E_k and noncrossing prefix gain l_k<=P. If n_k boundaries crossed let f0_k=P n_k. From 12292f36 on admissible cells
    A_k=(f0_k-D_k)_+ + min(l_k,E_k)/4,
    L_k=[max(f0_k,D_k)-G_k+W_k/2]_+,
    J_k=min(A_k,L_k).
On bad cells and uncompleted terminal suffix set J_k=0. The previous theorem applies to each grid uniformly: sum J_k>=NT/4-o(NT) under finitely many twins. In particular its first-bad-cell source payment O(NT/ell) uses kappa>>ell and P->infinity uniformly, and all previous O(NH/P+NP) errors are uniform. For each admissible k, L_k<=A_k+2. The original event lists, not just labels, are shared by all grids.

## 2. Averaging raw overshoot decreases

Define b_k as posthorizon minus LAST boundary crossed; 0<b_k<=min(P,g_last,k). Define virtual b_0=C_origin-(P ceil(C_origin/P)-P) in (0,P]. Exact f0_k-G_k=b_(k-1)-b_k holds including the first cell and multiple crossings. Define RAW variation down(P)=sum_(tags,k) (b_(k-1)-b_k)_+ and up(P)=sum (b_k-b_(k-1))_+, including BAD cells. The previous carry beta_k=(J_k-W_k/2)_+ is at most each down step, but we need the stronger raw variation, not just actual beta. Telescoping gives up(P)<=down(P)+NP.

For each grid, virtual initial carries total <=NP. The other down steps are indexed injectively per tag by their preceding actual crossing events; each contributes <=min(P,g_prev). Split preceding selected q into three bands:
* q<=P/u: each down step <=P/u and number <=NH/P+N. Total O(NH/u+NP/u).
* q>=uP: count <=NH/(uP-1), each contributes <=P. Total O(NH/u).
* P/u<q<uP: bound by the entire gain of the preceding event. Across all grids, these middle bands are disjoint, so an original event's gain is used at most once, whether or not it crosses on different grids. Total summed middle gain <=NH.
Summing and dividing by M gives
    mean_j down(P_j) <= O(N P_max + NH/u + NH/M)
                     = O(NT ell/u),                    (1)
since P_max<=B^.25=o(T ell/u). Also mean up(P_j)=O(NT ell/u). No hypothesis of noncoalescence, no cohort size or sieve used. In particular select any minimizer P_* of down(P) to have both directions and all carries O(NT ell/u). This selection is an allowed adaptive sufficient condition, not a claim that the previously fixed P has small carry. Moreover at most O(M/sqrt(M)) grids can have down>NH/sqrt(M) up to a constant, by Markov. Thus a 1-o(1) fraction has little-o carry. One can use the mean without selecting any grid. This resolves the separate narrow-band carry upper-bound problem for the adaptive or averaged family; its old graded cap is not needed here.

## 3. An L1 half-clock equivalence, and its limitation

For an admissible cell, the identity f0-G=bprev-b and D<=G imply
    W_k/2-(b_k-bprev)_+-2 <= J_k <= W_k/2+(bprev-b_k)_+.
The lower bound uses L>=W/2+bprev-b and J>=L-2, not a lower bound on all earlier scores. Thus |J-W/2|<=down_k+up_k+2. For bad cells the wait is <=3P+2g_last/u; their number <=NH/(kappa P-1), so total bad wait O(NH/kappa+NH/u), uniformly. Terminal suffix gain <=P and wait<=3P. Number of completed cells <=NH/P+N. Consequently if E_abs(P) includes ALL cells and suffixes, with J=0 on bad/tail,
    E_abs(P)=sum |J_k-W_k/2|
      <= down(P)+up(P)+O(NH/P+N+NH/kappa+NH/u+NP).
Combining with (1),
    mean E_abs(P_j)=O(NT(ell/u+1/kappa))=o(NT).           (2)
The same bound holds for P_* chosen above. The original half-clock allocation omega=min(J,W/2) uniformly across its actual ticks, zero on bad/tail, has pointwise <=1/2 coefficient and total L1 difference from half of all actual waits <=E_abs. The carry beta<=down. This proves equivalence of the averaged (or selected) unmasked score and half actual wait, up to o(NT), on every original ensemble without the no-twins hypothesis.

IMPORTANT: Simply replacing the previous objective by this carry-free clock criterion does NOT yield an independent strict asymptotic upper contraction. With identical fixed clock masks, their constant-margin liminf inequalities are equivalent. In particular one cannot claim the finite objective reductions observed in 12292f36 prove a smaller asymptotic clock than half of actual waits. Nor is a pointwise minimum of scores over grids justified by lower bounds on each total. We use arithmetic masks on different grids to obtain a new necessary multiscale structural constraint on remaining events, not a proof of the baseline.

## 4. Transfer discounted boundary payments back to full actual cell waits

For each grid P choose any frozen boundary mask of discounted J atom weights whose total paid score U(P) is independently bounded. Divide J_k evenly across its n_k strict crossing atoms. Each per-tag atom weight <=5P/4 since J<=A. Take h_k in [0,1] to be fraction of these equal atoms paid (including fractional portions), and set h=1 on bad, terminal, and J=0 cells. This latter convention costs no J. For every completed event e in cell k use this SAME h_{P,e}=h_k on each original occupied tick of e. Then
    h_k W_k <= 2 h_k J_k + 2 (W_k/2-J_k)_+,
so the transferred fractional clock payment satisfies exactly
    sum_(tag,e) h_{P,e} w_e <= 2 U(P)+2 E_abs(P).          (3)
Unlike simply transporting raw boundary counts at a constant cost, this uses the DISCOUNTED weights, including partial and even zero-score cells. It recovers a whole preceding cell's waiting time, not just the last jump's wait. All h values are frozen on original cells; no recomputation of matching or actual evolution. No duplication of weights within a grid.

An explicit uniform mask suffices. At projected key (K,C,p), p>y_j, fixed p,K have at most two possible even C in [K-p+2,K] via p|(C+sigma). Thus O(X/P) possible keys at p. Aggregate original J atom weight A_key, effective mass A_key/(5P/4), no greater than actual distinct tag count. Pay an entire key if effective mass <=H/(p u ell²). The total paid score is
    O(XH/(u ell²) sum_(p>y_j)1/p)=O(NT/ell)
uniformly. Optionally also use all applicable graded, rough, narrow range, and close-label cap masks with uniform proofs, by union. In particular the tail bound of 5b56248 uses progression length >=cB^.75 and log y=Theta(ell), both uniform here; the bound sum_C a(r)=O(X/P) supplies the graded cap H a(r)/(p u ell²), and rough support supplies the stronger log² p cap where applicable. The first-order simple mask alone is sufficient for the following theorem; additional masks require their own uniform o(NT) budget. The thresholds may be applied to the raw J aggregate before any other mask, so every positive unmasked atom belongs to a projected key with effective mass above the relevant cap.

## 5. Multi-scale actual-clock deletion and a necessary heavy-witness condition

Define for each original completed tag-event
    hbar_e = (1/M) sum_j h_(P_j,e).
By (2),(3) and the uniform bound on U,
    sum_(tag,e) w_e hbar_e = O(NT/ell).
This is an actual clock bound on fractional coverage, not the union of M payments. Take epsilon=ell^-1/2 and pay the ENTIRE actual wait of every event with hbar_e>epsilon. Markov gives
    W_multigrid_paid <= O(NT/(epsilon ell))
                     = O(NT/sqrt(ell))=o(NT).           (4)
The deletion can be combined with any earlier actual-clock masks by priority. All retained events satisfy hbar_e<=epsilon. At most 2 epsilon M grids have h_(P_j,e)>1/2. Hence for EVERY retained original tag-event, at least (1-2epsilon)M primorial scales have an actual admissible, positive-score completed cell containing it, whose at least half crossing atoms by equal allocation are unmasked. Each such atom belongs to a projected boundary key with effective mass greater than H/(p u ell²) (and any stronger applicable frozen cap used there). Thus the original tag-event has simultaneous heavy projected boundary witnesses on almost all of a growing number of separated scales. For any such grid the cell is actual, with final crossing no earlier than the focal event, and the gain distance from focal prehorizon to crossing prehorizon <=P; final crossing itself has gain<=B. These witnesses are not asserted to be distinct actual crossing events across scales, and projected effective mass need not be physical synchronous mass. Root and terminal cells, zero J, and bad cells are included automatically in coverage; for a retained event the good-grid condition excludes them only when they were actually assigned h=1 (root cells are allowed if positive and admissible). This is not a product or independence assumption.

The original clock sufficient inequality, after this and other justified linear masks, is liminf W_rem/(NT)<1/2, or equivalently half-clock threshold1/4. Indeed under finitely many twins W_all>=N(T-6)/2 by the deficit identity; (4) and old o(NT) masks leave that lower bound up to o. This is also equivalent to the selected or averaged carry-free actual score criterion with the same fixed clock mask, by (2). The new contribution is the uniform per-event multi-scale heavy-witness condition after a single o(NT) deletion. It is NOT a new strictly weaker constant-margin inequality: an o(NT) payment does not change such a liminf. No proof of an upper estimate on simultaneous heavy witnesses is given. In particular the same long jump may witness many grids, or a single huge coalesced cohort may persist across all of them. Need further arithmetic/ancestry control of that sector. Main and independent source branches unchanged; no novelty claim or Lean compilation.

## 6. Reproducible audit

[Standalone source](https://github.com/tara-sooo/A166944-Lean/blob/20dfa06d8213cc0f7b10e1ab34a3d9580f14546e/research/min_unified_multigrid_clock_transfer_audit.mjs), commit 20dfa06d8213cc0f7b10e1ab34a3d9580f14546e, exact remote readback. Eight runs (five normal, three focus) passed in ECMAScript runtime. Reproduce:
    node research/min_unified_multigrid_clock_transfer_audit.mjs 256 1024 4096 16384 65536
Finite fixed Ps=[6,30,210], eta=.5, large cutoff2P, disjoint bands (P/2,2P), kappa=2, old bad r<g/8, T=min(8B,floor(X/2)) or floor(B/2), diagnostic mass cap 2 normal or .5 focus, epsilon=.35. Some P exceed diagnostic T or B; they are deliberately finite substitute grids, NOT analytic P_j. Checks original geometry, strict primorial barrier, exact cell overshoot even on first and multi-boundary cells, both raw variation directions, per-tag disjoint middle gain packing, L1 score bounds including bad/tail, exact weighted coverage, key cap aggregation, fractional clock transfer, Markov whole-event deletion, retained-event many-good-grid property. No repeated LIFO test, analytic sieve estimates, growing grid census, literal gcd oracle, or cumulative historical masks. The inherited LIFO certificate and forbidden-word estimate come from earlier audits/proofs. No finite claim of small average E_abs at these grids (root and tail can dominate).

| X/mode | actual W | mean fractional covered wait | full wait paid by coverage >.35 | remaining actual wait |
|---:|---:|---:|---:|---:|
|256|2426|1809.666667|2066|360|
|1024|7377|5405|5539|1838|
|4096|67027|31217|28722|38305|
|16384|385422|153290.666667|139434|245988|
|65536|2395330|766109.666667|703728|1691602|
|4096 focus|30051|12397.333333|10069|19982|
|16384 focus|187263|51818|38125|149138|
|65536 focus|1238683|234348|174962|1063721|

Largest normal: 5709 roots,140255 completed events, no T reaches,138674 grid cell/score checks,5709 disjoint gain checks,140255 coverage checks. Per-grid raw down (51900,209356,591208), up (55960,191236,334832); middle gain (255158,444622,860080), sum below actual G3088970. Per-grid J (1181243,1210674,1382288.5), abs error (114052,399198,997285.5), discounted key payments (306064.5,310467.5,354870), transferred fractional waits (651057,743583,903689). 60810 event incidences paid in whole;79445 retained-event witness checks,200679 good-grid incidences. Largest focus:2886 T reaches,75256 events,73161 cell checks,53240 retained-event witness checks,135177 good-grid incidences. Raw down (27634,110810,341300), up (31988,99316,156080). The finite coverage trim may be large; analytic o(NT) comes from (1)-(4), not from these finite rates. No inference of the required strict clock upper inequality.
