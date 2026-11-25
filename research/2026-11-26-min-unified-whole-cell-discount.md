# Whole-cell negative variation and projected word discount

2026-11-26 JST. Continues [8008fbc06831](https://github.com/tara-sooo/A166944-Lean/blob/8008fbc06831c7c4db24a77248cd2e7cde0c60c2/research/2026-11-26-min-unified-discounted-boundary-support.md) and [5b562489c22e](https://github.com/tara-sooo/A166944-Lean/blob/5b562489c22e59bf34c2d245342026d340a68437/research/2026-11-26-min-unified-short-boundary-pairs.md). Preflight independent heads unchanged: prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New discount of total negative variation of the entire cell, including noncrossing events, pointwise smaller actual and projected-word envelopes at threshold 1/4, all-mass deletion of cheap cells with small adjacent offsets, and predecessor-long trim. No full upper contraction or Lean verification.

## 1. Original cells and adaptive consumption weights

Keep X,B,u,ell,N,T,H,P,y,kappa=u^.25,kappa'=u^.125 and cstar=(1+2/kappa)/(1-4/u)=1+o(1) as in 8008fbc. Original completed gain-stopped prime-root MIN prefixes, not extended or changed. Each selected odd prime p has gain g=p-1<=B, wait w<=2r<=2p and w<=3g, deficit increment delta=2w-g, D=(-delta)_+, E=(delta-3g)_+, initial deficit6, total gain G<H. Under finitely many twins all roots eventually reach T. Strict crossing means C<=K<C+g for K multiple P; n is its count. Old admissible means p<kappa P or r>=g/u, otherwise old bad. A bad crossing has f0=P n<=cstar D. This classification is not changed.

Partition each original completed event list into disjoint consecutive blocks ("cells"): each starts immediately after the previous crossing event (or at the original start), and ends with the next crossing event k, inclusive. A terminal suffix after the last crossing is left outside the cells. Its gain is <=P, but need not be paid separately: total strict grid flux over the whole original path differs from G by at most P. Each cell has a noncrossing prefix of gain l_k<=P and last crossing of gain g_k; it may cross multiple boundaries in its last event. Define D_cell=sum of D_i over its events, including the crossing. For an admissible cell with f0=P n_k, assign consumption weight gamma_i=min(1,f0/D_cell) to every negative event in that cell, using zero if D_cell=0. For an old bad cell keep the OLD bad-crossing weight gamma_k=f0/D_k at its crossing, and zero on its prefix. All events in the terminal suffix have gamma=0. This gives 0<=gamma<=cstar, and exact discounted crossing flux f_cell=(f0-D_cell)_+ for admissible cells, zero for bad cells.

Use the same original frozen LIFO level intervals L_ij, not a new stack at each cell. The new target charge c_ij=gamma_j |L_ij| excludes initial stock, but now can have noncrossing consuming events j. Exact
    sum f_cell + R_new = P n_all - I_new,
    0<=I_new<=6cstar per original tag.
This intermediate matched ledger need not obey the old charge caps: new negative events have nonzero weight. We only apply the following specifically justified deletion and the old BOUNDARY masks on the final objective.

## 2. Transfer of the source-cell proof even for noncrossing consuming events

Any source i contributing new charge has a completed cell: its consuming event j is in a completed cell and j>i. Let k be the first crossing at or after i (its cell's last event). If k=i, it is admissible because positive drift implies r>g/4. Suppose k is old bad. Then i<k. Since all prior events in the cell have gamma=0, no consuming event j<k can have new target charge from i (it would be in that same cell). At the prestate of k the deficit exceeds source pre-deficit by at most 5P, as the intervening total gain from source prestate is <=P. The bad crossing drop is >=(1-4/u)(p_k-1)>5P eventually. Thus all source levels have been popped no later than k, so j=k necessarily. At this sink gamma is unchanged from 2d1f1cf, and matching is unchanged. Its source label <=P+1, sink label >=kappa P, intervening gain <=P. Exactly the old disparate-pair all-mass estimate (q>=ell p,e<=q/ell) pays all these charges by O(NT/ell). This is valid even though other admissible cells have new gamma weights. Remove these first-bad-cell source charges only; write R' for the rest.

For each positive source with remaining charge R'_i use E'_i=(R'_i/cstar-3g_i)_+<=E_i. The disjoint positive/negative endpoint gains give R'<=cstar(3G+sum E'_i)/4. All remaining sources belong to admissible completed cells, so sum E'_i<=sum_admissible E_cell where E_cell=sum E_i in the entire cell. The forbidden-word lemma of 5249a07 gives E_cell<=l_k+8 (prefix bound l_k+4, last E<=4). Also E_i<=4 since w<=2p. Thus the exact ledger implies, on summing tags,
    sum_admissible [f_cell+(cstar/4) E_cell]
        >= (1-3cstar/4) sum G - NP -6cstar N -O(NT/ell).
Replacing cstar by1 costs o(NT) since total E_cell=O(NH); replacing E_cell by min(l_k,E_cell) costs at most 2 per completed crossing event, whose number is <=NH/P+N. Hence the actual whole-cell objective
    A_cell = (P n_k-D_cell)_+ + min(l_k,E_cell)/4
on admissible cells, zero otherwise, has aggregate >=NT/4-o(NT) under finitely many twins. Pointwise A_cell<= previous actual discounted cell (P n_k-D_k)_++l_k/4. Use equal weights A_cell/n_k on the original crossing atoms. All previously proved boundary masks, including the last short close-label/pair/graded masks, transfer to these identical atoms with no cost increase, since the new weights are smaller. They can be retained frozen. The sufficient condition liminf A_rem/(NT)<1/4 follows.

## 3. A projected WORD upper envelope

Set Db_i=(g_i-4r_i)_+. Since w<=2r, D_i>=Db_i. Further,
    E_i=(2w_i-4g_i)_+ <=4(r_i-g_i)_+ =4 1_(r_i=p_i),
because p,r are odd primes and r<=p. Define Db_cell=sum Db_i, Eb_cell=4 # events with r_i=p_i in that cell. Then the nonnegative word-dependent objective
    W_cell=(P n_k-Db_cell)_+ + min(l_k,Eb_cell)/4
on admissible cells, zero otherwise, obeys
    A_cell <= W_cell <= old projected discounted cell.
This is computable from the actual sequence of projected horizons and selected labels, with r evaluated at each horizon. It requires no actual wait values, deficit levels or matching. It is NOT determined by only the final projected key: different original tags reaching the same key may have different preceding words. Divide equally over the same n_k boundary atoms. Every old history-free J_star mask can be used with the old comparison, up to its already proved o(NT) replacement of l_k/4 for long events. Specifically on old weak-long sector W_cell<=old projected cell, so that trim costs o(NT). On retained long events W_cell can optionally keep its extra prefix correction or drop it at aggregate O(NT/kappa'), as in 8008fbc. On short events W_cell<=old J_star pointwise. Thus the new word criterion is implied by the old history-free criterion on identical frozen masks, with the old o(NT) errors. The actual whole-cell criterion is implied by the word criterion. No strict separation on asymptotic realized paths asserted.

## 4. Adjacent cell geometry and new all-mass masks

At a cell after the first, let K be its first crossed boundary and a=K-C_pre,k its offset, 0<=a<p_k-1. Let K_prev be the LAST boundary of the previous crossing, and b=C_post,prev-K_prev its strictly positive overshoot, b<=p_prev-1. Then exactly
    K=K_prev+P,    l_k=P-a-b.
This remains true when the previous event crossed many boundaries. The first cell has no such preceding offset. Only the following masks are claimed.

(i) The first cell with short crossing p<kappa'P has weight <=P n+P/4=O(kappa'P) per original tag. Paying all such first cells costs O(N kappa'P)=o(NT). For a short crossing p<kappa'P preceded by a crossing of label q>=kappa P, pay its whole cell weight: each original large previous event has at most one next cell, and there are <=NH/(kappa P-1) such events. Total O(NT kappa'/kappa)=o(NT). For the narrower current sector p<=P (one boundary), the same proof pays previous q>=kappa'P at O(NT/kappa'). These masks use no bound on cohort mass, and the previous crossing need not be admissible. Do not apply the one-boundary estimate to all p<kappa'P with the same previous threshold kappa'P.

(ii) Take eta=ell^(-1/2), tending to zero. Consider an admissible cell after the first with p<=eta P (so n=1), preceding overshoot b<=eta P. Then a<=eta P and l>= (1-2eta)P. Write W_pre=sum actual waits of its noncrossing prefix, r_sum=sum r_i over that prefix. If W_pre<=eta P, its total negative variation D_cell>=l-2 W_pre >=(1-4eta)P. Also E_cell<=2W_pre+4<=2eta P+4. Thus A_cell <= (9/2) eta P+1. For the word objective, if 2 r_sum<=eta P then Db_cell>=l-4r_sum >=(1-4eta)P; Eb_cell<=4 r_sum+4<=2eta P+4 (each event counted by Eb has r>=3, so this is even loose). Therefore W_cell <=(9/2) eta P+1. There are <=NH/P+N cells overall, so the corresponding separate actual or word trim costs O(NT eta+NT/P+NP eta)=o(NT). This is a payment of the new objective, not of raw P per crossing. No assumption that all such cells have cheap prefixes.

After the first/previous-large masks, the remaining very short sector p<=eta P must either have preceding overshoot b>eta P (hence previous label q>eta P, but q<kappa'P), or a noncrossing prefix with actual wait >eta P for the actual ledger, or sum r>eta P/2 for the word ledger. This recovers a real waiting-density or least-factor-density constraint within the preceding cell even when the crossing itself has r bounded. If desired a stronger previous-small assumption q<=eta P ensures b<=eta P. There is no inference that every remaining cell has a comparable immediate predecessor, and no total upper bound on those residual dense-prefix/large-overshoot cells.

## 5. Sufficient conditions and limits

All new payments are O(NT/ell) or o(NT) as explicitly calculated; the old masks from 5b56248 transfer on identical original atoms. The sufficient tests liminf A_rem/(NT)<1/4 and liminf W_rem/(NT)<1/4 remain conditional on independent arithmetic upper bounds; neither has been proved. This approach does not need direct estimates of the new intermediate matched ledger except the one old bad-source deletion. It does not establish that short crossings are negligible, or that every large cohort has a cheap prefix. Main and independent branches unchanged; no external novelty claim or Lean compilation.

## 6. Finite audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/0cb95cc32c9be5aafde15582e930f7018471f288/research/min_unified_whole_cell_discount_audit.mjs), commit 0cb95cc32c9be5aafde15582e930f7018471f288, exact remote readback verified. Eight runs in ECMAScript runtime passed, five normal and three focus. Reproduce: node research/min_unified_whole_cell_discount_audit.mjs 256 1024 4096 16384 65536. First code attempt had a missing closing brace; corrected before execution and save. Finite T=min(8B,floor(X/2)) or floor(B/2), P=6 or30, kappa=2, alpha=1/8, short threshold1.5P, eta=.4. Tests exact cell partition, original LIFO with new gamma at noncrossing sinks, initial stock, first-bad-cell attribution, disjoint source/sink packing with actual per-tag maximum gamma, weighted inequality before asymptotic O(1) per-cell correction, projected-word and actual pointwise domination, adjacent offset identity and cheap-prefix bounds. Finite old-bad source deletion includes finite exceptions; no claim of o(NT) at these substitutes. The diagnostic previous-long trim uses p<1.5P and q>=1.5P, which is a fixed O(P) current range; it is not a test of the growing analytic threshold ratios. Does not apply prior cumulative masks or test analytic sieve constants or a literal gcd oracle.

| X/mode | old actual cell | new actual cell | old projected cell | new word cell |
|---:|---:|---:|---:|---:|
|256|2197.5|2144.5|2801.5|2801.5|
|1024|7235|7077|9069|9067|
|4096|65234|64265.5|80988|80977|
|16384|376305.5|372079.5|464139.5|464100.5|
|65536|2392555.5|2374056|2870743.5|2870622.5|
|4096 focus|32327.5|29630.5|37777.5|37414.5|
|16384 focus|201755.5|188258.5|232275.5|230335.5|
|65536 focus|1344557|1278810|1548101|1539135|

Largest normal: 5709 roots,140255 events, no full reaches,84315 admissible cells,17 new noncrossing matched incidences,46605 source and38166 cell packing checks. Actual reduction18499.5, word reduction121. Largest focus: 2886 full reaches,75256 events,20840 admissible cells,4417 new noncrossing matched incidences,22536 source and11855 cell packing checks,10275 adjacent offset checks. Actual reduction65747, word reduction8966. Of actual reduction43505 due to min(l,E_cell) replacement, the rest22242 due to extra negative variation. Finite short first-cell weight128291, previous-long95781, actual cheap cells373 with charge6968, word cheap cells13 with charge353. Actual and word cheap trims are separate ledgers, not additive. New matched charge284843.728971, initial17068.271029, first-bad source deletion4755.786957 (finite exception6.666667). Reached-tag finite lower bound before per-cell/cstar correction247119.361797; actual objective1028840.5 and word1233605 on reached tags. Finite values are not asymptotic estimates; no strict 1/4 upper contraction inferred.
