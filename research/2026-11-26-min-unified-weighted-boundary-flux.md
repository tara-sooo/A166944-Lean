# Weighted boundary flux and unit excess packing by forbidden small-prime words

2026-11-26 JST. Continues [c4962b2463db](https://github.com/tara-sooo/A166944-Lean/blob/c4962b2463db81e8d766bf246c584673745694fd/research/2026-11-26-min-unified-direct-leaf-boundary-flux.md) and the earlier admissible boundary sieve of 26afc6c. Independent branch heads checked unchanged at preflight: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New: unconditional local excess bound with coefficient 1 (rather than the per-event coefficient 2); transfer of this excess to admissible boundary cells after the earlier disparate-label payment; a weighted boundary-only sufficient condition with threshold 1/4; the unweighted boundary-only threshold improves from 1/6 to 1/5. The needed upper contraction remains open. No Lean compilation.

## 1. Setup

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN completed prefixes, through first gain crossing T or original stop. Each event has selected odd p<=B, gain g=p-1, wait 1<=w<=2r<=2p, deficit increment delta=2w-g, initial deficit 6, all deficits nonnegative. Total gain G<H on each tag. The two signs satisfy p|(C+sigma), sigma=-1 or +1, and exits at v=0 mod 2p for sigma=-1 or v=p+2 mod 2p for sigma=+1. Under finitely many twins all tags reach T for sufficiently large X.

Keep P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1). Strict crossing count n is the number of grid multiples K of P in [C,C+g). Admissible crossings are those with p<kappa P (sector S) or p>=kappa P and r>=g/u (sector R). All other events are bad, have negative deficit increment, and gamma=P n/(-delta)<=cstar. Other negative events have gamma=0. Let F_S,F_R be the raw admissible flux in these sectors, F=F_S+F_R, where each original crossing contributes P. Retain the frozen LIFO matching of levels from positive sources to negative sinks; target charge c_ij=gamma_j times length of levels born at i and consumed at j, excluding initial stock. The parent exact identity is F+R_target=P n_all-I_initial, where I_initial<=6cstar per tag. No actual event, trajectory, or matching is changed.

## 2. Local excess packing

For any event define E_i=(delta_i-3g_i)_+=(2w_i-4g_i)_+. By w_i<=2p_i, always 0<=E_i<=4. Thus every non-3 event has E_i<=g_i. A 3 event has g=2 and could have E=4. We improve the bound on sums of E by using the following exact forbidden selected-prime words.

* Consecutive 3,3: the first prehorizon must be 2 mod 3 (sigma=+1), since a first 3 from 1 mod 3 leads to 0 mod 3. Its posthorizon is 1 mod 3, so the next 3 has sigma=-1. First exit is 5 mod 6; the next eligible even exit is the immediately next tick, at 0 mod 6. Since the second completed event is 3, its wait is exactly 1 and E=0. Thus any 3 with E>0 cannot be preceded by 3.
* q,3,q for any odd prime q>=5: the two prehorizons of q differ by (q-1)+2=q+1. The first is +/-1 mod q, the next would be 0 or 2 mod q, neither +/-1. Impossible by eligibility, independent of time or intervening deficit.
* 5,3,7,3,5: the two prehorizons of 5 differ by 4+2+6+2=14, so the latter would be 0 or 3 mod 5, neither +/-1. Also impossible.

**Lemma.** In ANY contiguous segment of actual completed events with total gain L,
    sum E_i <= L+4.                                          (1)
Proof: pair each 3 of positive E with its immediately preceding non-3 event within the segment, except a possible first event. These pairs are disjoint by the first word rule. Partition the segment in order into these two-event blocks and singleton leftovers. A singleton other than the possible first 3 has E<=gain; a paired block (q,3) has E<=8 and gain q+1. For q>=7 this is at most the gain; the sole possible excess block is (5,3), with E<=8 and gain6, surplus<=2. Its following block, if present, cannot start with 5. If it is a singleton 3, it has E=0 and gain2. If it is a singleton q>=7, its slack gain-E>=2. If it is a paired block q>=11, its slack>=4. Each of those compensates the surplus2 of (5,3). The remaining case is the paired block (7,3), whose slack may be zero. If a further block is present, it cannot start with 5 or 7, by the two forbidden word rules. Hence it starts with a singleton 3 of E=0 or a label>=11, and supplies slack>=2. Group each (5,3) with this one- or two-block compensation when available. No grouped following block is another (5,3), so groups are disjoint. All groups except a possible incomplete final group have E<=gain. The first unpaired 3 and incomplete final group each have surplus<=2. This proves (1). The segment need not start at a root, canonical state, or boundary.

The simpler pairing argument alone gives sum E<=4L/3+4, and leads to a boundary threshold 3/16 below; the forbidden words are what strengthen the coefficient to 1 and the final threshold to 1/5. No conjecture about the frequency of small labels is used.

## 3. Attribute the surviving target-source excess to boundary cells

Use the old all-mass disparate-label deletion with rho=ell, in particular delete pairs with q>=rho p and intervening gain e<=q/rho, at cost O(NT/ell). It suffices to make the following narrower deletion. For any source i with positive target charge at sink j, consider the first event k at or after i that strictly crosses a grid boundary. It exists since sink j has gamma_j>0, and k<=j. If i crosses, positive delta implies r>g/4, so k=i is admissible eventually. If i does not cross and k is bad, all gains from source prehorizon to k's prehorizon total <=P, so the deficit can have increased by at most 5P. Bad k has drop >=(1-4/u)(p_k-1)>5P eventually. Thus every level born at i is gone at or before k; the target sink must be k. This pair has p_i<=P+1, q=p_k>=kappa P and e<=P, hence falls in the stated disparate-label mask. In particular deleting all first-bad-crossing pairs costs O(NT/ell). This is the direct source-cell argument of c4962b2, now used only for the excess. Let R' be target charge after this deletion, and R'_i the remaining total from source i. All nonzero R'_i are attributed to one admissible first crossing k.

Define
    E'_i=(R'_i/cstar-3g_i)_+
for sources, zero for other events. Then 0<=E'_i<=E_i. Let E'=sum E'_i. The positive source events and negative sink events supporting R' are disjoint. With G_s,G_t their total gains, respectively,
    R'/cstar<=3G_s+E',   R'/cstar<=G_t,   G_s+G_t<=G.
Multiply the second by 3 and add the first:
    4R'/cstar<=3G+E'.                                    (2)
This is not an assertion that raw sum E_i=o(G). It controls only the excess needed by remaining target charge.

For each admissible crossing event k of count n>=1, let l_k be the total gain of the consecutive noncrossing events immediately preceding k, back to the previous crossing (excluded) or the original start. These gains lie in one grid cell, so l_k<=P. Every source attributed to k is either one of these noncrossing events or k itself. By (1) and E_k<=4,
    sum_(i attributed to k) E'_i <= l_k+8 <= P+8.          (3)
If the noncrossing segment is empty the bound is still valid. Terminal noncrossing events with no subsequent crossing cannot have positive target charge. Summing over original tags and crossings counts each source at most once. No restriction on the cohort mass, shared ancestry, or number of consuming sinks is required.

## 4. Three increasingly relaxed boundary-only sufficient objectives

The exact target identity and (2) give, after summing original tags,
    F + (cstar/4) E' >= (1-3cstar/4) sum G - NP - 6cstar N - U_bad,   (4)
where U_bad is the first-bad matched-charge deletion O(NT/ell). This follows directly from F+R'>=sum G-NP-6cstar N-U_bad and the upper bound on R'. No terminal-deficit estimate or separate lower bound for raw E is needed.

Use (3) to replace E' by sum_(admissible k)(l_k+8). Define refined weighted boundary objective
    F_cell = sum_(admissible original tag-events k) [P n_k + l_k/4].
The O(8) per crossing error totals O(NH/P) because the count of crossing events is <=the number of grid multiples crossed, <=G/P+1 per tag; hence o(NT). Also cstar=1+o(1), all raw flux and added l-weight are O(NT), and P=o(T). Under finitely many twins sum G>=NT eventually. Thus (4) yields
    F_cell >= (1/4-o(1)) NT.
For every boundary atom of event k, use weight P+l_k/(4n_k), in [P,5P/4]. This is a purely original gain-cell quantity; it no longer uses any matching or deficit variables. Its weighted cost on any previously justified frozen boundary mask is at most 5/4 times the original flux cost. In particular the two old short/rough projected cap masks cost O(NT/ell), and all may be applied without recomputing l_k or n_k. Therefore a sufficient criterion for infinitely many twins is
    liminf_(dyadic X->infty) F_cell,rem/(NT) < 1/4.         (5)

A simpler event-count objective is F_count=F+(P/4) times the number of admissible crossing tag-events (not the number of boundaries). Distribute this additional P/4 uniformly among the n_k boundary atoms of k. It dominates F_cell pointwise and obeys the same sufficient threshold 1/4. It distinguishes one-boundary jumps from multi-boundary jumps without needing l_k.

A projected sector-only objective needs no event-history data at all. For R-sector k, p_k>=kappa P, so n_k>=g_k/P-1>=kappa-1-1/P>=kappa-2 for large X. Thus the additional cell weight over R is at most F_R/[4(kappa-2)]=o(NT). For S-sector, it is <=F_S/4. The same dominance holds on any frozen residual subset of boundary atoms, by uniform allocation. Consequently a sufficient condition is
    liminf (F_R,rem+(5/4)F_S,rem)/(NT) < 1/4.               (6)
This improves the earlier unweighted condition 1/6: in particular
    liminf F_rem/(NT) < 1/5                                (7)
implies (6), since F_R+(5/4)F_S<=5F/4. All limits use unbounded dyadic scales. The actual implication chain for the same fixed boundary masks is old 1/6 condition -> new 1/5 -> weighted sector condition (6) -> cell condition (5). The event-count condition also implies (5); (6) implies the event-count condition asymptotically by the R-sector n lower bound. No strict separation on realized MIN paths is claimed. For a subsequence with F_S,rem=o(NT) the sector criterion reduces to liminf F_R,rem/(NT)<1/4, with that extra hypothesis stated explicitly. Neither F_S,rem=o(NT) nor (6) has been proved.

For comparison, using only the preliminary 4L/3+4 estimate instead of (1) gives F_R+(4/3)F_S threshold 1/4 and hence unweighted 3/16. The final unit bound removes that intermediate loss. These boundary-only tests need neither the targeted residual upper bound nor the earlier normalized clock baseline criterion. Retain the previous sufficient routes as alternatives. There is still no independent arithmetic upper bound at the new threshold.

## 5. Numerical audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/7826ce5fb9514dfbc04916d7f866e6ce4efa8d80/research/min_unified_weighted_boundary_audit.mjs), commit 7826ce5fb9514dfbc04916d7f866e6ce4efa8d80, exact remote readback. Eight runs of the final source passed in the available ECMAScript runtime (five normal and three reach-focused); the initial preliminary 4/3 audit also passed eight. One code-update attempt had a syntax error before execution; corrected and verified final version. Reproduce:
    node research/min_unified_weighted_boundary_audit.mjs 256 1024 4096 16384 65536
Finite T=min(8B,floor(X/2)) normal or floor(B/2) focus; P=6 or 30; kappa=2, alpha=1/8. These differ from the asymptotic parameters. Uses actual per-tag gammaMax in the finite source packing and finite version of (4). All first-bad pairs are discarded for finite testing, including finite disparity exceptions; no claim of an asymptotic cost bound for the finite substitutes. Tests actual trajectories, exact consecutive 3 rule and forbidden words, independent block grouping for (1) on every noncrossing cell, exact targeted matching and first crossing assignment, disjoint source/sink capacity, effective excess<=E, sum effective excess<=P+8 per cell, and finite inequality F+gammaMax E'/4 >=(1-3gammaMax/4)G-P-I_initial-U_bad per tag. The audit also tests the coarser replacement by P+8 per admissible crossing event. The refined l_k weighted objective and analytic limiting thresholds (5)-(7) are deductions from these proved inequalities, not separately evaluated at analytic parameters. Twenty independent modular cases and six abstract block cases per run exercise the forbidden patterns and compensation, including the (5,3),(7,3) bridge. Abstract cases are not claimed realized MIN words; the reported bridge-block counts in final finite tests include those abstract cases and should not be interpreted as positive observations of that bridge in original trajectories. No cumulative prior boundary mask, analytic prime estimates, or literal gcd oracle tested.

| X/mode | gain G | F_S | F_R | raw excess E | effective excess E' |
|---:|---:|---:|---:|---:|---:|
|256|2844|894|1866|194|0|
|1024|9434|2736|6204|418|6|
|4096|84476|17946|62292|2884|52|
|16384|503474|79740|384402|13646|889.179786|
|65536|3088970|334842|2538300|52318|3387.785135|
|4096 focus|38344|24420|12180|1300|10|
|16384 focus|232780|112110|113820|5864|90|
|65536 focus|1588558|513660|1005780|27402|1227.826087|

Largest normal: 5709 roots,140255 events, no roots reach diagnostic T,5106 consecutive 3 checks,43135 original forbidden-word checks,86031 noncrossing cell checks,7548 source excess checks,1307 positive effective excess sources. R_target202728.986045, first-bad removal2591.111478, R'200137.874566. Effective excess S2713.831449, R673.953687, total3387.785135. Actual-gamma weighted inequality aggregate left1871433.395218 <= right2874089.476691, P+8 replacement3015873.480471. Largest focus: 2886 roots reach T,75256 events,3591 consecutive 3 checks,21654 forbidden-word checks,21223 cell checks,3752 paired positive-3 occurrences inside cells,2092 source checks,429 positive effective sources. R_target54700.323711, first-bad removal4755.786957, finite disparity exception6.666667; no earlier bad crossing followed by a later consuming sink observed in either mode. Effective excess1227.826087, of which1089.826087 S and138 R. The reached-tag aggregate weighted lower bound1064941.391012 <= actual weighted objective1220589.556503. Of the block counts, 1047 compensated groups and1963 incomplete terminal groups include abstract cases. Finite gain/flux ratios do not establish the asymptotic sufficient upper inequality. No twin-prime proof or Lean verification; main and original independent branches unchanged by this task.
