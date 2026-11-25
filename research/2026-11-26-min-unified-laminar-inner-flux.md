# Laminar matched lifetimes, projected sink caps, and near-unit inner-flux Hall transport

2026-11-26 JST. Continues [746814754ac3](https://github.com/tara-sooo/A166944-Lean/blob/746814754ac332e8d30877bba22bff136f388f81/research/2026-11-26-min-unified-lifetime-rotation-pairs.md) and [2d1f1cf5e180](https://github.com/tara-sooo/A166944-Lean/blob/2d1f1cf5e180a11eff2628bfd60e2339ac9571ea/research/2026-11-26-min-unified-targeted-recycle-pairs.md). Preflight independent branch heads unchanged: prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New independent linear projected-sink payment, laminarity and exact interior targeted flux, near-unit Hall transport from long matched level charge to strictly internal original witness charge, and propagation of any previously paid small budget into long-match deletions. The previous sufficient condition is narrowed, not established. No Lean compilation.

## 1. Frozen original charge ledger

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN gain-stopped completed paths through first crossing T or original stop. Gain g=p-1<=B, w<=2r<=3g, deficit d=2t-C>=0, initial 6, total gain <H. P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1). An admissible crossing is one on p<kappa P or r>=g/u; F is P times the number of such original tag-crossings. A bad sink j has q>=kappa P, r<g/u, negative increment D_j=g_j-2w_j>0; its strict crossing count n_j satisfies P n_j<=cstar D_j. Its weight gamma_j=P n_j/D_j<=cstar; gamma_j=0 at all other negative sinks.

On each original tag use the frozen LIFO deficit stack from 2d1f1cf: push levels (d_pre,d_post] at a positive event, pop levels (d_post,d_pre] at a negative event. L_ij is the positive-length interval of levels born at i and popped at j>i, with initial stock separately indexed 0. Actual target charge c_ij=gamma_j |L_ij|, i>=1. We can combine pieces for one original (i,j); all later masks may leave fractional amounts. Sum of c_ij over each sink <=gamma_j D_j=P n_j<=cstar g_j; sum over each source <=5cstar g_i. Exact F+R_target=P n_all-I_initial, 0<=I_initial<=6cstar per tag, so under finitely many twins all tags eventually reach T and F+R_target>=NT-o(NT). The total raw ledger is O(NT) even without reachability. No trajectory or matching is changed by deletions.

## 2. Projected consumption-side thin mass payment

Group the remaining target charge at each projected sink key (A,q), prehorizon A and selected q, regardless of exit time or source. Let A_sink be that aggregate and n_eff=A_sink/(cstar q). Since each original tag visits A at most once and supplies <=cstar(q-1), n_eff is at most the distinct contributing tag count (not necessarily the full visiting cohort). For fixed q>=kappa P, the necessary congruence q|(A+tau), tau=+/-1, gives O(X/q) possible A in the original O(X) domain. Pay the entire remaining sink charge when n_eff<=m(q), where
    m_all(q)=H/(q u ell),
    m_high(q)=H/(q ell²) for q>=Q,
    m(q)=max of applicable caps.
The reciprocal prime sum over q>=kappa P is O(1), since log(kappa P)=Theta(u); the sum over Q<=q<=B is O(ell/u). These follow by dyadic prime upper bounds. Thus total cap cost in each sector is
    O(sum_q (X/q) * cstar q * m_all(q))=O(NT/ell),
    O(sum_(q>=Q) (X/q) * cstar q * m_high(q))=O(NT/ell).
The union has that same order. This applies to all targeted intervals at the sink, long or short, without the source roughness count or temporal CRT. At q comparable to B the high cap is Theta(B/(u^.25 ell²)), much larger than polylogarithmic caps for physical short-pair keys, though this is a different aggregation (projected sink rather than joint departure pair). No comparison as a pointwise refinement of the earlier physical-source caps. Both can be applied by priority.

## 3. Laminarity of matched lifetimes

For an original matched pair with positive length, its intervening gain interval is
    J_ij=[C_post,i, C_pre,j], e_ij=|J_ij|.
Its interior event indices are i<k<j, excluding both endpoints. The family of these intervals, on a single original tag, is laminar: any two are nested or have disjoint interiors. Indeed a strict crossing of indices i<k<j<l with both L_ij and L_kl nonempty is impossible. At k, some level born at i destined for j is still in the stack. Every level born at k lies strictly above that still-present level. A level born at k and destined for l would have to be popped before any level of the older source popped at j, contradicting l>j. Shared births or shared sinks allow nesting. The zero-length adjacent intervals cause no issue and will not be long sources below. This is per original tag, not a laminarity claim across different tags.

Define the RAW interior witness set W_ij as all admissible boundary flux of events strictly between i and j, plus all original targeted pair charges c_kl with i<k<l<j. A boundary atom can be each original crossing with weight P, and a pair atom the continuous level interval of weight gamma_l d lambda, or just its total charge. When using previous partial masks, split the atoms into fixed paid/unpaid portions. No copies of the same original atom. For i<k<l<j, the exact same interval L_kl is obtained if the stack is restarted at source i's poststate with its initial stock unlabelled; all levels born in the interior are labelled and popped exactly as in the full path. The local initial stock popped before the interior ends has length at most d_post,i - min_interior d. Choose any lambda in the nonempty L_ij: it survives every interior event, so min_interior d>=lambda, while d_post,i-lambda<=delta_i<=5B. Thus initial stock contributes at most 5cstar B to the local targeted score. Applying the exact flux identity to the actual interior segment gives
    e_ij-P-5cstar B <= W_ij(raw total) <= e_ij+P.             (1)
This also holds if the source/sink cohorts have distinct arrival times. For all contributors with common source departure and sink departure the actual interior suffix is deterministic; both the raw interior flux and all locally born-and-consumed witness intervals are identical. No common ancestry before the source exit is needed. Paid portions may differ across tags, so the next argument remains per-tag.

## 4. Near-unit Hall transport for ALL long source charges

Choose D=B ell² (round up), or any D/B->infinity with D<=H eventually. Consider any collection of remaining source charges from original pairs e_ij>=D. Let B0=P+5cstar B=o(D). Form a finite bipartite fractional allocation on EACH original tag: source nodes are the chosen pair charges (or remaining portions), allowed destinations are their strictly interior RAW witness atoms W_ij. Each destination has capacity K_D times its original raw weight, where
    K_D=cstar(1+B/D)/(1-B0/D)=1+o(1).                     (2)
This is an accounting transport, not an addition to the original ledger. In particular the destination atom may itself be a long targeted match, but it must be strictly inside its source.

For any subset of sources, take its maximal distinct intervening intervals. By laminarity they have disjoint interiors and every chosen source is contained in one of them. For a maximal J=[L,U] of length e, every selected nested source has its sink gain interval inside [L,U+B] (including an outer sink itself). Those actual sink gain intervals are pairwise disjoint on the original tag. By the per-sink bound on the TOTAL matched charge, the sum of selected source charges in this maximal interval is at most cstar(e+B). This bound uses the CONSUMPTION end; using source gain intervals would give factor 5 rather than 1. Each maximal interval's interior witness weight is >=e-B0 by (1); its witness atoms are disjoint from the others. Therefore any subset of sources has total demand at most
    sum_max cstar(e+B) <= K_D sum_max (e-B0)
                         <= K_D weight(union of their allowed witnesses).
This is exactly the finite fractional Hall condition, hence a feasible allocation exists by max-flow/min-cut. Fractional level endpoints pose no problem: aggregate finite atom pieces and use real-valued capacities. Summing original tags gives the same per-original-atom congestion K_D, and grouping by projected or physical keys preserves the bound on total capacity. No log(H/D) loss from overlapping nested lifetimes, no pair-energy or square of cohort mass. The coefficient tends to 1 for the stated D. This does not itself bound the total long charge, since long destination pairs may also be heavy. Do not recursively charge a destination as if its capacity were replenished at every depth.

## 5. Propagate earlier paid budgets through interior flux

A useful consequence requiring no construction of the flow: fix ANY union of previously justified paid portions in the F+R_target ledger, with total budget U_X<=beta_X NT, beta_X->0. This may include the new sink caps, previous boundary/source masks, the lifetime clipping and short-pair masks. It must be fixed before the following propagation; no circular dependence. Let W_paid(ij) be the paid weight in the RAW interior witness set. Mark for further payment every remaining pair e>=D whose W_paid(ij)>=eps e, with 0<eps<1.

On each original tag take maximal distinct intervals among the marked pairs. All marked remaining demands are bounded by sum_max cstar(e+B), as in the Hall proof. Their paid interior witnesses are disjoint and have combined weight >=eps sum_max e. Hence the total additional marked charge, summing all tags, is
    U_prop <= cstar(1+B/D) U_X/eps.                        (3)
In particular for a finite set of prior masks with beta_X=O(1/ell) (e.g. the new sink cap and the preceding O(NT/ell) charge caps), choose eps=ell^(-1/2), obtaining O(NT/sqrt(ell))=o(NT). For a general old little-o budget choose eps->0 slowly with beta_X/eps->0. The new propagation is a separate deletion of remaining source charge, not a second counting of the paid destination charge. It is applied once to the frozen old paid set; a repeated closure would need a separate budget.

Every remaining long pair now satisfies W_paid(ij)<eps e, so its interior RAW witness charge UNPAID BY THE OLD MASKS is at least
    (1-eps)e-P-5cstar B=(1-o(1))e
uniformly for e>=D=B ell². It consists only of admissible boundary flux and strictly nested targeted pair charge. This is a near-full density condition on the actual common intermediate trajectory, not merely the persistence of a deep deficit level or a small number of expensive ticks. The qualifier 'old masks' is essential; the witnesses might themselves be deleted by this new propagation. This is nontrivial even for extremely heavy cohorts and uses no root-independence assumption. If an independent uniform inner-residual contraction on long pairs were established, e.g. W_old,rem(ij)<(1-delta)e for some fixed delta>0 and all surviving e>=D, all the long charge would be payable. We have not established that contraction.

## 6. Sufficient condition and remaining obstruction

Use the parent sufficient condition liminf (F_rem+R_target,rem)/(NT)<1 along unbounded dyadic X. All the new masks in sections 2 and 5 have total o(NT) by their explicit rates. Under finitely many twins, the exact raw lower bound therefore still forces residual>=NT-o(NT). The new masks are reductions of this residual, no proof of its strict upper inequality. Long pairs e>=D now must have both a sufficiently massive projected sink and near-full old-unpaid interior flux; small or intermediate e remain in the earlier short/lifetime ledgers as appropriate. No bound on the total joint heavy boundary and heavy nested-pair occupation obtained. Acyclic strict nesting alone does not imply that iterated transport to short leaves has bounded congestion. No claim of proof or strict realized-path separation. Main and independent branches unchanged.

## 7. Audit

[Standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/09ade6be4c1f44bec5035b2953a51af86a413596/research/min_unified_laminar_flux_audit.mjs), commit 09ade6be4c1f44bec5035b2953a51af86a413596, exact remote content readback verified. Five normal and three focus runs passed in the available ECMAScript runtime. Reproduce: node research/min_unified_laminar_flux_audit.mjs 256 1024 4096 16384 65536. Same finite T, P, kappa=2, alpha=1/8, cstar=4 as parent. Finite D=max(4,floor(B/8)), not analytic D>>B; route only intervals e>=D with actual raw W>=e/2. The corresponding valid Hall capacity is K=2cstar(1+B/D), not near-unit at these finite scales. Diagnostic sink cap on aggregate charge 2cstar B normal or .12cstar B focus, boundary key (A,p) aggregate cap 2P or P (coarser than individual boundary keys; only a finite old paid set for the propagation test). eps=.25. Tests the exact targeted flux, laminar index relations, independent interior stack reset and initial-stock loss, equality of actual interior witnesses to locally reconstructed flux, innermost-first greedy fractional routing on nested destination sets, maximal-interval propagation budget. Finite diagnostic does not test analytic sieve/prime interval estimates or near-unit limiting coefficient. No prior cumulative masks or literal gcd oracle repeated.

| X/mode | long raw charge | Hall-eligible charge | routed | additional propagated charge |
|---:|---:|---:|---:|---:|
|256|0|0|0|0|
|1024|174.222222|174.222222|174.222222|0|
|4096|678.278308|678.278308|678.278308|0|
|16384|14747.810004|14341.656158|14341.656158|0|
|65536|89737.941623|88288.508428|88288.508428|0|
|4096 focus|229.329681|188.186823|188.186823|0|
|16384 focus|476.249577|476.249577|476.249577|0|
|65536 focus|15500.451330|15500.451330|15500.451330|619.065163|

Largest normal X65536: 5709 roots,140255 completed events,8069 positive target pairs,85151 laminar pair comparisons,2444 local raw flux and birth-slack checks. 2432 eligible sources,570 tags,2433 allocation edges, maximum eligible nesting count23. 408 projected bad sink keys,405 diagnostic thin, sink payment169332.986045; diagnostic boundary payment53916. No additional propagated source in this normal test. Largest focus: 2886 roots reach T,75256 events,2532 positive pairs,22772 laminar checks,768 local and Hall sources in165 tags;152 sink keys,91 thin, sink payment12827.891152; boundary payment65160. Seven previously unpaid source pairs additionally paid619.065163 by interior propagation. All 15500.451330 eligible charge routed exactly. Max observed nesting count15, max observed capacity use15.276498 times raw destination weight (finite bound72.571429). These finite values do not show a near-unit coefficient at the diagnostic scale, which is an asymptotic theorem using D/B->infinity, and do not establish the sufficient upper inequality.
