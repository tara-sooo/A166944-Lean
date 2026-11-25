# Multi-anchor gain redistribution, first-contact ranks, and prefix-conflict tail moments

2026-11-25 JST. Continuation of 9cff2d2c07e585cf17c423b3bcb348cf7440ec39 on the user-selected prime-root branch. A mass-conserving redistribution of each actual original anchor gain over multiple later LOW blocks gives a direct whole-pair exclusion at the first projected contact, including when the recent incoming label is tiny. Unlike adding another quota family, the new rank deletion can remove a specified entire pair contribution. The cut envelope is sharpened by multi-block prefix disjointness, the two-sided natural age cap, retained tails and a weighted witness moment inequality. No bound on unrestricted origin basins or twin-prime proof; no Lean compilation.

## 1. Original anchors and a conserved gain measure

Retain dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, F=T²Bu. Original prime-root MIN gain prefixes (including actual terminal vertices) unchanged. Each completed gain is p-1, total G_M<H, actual wait <=2r<=3(p-1). Use the independent LOW partition of 9cff2d2, threshold y, L=2 product of odd primes<=y. Every root has a sequence of disjoint ordered blocks A_(M,0),...,A_(M,n_M-1) of its actual original vertices, each starting at its initial vertex or its most recent completed non-LOW poststate. Each block contains at most L/2+1 original vertices. Use g_(M,i)=B for initial and q-1 for a noninitial anchor with incoming q>y. Then
    sum_(M,i) g_(M,i) <= G+NB <= N(H+B).
This includes terminal singleton blocks and all accounting-deleted vertices. No new transitions or path extensions.

For an integer k>=1 let U_(M,i,k) be the UNION of blocks i,...,min(i+k-1,n_M-1) on this same original root, with size n_(M,i,k)>0. Distribute the weight g_(M,i) uniformly over this actual union, assigning weight g_(M,i)/n_(M,i,k) to each member. More generally use any nonnegative fixed mixture theta_k with sum theta_k<=1 (even a growing finite number of scales). Define
    a_M(v) = sum_(i,k: v in U_(M,i,k)) theta_k g_(M,i)/n_(M,i,k).
Finite summation gives the exact budget
    sum_(M,v) a_M(v)
       = (sum_k theta_k) sum_(M,i) g_(M,i) <= N(H+B).    (1)
The same conclusion holds for arbitrary nonnegative distributions of each anchor weight of total at most g, even source-specific, provided they are frozen from the original histories before pair payment. The uniform truncated-block construction is the one audited. In particular taking k large does NOT pay a multiplicative kL factor, because every gain is divided by the actual number of recipients. For each vertex a_M can contain weight from many previous non-LOW selections, not only its latest anchor; it can be large even if its latest selected label is small. This redistributes accounting mass only; it is not elapsed physical clock and does not change the original actual medium allocation.

## 2. Directed first-contact ranks with tail-adaptive caps

At each projected horizon C use the FULL original source tag list V(C), including terminal tags and all earlier accounting holes. Every root visits C at most once. Sort by source M. Also sort by the full original reverse complexity kappa_M(C), then by M. The earlier projected first-contact Kraft lemma applies with the independent LOW threshold:
    kappa_M(C)=L product_(nonLOW events with posthorizon D<=C) [L d_y(D)],
    sum_(M in V(C)) 1/kappa_M(C) <=1,
where d_y(D) counts eligible odd incoming candidate labels >y dividing D(D+2), truncated at B. Indeed reverse from C, select its true even LOW offset from L/2 possibilities with probability 2/L, then either stop at its root with probability 1/2 or continue with probability 1/2 and uniform candidate label. Positive labels strictly decrease the horizon; each actual root identifies a distinct leaf. The resulting weight is exactly 1/kappa. This includes root+LOW paths and terminal snapshots, with d_y>=1 for every actual nonLOW transition. The finite audit sorts logarithms and verifies the Kraft sum at queried horizons. The mathematical order may use exact integer kappa, with deterministic ties. Nothing in the rank-degree bound requires the Kraft estimate, but it explains which low-complexity histories the order captures.

Fix the natural high list I as before. Let J be the actual retained high incidence set after the prior LINEAR deletions and density gate; alternatively use a frozen larger reference set containing every later retained incidence, and then keep that reference for all rank tests. For an actual original vertex at C, let
    R^J_M(C)=sum_(D>=C) r(D) 1_{(M,D) in J}.
This is a tail on the original root, not an extra ancestry mass. For any two roots M,M' with first common projected horizon C*, their entire retained ordered high pair weight, including arbitrary earlier absolute accounting holes, satisfies
    w_high(M,M') <= 2 min(R^J_M(C*), R^J_M'(C*)).
It includes all later synchronous and asynchronous recontacts. No time-order or same-tail assumption.

Take lambda=B u^1.5. At a focal tag M at C set
    m_M(C)=floor(lambda a_M(C)/(2 R^J_M(C))) if R^J_M(C)>0,
             0 otherwise.
Do not force a minimum positive cap. A focal zero tail cannot have a positive high pair weight. Admit another tag if either its relative source-rank distance in V(C) is <=m_M(C), or its absolute position in the increasing kappa order of V(C) is among the first m_M(C) (one-based). The directed degree, excluding self, is <=3m_M(C), no matter how large the actual earlier groups are. Every partner with kappa<=m_M(C) is included in the second test by Kraft. Additional orders with the same rank cap could be included at a constant-factor cost, but the two just described suffice.

Pay a whole retained high pair if either orientation is admitted AT ITS FIRST projected contact in the full original lists. Charge the pair to one admitting focal vertex; summing directed bounds even if both admit is safe. By the fixed tail bound and (1),
    E_multi <= sum_(M,C) 2 R^J_M(C) * 3m_M(C)
            <= 3 lambda sum_(M,C) a_M(C)
            = O(NH B u^1.5)
            = O(T² B u^.75) = o(F).                     (2)
This covers complete pair weight, not just current occupation or a fractional quota. The test can pay deep/deep pairs if the source ranks are close or the partner has a small complexity rank compared with the gain redistributed from multiple earlier anchor blocks. Relative source rank is in the full original projected list at the first contact, not a rank in a residual subset or an order of physical meetings. A rank can be large even at a small absolute source separation and vice versa. No assertion that all partners are low-rank.

The choice of mixture is flexible: fixed k=1,4,16 with theta=1/3 used in the finite audit; a growing sequence of depths is allowed by (1) with total mixture weight <=1. If one earlier large selected gain is spread across many vertices it becomes proportionally weaker, rather than creating unlimited capacity. For a pair not paid by (2), both orientations fail their corresponding source and complexity rank tests, or have zero cap. Unlike the previous gain-weighted per-source anchor quota (which can pay fractional charge), (2) selects entire pair products by explicit ranks and a reference tail.

### Directed actual medium analogue (paper only)

For a directed medium pair allocation M -> M' let C* be its first common original horizon. Every charged later medium E is >=C*, and the actual E-plus-LOW blocks of the focal M are disjoint. The inherited normalized endpoint bound (P/Q)^1/8 C0 b_M(E)/m_g, m_g=u^(19/4)/ell^4, yields
    w_med(M -> M') <= C1 Grem_M(C*)/m_g,
where Grem_M(C)=C_end(M)-C and C1 is an absolute constant. This holds for both directions separately and arbitrary previous fractional masks. At C* use
    m_med,M(C)=floor(m_g u^(-.25) a_M(C)/Grem_M(C))
when Grem>0, else zero. The same directed rank tests then pay every remaining directed charge with that focal orientation at total cost O(NT/u^.25) by (1). The partner's possibly much longer remaining trajectory cannot be charged to the focal tail. One may pay both directions of a pair only if each direction independently passes a valid test. The present audit keeps the previous medium flow unchanged; this additional directed medium result is not numerically audited. No assumption that the caps are positive for a large fraction of pairs.

## 3. Multi-block prefix incompatibility

Retain the extended cut keys of 9cff2d2: one original projected first-contact key, optional physical first-meeting key, compressed anchor-pair key, and both actual source-anchor keys at first contact. For any key subset S, the local LOW masks give a candidate envelope for W(S), ignoring optional physical key, earlier masks, and undetected prior contacts. For each candidate block pair with nonempty intersection let C0 be the least common LOCAL horizon in the two current blocks. Its incoming labels are reconstructed from previous bits or anchor labels; reject equal labels, apply earlier-anchor exclusion and require the corresponding projected/compressed and both tag keys in S. Distinct roots only; for medium additionally the same fixed original source cell. These are inherited filters.

For depth k>=1, let P_(M,k)(C0) be all original horizons STRICTLY below C0 in the current block and the previous k-1 blocks of that root (or all available blocks if fewer). Define P_(M,infty)(C0) to be its entire original prefix strictly below C0. As k grows these sets are nested. Every actual first-contact pair satisfies
    P_(M,k)(C*) intersect P_(M',k)(C*) = empty
for every k, including infinity. Thus reject a local candidate if that intersection is nonempty. This includes common prior horizons with neither equal to the two current anchors; the earlier-anchor exclusion alone misses such witnesses. No physical-time comparison required. A finite depth rejection is a necessary filter only, not proof of global first contact when it passes. At infinite depth a local candidate passing this test has exact global first projected contact C0; it can still have the wrong optional physical key, not be charged at all, or fail prior residual masks. Candidate counts can have multiplicities across different anchor pairs before exact filtering. Full original membership is used, never residual-only membership.

This is a structural constraint on actual ancestor histories. It does not claim that all thick incoming sets have overlapping prefixes: very large sets with disjoint earlier projected trajectories may remain. One may group by the current masks and prefix signatures at multiple depths to evaluate the envelope without individually traversing pairs. The finite audit uses two sorted original lists per candidate for the prefix witness test, for depths 2,4,8,16,infinity.

## 4. Sharper high tail envelope using already-paid shared clock and actual retained tails

The earlier source-distance-adaptive age test of 7e53c0f trims a pair at a natural high shared horizon if its earlier or later natural shared clock is less than K_j, where K_j is determined by its original source separation band j. This cap is frozen on FULL natural shared lists, not recomputed after holes. Let R^I_M(C0) denote full natural high tail at a candidate first contact C0 and R^J_M(C0) the retained tail from section 2. If any high pair product remains after the age test, its first remaining shared horizon has at least K_j natural shared weight strictly before it; its last remaining shared horizon has at least K_j strictly after it. These two disjoint sets of excluded or earlier/later natural hits are contained in the full natural shared list, which starts no earlier than C0 for a true first contact. The total surviving ordered weight therefore satisfies
    w_high <= 2 max(0,min(R^I_M(C0),R^I_M'(C0))-2K_j).
The bound is also true for a zero remaining pair. Do not subtract K_j from each retained tail separately: the excluded hits can already have been removed by the linear masks. Combine independent bounds by a MINIMUM:
    V(M,M';C0) =
       2 min(R^J_M(C0),R^J_M'(C0),
              max(0,min(R^I_M(C0),R^I_M'(C0))-2K_j)).
For all actual pairs internal to S, w_high<=V; ignore physical-key or other prior rank masks when evaluating the candidate upper sum, which only increases it. With any prefix depth k including infinity,
    W_high(S) <= sum_(filtered candidate occurrences) V.
Likewise W_med(S)<=O(H/m_g) times the filtered count, using the inherited directed pair bound in both directions. A sharper paper-only medium envelope uses the sum of the two remaining original gains divided by m_g. These are bounds on the ACTUAL cut weights, not identities equating them to the candidate products. The high cap is valid on an arbitrary subset of pair products obeying the prior age and retained-incidence masks; later absolute or quota payments cannot increase the weight.

The upper sum can be evaluated through a tail layer integral: within a fixed source-separation band j and current mask-pair stratum, C0 and K_j are fixed. Define each side's effective tail rho_M=min(R^J_M(C0), max(0,R^I_M(C0)-2K_j)). Then V=2 min(rho_M,rho_M'), so sums of V equal twice the integral of counts of eligible pairs with both rho>=x. Source-separation, distinct-source, cut-key and prefix conditions still apply; they must not silently be dropped when claiming equality. Dropping a necessary condition gives only an upper bound. This formulation allows ordered source-cell and tail-layer estimates without direct pair traversal.

## 5. Weighted prior-witness moment bound

Fix any collection of candidate occurrences after the single-block filters and cut-key conditions, and choose depth k. For each occurrence e=(M,M',C0,anchor pair) let
    Z_e = |P_(M,k)(C0) intersect P_(M',k)(C0)|.
Use nonnegative weight v_e=1 for counts, or V from section 4 for high. Let
    M0=sum_e v_e, M1=sum_e v_e Z_e, M2=sum_e v_e Z_e².
Cauchy-Schwarz on the measure v_e restricted to Z_e>0 gives
    sum_(e:Z_e>0) v_e >= M1²/M2   (M2>0).
If M2=0 the lower bound is 0. Thus the surviving candidate envelope is at most M0-M1²/M2, and is exactly M0-sum_(Z_e>0) v_e if the latter is evaluated directly. This is valid even when the original pair occurs more than once among candidate products. It needs no independence of prime factors, no randomness of projected paths, and no assumption of small individual masses.

For a fixed mask-pair stratum and hence fixed C0, M1 is a sum over common earlier horizon witnesses h<C0 of the weight of the eligible pairs whose two prefix sets contain h. M2 is the analogous sum over ORDERED pairs of witnesses (h,h'), including h=h'. Each term restricts each side's actual source set by one or two earlier visits. For counts, with no extra cross-side constraints, terms are the products of the two restricted group sizes (excluding identical source tags). With source cells, separation filters or earlier-anchor exclusion one must use the appropriate restricted pair counts, and with V one uses the tail layer formula of section 4 in each separation band. Partitioning into disjoint strata before applying the inequality can strengthen the bound: the summed ratio lower bounds are at least the global ratio by Cauchy again. This gives a specific alternative sufficient target for arithmetic work on joint earlier ancestry: obtain enough first witness moment relative to the second. It is not a proved limiting lower bound for this ratio. In particular all candidates with disjoint actual prefixes have Z=0, so the method cannot remove such pairs by prefix collisions alone.

## 6. Combining the absolute rank deletion with the joint quota flow

The new rank mask of section 2 acts on arbitrary retained high pair weights independent of the previous extended quota capacities. If applied after an already feasible flow, only count its unpaid fraction as additional removal. Alternatively remove its entire eligible pair weights FIRST, then run the same extended maximum flow on the remaining nonnegative pair ledger. Restricting the previous feasible flow to surviving pairs remains feasible, so this reoptimization cannot have a larger total residual than merely removing eligible unpaid fractions. Quota capacity on removed pairs can be reassigned. The absolute energy paid by the new mask is bounded by (2), and total quota payments by the previous O(F/u^.25); no double subtraction. The cut formula of 9cff2d2 then holds for the remaining pair weights. The sharper witness/tail envelope also applies to this new cut, but the finite audit computes its detailed envelope for the PRE-rank extended cut in order to make direct comparisons with 9cff2d2.

The preceding relative recent-sync/exit-imbalance terms remain relative on the actual retained energy. Linear-deletion costs and their removed quadratic products are not interchanged. Joint sufficient conditions remain the two little-o residual bounds on a common unbounded dyadic sequence. This paper does not establish them.

## 7. Reproducible finite audit

Standalone research/min_prime_root_multi_anchor_audit.mjs, final source commit 7aae65a0cbf821eb65f64342b7bbc2ab6e9c863c, blob ece237489920d03348570c3226ed0094dc0b9efd, exact remote readback.
    node research/min_prime_root_multi_anchor_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_multi_anchor_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in available ECMAScript runtime, not separate Node process. Initial 14 successful runs: analytic/concurrent at four X256..16384, then normal concurrent, combined eight-stress and analytic at X65536/262144. Final version adds independent range-difference redistribution, weighted witness moments and reoptimized flow; all18 final runs (three configurations at six X) passed. Other final modes not rerun. Prior canonical MIN and all accounting assertions retained. Independent exact original source weight sums; direct distribution vs difference-array range update checked at every original vertex; Kraft sum and full original rank degree at queried high first-contact horizons; retained tail upper bound on every positive residual pair; actual extended intersection flow unpaid fractions; rank deletion followed by reoptimized maxflow/mincut, no-worse check. For old extended cuts, enumerate candidate products from full anchor memberships, check nested prefix witness counts, inclusion of all actual cut pairs after full prefix exclusion and combined age/retained upper bound per actual pair and summed cut. Verify weighted moment lower bounds and exact count partition. Floating arithmetic for redistribution, logs, quotas and moments with tolerances, integer original vertex/pair counts exact. No Lean compilation.

Finite mixture k=1,4,16 equal weights; diagnostic lambda=B/8 normal, B/2 combined stress; analytic lambda=B u^1.5. Independent LOW normal y=5,L30, stress y=7,L210, analytic y=3,L6, unchanged from previous audit. These are chosen diagnostic thresholds; all tested analytic retained residuals were already empty before the new rank test (but full redistribution and existing controls nonempty). The high ledger is the same isolated natural high diagnostic with previous direct/window/reverse/age/stability/recent-sync and quota masks, not the full cumulative hybrid. Medium pair flow unchanged in this audit.

| X | old extended normal high residual | post-flow rank deletion remainder | rank-first reoptimized remainder |
|--:|--:|--:|--:|
|4096|0|0|0|
|16384|0|0|0|
|65536|91139.394603|89130.165658|89130.165658|
|262144|2182677.858517|1650639.209077|1516624.869605|

Largest normal X262144: conserved total mass45826490 over633075 original vertices, independent redistribution checks633075. Full queried projected rank degree checks10113, max58, weighted degree sum130570702, within bound. Whole additional absolute rank classifier on the PRE-quota isolated high ledger covers5301986; this overlaps earlier quota payments, so the post-flow incremental deletion is532038.649440 (async11135.624157), of which244208.911843 is covered by the mixture but NOT by either orientation under the single k=1 budget alone. Source-rank-only payment56423.660198; complexity-rank-only374234.872216; rest both. Post-flow residual1650639.209077 with async1732.422364. Rank-first joint reoptimization reduces to1516624.869605 (async0), new cut914 keys, internal weight2436905, quota920280.130395. Combined stress old271034.239168 ->55225.328102 post-flow ->47744.864415 reoptimized (async0); rank classifier on pre-quota isolated ledger covers3439231, post-flow incremental215808.911066 (119762.467798 not single-block-covered); new cut29 keys, weight124824, quota77079.135585. These finite caps need not be small asymptotically at tested X.

Old extended normal largest high cut: actual2977 unordered pairs, internal weight3805133. Old local envelope3719 candidate occurrences, full natural tail sum14244770. Results with depth:
| depth | medium candidate occurrences | high candidate occurrences | full natural high tail envelope | combined age/retained envelope |
|--:|--:|--:|--:|--:|
|2|158|3712|14209686|8740336|
|4|158|3643|13875628|8473334|
|8|158|3616|13774296|8393712|
|16|158|3547|13553986|8205816|
|all|150|3521|13476140|8169116|

All2977 actual high and129 actual medium internal pairs survived every prefix test. Prefix tests19015, conflicting candidate occurrences206 across both metrics (with overlap if a candidate qualifies for both). High full-prefix moment totals M1=1464028,M2=4638156 using combined tail weights, actual eliminated combined weight597008, moment lower bound462118.562805. Medium full-prefix witnesses M1=28,M2=148, actual8 eliminated, moment lower bound5.297297. This is diagnostic evidence of nontrivial prior contacts that the single-block masks missed, not an asymptotic estimate of moments. Combined stress old high cut522 candidates ->510, full natural tail1660280->1627904, combined envelope930748, actual old internal weight644133. High moment lower bound15850.536301 vs actual prior-conflict weight16500. The envelope is still larger than actual cut weight; it is not a solution of the mass problem.

## 8. Next proof target

Several prior non-LOW blocks now contribute to first-contact rank admission with one conserved original gain budget. The cut envelope also uses actual prefix conflicts instead of merely counts of candidate keys. A next substantive step is to bound the tail-layer products of the two actual origin sets with disjoint earlier projected prefixes, particularly where both source/complexity ranks are large and retained natural tails remain long. The witness moments can be estimated by actual one- and two-horizon membership intersections; mere counting of relaxed arithmetic keys does not give them. The full-prefix filter does not remove true first-contact pairs, so an actual mass or dynamical restriction is necessary for those. The joint actual medium o(NT) and high o(F) targets remain OPEN; no proof of twin-prime infinitude. Main and independent branches unchanged.
