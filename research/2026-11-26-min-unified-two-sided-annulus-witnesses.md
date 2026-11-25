# Two-sided multigrid clock cells and separated heavy witnesses

2026-11-26 JST. Continues [bc6e3b74bb40](https://github.com/tara-sooo/A166944-Lean/blob/bc6e3b74bb4088210cc0d550664d3a34056d6b59/research/2026-11-26-min-unified-multigrid-clock-transfer.md). Independent source heads at preflight remain prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New: a direct symmetric raw-clock support budget, without any discounted-score certificate, and an all-mass multiscale geometric trim. A surviving event either itself crosses a scale with a large label, or has two distinct heavy crossings on opposite sides, with small labels in disjoint scale annuli. This resolves duplication of *nonself* witnesses on the good scales; the large self sector is not bounded. No final upper contraction, twin-prime proof or Lean compilation.

## 1. Setup and two directions of the clock cell allocation

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, and the identical original completed MIN prefixes through first gain crossing T or original stop. Actual event e has selected odd prime p_e<=B, gain g_e=p_e-1, prehorizon C_e, posthorizon C_e+g_e, wait w_e<=2r(C_e)<=2p_e and w_e<=3g_e. Each tag has total gain G<H and total actual wait <=3H. No change to original terminal or matching. Under finitely many twins all original roots reach T eventually.

Use the M=Theta(u/ell) separated nested primorials P_j from bc6e3b7 section 1: largest even primorial <=B^(1/8) u^(4j), 0<=j<M, M=floor(u/(32 log u))+1. Uniform B^(1/8)/(C u)<=P_j<=B^(1/4), largest prime factor y_j=Theta(u), successive ratio >=u³/C. A crossing event k contains the strict boundaries K in [C_k,C_k+g_k); their number n_k>=1. Each such K is crossed at most once on a tag, and p_k>y_j (the inherited primorial barrier).

For a fixed grid, define left witness of e to be the last crossing event at or before e and right witness to be the first at or after e; a crossing event is its own witness in both directions. Missing left or right is permitted only at original endpoint portions. In each direction separately partition the events that have that witness into disjoint cells, assigning the entire actual wait of each event to its witness. The left cell starts with the crossing and ends just before the next crossing, or at original stop; the right cell ends with the crossing and starts just after the preceding crossing, or at original root. In either case the total gain of the noncrossing part is <=P. Thus the whole cell has wait <=3(g_k+P). Since n_k boundaries lie in the gain interval, g_k<=(n_k+1)P, and so the cell wait <=9P n_k. Assign it evenly across the n_k raw projected boundary atoms (K,C_k,p_k). Each original tag contributes at most 9P per atom in each direction. The initial noncrossing prefix and terminal noncrossing suffix have wait <=3P each, and all tags with no crossings have entire gain <=P. Pay the missing-witness events at cost <=6NP, counted only once.

This construction requires no admissibility classification or discarded negative deficit. It applies to all completed crossings, including old bad crossings. It is a partition in each direction, not an assertion that the two full clock ledgers can be added without factor two. Below all payments are unioned on original event incidences.

## 2. Uniform thin projected witness mask on both directions

Let n(C,p) be the actual distinct tag count of the original completed event at prehorizon C with selected label p, ignoring actual arrival/departure time. For a grid on which this event crosses, every one of its boundary keys (K,C,p) has exactly the same original tag count n(C,p). All tags executing that event cross the same boundaries. Use raw counts, not the discounted effective masses of bc6e3b7. Freeze all counts before any mask.

At fixed p>y_j and K, necessary p|(C+sigma), sigma=+/-1, and C even in [K-p+2,K] imply at most two possible C. The total candidate support is O(X/P) per p. Mark all crossing keys whose n(C,p)<=m_plain(p)=H/(p u ell²). For either directional cell allocation, the total assigned actual wait on marked keys is at most
    sum_(p>y_j) O(X/P)*9P*m_plain(p)
       = O(NT/ell),
using sum_(p<=B)1/p=O(ell). Because the counts and cap are identical across the n_k atoms, either all atoms of one crossing are marked or none. Hence pay the ENTIRE actual waits of events having a marked witness on either side, cost O(NT/ell) by summing the two directional bounds. No overshoot error and no need to use J or its L1 approximation. This does not make the final absolute clock condition easier numerically by itself, but supplies a necessary two-sided condition.

Optional stronger uniform caps for the same raw count: apply the proved support bounds in 5b56248 section 3 and 8008fbc section 4 to replace m_plain by H a(r)/(p u ell²), a(r)=log²(2+r)/(1+log log(2+r))². On p>=sqrt P replace ell² by ell, using O(1) reciprocal prime sum; on r>=(p-1)/log(2+p) replace a(r) by log²(2+p) using rough support. Taking maximum of applicable caps and unioning their budgets gives O(NT/ell) for each side uniformly in P. These are the SAME cap functions as earlier but now applied to raw counts and a two-direction whole-clock transfer, at most 9P rather than 5P/4 per atom. No implication of heavy raw mass to heavy synchronous mass or to heavy discounted mass. The theorem below already holds with the plain cap; earlier discounted-grid constraints can be retained by an additional o(NT) payment.

## 3. All-mass geometric trim averaged over scales

Write a=u^(1/4) (a different quantity from the graded function a(r) above); s=P/sqrt(a). For sufficiently large X, a>4 and adjacent P ratios exceed a² and 4 sqrt(a). We apply the following masks separately at each P, on actual original tag-event waits, with priority. This is not a change to crossing definitions when some events are paid.

(i) Missing witnesses and thin witnesses: section 1-2, cost O(NP+NT/ell).

(ii) Middle-band labels: mark the whole wait of each event whose own label, left witness label, or right witness label belongs to (P/a,aP). For a middle crossing q its two directional cell waits are at most 6(g_q+P)<=6(1+2a)g_q, since g_q>=q/2 and P<a q. An own middle label adds at most 3g_e. The bands over all P_j are disjoint; hence summing all middle-label gain over all scales and original tags is <=NH. The average cost of (ii) is O(NH a/M), not O(NH/M) since the preceding/following cell may be longer than its middle jump. This is why a=u^1/4, rather than the previous u, is used for this trim.

(iii) Large NONSELF witness: mark events e whose left or right witness is a different actual event with label q>=aP. The assigned NONCROSSING part of either directional cell has gain<=P and wait<=3P. At most NH/(aP-1) large events overall on that grid. Total O(NH/a), uniformly. This does not pay the wait of the large crossing itself.

(iv) Small SELF witness: mark all crossing events with p<=P/a. Their gain<=P/a, and the number of crossing events is <=NH/P+N, since each crosses at least one distinct boundary on that tag. Their actual wait totals O(NH/a+NP/a). No sieve or cohort cap required.

(v) Near-boundary small noncrossing events: after (ii)-(iv), a remaining noncrossing e has p<=P/a, because p>=aP would cross and all middle own labels were removed. Mark it if its prehorizon is within distance s of any multiple of P. Each such e has its full gain interval in an enlarged strip [K-s,K+s+P/a]. On one tag the intervals are disjoint in gain. Only O(H/P+1) boundaries meet the original horizon range enlarged by s+P/a. Thus the total gain of these events is O((H/P+1)(s+P/a)) per tag and the total actual wait is O(NH/sqrt(a)+NP/sqrt(a)). This also applies at the endpoints of a strip; choose weak/strict inequalities consistently (exact equality does not affect bounds).

Let h_{P,e} be the indicator of this union of paid events, and hbar_e its mean over M grids. Combining the explicit uniform and averaged budgets gives
    sum_e w_e hbar_e
       << NT(1/ell+a/M+1/sqrt(a)) + N P_max
       = O(NT/ell).
Here a/M=O(ell/u^(.75)), 1/sqrt(a)=u^(-.125), P_max=o(T/ell). No independence and no product of densities. Pay the ENTIRE wait of e when hbar_e>epsilon=ell^(-1/2); cost O(NT/sqrt(ell))=o(NT). Retained e is good (unpaid under the above grid-local masks) on >=(1-epsilon)M scales. Can also combine the earlier bc6e3b7 forward discounted witness masks and any other justified original clock masks by priority at total o(NT).

## 4. Two-sided disjoint scale annuli theorem

Fix one original retained tag-event e. On every good scale exactly one of two cases occurs:

A. SELF: e is itself a crossing, with p_e>=aP. Both witnesses equal e. Its projected count n(C_e,p_e) exceeds the applicable frozen cap. The same physical jump can be used on arbitrarily many such smaller grids. All self witnesses across scales for this event are the same jump, and the theorem does not count them as distinct.

B. NONSELF: e is not a crossing, p_e<=P/a, and there are actual different preceding and following crossings L,R with labels q_L,q_R<=P/a (and >y_j by the primorial barrier). Their raw projected counts exceed the respective caps. Each crosses exactly one boundary, because its gain <P. Denote those boundaries by K_L,K_R. Since there is no crossing between L and R, K_R=K_L+P. Moreover posthorizon of L <=C_e and posthorizon of e <=C_R. By (v), C_e lies in [K_L+s,K_R-s]. Thus
    C_e-C_L >= s,
    C_e-C_L <= P+P/a,
    C_R-C_e >= s-P/a,
    C_R-C_e <= P.
The lower bounds follow from C_L<=K_L, C_R>=K_R-(q_R-1), and the upper bounds from C_L>=K_L-(q_L-1), C_R<=K_R. In particular BOTH positive prehorizon distances lie in [P/(2 sqrt(a)),2P] for a>=4. They are actual recorded horizons on the same original tag, not inferred projected paths. The left and right witnesses are strictly before and after e in the event list.

The annuli [P_j/(2 sqrt(a)),2P_j] are disjoint for different j. Consequently all left witnesses of good nonself scales are distinct actual events, all right witnesses likewise; and left events cannot equal right events. For a fixed e, define M_large(e)=# grids with P>=a p_e, M_small(e)=# grids with P<=p_e/a. (These names refer to grid size relative to event label.) All good grids in the first set are case B, and all good grids in the second are case A. At most one grid lies strictly between the two size ranges, by the separated ratios. Therefore the number of DISTINCT nonself witnesses on e's original path is at least
    2 max(0, M_large(e)-epsilon M).
Every such witness has a heavy raw projected count and label in (y_j,P_j/a]. In particular if p_e<=P_min/a, there are at least 2(1-epsilon)M distinct heavy witnesses, half before e and half after it. This applies to ALL retained small-label events, no roughness predicate on the focal event required. For p_e>=a P_max only self case can occur; no multiplicity gain is claimed in that sector. At most one transitional scale is possible, but it is already paid by (ii).

The witness constraints include scale-localized distances, not merely a large count of possibly repeated future jumps. They do NOT require the witnesses at distinct scales to have distinct prime labels, nor do they ensure that the heavy projected tag sets intersect in a large common physical cohort. Those would be additional arithmetic/ancestry requirements. This theorem avoids claiming that multiplying the counts of heavy keys yields any upper or lower mass estimate. It also does not assert every possible trajectory admits small-label witnesses; the nonself alternatives are necessary conditions after the proved average deletion.

## 5. Remaining sufficient criterion

Let W_ann,rem be actual clock after this new o(NT) mask and optionally the previously justified original clock masks. Under finitely many twins, W_all>=N(T-6)/2 from the deficit identity and reachability, so W_ann,rem>=NT/2-o(NT). The sufficient condition remains
    liminf_(dyadic X->infinity) W_ann,rem/(NT)<1/2.
This is not a strictly weaker constant-margin liminf inequality than before, since only o(NT) is removed. Its improvement is a structural reduction to large self jumps and scale-separated pairs of heavy past/future witnesses. The multigrid carry elimination in bc6e3b7 remains valid; this direct symmetric construction needs neither the new cell slack nor any asymptotic upper estimate for carry. No proof that the residual is small, or that the large self sector or small-label two-sided sector is negligible. Main and independent source branches unchanged. No external novelty claim or Lean compilation.

## 6. Audit

[Final standalone source](https://github.com/tara-sooo/A166944-Lean/blob/a42a6dd7d8dd31e9e1f6cce0a1b8225ad09af7ec/research/min_unified_two_sided_annulus_audit.mjs), exact remote readback at a42a6dd7d8dd31e9e1f6cce0a1b8225ad09af7ec. All ten final-source runs reexecuted in available ECMAScript runtime on the remote bytes, five ordinary, three focus, two wider-grid ordinary. Reproduce:
    node research/min_unified_two_sided_annulus_audit.mjs 256 1024 4096 16384 65536
Original diagnostic grids [6,30,210], a=2, strip P/sqrt(2), count cap 2 ordinary or .5 focus, epsilon=1/3. This initial finite strip leaves NO interior nonself good events (s>P/2). It is a valid but vacuous test of annulus conclusions and is not presented as a positive exercise of case B. To exercise that case, add wider grids [30,210,2310], finite strip P/8 and independently require forward prehorizon distance>=P/8; the latter extra deletion is contained in a near-right-boundary strip of width P/8+P/a. The finite enlarged strip bound includes this extra width. These are deliberate substitute cutoffs, not asymptotic parameters. For separated-scale checks in wide tests require actual lower bound P_large/8>1.5 P_small; otherwise do not count the pair as a checked disjoint-annuli comparison. Normal T=min(8B,floor(X/2)); focus floor(B/2). The audit reconstructs original actual trajectories, both directional clock partitions/capacities, equal original tag counts across all crossed atoms, thin union budget, disjoint middle-band gains, endpoint and strip gain bounds, exact adjacent-boundary geometry, both directional distances, average whole-event mask, and distinct witnesses when finite annuli separate. No analytic sieve census, growing analytic grid family, old cumulative masks or literal gcd oracle tested. Final source includes original tests and wide tests. Some finite grids exceed B or T; large finite paid shares are NOT an asymptotic saving.

| X/mode | original W | finite paid W | remaining W | nonself annulus checks | disjoint-scale checks |
|---:|---:|---:|---:|---:|---:|
|256|2426|2426|0|0|0|
|1024|7377|6947|430|0|0|
|4096|67027|52978|14049|0|0|
|16384|385422|245409|140013|0|0|
|65536|2395330|1039528|1355802|0|0|
|4096 focus|30051|23315|6736|0|0|
|16384 focus|187263|103786|83477|0|0|
|65536 focus|1238683|477906|760777|0|0|
|16384 wide|385422|374730|10692|5103|0|
|65536 wide|2395330|2201619|193711|15710|58|

Largest standard normal: 5709 roots, 140255 events, no T reaches, 277348 directional cell capacity checks, 10225 retained event incidences. Largest focus: 2886 T reaches, 75256 events, 146322 capacity checks, 5824 retained incidences; finite .5 raw-count cap marks no nonzero count. Largest wide: 108154 directional capacity checks, 1658 retained incidences, 992 with some good nonself scale, 586 with at least two good nonself scales, 582 retained small-label incidences (p<=min grid/a), 58 checks with disjoint finite annuli, zero repeated same-side witnesses among the checked retained nonself scale pairs. The wide retained counts are finite diagnostics, not a demonstration of the required strict asymptotic clock upper bound. No Lean verification.
