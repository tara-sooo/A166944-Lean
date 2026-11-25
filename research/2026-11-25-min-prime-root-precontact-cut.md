# Directed medium multi-anchor ranks and arithmetic precontact crossing cuts

2026-11-25 JST. Continuation of d31bbf0f901c4391d6782af60b59a12d9f922c23 on the selected prime-root branch. Implements its previously paper-only directed medium rank theorem. New precontact crossing-cut theorem excludes entire high pair products and individual directed medium pair charges by ranks at an earlier common gain level, with a uniform actual thin-crossing-cohort criterion. Same outgoing label across that cut forces opposite arithmetic sides and gives an aggregate product quota. These bounds apply to full original histories with disjoint earlier projected prefixes, but do not control all thick cohorts or prove twin infinitude. No Lean compilation.

## 1. Ensemble and directed medium rank implementation

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime starts M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu. Original gain-stopped MIN histories include actual terminal vertices. Each completed gain p-1 is <=B, total G_M<H, actual wait <=2r<=3(p-1). Natural high list I and actual retained reference J as in d31bbf0. Actual medium charge ledger has directed charges at a common later projected horizon E, with inherited endpoint bound C0(P/Q)^1/8 b_M(E)/m_g, m_g=u^4.75/ell^4. The E-plus-LOW blocks of each focal M are disjoint. For a directed pair with first projected contact C*, every charged E>=C*, so its whole remaining directed charge satisfies
    w_med(M->M') <= C1 [C_end(M)-C*]/m_g.
The partner's gain is not used in this bound. The two directions can differ in size and are retained separately even when both attach to the same unordered-pair flow node. Never-physical-meeting is a property of the entire pair.

Use the conserved multi-anchor measure a_M(v) from d31bbf0, with total <=N(H+B). At a first projected contact C* put
    m_M(C*)=floor(m_g u^(-.25) a_M(C*)/[C_end(M)-C*]),
with zero cap for zero remaining gain. On the complete original projected tag list, admit partners by source rank distance <=m or absolute reverse-Kraft complexity rank <=m. Directed degree <=3m. The sum of all admitted directed costs is O(NT/u^.25), by the focal gain bound and conservation. Pay only admitting orientations; a successful test on one side need not pay the other. This is the preceding paper's medium analogue, now implemented. The high multi-anchor rank deletion is unchanged. Re-run the previous extended quota flow on the nonnegative pair weights that remain after these absolute exclusions.

## 2. First contact and a preceding aligned gain cut

Fix an integer d>=1, d<=H, and the fixed absolute grid d Z. For a pair's FIRST common original projected horizon C*, set
    x=d floor((C*-1)/d).
Then x<C*, 1<=C*-x<=d. Let the smaller and larger sources be M<M'. If x>=2M'-2, both original trajectories cross x on a UNIQUE completed edge with pre-horizon A<=x and post-horizon D=A+p-1>x. This includes a crossing whose post-horizon is exactly C*: both roots visit C*, so both crossing post-horizons are <=C*. No extended trajectory, physical-time alignment or extrapolation beyond the original stop. When x<2M'-2, call the pair shallow for this grid and make no cut estimate for it. In particular contact at the larger root's initial horizon is shallow. Choosing x strictly below C* is sufficient; a buffer of B before C* is unnecessary.

For any eligible pair, their crossing pre-horizons are distinct, since both are strictly before C*. Their post-horizons either differ or are BOTH C*. A pre-horizon of one cannot be the post-horizon of the other at the same cut, since they lie on opposite sides of x. Therefore any repeated projected endpoint strictly below C* is impossible; equal landing at C* with distinct incoming labels is allowed. These restrictions are on the true first contact of the full paths, even when earlier accounting masks have removed all occupation at some common states.

At a fixed x, each original crossing edge is labeled by (A,p), or equivalently (D,p). An incoming p to D must divide D or D+2. Since D is even, its residues mod 2p are 0 or -2. Also D lies in (x,x+p-1]. Each side contributes at most one candidate D; there are at most two distinct crossing edges of label p. If both exist, their D values differ exactly 2, since the other possible difference 2p-2 exceeds the interval length. This is an arithmetic bound, independent of actual MIN eligibility and ancestry. For p=3 there cannot be two such slots at the same x.

Thus if an actual first-contact pair crosses x with the SAME selected p, it uses the two opposite-side slots, has distinct pre and post horizons at distance 2, and its post-arrival ticks differ by at least p-2 (the two period-2p clock progressions 0 and p+2). In particular it cannot already have physically merged on this crossing. This remains true if later common landing or physical merger occurs on a different edge. Different labels can land together at C* and are not subject to the same-label bound.

The full crossing list V_x consists of all ORIGINAL root tags crossing x, including those with no charged later event. Each root has at most 1+H/d memberships in the grid, up to harmless rounding. Hence
    sum_x |V_x| <= N(1+ceil(H/d)).
For medium use also the same fixed source cells as in the original medium ledger, with V_x split by source cell. This partitions membership and creates no factor equal to the number of cells. No new gain is charged at x.

## 3. Crossing-cohort rank tests and uniform thin-cohort theorem

For each full V_x (or each source-cell sublist for medium), order source tags by source M and form disjoint cohorts by outgoing label p or exact crossing edge (A,p). Let a_x be the number of occupied edge cohorts. By section 2,
    a_x <= 2 pi(B) = O(B/u).
Let Y0=max(5,floor(u²)), and let a_x^small be the number of occupied edge cohorts with p<=Y0. Then a_x^small <=2 pi(Y0)=O(u²/ell). These are bounds on number of cohorts, not their root populations.

For a directed focal tag a at a cut, let m be a nonnegative integer. Exclude self and any candidate sharing its pre-horizon. Admit a partner b if any of the following holds:
  1. source rank distance in the full list <=m;
  2. same outgoing label, relative source rank in that label cohort <=m;
  3. relative source rank in the partner's exact edge cohort <=floor(m/a_x);
  4. partner outgoing p<=Y0 and relative source rank in its edge cohort <=floor(m/a_x^small);
  5. partner edge has either pre- or post-horizon within a fixed distance 2 of the corresponding focal endpoint; relative source rank in partner edge cohort <=floor(m/a_near), where a_near counts all occupied nearby edge cohorts for this focal edge.
An empty set has no admitted partners. Relative rank counts source tags between the focal source and partner, including partner and excluding focal; the focal need not belong to that cohort. A cap c admits at most 2c partners in one cohort. Therefore the combined directed degree is <=10m. In particular the nearby test has no factor for the number of distinct outgoing labels at a nearby pre-horizon. No minimum positive cap or requirement of disjoint source cells for high. The arithmetic exclusion of equal pre-horizon cannot remove an actual first-contact pair at x.

Take d=floor(H/u²) with min1 for asymptotically large X, and
    m_high=floor(B u^1.5 d/H),
    m_med=floor(m_g u^(-.25) d/H).
High: assign each eligible pair to its one x. If either orientation passes, pay its entire retained ordered high pair weight (<=3H). The number of eligible pairs admitted is at most 10 m_high sum_x |V_x|, so
    E_pre <= O(H m_high NH/d)=O(NH B u^1.5)=O(F/u^.25)=o(F).
This is valid for arbitrary retained incidence holes, async or sync, and long after first contact. No use of occupation density along the earlier history.

Medium: charge an actual directed pair only when that focal orientation passes at its own assigned x, in the original fixed cell. Its whole charge is O(H/m_g) from section 1, hence
    W_pre <= O((H/m_g) m_med NH/d)=O(NT/u^.25)=o(NT).
All allocations at later E remain as originally computed; this is a whole-directed-pair accounting mask, not a new partner allocation. The same construction works for any d<=H with the stated scaled rank caps (zero possible at very fine grids); a bounded number of grids incurs constant-factor cost, or weight their caps with a summable mixture.

Actual thin-cohort corollary: For the asymptotic d above, m_high~B/u^.5, so uniformly over every occupied cut list the cap floor(m_high/a_x) is >=c sqrt(u) eventually for some absolute c>0. If either actual crossing edge cohort of an eligible first-contact pair has mass <=c sqrt(u), the entire high pair weight is paid (orient toward that cohort). There is no restriction on the other cohort mass. In the medium cell list, m_med~u^2.5/ell^4, so floor(m_med/a_x^small)>=c' u^.5/ell³ eventually. If the PARTNER's actual crossing cohort has p<=Y0 and mass <=c' u^.5/ell³, its incoming directed charge from the other source is paid, regardless of the focal cohort mass. The opposite directed charge requires its own condition. Hence surviving cut-eligible high pairs require two thick crossing cohorts; surviving medium directions with small partner p require a thick partner cohort. These are restrictions on actual precontact ancestor memberships, not merely candidate arithmetic support counts. They do not control shallow pairs, or pairs with both thick cohorts. The exact occupied counts in the caps may permit much larger cohorts than these uniform lower bounds.

## 4. Same-label crossing product and additional quota

At x and p, let A_(x,p), B_(x,p) be the two actual opposite-side crossing source sets, empty when a slot is unoccupied. An eligible first-contact pair using that same label must lie in their cross product. The sets are disjoint because a root has one crossing at x. The whole retained high weight of all such pairs assigned to (x,p) is <=3H |A_(x,p)||B_(x,p)|. One may instead bound it by the sum of twice the minima of remaining retained high tails from the crossing pre-horizons, which are original vertices preceding C*. Medium directed weight is bounded by C1 H/m_g times the number of directed eligible pairs in the same source cell. These are upper envelopes; many product pairs may share some other earlier horizon or have a different assigned cut.

Use the prior A_med=NT/(X u^.25), A_high=F/(X u^.25). Give the optional same-label key (x,p) capacity A d u/B in either metric. There are O(X/d+1) possible grid cuts in the horizon strip and O(B/u) primes. Their total capacity is O(X A) because d<=H=O(X). For any group with aggregate actual weight below its capacity, this can pay every residual weight of that group without any individual root-rank hypothesis. A sufficient high raw-product threshold is floor(A_high d u/(3HB)), of order d u^1.5 for the asymptotic ensemble; not a claim that every product is this small. No multiplicity for C* or subsequent shared states is used.

Add this optional key to the existing extended contact/anchor key network, only when actual pair crosses the chosen x with equal p. At most six eligible keys; exact cut formula unchanged. Sum of all quotas still O(XA), regardless of assignment of weights to keys. Apply rank masks first, then reoptimize both flows. The old feasible flow restricted to survivors remains feasible, so neither absolute mask nor additional key increases the optimal total residual. Relative absorption errors and previous linear deletions remain as in d31bbf0.

## 5. Finite audit

Standalone research/min_prime_root_precontact_cut_audit.mjs, final source commit 8edd696ffbc4db27cc4f03b8beb42018c360a259, blob 06090f36413bcfa7cc024835f8685223a07afbcd, exact readback.
    node research/min_prime_root_precontact_cut_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_precontact_cut_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in available ECMAScript runtime, not separate Node process. Initial 14 runs used x=d floor((C*-B-1)/d) (strict earlier landing); only15 eligible normal pairs at largest X and no incremental payment. Replaced this unnecessarily restrictive buffer by the immediately preceding cut and allowed common landing at C*. Six subsequent normal/combined runs at X16384,65536,262144, then final18 runs (analytic/concurrent/combined nine-stress across six X) all passed. Final independent arithmetic slot oracle enumerates two residues mod 2p and checks every occupied slot, including eight additional fixed aligned control cuts when not already queried. Independent linear scan for original crossing edges on up to128 queried pairs; exact original membership bound, disjoint prior endpoints, common landing only at C*, same-label slot gap and clock lag, directed medium aggregation, full-list degree checks at queried focal tags, thin group implication, cross-product bound, rank-first flow input partition and mincut equality. Finite medium ratios to asymptotic envelope are diagnostics only; at largest normal max(w*m_g/Grem)=1.204813. Numerical tolerances for fractional flow/log/redistribution. No Lean compilation. Analytic earlier residuals empty at these scales; the added control cuts check arithmetic slots even there.

Normal finite choices d=floor(B/8), m_high=m_med=4, medium multi-anchor coefficient32, Y0=max(5,floor(B^.125)); combined stress d=floor(B/4), caps12/16, medium coefficient128, same finite Y0 rule. Analytic d=floor(H/u²), caps as above, Y0=floor(u²) with min5. Fixed depth mixture1,4,16 inherited. These diagnostics intentionally use smaller rank caps and different gain lengths than asymptotic analytic configuration; no convergence inference. High remains the isolated natural ledger of preceding audits, not the full cumulative hybrid.

|X|old normal medium|after directed multi-anchor rank flow|final precontact medium|old rank-reoptimized high|final precontact high|
|--:|--:|--:|--:|--:|--:|
|4096|0|0|0|0|0|
|16384|28.823997|23.470425|10.772642|0|0|
|65536|12.320120|8.320120|8.320120|89130.165658|75532.838631|
|262144|14.492289|11.195993|10.716343|1516624.869605|1427011.695034|

Largest normal X262144: previous never10.136986659333 ->6.840690363037 after directed medium rank flow ->6.361040332402 final. Full directed rank deletion before quotas5.243386243386 in19 orientations; new crossing mask deletes0.740740740741 medium before reoptimization. High crossing mask deletes271059 from pre-quota ledger after previous multi-anchor rank mask, overlapping prior quota payments; optimal final high residual decreases by89613.174571, NOT by271059. Async remains0. Of3078 queried remaining pairs,2280 cut-eligible,798 shallow including31 contacts at larger root start;5 same outgoing p in one same-label key (cross product36),68 mixed-label common landings. Full-list membership3457 (includes7 extra control cuts),549 occupied slots vs18800 relaxed arithmetic slots, all independently verified;1874 focal degree checks (global and cell);6 high and102 small-medium thin implications checked, counted as orientation occurrences, not necessarily positive paid weights. New high final cut866 keys, medium77. High priority raw mask amounts by tests1..5:0,0,40169,157381,73509. No claim that individual key quota allocations or these raw mask weights equal incremental residual reduction.

Largest combined nine-stress: previous high47744.864415->17567.384278, async0, high cut28 keys. Medium previous0 remains zero up to floating rounding7.1e-15 (not positive mathematical residual). 313 eligible,185 shallow, no same-label or common landing in this stress sample. 678 memberships with8 controls,93 actual vs3236 relaxed slots,228 degree checks,80 high thin implications. At X65536 stress both final residuals zero. Full crossing rank raw payment may be nonzero even when prior optimized residual was zero, due to overlap with old quota payments.

## 6. Remaining problem

The directed actual medium theorem is now implemented. Earlier crossing geometry gives a uniform thin-population deletion for eligible first-contact pairs and makes same-label products explicit. At the largest normal scale many residual pairs are still shallow for a single grid (and all thick groups remain possible); a hierarchy of cuts with controlled membership budget or a different short-prefix argument may help, but repeated rank masks do not prove actual thick-cohort mass control. A useful next target is an upper bound for cross-products of thick actual crossing groups having disjoint original projected prefixes, possibly using multiple cuts, arithmetic side restrictions and actual source-start distributions. The two joint little-o estimates on a common unbounded dyadic sequence remain OPEN. Main and independent branches unchanged.
