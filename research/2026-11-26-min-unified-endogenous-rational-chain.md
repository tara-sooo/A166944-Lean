# Integration XLV: endogenous rational chains on bounded closed excursions and graph-derived anchors

2026-11-26 JST. Parent 0c25d04cd639e861486062d63183ea66e3a96451. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). New: remove the common-anchor or bounded-rational hypothesis for bounded-length closed inventory excursions by using the actual postdeficit multipliers as rational-chain coefficients. The odd/even obstruction now concerns the entire signed capacity of a closed excursion, not just an adjacent pair. Separately, a bounded-radius rational relation graph produces a common anchor without an independent anchor hypothesis. Both results concern ORIGINAL branching transport; neither establishes the final overlap gap.

## 1. Whole-tag slack and short closed excursions

Use XLIII--XLIV notation for arbitrary retained nonreused actual last-up units above6, source and target labels >=Y>=11, original canonical tag G<=H, initial d=6. A=3G_U+4n_U-M, D=G_D-M, Delta=A/3+D+G_O=G-4M/3+4n_U/3>=0. P=max actual open inventory. TV(d-O)<=5Delta and every actual postheight <=6+5Delta+P. Select any disjoint family of complete zero-inventory excursions with at most R endpoints, fixed integer R>=2, all their labels in [Y,KY] fixed K. Other endpoints in the original population need not be comparable. Excursions are contiguous in the original retained endpoint list and closed in its actual open inventory; no skipped selected endpoints inside. Let M_R be their actual mass. No branching bound, sparsity, low-relay cutoff, local bin length, rational proximity or multiplier cap assumed.

For one such excursion Q with n<=R endpoints, let x_i be their unsigned retained masses, epsilon_i=3 for a source and -1 for a target, p_i actual labels. Define A_Q=sum_sources(3p_i+1-x_i), D_Q=sum_targets(p_i-1-x_i), nonnegative. As actual source/target masses balance in a closed excursion,
    S_Q=sum epsilon_i p_i = A_Q-D_Q-n.
In particular D_Q>=2 times the number of targets, by positive waits, and n<=R D_Q/2 because every nonempty excursion has at least one target. This fact absorbs boundary constants even if unequal source/target counts make the unadjusted whole-tag slack slightly negative. Let c_i be the odd shift of XLIII on successive actual endpoints in this excursion:
    2h_i p_i-(2h_(i+1)+sigma_(i+1))p_(i+1)=c_i,
    sigma=-3 next source, +1 next target.
For any such collection of interior transitions sum |c_i|<=5Delta+7J, with J<=sum n; the complementary intervals are disjoint and next endpoint clock corrections counted once. Define local cost
    L_Q=A_Q+D_Q+n+sum |c_i|.
Over selected bounded-length excursions, sum L_Q<= (8+4R) Delta: use A+D<=3Delta, sum n<=R D/2<=R Delta/2, and the preceding bound for c_i. This is a bound on the same original slack, not an additive independent gain.

## 2. Construct the rational chain directly from the MIN identities

If some |c_i|>=Y, then L_Q>=Y, and this excursion already costs order Y. Otherwise let a_i=2h_i and b_i=2h_(i+1)+sigma_(i+1). All a_i are strictly positive even integers, b_i strictly positive odd integers: if a_i=0 or b_i<0 the displayed adjacent identity would give |c_i|>=p_(i+1)>=Y. (b_i cannot be zero.) These are actual coefficients, not externally assumed approximants. Since p_i,p_(i+1) comparable and |c_i|<Y,
    0<a_i/b_i<=K+1.
Define B_Q=product_(i=1..n-1) b_i, and integer coefficients
    C_i=(product_(j<i) a_j)(product_(j>=i) b_j), 1<=i<=n.
Then C_1=B_Q odd, every C_i for i>1 is even, C_(i+1)/C_i=a_i/b_i. In particular their dyadic ranks strictly increase. Choose the real anchor Z=p_1/B_Q; the predicted labels Z C_i follow exactly these rational ratios. Actual errors propagate by
    p_(i+1)-Z C_(i+1)=(a_i/b_i)(p_i-Z C_i)-c_i/b_i.
Therefore max_i |p_i-Z C_i| <= (K+1)^(n-2) sum |c_i| (or the sharper individually weighted sum retaining b_i). The integer T=sum epsilon_i C_i is odd, because exactly its first coefficient is odd. Thus |Z T|>=Z>=Y/B_Q. Using closure and |epsilon_i|<=3,
    Y/B_Q <= A_Q+D_Q+n + 3n(K+1)^(n-2) sum |c_i|.       (1)
This argument needs no closeness to a common anchor before it starts. It uses the positive ODD denominators of the actual identities. It also works with large multipliers, at the price of a potentially large B_Q. For expensive excursions set B_Q=1 and use L_Q>=Y. With C=3R(K+1)^(R-2), all selected excursions satisfy Y/B_Q<=C L_Q and M_Q<= (3K+1)R Y, so
    sum_Q M_Q/B_Q <= F Delta,
    F=(3K+1) R C(8+4R).                                (2)
This weighted denominator version is useful if actual denominator products are bounded on a subpopulation, even if the absolute baseline on other parts of the tag is high. In particular if a macroscopic fraction of original transport lies in bounded-length excursions with bounded denominator products, it forces a macro slack (after the O(NH/Y) correction). No independent hypothesis on prime-ratio supports is needed.

## 3. Quantitative bound without multiplier cap

The canonical baseline/inventory inequality gives b_i<=1+(6+5Delta+P)/Y=:Q_D. Hence B_Q<=Q_D^(R-1) (also for expensive excursions), so
    M_R <= F Delta [1+(6+5Delta+P)/Y]^(R-1).             (3)
For uniform P<=K0 Y, fixed K0, put C0=7+K0 so Q_D<=C0(1+Delta/Y) for Y>=11. It follows, by splitting Delta<=Y or >Y, that
    Delta >>_(K,R,K0) min(M_R,(M_R Y^(R-1))^(1/R)).
Alternatively use M_R<=M<=G<=H and split Delta<=Y(H/Y)^(1/R) or greater to obtain the convenient linear lower
    Delta >= M_R (Y/H)^((R-1)/R) / [F(2C0)^(R-1)].
Indeed in the first case Q_D<=2C0 (H/Y)^(1/R); in the second Delta>=H (Y/H)^((R-1)/R). Sum WHOLE original tags, with M_R,all=sum M_R:
    G_all-4M_all/3 >= c_(K,R,K0) M_R,all (Y/H)^((R-1)/R)
                          - 4NH/[3(Y-1)].              (4)
Here M_all is the full ORIGINAL branching population, not the selected short mass. If M_R,all>=rho NH and Y (Y/H)^((R-1)/R)->infinity, the correction is absorbed and raw slack >> N H^(1/R)Y^((R-1)/R). At top Y~sqrt X,H~X/log^.25 X, the absorption holds for every fixed R, and this scale is N X^((R+1)/(2R))/(log X)^(1/(4R)). For R=2 it recovers the scale of XL, and for R>=3 it applies to split/merge excursions without impurity/dispersion conditions. This is submacro for Y=o(H); it is not a fixed saturation gap. At smaller Y the adjusted bound (3) is valid but (4) may be ineffective after the explicit correction. No claim that bounded P alone forces bounded n, or that macro M_R follows from small missing. Conversely if raw saturation error is little-o of the lower scale, bounded excursions contribute o(NH), under the absorption condition.

## 4. Common anchor from a bounded-radius rational graph

Separately take an entire closed excursion of arbitrary length with actual labels [Y,KY]. On its DISTINCT label set construct any undirected graph, with each oriented edge p->q certified by positive integers a,b<=D0, |ap-bq|<=W, reverse certificate b,a. Here D0 fixed, W=o(Y); edges need not be actual adjacent occurrences, provided the label arithmetic relation is true. Suppose a root p0 reaches every vertex by a path of at most r edges, fixed r (e.g. graph diameter <=r). Choose a shortest-path tree. Put Q=lcm(1,...,D0)^r and Z=p0/Q. Set C_root=Q and along a tree path define C_q=C_p a/b. All C_q are positive integers, since each path has at most r denominators dividing lcm(1,...,D0), and C_q<=Q(K+1)^r because a/b<=K+1 for W<=Y. Error propagation gives
    |p-C_p Z|<=r(K+1)^(r-1) W
at every actual label. Thus the hypotheses of XLIV hold with fixed D_*=ceil(Q(K+1)^r), W0=r(K+1)^(r-1)W. This construction does not require cycle consistency of the rational certificates: only the chosen tree and the error bound are used. It is a sufficient condition on actual support geometry, not a claim that every rational graph has bounded radius. For example a connected graph on s labels of minimum degree >=delta s, fixed delta>0, has diameter <=3/delta+3, since closed neighborhoods of every third vertex on a shortest path are disjoint. Then the bounded-radius criterion holds independent of s. If macro mass occurs on excursions with such graphs, P=O(Y), W=O(Y²/H), W=o(Y), XLIV gives a fixed positive gap for the original transport. This replaces the common anchor hypothesis with bounded rational graph connectivity; it does NOT follow merely from XXXIX's source-only local support clustering, where target labels, degree and the coefficient bounds are not established.

## 5. Diagnostics

Run node research/min_unified_endogenous_rational_chain_audit.mjs 4096 16384 65536. Extend actual original last-up extraction from XLIV, six actual prime-root runs and 48 finite threshold/bin controls, comparable Y..6Y. Whole original transport retained, no reweighting. Verify actual adjacent identities, closed signed capacities, classify expensive |c|>=Y or construct positive even/odd rational chain on actual short excursions, exact BigInt coefficient parity, propagated errors and denominator bounds. Check disjoint weighted and polynomial budgets and whole-tag linearized bound for R=2,3,4,6. Construct finite bounded-rational graphs with D0=2,4,6, W=0,1,max(2,floor(Y/8)), root radius3, verify derived integer anchor and strict-rank capacity. Count covered long excursions separately. Independent abstract chains and graph controls are not MIN paths. No analytic sieve used, no full cumulative core/kernel or Lean verification.
```json
{
  "totals": {
    "controls": 48,
    "tags": 24454,
    "edges": 41658,
    "M": 1002656,
    "endpointN": 74294,
    "transitions": 49840,
    "oddChecks": 49840,
    "baselineChecks": 882624,
    "excursions": 32421,
    "shortExc": 32346,
    "shortMass": 993050,
    "shortSplit": 6231,
    "cheap": 15404,
    "expensive": 16942,
    "chainChecks": 16738,
    "parityChecks": 15404,
    "capacityChecks": 32346,
    "denominatorChecks": 15404,
    "tagChecks": 97816,
    "graphControls": 291789,
    "graphCovered": 43396,
    "graphMass": 737580,
    "graphLabels": 89242,
    "graphEdges": 48668,
    "graphAnchorChecks": 96484,
    "graphParityChecks": 10858,
    "graphLong": 432,
    "thresholds": [
      {
        "R": 2,
        "M": 656350,
        "exc": 26007,
        "split": 0,
        "weighted": 460470.1339024473,
        "lower": 1.0801577812004481,
        "rawLower": -47049.586508885324
      },
      {
        "R": 3,
        "M": 843530,
        "exc": 30468,
        "split": 4461,
        "weighted": 589087.2053840038,
        "lower": 0.0018625590330718317,
        "rawLower": -47050.66480410748
      },
      {
        "R": 4,
        "M": 922878,
        "exc": 31706,
        "split": 5591,
        "weighted": 659795.5637475185,
        "lower": 0.000005225383820721935,
        "rawLower": -47050.66666144135
      },
      {
        "R": 6,
        "M": 993050,
        "exc": 32346,
        "split": 6231,
        "weighted": 729475.5659024371,
        "lower": 8.580927831445639e-11,
        "rawLower": -47050.66666666661
      }
    ]
  },
  "independent": {
    "cases": 1368,
    "checks": 5832,
    "graphs": 68,
    "graphLong": 68
  }
}
```
Main/direct unchanged. Next: prove macro short closed excursions or bound long positive-inventory runs, or derive a rational graph on original consumer as well as source supports. Original overlap-to-transport saturation implication and fixed NT-scale overlap gap remain open.
