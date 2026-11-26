# Integration XLIII: adjacent endpoint odd-rational obstruction on the original branching transport

2026-11-26 JST. Parent b76421ee8946ebc19dc01a97355a2e2de0b0b916. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). New: apply the MIN odd-shift constraint to consecutive actual retained ENDPOINTS, regardless of whether they are matched to each other or even have opposite signs. This removes the need to prune or round the original edge weights for this particular arithmetic obstruction. The price is a hypothesis on the number of adjacent endpoint label ratios close to a rational with both numerator and denominator odd. It includes a common narrow band at odd multiples of an anchor. This is not forced by XXXIX's source-only clusters. No final overlap gap.

## 1. General endpoint budget, not a pair budget

Work on one WHOLE canonical tag, initial ordinary deficit 6, gain G<=H. Arbitrary retained nonreused actual last-up height units above 6, endpoint labels at least Y>=11. M total mass, x_j signed endpoint total (+ outgoing source mass, - incoming consumer mass, 0 otherwise), open inventory O=sum of signed increments, P=max O. At every cut O>=0 and O<=max(0,d-6), initial/final O=0. No restriction on split/merge, endpoint counts, comparability or bins. Write n_U,n_D for distinct actual source/target counts, G_U,G_D their actual gains, G_O=G-G_U-G_D. Define
    A=3G_U+4 n_U-M, D=G_D-M,
    Delta=A/3+D+G_O=G-4M/3+4 n_U/3.
All three components nonnegative. At a source of label p and wait w, the rise u=3p+1-2a with a=2p-w>=0. At a target of label r and wait w, fall v=r-1-2w. Since outgoing/incoming masses <=actual rise/fall,
    sum_sources 2a<=A, sum_targets 2w<=D.
Residual b=d-O has exact increments (u-x) at sources, (|x|-v) at targets and physical change elsewhere. Thus TV(b)<=A+D+5G_O<=5Delta and all actual postheights d'<=6+5Delta+P. This uses the actual original initial state, not free entry height in each bin. Unlike XLI unique-endpoint pairs, n_U may differ from n_D, so do NOT use Delta0>=Delta/3 for the unadjusted slack G-4M/3. Instead retain the explicit correction 4 n_U/3<=4G/[3(Y-1)]. No re-pairing, no branching or dispersion penalty.

## 2. Exact odd-shift identity for any adjacent selected endpoints

List ALL actual endpoints of the retained transport in chronological order on this tag, including across zero-inventory cuts and bins. Take two successive ones i,j, labels p,q and ordinary postdeficits 2hp+6I, 2kq+6J, respectively. Let E be the actual gain strictly between them and B=d_j-d'_i the signed intervening deficit change. All intervening events are complementary (not endpoints of this population), so |B|<=5E and the intervals are disjoint across successive endpoint transitions. Let sigma=-3 if j is a source, +1 if j is a target. Define clock correction v=2(2q-w_j) in the source case, -2w_j in the target case. The actual preheight at j is
    d_j=(2k+sigma)q+6J-1+v.
Hence the exact odd identity
    2hp-(2k+sigma)q=c=6(J-I)-1+v-B,
    |c|<=5E+|v|+7.
For ANY subset of J0 such transitions, sum|c|<=5G_O+A+D+7J0<=5Delta+7J0. The positive waits and actual competing-clock bound w<=2q justify these formulas. This holds for source-source, source-target, target-source and target-target transitions. It does not claim that source and target are actual matched partners.

Suppose there are positive ODD integers a,b<=D_* and |ell|=|a p-b q|<=W on a chosen transition. They may be selected adaptively and independently for each transition; no need to use the same rational or to have reduced fractions. Multiply the preceding identity by a and subtract 2h ell:
    [2h b-(2k+sigma)a]q=a c-2h ell.
The bracket is odd nonzero even if k=0 or sigma=-3. Consequently
    Y<=q<=D_* |c|+2h W.
This is the odd-rational obstruction. For even numerator or denominator one cannot apply this argument indiscriminately; in particular if a is even the bracket is even and can be zero. We use only the both-odd class, which is invariant under reversing a rational approximation. (Actually odd a alone is sufficient in the displayed direction.) The coefficients must be small for the quantitative lower to be useful. No upper bound on actual multipliers used except d'_i<=6+5Delta+P, p>=Y, so 2h<=(6+5Delta+P)/Y.

## 3. Exact loss bound and macro consequence

Let J0 be the number of selected adjacent transitions satisfying the above odd-rational hypothesis with fixed D_*,W>=0. Sum the obstruction with the actual complementary budget:
    Y J0 <= D_* (5Delta+7J0) + (W J0/Y)(6+5Delta+P).
Therefore
    Delta >= J0 [Y-7D_*-W(6+P)/Y]_+ / [5(D_*+WJ0/Y)].       (1)
For J0=0 the bound is zero. This is a direct inequality on the ORIGINAL transport, independent of its edge impurity, with no weighted arc relay charged twice. If Y>=28D_* and W(6+P)<=Y²/4, the simpler lower is
    Delta >= Y J0/[10(D_*+WJ0/Y)]
          >= (1/20) min(Y J0/D_*,Y²/W),                     (2)
with the second argument interpreted as infinity for W=0. In particular adjacent identical labels (a=b=1,W=0) cost a fixed multiple of Y each, even if their endpoints have the SAME sign or are not linked by any edge. This does not contradict an isolated high same-label source and consumer separated by a distinct selected endpoint.

Now sum on original tags i, G_i<=H. Suppose P_i<=K0Y uniformly, D_* fixed, W=o(Y), and Y->infinity. Then the hypotheses of (2) hold eventually. Since J_i<=number of endpoints<=H/(Y-1),
    sum Delta_i >= (Y sum J_i/20) min(1/D_*,Y(Y-1)/(WH)).
Writing total M and G_all and using sum n_U<=NH/(Y-1):
    G_all-4M/3 >= (Y sum J_i/20) min(1/D_*,Y(Y-1)/(WH))
                     -4NH/[3(Y-1)].                         (3)
If Y sum J_i>=rho1 NH, rho1>0 fixed, this gives a fixed positive fraction of NH whenever W=O(Y²/H) and W=o(Y), with no source/consumer support condition or one-to-one approximation. More generally if WH/Y²=o(Y), the correction is absorbed and the lower has order NH min(1,Y²/(WH)). For W=0 it gives a fixed loss. In the top-scale canonical Y~sqrt X,H~X/log^.25 X, the macro sufficient width is W=O(log^.25 X), not X^.3. At W~(Y²/L)log^gamma Y with L=X^.7 and fixed D_*, (3) gives a conditional lower of order N L/log^gamma Y, because the correction O(NH/Y) is smaller. It is submacroscopic. More generally one may retain variable D_* in (1)-(3), provided Y>=28D_* and the positive correction remains negligible. For instance D_* a fixed power of logY produces an additional polylog loss at most, not a uniform constant. No assertion that the target width or count J_i is forced.

## 4. Common odd-multiple cluster corollary and relation to earlier work

On each zero-inventory excursion of the original transport, take any anchor Z>0 and suppose every actual endpoint label p there lies within W0 of c_p Z for some positive odd integer c_p<=D_* (not necessarily the same coefficient at every occurrence). This includes a source cluster at Z and target cluster at 3Z, or multiple odd-multiple clusters. For consecutive endpoints within the excursion take a=c_q,b=c_p; determinant |a p-b q|<=2D_* W0, hence they all satisfy the criterion of section2. If the endpoint labels there are also <=KY, the actual total mass M_exc in that excursion is <=(3KY+1) times the number of source endpoints. Every nonzero excursion has at least two endpoints, so #adjacent transitions inside >= half its endpoint count, and in fact >=number of sources. Consequently Y sum J_i>= sum_good M_exc/(3K+1/Y). If such excursions carry macro mass, section3 applies with W=2D_* W0, regardless of branching or edge impurity. There is no charge for transitions between excursions in this sufficient condition. The adjacent list still comes from the original whole tag, so omitted outside endpoints cannot be silently skipped and charged as complementary gain; we count only transitions that really are consecutive in that list.

Under a common width O(Y²/H), this proves a fixed gap, whereas XLII's grid lemma required dispersion o(N sqrt(HY)) to transfer its submacro inverse-height loss. These are different width/structure assumptions; the new result is not a general strengthening at every width. It avoids any re-pairing and does not need to compare original and virtual transport. At wider clusters the bound can be only submacro, or vacuous if the determinant width and inventory are too large. It does not follow from XXXIX that adjacent ORIGINAL endpoints satisfy the odd-ratio condition: XXXIX concerned consecutive selected UPWARD sources of an ordered direct population, not adjacent endpoints of arbitrary split/merge transport, and allowed even coefficients. It also did not force concentration of consumers. Neither a large J_i nor a macro original transport at near saturation is presently forced from the overlap ledger.

Small correction to XLII section1: for R_a=sum[2(x-a)_+ +(a-x)_+], the minimizing quantile is the **2/3 quantile**, not the 1/3 quantile (derivative #x<a minus twice #x>a). The grid guarantee for any a and finite median audit are unchanged. This correction does not change any preceding inequality.

## 5. Finite diagnostics

Run node research/min_unified_adjacent_odd_ratio_audit.mjs 4096 16384 65536. Same six actual prime-root runs and 48 finite threshold/bin controls. Generate actual last-up edges with endpoint labels Y..6Y and same-bin restriction, retain every edge without pruning or altering weights. Verify general endpoint capacities, whole-tag residual variation, actual signed odd relation at every adjacent selected endpoint of all four sign types, disjoint complementary gain, and odd rational determinant identity for finite D_*=1,3,5 and W=0,2,floor(Y/4). Check exact bound (1), simplified bound when its finite hypotheses hold, and complete good-excursion count. Count original branching as well. Finite controls not intended to realize asymptotic saturation or macro odd-rational transition hypotheses. No analytic sieve used, full core/kernel rerun or Lean verification.
```json
{
  "controls": 48,
  "tags": 24454,
  "edges": 41658,
  "M": 1002656,
  "endpointN": 74294,
  "sourceN": 35288,
  "targetN": 39006,
  "splitSources": 5204,
  "mergeTargets": 2495,
  "transitions": 49840,
  "upUp": 2248,
  "upDown": 33040,
  "downUp": 8586,
  "downDown": 5966,
  "oddChecks": 49840,
  "baselineChecks": 882624,
  "excursions": 32421,
  "excursionChecks": 24493,
  "relationChecks": 46369,
  "relationBoundChecks": 191274,
  "nontrivialBounds": 10021,
  "sameLabel": 1261,
  "oddRational": 14784,
  "rawNegative": 0,
  "adjusted": 16349738.000000011,
  "lower": 15647.197530850353,
  "maxInventory": 478
}
```
Main/direct unchanged. Next: derive actual adjacent endpoint odd-ratio concentration or use the complementary even-denominator structure, and revisit the implication from original overlap to macro transport saturation. No final NT-scale overlap gap.
