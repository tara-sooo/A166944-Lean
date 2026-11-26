# Integration XLII: inventory-grid re-pairing and endpoint-size dispersion

2026-11-26 JST. Parent 73af2feb69c2aa358f9c1bb9954c5614c621efca. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). New: XLI's split/merge impurity is not necessary when endpoint masses have small dispersion. Re-pair on a shifted grid of the actual open-inventory trajectory, with a new endpoint-capacity weight. This creates a laminar unique-endpoint population without requiring the original edge weights to be preserved. The resulting loss is controlled by endpoint-size dispersion, not branching. Gives another conditional transport gap, not the final overlap gap.

## 1. Compression and grid lemma

On a whole original tag take an arbitrary retained nonreused last-up height population with both labels >=Y>=11. Total mass M0; x_j>0 is the total outgoing retained mass at a source, -x_j>0 the total incoming at a target, x_j=0 elsewhere. O_j=sum_{i<=j} x_i, nonnegative with initial and final zero; P0=max O_j. The actual retained units are ordered by height at each cut. A source appends its units above all older open units, and a target removes the highest retained open units, since it downcrosses all higher levels before lower ones. Thus chronological LIFO matching on the compressed inventory O reconstructs the actual retained edge masses (ignore boundaries of measure zero). This is true with omitted physical events, omitted levels and split/merge endpoints. It is not true for an arbitrary endpoint-capacity flow.

Take a reference size a>0. Choose shift uniformly on [0,a), and mark positive levels shift+k a. Null boundary cases ignored. An event with endpoint mass x=|x_j| crosses n_j grid levels. E n_j=x/a, and n_j is either floor(x/a) or ceil(x/a). Match each marked upcrossing to its next downcrossing on O. These grid arcs have the old actual edge as support (by compression), but their new weights will NOT be restricted to the old edge's mass. The full grid has expected weight a per arc, total expected mass M0. Delete arcs incident to any event crossing >=2 grid levels. The expected removed weight is at most a sum E[n_j 1_{n_j>=2}] <=2 sum (x-a)_+: for x<=a it is zero; for a<x<2a it is 2(x-a)/a; for x>=2a it is x/a<=2(x-a)/a. Endpoints counted at most twice for this upper bound. On surviving arcs assign weight m=min(a,x_s,x_t). The additional reduction is <=sum_{x_j>0}(a-|x_j|)_+, since each endpoint used at most once. Define
    R_a = sum_{x_j!=0} [2(|x_j|-a)_+ +(a-|x_j|)_+].
There exists a shift with new total M>=M0-R_a. Also M<=M0 by the original outgoing capacities. The new pairs have unique actual source/target endpoints, are laminar, and m<=actual rise and fall. At any cut number of open marked arcs <=O/a+1; since m<=a, new open inventory <=O+a, hence P<=P0+a. No new physical gain or extra original transport credit. In particular this is a re-pairing with modified weights, not a submeasure of the old matched height units: a single old edge may receive weight larger than its old mass. It is valid for real masses by the shift expectation; for integer masses and integer a the a shifts at half-integers give exactly the continuous average.

The lemma also applies separately to every maximal nonzero excursion of O between zero cuts. Choose references a_j independently on these excursions, optimize or use a median of the nonzero endpoint sizes, and choose the best shift per excursion. Since excursions are disjoint in time and have zero inventory at boundaries, union of the new pairs is laminar with unique endpoints, M>=M0-R where R=sum R_{a_j}, P<=P0+a_max. A different reference may be chosen only at zero cuts in this version, not across an arbitrary cut carrying open mass. No new free physical baseline is introduced at these boundaries. The choice of median is a convenient diagnostic, not the exact minimizer of the asymmetric loss; a lower 1/3 quantile minimizes the piecewise-linear expression (with ordinary quantile conventions).

## 2. Why XLI applies to the new weights

The proof of XLI sections 2-3 used only: actual physical endpoints with correct rise/fall signs, unique endpoints, chronological laminarity, m<=min(u,v), conserved open mass at the cuts just after s and before t, canonical initial deficit 6, and a bound on maximum open inventory. It did NOT use that the selected open mass occupies its old physical height levels in deriving the residual variation or the odd identity. For the new pairs define O_new as their actual weighted open-arc sum; it need not be <=d-6, but the residual b=d-O_new still has exact increments u-m at sources, m-v at targets, and physical change elsewhere. TV(b)<=5 Delta, hence d<=6+5Delta+P. The signed relay identity follows from laminarity with unique endpoints. Thus the entire inverse multiplier inequality and XLI's numerical lower bound (6) hold for the new population with its measured P. No claim that the inflated edge weights are actual last-up height weights; this extension to virtual weights is an algebraic statement about endpoint budgets on the same original physical tag.

Let G<=H denote original whole-tag gain, n the number of new pairs, Delta=G-4M/3+4n/3. Since all retained targets have positive waits, Delta0=G-4M/3>=Delta/3. With
    f=min((1+(P0+a_max)/Y)^(-2), sqrt(Y/((1+(P0+a_max)/Y)H))),
the XLI bound gives G-4M/3>=M f/600. Using M0-M<=R and f<=1 yields
    G-4M0/3+2 R >= M0 f/600.                            (1)
One may use actual rounding loss instead of R with coefficient 4/3+f/600. If P0+a_max=O(Y) uniformly, macro M0>=rho NH and sum R=o(N sqrt(HY)), summing original tags gives G_all-4M0/3 >> N sqrt(HY), WITHOUT requiring split/merge impurity to be small. More generally use the better of XLI's impurity penalty and the new dispersion penalty, since both are alternative re-pairings of the same original population; do not add them as physical gain losses. For fixed uniform bound K0Y on P0 and a_max the constant depends on K0,rho. This is a submacroscopic gap in the canonical scales; does not imply original overlap loss.

## 3. Prime-label capacity dispersion

For original sources and targets put U_s=3p_s+1, V_t=r_t-1. These are upper capacities (not actual rise/fall); write A0=sum U_s-M0, D0=sum V_t-M0, both nonnegative. Let a_j be a common reference for endpoint sizes on an inventory excursion. Triangle inequality yields
    R <= 2 sum_sources |3p_s+1-a_j| +2 sum_targets |r_t-1-a_j| +2(A0+D0).
The dispersion term can therefore be expressed using the source and target prime label ranges plus original endpoint slack. This inequality does NOT imply those ranges are narrow. In particular, if the source labels are near P_j and targets near 3P_j on the same excursions, choose a_j=3P_j+1. If labels lie within W_j of these respective centers, the prime dispersion is O(sum (W_j+1) times endpoint count on that excursion). If max W_j=o(Y sqrt(Y/H)), with comparable reference scales a_j=O(Y) and original endpoint slack sum(A0+D0)=o(N sqrt(HY)), then R=o(N sqrt(HY)) because distinct original endpoint count <=NH/(Y-1). This is a sufficient condition, not obtained from XXXIX's clustered-source result: that result concerns ordered direct populations, permits multiple clusters and does not force original target concentration at three times the source center. The new theorem identifies the arithmetic quantity to bound even in the split/merge case.

The penalty is genuinely different from old edge impurity. Example: abstract closed inventory with n jumps +a followed by -b, then n-1 jumps -a, then -(a-b), 0<b<a. All source masses equal a, all but two target masses equal a. R=a, independent of n (the two small jumps' deficits sum a). Yet if b=a/2, most original source blocks split approximately equally across two targets, and old split impurity grows proportionally to n a. The grid re-pairing retains at least (n-1)a. This is an abstract inventory example, not asserted to be an actual MIN trajectory; its P0=n a also grows with n. The example illustrates why original impurity need not be controlled to obtain a useful endpoint-capacity matching.

## 4. Diagnostics

Run node research/min_unified_inventory_grid_audit.mjs 4096 16384 65536. Six actual prime-root runs, 48 finite threshold/bin controls, endpoint labels Y..6Y, local same-bin original physical last-up edges. Reconstruct original edge table by compressed LIFO, form actual zero-inventory excursions, use integer median reference, enumerate ALL half-integer shifts, verify exact average grid mass and loss guarantee. Check every re-paired edge is supported by an original actual edge, record when weight increases, verify actual physical endpoint slack, virtual residual variation, weighted signed relay, odd identity and original dispersion alternative. Independent abstract split-stack examples check the grid lemma; not MIN paths. No analytic sieve or full core/kernel/Lean verification. Main/direct unchanged.
```json
{
  "totals": {
    "controls": 48,
    "edges": 41658,
    "M0": 1002656,
    "mutual": 882434,
    "impurity": 123720,
    "roundMass": 854876,
    "roundLoss": 147780,
    "disp": 440296,
    "better": 488,
    "betterMass": 4856,
    "excursions": 32421,
    "shifts": 866458,
    "gridChecks": 6023408,
    "gridPairs": 32538,
    "oldEdgeChecks": 32538,
    "oldEdgeInflated": 256,
    "baselineChecks": 882624,
    "relayChecks": 32538,
    "budgetChecks": 24454,
    "primeDispChecks": 24454,
    "primeDisp": 5199784,
    "endpointSlack": 5159364,
    "lower": 55.82583453746802,
    "maxOpen": 478,
    "maxRounded": 296
  },
  "independent": {
    "cases": 188,
    "checks": 70488,
    "perfect": 0,
    "best": 31992,
    "disp": 4272
  }
}
```
Next: derive common size dispersion or a broader multi-size rounding theorem from actual MIN arithmetic, or connect the original overlap to required transport saturation. No fixed NT-scale overlap gap.
