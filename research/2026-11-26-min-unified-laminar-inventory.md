# Integration XLI: laminar last-up transport and inventory-weighted inverse-multiplier budget

2026-11-26 JST. Parent 26942a9c628149f15f521260a49b0059d84794d8. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). New: extend XL's chronological nonoverlapping pair result to nested causal last-up arcs, without charging the whole interior gain of a nested pair to every ancestor. Use the actual open matched-height inventory, not the maximum number of nested arcs. For general split/merge transport obtain an explicit alternative between loss of saturation, branching mass, and large open inventory. Not the final overlap loss.

## 1. Actual causal height transport and noncrossing

On an original canonical tag starting ordinary deficit d=6, let actual events have gains g=p-1 and change 2w-g. A matched unit at integer height a>=6 is created on an upcrossing (d<=a<d') and consumed on the next downcrossing (d'<=a<d). Equivalently use Lebesgue height intervals and ignore endpoints. Every unit is last-up matched, with no reuse at a source or consumer. The result works for any retained submeasure of these actual chronological units, including XXVII local fragment matches and XXIX source-preserving buffer extractions. Aggregate retained mass m_st>0 once per actual source/consumer edge. Both endpoint labels >=Y>=11, no comparability required. For any source total outgoing mass <=its rise u; any consumer total incoming mass <=its fall v.

Two positive edges with STRICTLY distinct endpoints cannot have s1<s2<t1<t2. Indeed choose matched heights a1 and a2 from the respective edges. The first unit is still open at s2, so d_(s2)>a1 (integer convention), and a2>=d_(s2)>a1. At t1 the second unit is still open, but downcrossing a1 requires postheight <=a1<a2, which consumes that second unit at or before t1, a contradiction. Shared endpoints can occur. Thus after selecting at most one edge per actual source and per actual target, the time intervals form a laminar forest: disjoint or nested, not necessarily chronologically disjoint. This is specific to actual last-up matching; arbitrary fractional flows with only endpoint capacities need not be noncrossing.

At any cut just before or after an event, define O the sum of retained matched mass whose source has occurred and target has not. All these units occupy distinct actual heights a>=6 below current ordinary deficit. Thus 0<=O<=max(0,d-6). Let P=max O over the whole tag. For a retained local matched population on disjoint physical fragments with guard width at most M_* as in XXVII, O<=M_* because no matched arc crosses fragment boundaries. For XXIX enlarged guards use their enlarged width. The proof below requires no guard assumption; P is measured on the actual selected transport.

## 2. Unique endpoints, but arbitrarily nested arcs

First select a laminar edge population with unique source and target endpoints. Let M=sum m_st, n=#edges, G_U,G_D gains of actual endpoints, G_O=G-G_U-G_D nonnegative on the full original tag, G<=H. As in XL, A=3G_U+4n-M, D=G_D-M, Delta=A/3+D+G_O=G-4M/3+4n/3. Here D>=2n by positive downward waits, so Delta0=G-4M/3>=Delta/3 and n<=Delta/2. These facts use unique endpoints but not chronological nonoverlap.

Define residual baseline b=d-O. Across a selected source its change is u-m, across a selected target m-v, and across any other event exactly the physical change. Therefore the actual total variation of b along the WHOLE tag satisfies
    TV(b)<=sum_sources(u-m)+sum_targets(v-m)+5G_O
         <= A+D+5G_O <=5Delta.                         (1)
The canonical initial value is 6, so b<=6+5Delta and at every cut d<=6+5Delta+P. No new free baseline at a bin boundary. This identity also works for GENERAL nonreused last-up matching with multiple edges per endpoint, by replacing m at an event by total outgoing/incoming mass; then A uses number of distinct sources, D uses actual targets, and the comparison Delta0>=Delta/3 need not hold with unequal endpoint counts.

For a selected edge s,t, the open inventory just after s equals that just before t. All strictly interior selected endpoints are paired with another strictly interior endpoint, because of laminarity and uniqueness; ancestors remain open, descendants finish. Thus the signed change of ordinary deficit through the strict relay is exactly
    d_t-d'_s=b_(t,pre)-b_(s,post).                       (2)
It is bounded by residual variation in that relay, NOT by its total physical gain. This is crucial for nested arcs: the rise and fall of a completed descendant pair cancel except its residual mismatch. Although relay intervals overlap, weight each by m_st/p_s<=4. At an actual intermediate event the sum of m_st/p_s over all strictly containing arcs is <=O/Y<=P/Y, since each such arc is open at that event. Hence by a finite nonnegative sum interchange,
    sum_(s,t) (m_st/p_s) |d_t-d'_s|
        <= (P/Y) TV(b) <=5(P/Y)Delta.                   (3)
No maximum number of nested arcs is needed. This uses the ACTUAL open mass and the signed relay change, not a sum of repeated gross relay gains.

## 3. Weighted odd-multiplier loss

For each edge p,r, ordinary postdeficits d'_s=2hp+6I, d'_t=2kr+6J. The exact XL identity, now with signed relay change, reads
    2hp-(2k+1)r=c=-(d_t-d'_s)-1-2w_t+6(J-I).
Oddness gives p/(2k+1)<=|r-3p|+|d_t-d'_s|+2w_t+7. As before, with a=2p-w_s, r-3p=v-u+2-2a+2w_t; sums of |u-v|<=A+D, 2a<=A, 2w_t<=D. Thus sum |r-3p|<=2(A+D)+2n, since each selected endpoint counted once, regardless of nesting. Multiply each odd obstruction by m/p<=4, use (3), and sum:
    sum m/(2k+1)
      <=4[2A+3D+9n]+5(P/Y)Delta
      <=(42+5P/Y)Delta.                                (4)
Here 2A+3D<=6Delta and n<=Delta/2. As in XL, sum mY/(Y+d'_t) is no larger than the left hand side. In particular matched shallow-multiplier mass k<=k0 costs at least its mass divided by (2k0+1)(42+5P/Y). This holds even if a large number of tiny edges are simultaneously open. We have not assumed source or target supports sparse, relay length small, or any local bin length.

Put Lambda=P/Y. By (1) and d'_t>=2kY, (4) implies
    M <=47(1+Lambda)Delta(1+(6+5Delta+P)/Y)
      <=94(1+Lambda)^2 Delta+235(1+Lambda)Delta²/Y.     (5)
Use Y>=11. At least one of the two terms on the right is >=M/2; since M<=H and Delta0>=Delta/3, a conservative common constant yields
    G-4M/3 >= (M/600) min((1+Lambda)^(-2),
                                 sqrt(Y/((1+Lambda)H))).     (6)
For uniform P<=K0Y on every tag, summing (6) gives loss Omega_K0(M sqrt(Y/H)) just as XL, now for any nesting with unique endpoints. More generally with actual tag-specific P_i sum the right hand sides individually; no uniform bound necessary. This proof does not turn the loss into a fixed fraction of NH when Y=o(H). It cannot charge nested arcs as disjoint direct pairs in the earlier cycle-gap sieve: their chronological ordering differs. The new weighted argument is what permits nesting.

## 4. Split/merge defect and general last-up populations

For an arbitrary original retained causal edge set with total mass M0, define split impurity
    I_U=sum_sources [total outgoing m - maximum outgoing edge mass],
and merge impurity I_D analogously at consumers. Choose one largest outgoing edge per source and one largest incoming edge per consumer, breaking ties deterministically. Keep their intersection. The removed mass L0=M0-M satisfies
    0<=L0<=I=I_U+I_D,
by union bound on the two discarded edge families. The surviving population has unique endpoints and is laminar. Its open inventory never exceeds original P0, because only edges are removed. Apply (6) to it, put f0=min((1+P0/Y)^(-2),sqrt(Y/((1+P0/Y)H))). Since f0<=1 and G-4M/3=G-4M0/3+4L0/3, obtain exact conservative alternative
    G-4M0/3+2I >= (M0/600) f0.                         (7)
One can keep the actual L0 instead of I with coefficient 4/3+f0/600. This inequality is meaningful also when the original unadjusted slack G-4M0/3 is slightly negative: with unequal endpoint counts one must not assume its nonnegativity. The adjusted general endpoint slack is always nonnegative, and its O(n_U) correction can be bounded by G/(Y-1) if desired. No such correction is needed in (7), since pruning establishes equal endpoint counts and positive waits there. On all tags, sum (7) over the full original lifetimes, never count the new selected mass as additional old credit.

In particular when original P0<=K0Y uniformly and macro M0>=rho NH, (7) gives
    G_all-4M0/3+2 I_all >>_(K0,rho) N sqrt(HY).
If I_all=o(N sqrt(HY)), this proves a positive submacroscopic non-saturation loss for the actual original transport, allowing nested and even sufficiently small branching mass. If branching is larger, (7) identifies it as a separate alternative, not a loss automatically charged to the physical gain. Alternatively for a population already unique endpoints with any P, use (6) directly. Narrow guards imply small P but do not imply small impurity: one source can split into many consumers at different levels and one consumer can take many source levels. Neither sparse supports nor finite twins presently force the requisite impurity bound. No conversion of this transport deficit to XVII's uncovered clock is claimed.

## 5. Diagnostics

Run node research/min_unified_laminar_inventory_audit.mjs 4096 16384 65536. Six actual prime-root runs, 48 finite controls Y11/17/31/61,L=H or floor(H/2), comparable endpoint cutoff K6 for diagnostics only. Generate actual per-height last-up matches above6 on full original tags, restrict both endpoint labels and same original bin. Test noncrossing of every edge pair, endpoint capacities, mutual largest-edge pruning and impurity union bound; open inventories of original and pruned edges, residual variation and canonical baseline, signed relay cancellation, weighted relay and odd multiplier identities, whole-tag quadratic and impurity alternative. Actual nested edges counted, not inferred from synthetic diagrams. No independent analytic sieve needed in this argument; no full cumulative core/kernel rerun or Lean.
```json
{
  "controls": 48,
  "edges": 41658,
  "allMass": 1002656,
  "splitLoss": 91908,
  "mergeLoss": 31812,
  "removed": 120222,
  "selected": 33047,
  "M": 882434,
  "G": 43258576,
  "nested": 493,
  "noncross": 34551,
  "inventoryChecks": 2223896,
  "baselineChecks": 2223896,
  "residualVariation": 45653740,
  "relayChecks": 33047,
  "weightedRelay": 241969.24996442598,
  "weightedRelayCap": 560639.4361718062,
  "inverseChecks": 33047,
  "inverseSum": 433636.2637543329,
  "quadraticChecks": 124560,
  "impurityChecks": 124560,
  "tagWithSelected": 24454,
  "rawSlack3": 125765104,
  "selectedSlack3": 126245992,
  "lowerBound": 86.35232224004756,
  "allOpenMax": 478,
  "selectedOpenMax": 296,
  "selectedDepthMax": 3
}
```
Main/direct unchanged. Next: bound split/merge impurity or exploit its actual level-order structure, or connect the narrow guard/actual transport saturation to XVII. Fixed NT-scale overlap gap still open.
