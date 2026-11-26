# Integration XXXIX: short-core prime-support concentration from the residual rational lines

2026-11-26 JST. Parent b5caf21e333f44772801665886411b972ec70187. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md). New: on short original tag bins, the residual short-index exception of XXXVIII cannot use a dispersed near-minimal source support. Near-saturation forces almost all ACTUAL source matched weight into a small union of narrow prime-label intervals, with nearly log²Y actual source labels near each surviving label. This is a conditional concentration theorem, not elimination of clustered supports.

## 1. Hypotheses and the residual edge

Retain XXXVI--XXXVIII original tagged paths, actual chronological nonoverlap s_i<t_i<s_(i+1) of up/down pairs, all endpoint labels in [Y,KY], Y<=B, fixed K, polynomial Y>=X^a0 for fixed a0>0. Original tag-bins L<=H, L>=Y^(1+epsilon) for fixed epsilon>0. Actual matched weights m_i<=min(u_i,v_i)<=3KY+1, M=sum m_i>=rho NH, local source support S_j and cardinality s_j with sum s_j<=C0(NH/L)log²Y. No consumer support or low-relay assumption. Define Delta=G_all-4M/3+4n/3. The exact cycle ledger sum |d_i-4p_i|<=6Delta+4n, n<=NH/(Y-1), holds for all actual consecutive selected sources on a bin. Weight either starting or ending source m_i or m_(i+1); each ledger loses only one boundary source per bin, O(NHY/L)=o(NH). The same upper per transition works for either direction of weighting; the two ledgers are not additive.

Fix 0<tau<=1/4, near |d_i-4p_i|<=tau Y. As XXXVII, nonresonant distinct pairs have per-edge weighted capacity O(tau L/log^4Y). As XXXVIII, resonant pairs with long line-index interval Kc>=log^gamma Y have same bound, with constant independent of fixed tau (threshold may depend on tau), for every fixed gamma>0. Same-label near and proportional c=0 parts sum to o(NH), for either endpoint weight. It remains to count distinct resonant pairs with short index interval Kc<log^gamma Y and nonzero c. Here use exactly the reduced rational certificate of XXXVIII, h,A>0, ell=hp-Aq!=0, Kc>=D0=|ell| U_p/q+2h tau Y/q, U_p=L/p+O(1) padded above the actual cofactor span, so
    h <= C_K tau^-1 log^gamma Y, A <= C_K tau^-1 log^gamma Y,
    |ell| <= C_K (Y²/L) log^gamma Y.                        (1)
Use the XXXVIII pointwise line estimate and (V+2)Kc=O_K(L/Y), so for every fixed ordered p,q, including all four sides,
    W_short(p,q) <= C L (loglog(3Y))^C1/log^4Y.            (2)
The certificate and interval can be chosen for each pair and sides using the old proof; (1) bounds their union, and only actual transitions are charged. C1 can be fixed absolute, e.g. 20. This step does not apply the long-index mean to a short interval.

## 2. Two-sided prime interval relation independent of bin translation

Choose W=ceil(C2 (1+Y²/L) log^gamma Y) with a sufficiently large fixed C2 depending only on K. Equation (1) implies
    |q-hp/A| <= W,  |p-Aq/h| <= W.                         (3)
Importantly W does not depend on fixed tau, since the bound on ell uses the FIRST term in D0 alone; tau only affects the number of possible h,A. For each fixed p and any allowed h,A, all possible successors q are in a single interval of radius W around hp/A. For each fixed q and the same h,A, all possible predecessors p are in a single interval of radius W around Aq/h. The union over all coefficient pairs uses at most O_(K,tau)(log^(2gamma)Y) intervals in EITHER orientation, even if the actual source support and certificates depend on the tag-bin. No primes in those intervals are assumed equidistributed. This is a stronger statement than the old total degree bound when the support itself is dispersed.

Fix any 0<delta<2, choose 0<gamma<delta/2, e.g. delta/4. Let k=ceil(log^(2-delta)Y). For each bin define its crowded support
    C_j={p in S_j : # (S_j intersect [p-2W,p+2W]) >= k}.
This is defined from the original selected source support and is independent of tau and of the actual successor edge. A radius-W interval containing an uncrowded support label contains FEWER than k support labels in total, since all other labels there lie within 2W of that uncrowded label. Consequently for any fixed p there are at most O_(K,tau)(k log^(2gamma)Y) possible uncrowded q on the short-index relation. Symmetrically for fixed q there are at most that many uncrowded p. Apply (2) per ordered edge, and sum over all support labels in every original tag-bin:
    F_short with at least one uncrowded endpoint
      <<_(K,tau) L k log^(2gamma)Y (loglog(3Y))^C1 /log^4Y * sum_j s_j
       = O_(K,tau,C0)(NH log^(2gamma-delta)Y (loglog(3Y))^C1)
       = o(NH).                                            (4)
This works for either starting or ending weight. It does not require s_j bounded individually, only the stated aggregate support. It also handles a union over different sides without extra growing factors. There is no assumed probability on the location of a bin, or on whether a prime is crowded.

## 3. Concentration of actual matched source mass at near saturation

Let M_unc be actual matched weight of sources with p not in C_j on their own bin. Using the STARTING weight ledger, charge all except last sources by their next consecutive selected-source transition. Its far-gap part is <=(3K+1)(6Delta+4n)/tau by XXXVI. Discard bins with s_j>C3 log²Y at weight O(NH/C3), since their number is <=sum s_j/(C3 log²Y) and bin source mass O_K(L+Y)=O_K(L). On the remaining bins the nonresonant and large-index near supply sums to O(C3² tau NH); same-label and c=0 contributions o(NH); uncrowded short-index contribution (4) o(NH). Therefore
    M_unc <= O(NH/C3)+C C3² tau NH
                     + C_K(Delta+n)/tau + o(NH).           (5)
The o term is for fixed tau,C3,delta,gamma. The identical bound holds if one charges ending rather than starting source weight, by dropping first instead of last; also for a transition with an uncrowded opposite endpoint. The same slack must not be counted twice. If Delta=o(NH), choose C3 large and then tau small for an arbitrary fixed tolerance, and finally X large. Since C_j,W are INDEPENDENT of tau, this yields
    M_unc=o(NH).                                           (6)
Equivalently almost all direct matched weight lies at labels with at least log^(2-delta)Y distinct actual source labels within distance 2W. This holds for every FIXED delta in (0,2), gamma<delta/2, with no need to let parameters tend to zero together.

Conversely if M_unc>=rho1 NH for any fixed rho1>0, choose C3 large and tau small in (5) so the first two terms are <=rho1 NH/2. Since n=o(NH), the inequality forces Delta>=c NH, and hence M<=3G_all/4-c' NH for large X. Thus the all-scale fixed-gap theorem of XXXVIII extends to short bins PROVIDED a macroscopic part of matched source weight uses uncrowded labels. This is not an assertion that such a part must exist.

## 4. Few-interval cover, physical scale, and independent recycling restriction

In each bin greedily choose a maximal subset of crowded labels separated by >4W. Their radius-2W neighborhoods are pairwise disjoint and each contains >=k support labels. Hence there are <=s_j/k centers; their radius-4W intervals cover every crowded label. Sum the number of intervals over bins:
    #intervals <= sum_j s_j/k = O((NH/L) log^delta Y).
Their centers can all be actual source primes. Under saturation they cover M-o(NH) matched mass. For bins with s_j<=C3 log²Y this is at most O(C3 log^delta Y) intervals of length O(W), each center with >=k distinct source labels nearby. For a fixed positive fraction of total M there are Omega(NH/L) such bounded-support busy bins; by (6) and bin mass O(L), Omega(NH/L) bins carry Omega(L) crowded weight. This is a tagged statement, no assertion of distinct physical rays or label intervals globally. At L=X^.7, Y~sqrt X, W=O(X^.3 log^gamma X); near saturation forces concentration into few such intervals rather than across the whole sqrt X-scale. At L~Y²/log^beta Y with beta<2, choose delta,gamma small with beta+gamma<2-delta; then even the number of integers in a crowded interval is o(k), recovering the previous long-bin exclusion. At short L=X^.7, the integer/prime count is NOT small enough to contradict (6). No unconditional prime-cluster bound is claimed.

There is also an actual occurrence restriction independent of the saturation ledger. Apply direct cb54101's averaged same-label return bound to the ordered list of all retained upward sources with the actual matched weights m_i<=3KY+1. In a bin, first/last weights O(Y s_j), short preceding/following gaps m=(a2-a1)/2<=K0 count with weight O(L s_j K0/log^4Y), long gaps m>K0 weight O(L s_j/(K0+1)). The source labels comparable Y, actual cofactor interval L/p>=cY^epsilon, and direct proof applies to arbitrary selected upward occurrences. Under aggregate near-minimal support and M>=rho NH, for any fixed tolerance almost all except that tolerance of matched mass has both preceding and following same-label halfgaps between a0' log²Y and b0' log²Y+1 with fixed positive constants. Thus in a saturation sequence, the crowded weight in (6) can also satisfy these two-sided recycling gaps on the SAME original source lists, losing arbitrarily small mass (union bound, not independence). If further selecting crowded sources, note crowded membership depends only on label in a bin, so all occurrences of any crowded label are preserved; the same-label lists are unchanged there. No assumption that different clusters have disjoint physical paths or that the gap bounds hold for every visit. This combines the short-index concentration with recurrence on the actual support rather than an inferred candidate graph.

## 5. Finite diagnostics and scope

Run node research/min_unified_short_index_cluster_audit.mjs 4096 16384 65536. Extend XXXVIII six actual prime-root runs and 48 finite controls. For each bin form actual distinct source set, use finite k=3, Kc=5, W=ceil(K² Kc(1+Y²/L)); verify disjoint-neighborhood greedy cover, matched dense/sparse partition, short-index coefficient and two-sided interval bounds, and uncrowded degree per fixed rational coefficient and fixed endpoint in both orientations. Keep old actual line/rotation checks. Independent integer-set controls vary widths and spacings and test sparse interval cardinality; these are not prime/MIN trajectories. Finite controls are not claimed to realize asymptotic saturation or near-minimal support. No independent analytic sieve proof, full core/kernel rerun or Lean.
```json
{
  "totals": {
    "controls": 48,
    "pairs": 29671,
    "M": 726042,
    "gapChecks": 6968,
    "clusterBins": 22703,
    "clusterLabels": 28714,
    "clusterDense": 3752,
    "clusterCenters": 1110,
    "clusterDenseMass": 64592,
    "clusterSparseMass": 661450,
    "shortIndexGroups": 14,
    "shortIndexMass": 2156,
    "shortIndexDenseStart": 0,
    "shortIndexDenseEnd": 0,
    "shortIndexSparseStart": 2156,
    "shortIndexSparseEnd": 2156,
    "shortIndexEdges": 14,
    "clusterRelationChecks": 28,
    "clusterDegreeChecks": 28,
    "clusterCoverChecks": 22703
  },
  "independentClusters": {
    "controls": 144,
    "dense": 1943,
    "sparse": 1273,
    "centers": 308,
    "intervalChecks": 3216
  }
}
```
Main/direct unchanged. Next: count repeatedly utilized crowded prime clusters using actual MIN clock/phase or common-core merging constraints, or derive direct near-saturation from the original overlap ledger. This result does not force saturation or near-minimal supports, or eliminate the crowded short-index branch. No final NT-scale overlap gap.
