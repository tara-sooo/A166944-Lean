# Integration XXXIII: local first-high recovery and forced deep multiplier states

2026-11-26 JST. Parent 20f444ec5796970cde7e6cb4dedb93b619f47d23. Direct preflight [6e2a198](https://github.com/tara-sooo/A166944-Lean/blob/6e2a198921a95d21643afce389e15ff20625458b/research/min_direct_fast_pair_multiplier_shift_audit.mjs) and theorem [0782bd1](https://github.com/tara-sooo/A166944-Lean/blob/0782bd1a321319f7de58dfa1ba15fd10382029fd/research/2026-11-26-min-direct-first-pair-gap-and-direct-recovery.md). New: apply the first-high recovery result with LOCAL weighted source support rather than global support, and derive a power-scale exclusion of shallow source AND target multipliers, without assuming sparse consumer labels or long product CRT. Even at near-square-root label scales. For polynomial labels, macro direct supply also forces large local multiplier-state diversity and selected-post height range. This is a conditional alternative, not a global small-missing contradiction.

## 1. First high successor on the original tag

Use the actual XXIX extracted cross-label matched population, restricted to pairs in the same original tag-bin L with both endpoint labels [Y,KY], actual intervening gain E_st<=A Y, Y->infinity, fixed K,A. Let M>=rho NH be its mass. Aggregate weights a_s once per upward source, a_s<=3p+1. All targets are downward; retain the original chronological nonreuse. Assume L>=B Y^epsilon, L<=H, fixed epsilon>0 (feasible at top Y~B for epsilon<1). Assume total distinct actual source labels across original bins
    sum_j s_j <= C0 (NH/L) log²Y.
The near-minimal weighted support of XXVIII implies this on comparable narrow guards. No bound on consumer support, no requirement L>=Y², no same-label return separation needed for this theorem. The hypotheses include the quantitative budget
    G_low,all=o(NH log²Y/Y),                             (1)
where G_low,all counts actual low p<Y gain INCLUDING resets over original tags (not just selected core gain). Alternatively restrict to a deep starting population with d'_s>6+AY and use G_low,nonreset in (1), by XXXII: first high successor is at or before the earliest original target; all intervening events are nonreset. Neither budget follows merely from small missing or little-o low nonreset gain.

For each source choose its earliest retained target. Its actual FIRST subsequent high event b (label r>=Y) exists at or before that target and in the same original bin. Because intervening gain to the target <=AY, r<=K1Y with fixed K1=max(K,A+2): if it is strictly before the target, its gain fits inside that interval, otherwise its label is the target label. Every intervening event between source and first high b has label <Y. Their total gain E and wait V satisfy V<=3E. Strict low interiors for different source-first-high pairs are disjoint, since every source itself high and each pair lies between consecutive actual high events. This includes sources that have no later SELECTED upward source in the bin; no loss of last selected source needed. With q=Y G_low,all/(NH), choose
    b_cut=ceil(max((log Y)^.5, sqrt(q log²Y))).
Then b_cut=o(log²Y), q/(b_cut+1)=o(1), b_cut<Y-3 eventually. Discard E>b_cut costing <=O(Y G_low,all/(b_cut+1))=o(NH) of ORIGINAL source weight. For a deep population the same proof uses the nonreset budget and that q.

## 2. Local first-successor four-form sieve, at all label scales

Fix any alpha in (0,1) and let W=ceil(Y^alpha). The source is genuinely upward and so w_s>g_s/2; a first high successor with w_b>=W is also rough to a power of Y. Use direct 0782bd1 section3: at fixed source label p, side e, and E<=b_cut, write C=pz+e and shift D=p-1+E. Four forms z,pz+2e,pz+e+D-1,pz+e+D+1, distinct generic roots except f|D(D²-4), both endpoints exclude primes below a fixed power of Y. Pad cofactor interval to ceil(L/p)+2 (not full X), use cutoff min(Y^alpha,L/p)^(1/12) reduced by fixed factor; L/p>=c Y^epsilon so log cutoff comparable to log Y and sieve error absorbed. The direct averaged singular-factor lemma (3) applies to b_cut+1>=log^.5Y, even though the interval is only polylogarithmic. No assumption about the successor label's support or independent distribution. Count times original source weight <=O(Y); sum E, sides:
    F_extended,j << L s_j (b_cut+1)/log^4Y.
Sum actual bins using the support bound gives o(NH). Thus except o(NH) ORIGINAL source mass, E<=b_cut, w_b<W; labels p!=r by same-label spacing E>=p-1, target ordinary drop v_b=r-1-2w_b=(1-o(1))r. This works for L<Y² as well, using a progression only in the source cofactor. In particular no new near-square-root obstruction from the product CRT.

For a direct causal re-pairing, discard weak source weights a_s<eta p (cost <=(1+o(1))eta NH) for fixed small eta>0 if needed. Then source rise u_s>=eta p and first high target drop >=(1-o)Y. Direct 0782bd1 (5) gives actual full-axis last-up matching weight >=min(u_s,v_b)-10E, because low variation <=5E. Restrict to heights >6 losing at most 6; choose a submeasure with weight a_s^new=min(a_s, actual direct mass). This is >=c_(eta,K1) a_s eventually on retained sources, and <=a_s. Different direct pairs are event-disjoint: each joins consecutive physical high events, first endpoint upward, second downward; two such pairs cannot share a physical high endpoint. All new matched units are actual chronological matches. Thus macro direct matched mass, unchanged subset of source occurrences, nonincreased weights and same local support. The new matched levels need not be those of XXIX or even lie in its old guard; do NOT add new mass to old transport or treat old consumers as the new ones. Retaining old source weights for counting below avoids this issue entirely.

## 3. Exact odd-shift state counting without a target-support assumption

For the retained fast first pairs write ordinary postdeficits d'_s=2hp+6I, d'_b=2kr+6J; h>=1 (source supports heights >6), k>=0. The exact elapsed ticks from source departure to target departure are V+w_b, and the horizon difference of their departures is E+r-1. Hence
    2hp-(2k+1)r=c,
    c=E-1-2(V+w_b)+6(J-I),   c odd,
    |c|<=Q=5 b_cut+2W+7.                                (2)
This is the latest direct audit identity. In particular r divides 2hp-c, and p divides (2k+1)r+c. Both numbers positive by (2), and bounded by O(H+Q+B) on a canonical lifetime. For fixed (p,h,c,E,I,J), at most b_h=floor(log(2hp+Q)/logY) distinct eligible r>=Y (increase to 1 if necessary). After r is chosen k determined. Horizon residues C=e_s mod p and C+p-1+E=e_b mod r specify one CRT progression mod pr. In one ORIGINAL bin at most 1+L/(pr) candidates. The actual phase modulo 4pr can be imposed but is not needed for the upper. Each candidate specifies at most one actual first pair. Count with original source weight <=O(Y). Write S_j^* set of actual (p,h) states of fast pairs; T_j^* set of actual (r,k). Then
    F_fast,j << Y(1+L/Y²)(b_cut+1)(Q+1)
                     sum_(p,h in S_j^*) max(1,b_h).       (3)
The symmetric target-state bound uses b'_k=max(1,floor(log((2k+1)r+Q)/logY)); choose c,E,sides and p, count same CRT, still weight <=O(Y) because comparable endpoints. No sieve error, no assumed target-label sparsity, no restriction that height be below Y². This is a local weighted extension of direct's exact finite two-sided state capacity. For arbitrary absolute heights one may bound both divisor multiplicities by b_H=O(1+log H/logY). The state count is not just the number of distinct primes, since one prime may appear at many heights.

## 4. Forced depth even without bounded global multiplier multiplicity

Let sigma=min(epsilon,1) and choose fixed alpha,delta>0 with alpha+delta<sigma. Apply (3) to h<=C1 Y^delta for any fixed C1. Then b_h=O_(delta,K1)(1) uniformly even for arbitrarily slowly growing Y, since 2hp+Q=O(Y^(1+delta)+Y^alpha). Each source label has O(Y^delta) such possible h. Sum (3) over original bins using sum s_j:
    F_shallow/(NH) << log²Y (b_cut+1)(Q+1) Y^delta
                                  (Y/L+1/Y)
                    = o(1).
Indeed Y/L<=Y^-epsilon because B>=Y, b_cut+1=O(log²Y), Q=O(Y^alpha), and strict power slack absorbs logs. This upper applies to ORIGINAL retained source mass, not just the new direct mass. By (2), k<=Y^delta would force h<=C1 Y^delta because r/p bounded and Q=o(Y). Hence outside o(NH) source mass both
    h>Y^delta,  k>Y^delta,                              (4)
and both ordinary postheights exceed 2Y^(1+delta). In particular reset first targets (k=0) and bounded multipliers have negligible original weight, WITHOUT assuming a sparse consumer support. Combining section2 re-pairing and (4), macro actual direct height transport can be selected entirely between deep nonreset endpoints with distinct labels, fast target and low relay. For any fixed A' their subsequent short relays of gain <=A'Y from these source postheights are reset-free by XXXII. This last implication does not justify retrospectively replacing hypothesis (1) for the original shallow population with only low nonreset scarcity: that replacement is valid when the original population is already deep as in section1. Nor does it show that deep multiplier states are impossible.

## 5. Polynomial labels: forced local state diversity and range at arbitrary baseline

If Y>=X^a fixed a>0, b_H=O_a(1) since H=O(X). Thus if a bin has fast-pair original source mass >=rho0 L then (3) in BOTH directions gives
    |S_j^*|, |T_j^*| >> L/[Y(1+L/Y²)(b_cut+1)(Q+1)]
                     >> min(Y,L/Y)/[(b_cut+1)(Q+1)].      (5)
No assumption of target label count. There are Omega(NH/L) such bins with source support <=C2 log²Y if total fast original mass macro: each bin mass O(L+Y), and discard high-support bins via Markov with sufficiently large fixed C2. On such a bin let R_s be the ordinary source postheight range. Each p permits at most 2+(R_s+6)/(2p) multipliers, so |S_j^*|<=s_j(3+R_s/Y). In particular (5) implies
    R_s >> Y min(Y,L/Y)/[(b_cut+1)(Q+1)log²Y]
for large Y (subtract the lower-order O(Y) term), hence R_s>=Y^(1+delta) eventually for alpha+delta<sigma. This range bound holds regardless of inherited high baseline. Actual selected-post absolute variation on each bin is >=R_s; sum ranges only over disjoint original tag-bins, not per source label. Therefore total actual selected-post variation >= const (NH/L)Y^(1+delta). More generally (3) directly upper bounds any restricted range population with R_s<=Y^(1+delta) on polynomial labels by o(NH), even with unrestricted source absolute height. Target-side state diversity (5) holds without a range bound; if target label support also small one obtains the analogous target range lower, but no proof of that support bound here. No unconditional macro variation or macro missing follows.

For polynomial scales, the direct first-pair label-gap count can also be localized without long CRT: fixed E<=b, |p-r|<=A0 distinct, both primes comparable Y, <=O(Y A0/log²Y) candidate label pairs by direct 0782bd1 section2, at most 1+L/Y² starts and O(Y) weight each. Thus per bin F_gap<< (L+Y²) A0(b+1)/log²Y, and summed original bins F_gap<<NH (1+Y²/L) A0(b+1)/log²Y. This gives the direct gap/relay tradeoff when L>=cY², but not uniformly at shorter L; the depth proof (3)-(4) does not rely on it.

## 6. Scope and finite audit

Run node research/min_unified_first_high_depth_audit.mjs 4096 16384 65536. Extended six actual prime-root runs and 48 finite controls. From actual extracted source weights find earliest actual target and first high successor, finite b_cut=floor(Y/8) (at least1), W=floor sqrtY. Some finite buffer targets below Y have no first high by that target; skip them, unlike the high-only theorem. Some finite short successors are not downward; skip them too. Check disjoint strict low gain, rough extended endpoints where finite cutoff allows, exact direct last-up overlap above6 and lower bound (including low-height correction), nonincreased re-pair weights, disjoint fast endpoints, odd multiplier identity, both shifted divisor conditions, actual phase and CRT tuple capacities, shallow and two-sided state capacity, ranges. Finite data do not realize asymptotic support/budget/depth hypotheses; the inequalities (3)-(5) are mathematical deductions. No new full core graph/cumulative kernel test, independent sieve proof or Lean verification. Main/direct unchanged.

```json
{
  "controls": 48,
  "firstPairs": 12223,
  "firstMass": 306462,
  "firstLow": 127640,
  "firstLowReset": 0,
  "firstLowTail": 180034,
  "firstExtended": 61566,
  "firstFast": 2771,
  "firstFastMass": 64862,
  "firstActualDirect": 59894,
  "firstGuaranteed": 56808,
  "firstRetained": 59894,
  "firstOdd": 2771,
  "firstFactor": 5542,
  "firstPhase": 2771,
  "firstTuple": 2771,
  "firstTupleCap": 938464,
  "firstStateChecks": 2657,
  "firstRangeChecks": 5314,
  "firstShallow": 2111,
  "firstShallowMass": 52800,
  "firstShallowTarget": 1839,
  "firstReset": 0,
  "firstDeep": 660,
  "firstSourceState": 2771,
  "firstTargetState": 2771,
  "firstSourceLabels": 2770,
  "firstTargetLabels": 2759,
  "firstRough": 1430,
  "firstFourRoots": 1430,
  "firstDisjoint": 2771
}
```

Next: use direct fast deep pairs and their necessarily large state support to bound actual variation/height exposure, or derive the quantitative low-relay condition without assuming it. This route removes consumer-sparsity and long-product CRT requirements for the depth conclusion, not for XXXII's extra-alphabet saturation gap. Macro missing, broad guards, high source support, and low-relay alternatives remain. No strict NT overlap gap yet.
