# Integration XXXVI: four-form cycle-gap rigidity and fixed non-saturation without low-relay scarcity

2026-11-26 JST. Parent fb20d9c5f20b7f13f242f9e672c485c04d34a9f9. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md). New: use the ratio rigidity of XXXV on the COMPLETE cycle from one upward source to the next upward source. Near saturation would force the prehorizon gap to concentrate around 4p. Both sources are rough, so the old four-condition sieve (XXX) now controls this concentration. This yields a fixed positive loss in the conditional direct-transport budget with NO small-low-relay assumption and no consumer-support bound, at the lower/intermediate label scales where the local pair CRT has polynomial length. Not a global overlap gap.

## 1. Exact cycle gap ledger

Original prime-root tagged complete paths, total gain G_all<=NH, bins of length L<=H by prehorizon. Retain actual direct height pairs s_i,t_i with upward source and downward target, both label p_i,r_i in [Y,KY], Y->infinity, K fixed, <=B. In each tag-bin assume actual chronological nonoverlap s_i<t_i<s_(i+1), and both endpoints in the bin. This includes disjoint consecutive-high up/down pairs of XXXIII–XXXV. No restriction on the actual relay gain, target wait, source multiplier, or total low gain. More generally arbitrary ordered nonoverlapping pairs with actual matched mass m_i<=min(u_i,v_i) work; the counting below uses only their upward sources. M=sum m_i; u_i=2w_s-g_s>0, v_i=g_t-2w_t>0. No reuse of other cross-transport mass. Put n=#pairs, G_U,G_D endpoint gains, G_O=G_all-G_U-G_D>=0, A=3G_U+4n-M, D=G_D-M. Nonnegative slack Delta=A/3+D+G_O=G_all-4M/3+4n/3. From XXXV
    sum_i |r_i-3p_i|<=2(A+D)+2n.
For two consecutive RETAINED pairs in the same original bin put d_i=C_(s_(i+1))-C_(s_i). Their intervening physical gain contains source gain p_i-1, target gain r_i-1, and complementary actual gain e_i>=0 (inside the pair and after the target, before the next source). Exact identity:
    d_i-4p_i=r_i-3p_i-2+e_i.
Complementary interiors of these cycle gaps are disjoint on each tag; each has no retained endpoint besides those removed in the formula. Hence sum e_i<=G_O. Sum across all original bins and tags:
    sum_i |d_i-4p_i| <= 2(A+D)+G_O+4n <=6 Delta+4n.       (1)
This is the SAME slack as XXXIV's baseline drift and XXXV's ratio rigidity, not another additive charge. It counts even large intervening low or high events; no cutoff on their gain. Charge each transition with its STARTING matched mass m_i<=3KY+1. Last pair in each bin loses at most O(Y), total O(NHY/L) for L<=H. For 0<tau<=1/2, weighted far-gap mass with |d_i-4p_i|>tau Y is at most
    (3K+1/Y)(6 Delta+4n)/tau.                            (2)
At near saturation, Delta=o(NH), for any fixed tau>0 all but o(NH) weight has cycle prehorizon shift within tau Y of 4p_i. Unlike the earlier single source-to-target ratio, this gives TWO rough endpoints within the sparse SOURCE support.

## 2. Local capacity for near-fourfold source transitions

Assume L>=Y^(2+epsilon) for fixed epsilon>0, L<=H. This implies L/Y->infinity. In a given bin let S be actual distinct retained source labels, s=|S|. Consecutive retained sources are genuine upward events, so both source horizons C and C+d have both neighbors free of odd primes f<(min(p,q)-1)/4, by the competing clock rule. (q denotes the NEXT source prime here, not a cofactor.) Neither target is required rough. For fixed distinct p,q in S, sides e,f and shift d with |d-4p|<=tau Y, necessary horizon CRT C=e mod p, C+d=f mod q, one progression mod pq. Every candidate C can occur at most once on the original tag. The four forms C+-1,C+d+-1 on this progression have four generic roots for primes l>4 below Y unless l divides d(d²-4). Here d~Y, d>2. Apply the same translated four-condition Selberg estimate as XXX, cutoff min(Y,L/(pq))^(1/12) reduced by a fixed factor, padded interval ceil(L/(pq))+2. The polynomial length hypothesis ensures log cutoff comparable to log Y, error absorbed. Weight by <=3KY+1 and sum sides: fixed tuple capacity
    << L J(d)/(Y log^4Y), J(d)=J4(d)J4(d-2)J4(d+2),
where J4(v)=prod_(prime l>4 dividing v)(1-4/l)^(-1).
Use XXXI's translated-interval singular-factor average, not the weaker arbitrary-subset Cauchy bound: for interval I of length h in [1,O(Y)], sum_I J(d) << h+log^12(3Y). Indeed J4(v)^3 has nonnegative squarefree divisor coefficients a(l)=O(1/l), sum a(m)/m converges and sum_(m<=O(Y))a(m)=O(log^12Y); apply the divisor count h/m+1, then Holder to three shifted factors. Thus if tau Y>>log^12Y, sum over |d-4p|<=tau Y is O(tau Y), uniformly in p and even for adaptive actual shift subsets by positivity. Distinct-source near-gap mass per bin
    F_near,distinct <= C L s² tau/log^4Y.                 (3)
The constant is independent of tau in the stated range (epsilon,K fixed). No assumed independent shifts, no same-label separation or return-gap hypotheses.

Same-source-label case q=p must not use modulus p². Both horizons C=e+p z and C+d=f+p z' with odd cofactors z,z', so d=2mp+f-e, m>=1. Since |d-4p|<=Y/2 and p>=Y, for sufficiently large Y this forces m=2, d=4p+f-e. Fixed p and sides now one progression mod p with four horizon-neighbor forms, same generic root condition; padded length ceil(L/p)+2, logarithm comparable to logY. Weight O(Y), candidate count gives << L J(d)/log^4Y. Uniform elementary bound J(d)<< (loglog(3Y))^12 by splitting prime divisors at log Y (d,d+-2=O(Y), nonzero). Summing s labels gives
    F_near,same << L s (loglog(3Y))^12/log^4Y.             (4)
The singular factor bound may be improved but is sufficient. The result counts only necessary candidates, not actual reachability. It is valid for arbitrary actual subsets including core-selected pairs, if bin length and support hypotheses hold on the original tags. It does not count a downward target as rough.

## 3. Fixed conditional non-saturation, without any low-gain bound

Assume M>=rho NH and aggregate original local source support sum_j s_j<=C0 (NH/L)log²Y for fixed rho,C0>0. A bin's total M_j is O_K(L+Y)=O(L) by monotone actual source prehorizons and distinct source gains. There are O(NH/L) original bins. Discard entire bins with s_j>C1 log²Y, losing <=rho NH/4 by Markov for fixed large enough C1. The remaining bins have M>=3rho NH/4; last source masses O(NHY/L)=o(NH). The near-gap mass from (3) summed over these bins is <=C' C1² tau NH, and the same-label term (4) is o(NH). Choose fixed tau in (0,1/2] small enough so near-gap mass <=rho NH/4 eventually. Thus far-gap mass >=rho NH/4, while (2) bounds it by O_K((Delta+n)/tau) even if using the FULL original slack before discarding bins. Since n<=NH/(Y-1)=o(NH), obtain
    G_all-4M/3 >= c NH,
    M <=3G_all/4-c' NH,                                (5)
for sufficiently large X, with fixed c,c'>0 depending on rho,C0,K,epsilon. Equivalently, on this conditional macro population the transport saturation fraction is strictly below 3/4. There is NO hypothesis q=Y G_low/(NH)=O(logY), or even q=o(Y). No near-minimal consumer support, no same-label return constraint, no fast-target requirement, no low reset exclusion, no narrow guard or multiplier cap required for (5) itself. To PRODUCE a macro ordered direct population from the earlier general matched transport, XXXIII still requires its separate hypotheses (or another proof). We cannot infer (5) for arbitrary overlapping source-consumer arcs or the original pre-repair matched mass. We cannot transfer the local source support to coarser bins without checking. The pair-scale length L>=Y^(2+epsilon) matters, in particular top labels near sqrt X may not fit even L=H. XXXV's hyperbola argument remains useful there. For L~X^.7 this theorem applies for e.g. Y<=X^.3 with suitable epsilon, not at all scales.

## 4. Support versus saturation tradeoff

More generally let Sbar=max(log²Y,(L/(NH))sum_j s_j) and assume Sbar=O(log^(4-zeta)Y) for a fixed 0<zeta<=2. Discard bins s_j>C1 Sbar at the same small loss; (4) sums to O(NH Sbar(loglog)^12/log^4Y)=o(NH). Choose tau=c0 min(1, log^4Y/Sbar²), c0<=1/2 fixed small, so tau Y>>log^12Y and (3) is <=rho NH/4 after summing. The last mass is unchanged. By (2) and n=O(NH/Y), which is negligible relative to NH tau,
    G_all-4M/3 >> NH min(1, log^4Y/Sbar²).                (6)
This makes explicit the required expansion of source support if macro direct transport approaches saturation. In particular under L>=Y^(2+epsilon) any macro direct population with G_all-4M/3=o(NH) must satisfy (L/(NH))sum s_j/log²Y -> infinity (otherwise apply (5) along a bounded subsequence). No upper on actual support is proven; the large-support branch persists. Neither (5) nor (6) is a positive constant loss in XVII's overlap inequality: M is actual DIRECT matched height transport, not the overlap clock. No proof that finite twins force this saturation or a macro direct transport of the required type.

## 5. Finite diagnostics

Run node research/min_unified_cycle_gap_saturation_audit.mjs 4096 16384 65536. Standalone six actual prime-root runs, 48 threshold/bin controls Y11/17/31/61, L=H or floor(H/2), K6, finite near threshold floor(Y/2). Construct all actual consecutive-high upward/downward pairs in bins with positive direct last-up overlap above 6 (computed by the minimum intervening deficit), NO low-relay cutoff. Verify nonoverlap, ratio and cycle identities, complementary gain disjoint budget, exact adjusted saturation slack and weighted near/far/last partition, actual same/different source-label congruence, generic four-root collisions and finite CRT candidate capacity. Finite controls are not assumed to realize macro near-minimal support, asymptotic pair-scale length or saturation. No independent analytic sieve proof, full kernel/core rerun or Lean verification. Main/direct unchanged.
```json
{
  "controls": 48,
  "bins": 122416,
  "nonempty": 22703,
  "pairs": 29671,
  "M": 726042,
  "G": 43258576,
  "Gu": 1388602,
  "Gd": 1569636,
  "Go": 40300338,
  "slack3": 126990244,
  "ratioAbs": 2824620,
  "gapAbs": 1715048,
  "gapOutside": 1834716,
  "gapChecks": 6968,
  "firstPairLow": 284028,
  "lastMass": 595894,
  "transitionMass": 130148,
  "nearMass": 10496,
  "farMass": 119652,
  "sameMass": 412,
  "distinctMass": 10084,
  "sameChecks": 64,
  "distinctChecks": 300,
  "rootChecks": 642,
  "tupleChecks": 364,
  "finiteCandidates": 15693,
  "finiteCapacity": 678264,
  "sourceLabels": 28714,
  "largeRelayPairs": 3361,
  "sameTuple": 64,
  "distinctTuple": 300
}
```
Next: remove the local pair-scale restriction near the top, or derive the near-minimal source support / ordered direct macro saturation from the original clock ledger. The low-relay loophole for this lower-scale saturation theorem is closed; high-support and non-direct alternatives remain. Final NT-scale overlap loss open.
