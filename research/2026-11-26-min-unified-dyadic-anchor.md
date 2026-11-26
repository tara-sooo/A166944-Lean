# Integration XLIV: dyadic-rank obstruction for general integer-multiple endpoint clusters

2026-11-26 JST. Parent 928087104ac710306919017f46a92cdd874e03a5. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). New: extend XLIII's common-anchor corollary from ODD anchor coefficients to arbitrary bounded positive integer coefficients. The even-coefficient escape can only advance a bounded dyadic rank. A closed inventory excursion with no rank descent necessarily has a nonzero signed capacity imbalance. This gives a quantitative loss without changing original edges, even with arbitrary split/merge. The common-anchor assumption is still conditional; no claim that it follows from XXXIX.

## 1. Original population and exact adjacent endpoint identity

Use XLIII's arbitrary retained actual last-up mass M on each whole canonical tag, endpoint labels >=Y>=11, G<=H. A=3G_U+4n_U-M, D=G_D-M, Delta=A/3+D+G_O=G-4M/3+4n_U/3. All components nonnegative. P=max actual open inventory; d'<=6+5Delta+P. For actual consecutive retained endpoints p,q (any signs), ordinary adjusted multipliers h,k and sigma=-3 at next source, +1 at next target, have 2hp-(2k+sigma)q=c odd. For any J distinct adjacent transitions, sum|c|<=5Delta+7J. For positive integers a,b with a ODD, a,b<=D_* and |ap-bq|<=W, the determinant
    [2hb-(2k+sigma)a]q=a c-2h(ap-bq)
has an odd nonzero bracket, even when b is even. Consequently for J such transitions
    Delta >= J [Y-7D_*-W(6+P)/Y]_+ / [5(D_*+WJ/Y)].
If Y>=28D_* and W(6+P)<=Y²/4, then
    Delta >= YJ/[10(D_*+WJ/Y)].                         (1)
This is the forward-oriented version of XLIII; no oddness of b is needed. Actual adjacent endpoints only; omitted selected endpoints cannot be treated as complementary gain. All original transport edges and weights remain unchanged.

## 2. Common anchor with arbitrary integer coefficients

A closed excursion is a contiguous segment of the actual endpoint list beginning and ending at zero retained open inventory. Use maximal nonzero excursions, or any disjoint union of entire closed excursions. Select any family of such excursions on each tag. For every endpoint on a selected excursion assume there exists a COMMON positive real Z (can vary by excursion) and integer c_i in [1,D_*] such that
    |p_i-c_i Z|<=W0,   Y<=p_i<=KY.
Here D_*,K fixed, W0=o(Y) uniformly, Y->infinity. No restriction on the parity of c_i; no support count, no sparsity, no relays cut, no unique endpoint assumption. If several certificates exist, choose any one for the whole excursion. The anchor satisfies Z>=(Y-W0)/D_*.

For adjacent endpoints set g=gcd(c_i,c_(i+1)), a=c_(i+1)/g, b=c_i/g. Then |ap_i-bp_(i+1)|<=2D_* W0=:W. Write v2(c) for the exponent of 2 in the positive integer c. If v2(c_(i+1))<=v2(c_i), a is odd, so the transition is subject to (1), INCLUDING the case of even b. The only edges not covered by this argument have strictly increasing dyadic rank. Each strict ascent has at most R-1 steps, R=1+floor(log2 D_*). On an excursion with n endpoints and J_exc nonascending transitions, partition into maximal strictly increasing runs:
    n<=R(J_exc+1).
When J_exc>=1 this gives n<=2R J_exc. This needs no assumption about the order of labels by magnitude; the rank is the 2-adic valuation of the COMMON anchor coefficient, not of the actual odd prime.

## 3. The zero-inventory condition eliminates a free strictly ascending excursion

Let A_exc=sum_sources(3p+1-x), D_exc=sum_targets(p-1-x), where x is the nonnegative endpoint mass (outgoing or incoming). Each is nonnegative. Since the excursion is closed, sum source x=sum target x=M_exc. Thus their difference is
    A_exc-D_exc=3 sum_source p - sum_target p + n
              = Z T + n + error,
    T=3 sum_source c_i - sum_target c_i, |error|<=3n W0.
If J_exc=0, all ranks strictly increase, so the first coefficient has a unique minimal v2. Its sign-weighted factor is odd (3 or -1). Hence T/2^v2(c_1) is an odd nonzero integer and |T|>=1. In particular exact signed capacity balance at the anchor is impossible, even with both even and odd coefficients. Since n<=R,
    A_exc+D_exc >= [ (Y-W0)/D_* - R(3W0+1) ]_+.
For fixed D_* and W0=o(Y), eventually this is >=Y/(2D_*). This is a per-excursion charge on actual unfilled capacities, not a new physical gain. It does not assume that the true deficit returns to 6, only that retained inventory returns to zero. For nonzero-inventory cuts the corresponding identity includes the inventory difference; the zero-cut condition cannot simply be removed.

## 4. Quantitative theorem for the original branching population

Let M_g be total actual mass on the selected anchored closed excursions on one tag; J the number of their nonascending adjacent transitions. Different excursions are disjoint in endpoint events, so sum(A_exc+D_exc)<=A+D<=3Delta. Each excursion's mass <=(3K+1)Y n. For J_exc>=1 use n<=2R J_exc; for J_exc=0 use n<=R and the imbalance lower above. With C_*=6(3K+1)D_* R, obtain
    M_g <= C_* (YJ+Delta).                             (2)
This is the new step: high-mass anchored excursions cannot all avoid the odd-numerator obstruction at negligible slack by being short. Combine (1) with J<=H/(Y-1):
    Delta >= M_g/[C_* (1+10D_*+10WH/[Y(Y-1)])].          (3)
Assumptions for (3): common anchor as above on the selected closed excursions, Y>=28D_*, W(6+P)<=Y²/4, and (Y-W0)/D_*-R(3W0+1)>=Y/(2D_*). For P<=K0Y uniformly and W0=o(Y), all hold eventually for fixed K0,D_*. Sum whole original tags, M_g,all=sum M_g, and subtract the explicit correction 4sum n_U/3<=4NH/[3(Y-1)]:
    G_all-4M_all/3 >= M_g,all/[C_*(1+10D_*+10WH/[Y(Y-1)])]
                        - 4NH/[3(Y-1)].                (4)
In particular if M_g,all>=rho NH, this gives a fixed positive saturation gap when W0=O(Y²/H), W0=o(Y), P=O(Y), with NO parity restriction on anchor coefficients, no small branching, no near-minimal support, no long bin or small-relay assumption. It is a bound on total ORIGINAL M_all, not only on M_g,all: slack is computed for the entire original population. In a near-saturation sequence under those uniform width and inventory conditions, the actual mass on such anchored excursions must be o(NH). More generally if WH/Y²=o(Y), the correction is absorbed and the loss is Omega(NH min(1,Y²/(WH))) for macro M_g. This includes conditional submacro widths discussed in XLIII. For W=0 read the expression with no division by W.

One may also retain exact J, local P_i, or the stricter actual imbalance in (2). These are alternative bounds on the SAME slack. No sum of the odd obstruction, the baseline cost and the imbalance as independent physical resources. The common anchor must fit the actual endpoints of each complete excursion, including consumers. XXXIX's clustered UPWARD source support alone neither produces such anchors nor forces bounded integer coefficients across all endpoint transitions. No proof of an anchored macro population, of saturation from finite twins, or of final NT-scale overlap loss.

## 5. Finite diagnostics

Run node research/min_unified_dyadic_anchor_audit.mjs 4096 16384 65536. Extend XLIII six actual prime-root runs/48 controls with original unmodified last-up edges. Search finite common anchors by exact interval endpoints for D_*=2,4,8, W0=0,1,max(2,floor(Y/16)); finite real arithmetic uses tolerance 1e-8 (input labels and bounds integers, candidate anchors rational). Count actual covered excursions and branching, verify signed capacity balance, reduced numerator parity, nonascending determinant, dyadic run inequality, unique minimum for strict excursions, disjoint slack, exact and simplified lower where finite hypotheses apply. Independent abstract coefficient words exhaust bounded ranks and sign masks on strict words, plus capacity-balanced words of length4. These independent words are not MIN paths. Finite controls do not realize all asymptotic hypotheses; no analytic sieve used, full core/kernel rerun or Lean verification.
```json
{
  "totals": {
    "controls": 48,
    "tags": 24454,
    "edges": 41658,
    "M": 1002656,
    "endpointN": 74294,
    "transitions": 49840,
    "anchorControls": 220086,
    "anchorExc": 110712,
    "anchorMass": 2119892,
    "anchorEnds": 237266,
    "dyadicEdges": 126554,
    "dyadicAsc": 41397,
    "dyadicNonasc": 85157,
    "strictExc": 33223,
    "strictMass": 784758,
    "strictImbalance": 3447220,
    "strictPositive": 794,
    "strictSimple": 66,
    "dyadicIdentity": 85157,
    "dyadicBound": 220086,
    "dyadicCombined": 34958,
    "dyadicMacroEligible": 5904,
    "dyadicLower": 2196.299834606345,
    "dyadicSplitExc": 12950
  },
  "independent": {
    "cases": 310300,
    "strict": 214,
    "strictOdd": 1340,
    "closed": 80,
    "nonasc": 310086,
    "maxRun": 4
  }
}
```
Main/direct unchanged. Next: derive common anchor structure (or replace it by a bounded-rational graph with controlled certificate growth), and connect original overlap loss to actual transport saturation. No final twin-prime contradiction.
