# Integration XXXV: localized hyperbola sieve and logarithmic direct-transport loss

2026-11-26 JST. Parent 560e7b1feac211142396acd20ac745e9cd05bcbd. Direct preflight [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md). New: transfer the direct three-condition modular hyperbola sieve to sufficiently long ORIGINAL tag bins, including a short target-prime interval about 3p. The local product restriction is a curved strip, not a rectangle of cofactor length L/Y; we explicitly cover it by translated rectangles and pay their errors. Near saturation requires r~3p, so the short interval gives a stronger loss on direct height transport: order at least NH/log Y under the quantitative low-relay and near-minimal source-support hypotheses, and a fixed positive loss if the normalized low relay is O(log Y). No consumer support restriction, no multiplier restriction, no claim of final overlap loss.

## 1. Local setup and two counting routes

Canonical original prime-root ensemble as previously: C~X, B=ceil sqrt(7X), H=T+B~X/(log B)^.25, total actual gain <=NH. One original tag-bin of prehorizon length L, starting at C_*, with X^(15/16+eta)<=L<=H for FIXED 0<eta<1/16 (if interval empty no application). Y->infinity, Y<=B, labels p,r in [Y,KY] also <=B, K fixed. Actual first pairs from an upward event to the next actual p>=Y event; intermediate labels <Y. Let E be strict intervening gain, E<=b<Y-3. Weight <=K_w Y. No target wait condition for the counting result. Distinct p,r by same-label spacing; H_s=C=pq+e, H_t=rs+f=C+p-1+E, so rs=p(q+1)+a, a=E+e-1-f odd nonzero, |a|<Y. Source upward ensures both source neighbors avoid odd small primes f0<(p-1)/4. Direct's three exclusions at prime l>3, l<Y and l<(p-1)/4:
    r !=0, rs !=p+a, rs !=p+a-2e (mod l).
Exactly 3l-2 forbidden residue pairs, including either zero product residue, since r=0 already forbidden. No roughness assumed at target. Every actual pair corresponds to an integer (r,s) on rs=a mod p; at fixed p,E,e,f it determines C. At most one actual pair per C on a deterministic tag path.

Let target r be further restricted to ANY interval I of length at most 2 tau Y+2, with tau between c/(log Y)^D and a fixed constant, c>0,D fixed. It may depend on p and on the bin, e.g. |r-3p|<=tau Y. Intersect with [Y,KY] and r<=B. Claim uniform per source label and fixed E,sides, weighted necessary supply
    F(p,E,e,f;I) <<_(eta,K,K_w,c,D) tau L/log^3 Y.           (1)
We prove two routes to cover the whole growing label range at the stated L. This does NOT assert the bound on arbitrary shorter common cores (e.g. X^.7).

## 2. Lower label range Y<=X^(1/3)

Here L/Y² is a fixed positive power of X, hence >=Y^eps for some fixed eps>0. Fix r prime in I, r!=p. The starting C progression is mod pr; padded parameter length ceil(L/(pr))+2. On that progression source cofactor q and opposite neighbor pq+2e have two distinct roots at odd primes l<Y (coefficients p,r invertible). Use earlier translated 2D upper sieve with cutoff floor(min(Y,L/(pr))^(1/12)) reduced by fixed factor; error absorbed, log cutoff comparable to log Y. Actual candidate count << L/(pr log²Y). For the prime r choices, ordinary translated one-dimensional upper sieve on the interval padded to length O(tau Y+1) gives << tau Y/log Y (tau>=c/log^D Y). One may use the same fixed-dimensional Selberg proof from the prior direct notes. Weight O(Y) per candidate. Summing proves (1). No need to approximate the actual product strip by a rectangle in this range.

## 3. Larger labels: cover the local product strip

Y>=X^(1/3). Set R=max(1,floor(LY/X)). Eventually LY/X grows by a fixed power. Split the integer r interval into consecutive intervals of length <=R. At most O(1+X/L)=O(X/L) such intervals even for full comparable band. For each interval I_i=[r0,r1], all actual cofactors s are in
    J_i=[ floor((C_*+p-1+E-f)/r1), ceil((C_*+L+p-1+E-f)/r0) ] intersect positive integers.
Because r~Y, C_*~X, p+E=O(Y), and r1-r0<=R, the length is O(1+L/Y+XR/Y²)=O(L/Y). This is why merely using one rectangle with cofactor length L/Y is invalid; the cofactor changes with r even at fixed C. The union may overcount candidates outside the true product strip, which is harmless for upper bounds. Sum_i |I_i|<=O(tau Y+1). Total area sum_i |I_i||J_i|=O(tau L).

For each rectangle and squarefree d coprime to p, direct section2's elementary complete Kloosterman bound O(p^.75) applies. For residue pair mod d, Fourier inversion, progression nonzero normalized l1 O(log(2p)), zero components bounded by O(|I_i|/p+1/p) and O(|J_i|/p+1/p). Using the direct long-rectangle proof, actual count in each residue pair is
    (p-1)|I_i||J_i|/(p² d²)
      + O_K(Y^.75 log²(2Y)(1+L/Y²)).
Rounding arithmetic progressions contributes O(1+L/Y²), absorbed. This estimate remains valid with a short I_i; we are not assuming uniform distribution of the zero mode. Summing boxes, total main coefficient N0=O(tau L/Y); error per residue pair O((X/L)Y^.75 log²Y(1+L/Y²)). Relative to L/Y, the error factor without logs is
    X Y^1.75/L² + X/(L Y^.25)
       << X^(-2eta)+X^(-1/48-eta),
using Y<=B=O(sqrt X) and Y>=X^(1/3). The inequalities hold up to fixed constants, including near the adaptive ceiling B. Thus there is a fixed power saving uniform in the high range.

Now apply the exact three-condition Selberg quadratic form of direct 14c6176, using squarefree support d<=z=Y^gamma for a sufficiently small FIXED gamma>0 in eta (e.g. gamma=min(eta/16,1/512)). All primes used >3 and below (Y-1)/4. The local density rho(l)=3l-2 yields G(z)>>log³ z as in direct. Quadratic error amplification <=z^8 (rho(lcm)<=lcm², |lambda_d|<=d). It is still O((L/Y)Y^-c_eta), absorbing log²Y, whereas tau>=c/log^D Y. Sieve surviving pair count << tau L/(Y log³Y). Weight by O(Y) proves (1). Constants uniform in the choice of interval and actual adaptive supports. No singular-factor average, no product CRT progression length, no multiplier cap. The proof uses the elementary exponential sum and Selberg diagonalization already proved on direct; the finite audit below is not a re-proof of that analysis.

## 4. Source support versus low relay, locally

On original bins suppose aggregate actual distinct source labels sum s_j<=C0 (NH/L) log²Y. No sparsity on target support. For arbitrary actual first pairs with comparable endpoints and upward source, source weight <=K_wY, strict low interiors disjoint (consecutive physical high events), write F total weight, G_low all actual gain p<Y, q=Y G_low/(NH). Full interval tau=O_K(1) in (1), summing E<=b, sides, actual supports, gives
    F <= C NH (b+1)/log Y + K_w Y G_low/(b+1).          (2)
This localizes direct (7) even when actual local source sets vary completely across bins; no multiplication of whole-lifetime error per short core. If F>=rho NH, choose b=floor(c log Y) with small fixed c to force q>>log Y. Equivalently low gain >=c NH log Y/Y. General support form before substitution:
    F <= C L(b+1) sum_j s_j/log³Y + K_w Y G_low/(b+1).
For q=o(Y) and macro F, choose b+1 comparable to a sufficiently large fixed multiple of (1+q) (b<Y-3 eventually); then (L/(NH))sum_j s_j * (1+q)>>log³Y. In particular q=O(1) forces mean local source support Omega(log³Y), not just log²Y. These statements apply also to XXXIII's original source weights re-paired to the first high successor before fast reduction, if both endpoints comparable as there. A deep starting subpopulation d'_s>6+AY with actual strict relay gain<=AY can replace G_low in the tail by low NONRESET gain, since no reset can occur there. The overall gain budget below still counts all actual gain, including resets.

## 5. Prime-ratio rigidity of near-saturated direct pairs

Now use actual disjoint upward/downward first pairs, not original long-range cross weights. Let u_i=2w_s-g_s>0, v_i=g_t-2w_t>0, m_i<=min(u_i,v_i) actual direct chronological matched mass. Denote M=sum m_i>=rho NH, G_U,G_D source/target gains, G_O=G_all-G_U-G_D. Let n=#pairs, define previous XXXIV slack
    Delta=G_all-4M/3+4n/3 = A/3+D+G_O,
    A=3G_U+4n-M, D=G_D-M.
All three summands nonnegative. Put a_i=2p_i-w_s>=0. Then u_i=3p_i+1-2a_i and v_i=r_i-1-2w_t. Exact relation
    r_i-3p_i=v_i-u_i+2-2a_i+2w_t.
Sum absolute values, using sum|v-u|<=A+D, 2sum a<=A and 2sum w_t<=D:
    sum_i |r_i-3p_i| <= 2(A+D)+2n <= 6 Delta+2n.        (3)
No extra charge to baseline drift; these are alternative uses of the SAME saturation slack. Thus direct matched weight with |r-3p|>tau Y is <=K_w(6 Delta+2n)/tau. Small slack forces nearly all saturated pairs to use r near THREE TIMES p, not near p. This uses the upper bound w_s<=2p and the exact down length, not the adjusted multiplier relation. If the comparable band excludes r~3p altogether, (3) alone gives a macro loss.

## 6. Logarithmic non-saturation theorem

Assume the hypotheses of section4 for these direct pairs, M>=rho NH and q=O(log²Y) (includes XXXIII's o(log²Y)), with the LONG original bins of section1. No consumer-support assumption; no target wait or multiplier cutoff needed. Choose integer b+1 comparable to C_rho(1+q), with fixed C_rho large enough to discard at most rho NH/4 direct mass from E>b by strict low relay disjointness. Eventually b<Y-3. Set
    tau=c0 min(1, log Y/(b+1)),
where fixed c0>0 sufficiently small depending on constants and rho. In this range tau>=c/log Y, so (1) applies to I=[3p-tau Y,3p+tau Y] and yields
    F_near(E<=b) <= C NH tau(b+1)/log Y <=rho NH/4.
Here constants in (1) can be chosen uniform for tau>=c/logY with any fixed c: the error is polynomially small and the logarithm of the interval length comparable to logY for sufficiently large Y (threshold may depend on c); thus the choice of c0 is not circular. At least rho NH/2 remains at |r-3p|>tau Y. By (3), n<=NH/(Y-1), so
    Delta >> NH min(1, log Y/(1+q)),
    G_all-4M/3 >> NH min(1, log Y/(1+q)).             (4)
The O(NH/Y) adjustment is absorbed uniformly for q=O(log²Y). Equivalently
    M <= 3G_all/4 - c NH min(1, log Y/(1+q)).
This is stronger than XXXIV's NH/(Y^alpha log^4Y) in the stated long-bin regime, and uses no sparse combined endpoint alphabet as in XXXII. If q=O(log Y), the loss is a FIXED positive fraction of NH. If q=o(log²Y), the gap divided by NH/logY tends to infinity (constants fixed), though it need not be macro. Conversely saturation slack o(NH) requires q/logY->infinity along that sequence. This precisely identifies an intermediate low-relay region: macro near-minimal first supply forces q>=c logY; near-saturation further requires q much greater than logY. The theorem applies to direct matched population, not the earlier original cross mass. Does not derive saturation from finite twins or exclude q growing between log and log². Does not apply to X^.7 bins merely by replacing L with H: source support on coarser bins must satisfy the stated aggregate condition. The long-bin hypothesis is a new restriction.

## 7. Audit and scope

Run node research/min_unified_local_hyperbola_ratio_audit.mjs 4096 16384 65536. Six actual prime-root runs and 48 threshold/bin controls. Generate all actual upward-first comparable high pairs within bins, check product relation, nonzero hyperbola for finite E cutoff, three exact local exclusions including zero product residue, disjoint strict low relay budget. Restrict to finite near-3p ratio intervals, cover actual cofactor strip by explicit integer rectangles, enumerate necessary modular-hyperbola points passing finite small-prime conditions, verify coverage and capacity. For actual downward first targets with small relay use last-up height overlap above6 from source interval and minimum intervening height; check exact clock slack, event disjointness, actual prime ratio and weighted ratio tail. Separate finite exact density checks. Finite controls do not establish asymptotic near-minimal support, low-relay regime, long-bin scale, exponential sum constants or sieve estimates; direct a98ccdf has separate Fourier diagnostics. No full cumulative kernel/core rerun or Lean. Main/direct unchanged.
```json
{
  "controls": 48,
  "densities": 144,
  "firstPairs": 96132,
  "firstMass": 6952612,
  "lowGain": 1592240,
  "lowChecks": 122416,
  "hyperbolaChecks": 53778,
  "threeConditions": 98289,
  "zeroProductCases": 34188,
  "boxGroups": 3327,
  "rectangles": 32587,
  "boxActual": 3333,
  "boxMembership": 3333,
  "boxCandidates": 158719,
  "boxSurvivors": 151450,
  "directPairs": 21913,
  "directMass": 471648,
  "ratioChecks": 21913,
  "ratioSum": 1807336,
  "ratioTailMass": 439752,
  "nearMass": 31896,
  "delta3": 35313574,
  "disjointChecks": 17395,
  "matchChecks": 25875
}
```
Next: remove the long-bin restriction via short product-strip estimates, or derive q=O(logY) and near-minimal support on a branch where near saturation is forced. Need connect M to overlap loss (different measures). Final twin contradiction open.
