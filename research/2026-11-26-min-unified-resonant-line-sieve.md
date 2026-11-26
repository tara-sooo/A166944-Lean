# Integration XXXVIII: resonant line average and all-label constant gap on long original bins

2026-11-26 JST. Parent 74032ffab29ee99639c9680febdaa621ff552692. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md). New: sieve the exceptional rational lines from XXXVII. The fully proportional cofactor line has bounded label degree. The nonzero lines have dimension four, with a uniform mean correction even for primes dividing a line direction coefficient, provided the local interval of line indices has logarithmic length. The remaining short index intervals have a sparse label relation on sufficiently long bins. This removes the resonance exception at the top label scale on original lifetime-sized bins, under the same conditional macro direct transport and near-minimal source support hypotheses. No global clock-overlap gap.

## 1. Setup, line lengths and area

Use XXXVI--XXXVII actual ordered nonoverlapping up/down pairs, comparable labels [Y,KY], original tag-bins L<=H, actual direct matched mass M>=rho NH, aggregate source supports sum s_j<=C0(NH/L)log²Y. Fix L>=Y^(1+epsilon) and polynomial labels Y>=X^a0 for fixed a0>0 in this note (smaller labels can use XXXVI if L>=Y^(2+epsilon)). Actual source horizons C=p a+e and next C+d=q b+f, p!=q, |d-4p|<=tau Y, fixed 0<tau<=1/4. Put U=L/Y, R=floor(U/Y^kappa), 0<kappa<min(epsilon/3,1/8). Nonresonant pairs already bounded in XXXVII. Resonant pair has reduced positive A/h with h<Y^kappa, A=O_K(h), ell=hp-Aq nonzero and |ell|<=q/R. Define c=h b-A a; q c=ell a+h(d+e-f). In a given bin the allowed a interval has length at most U_p=L/p+O(1), and d interval width 2tau Y. Thus c is in an interval of real length at most
    D0=|ell| U_p/q + 2h tau Y/q.
Take a padded consecutive integer interval of length Kc<=D0+3 containing all possible c (may include extra values). On each line the integer direction is (h,A); the horizon gap changes by -ell per unit parameter. Its parameter interval has length at most
    V=min(U_p/h, 2tau Y/|ell|).
Both upper bounds in the minimum are >=c_tau Y^(epsilon-kappa), by |ell|<=q/R, h<Y^kappa, so a padded interval ceil(V)+2 has polynomial length even if the actual line is short. Also
    V D0<=4tau Y U_p/q=O_K(tau U).
If Kc>=log^gamma Y, gamma>0 fixed, then D0>=Kc-3 and (V+2)Kc=O_K(tau U) for large Y (Kc=O(Y^kappa), V polynomial, fixed tau). If Kc is smaller, (V+2)Kc=O_K(U) without a tau gain. Constants for the large interval conclusion can be uniform in fixed tau; thresholds in Y may depend on tau. Padding does not change the actual event count. No assumption that the whole strip lies in a single line.

## 2. The proportional c=0 case

If c=0, then a=h t,b=A t, positive integer t, since gcd(h,A)=1. Actual cofactors a,b are odd, and because both sources are upward they have no odd prime factor <(Y-1)/4. For sufficiently large Y, h,A=O(Y^kappa)<(Y-1)/4. Any prime dividing either coefficient is forbidden (2 by parity). Thus ACTUAL c=0 candidates require h=A=1, a=b. The gap d=(q-p)a+f-e is positive and <=(4K+1)Y. The actual eligibility p²<=C+1 gives a>=(p²-1-e)/p>=p-2/p. Hence q>p and 0<q-p<=O_K(1). In each bin each source p has O_K(1) possible q, independently of the entire support size. For fixed p,q,sides, the three forms a,pa+2e,qa+2f have three distinct generic roots at primes l>3 except l|pf-qe (nonzero for distinct positive p,q), with l=p,q omitted. A one-dimensional three-condition upper sieve on padded length L/p+2, cutoff a small fixed power of Y, gives weighted capacity << L (loglog(3Y))^3/log³Y. For instance the singular factor bound follows by splitting prime divisors of the nonzero O(Y) determinant at log Y. Summing O(s_j) possible edges and then bins yields o(NH). This does not require long bins L>=Y², only L>=Y^(1+epsilon). It uses actual roughness and eligibility, not primality of the cofactors. The c=0 line may occur; it is negligible in this conditional population, not impossible.

## 3. Nonzero line sieve with correct constant-coordinate correction

On c!=0, write a=a0+h t,b=b0+A t. Four affine forms a,pa+2e,b,qb+2f, for primes l>4 not dividing pqhA, have four distinct roots except l dividing
    D(c)=c(qc+2fh)(pc-2eA)(pqc+2fhp-2eAq).
The last three factors are nonzero by q not dividing 2h, p not dividing 2A, and p not dividing 2eAq, respectively. Thus D(c)!=0. All relevant |c|,|D(c)|,hA are polynomially bounded in Y since original C=O(X), Y>=X^a0. The bound is uniform over bins and signs. Define J(c)=prod_(l|D(c),l>4,l not dividing pqhA)(1-4/l)^-1.

For l>4 dividing hA, only one coefficient h,A vanishes mod l. If l|h, a=-c/A is fixed mod l, and b varies through all residues; if l|A, b=c/h is fixed and a varies. Thus there are EXACTLY two forbidden c residues mod l (one zero), and on an allowed c line there are exactly two forbidden t residues. Every actual line must satisfy all those c restrictions since l|hA implies l<=O(Y^kappa) in the roughness range. Let I(c) be their indicator and J_H=prod_(l|hA,l>4)(1-2/l)^-1. We may ignore l=2,3 in the line sieve (except actual proportional argument).

Use one-dimensional Selberg upper sieve on padded parameter interval ceil(V)+2. Choose cutoff z a sufficiently small fixed power of Y below the roughness threshold, and use the Euler-product/weighted Markov lower bound on its diagonal denominator over primes <=z^eta for fixed sufficiently small eta. If nu(l) forbidden roots, the bound is O((V+2) prod_(5<=l<=z^eta)(1-nu(l)/l)), plus power-saving error absorbed uniformly. This is the same proof as direct 14c6176: nu(l)<=4, weights <=l, discrepancy O(nu(d)), error <=O(z^6); choose z so it is small relative to V. If a constant coordinate is forbidden, the actual line is empty. Relative to generic product dimension four, collision primes cost at most J(c); at allowed l|hA the factor is (1-2/l)/(1-4/l)=(1-2/l)^-1(1+O(l^-2)). Primes p,q are above the cutoff. Extending all positive factors to their full products gives weighted count per line
    << Y (V+2) I(c) J_H J(c)/log^4Y.                  (1)
This keeps the TWO-root correction at direction-divisor primes, rather than discarding those primes and paying a four-root loss. The finite analytic constants depend on K,epsilon,kappa,a0, not the particular line. At fixed tau the power-saving error is absorbed eventually, including when tau is a small fixed constant.

## 4. Uniform average over nonzero c on logarithmic intervals

Claim for any translated interval of Kc>=log^gamma Y consecutive integers in the polynomial range of section3,
    sum_(c in interval,c!=0) I(c) J_H J(c) <<_gamma,a0,K Kc.     (2)
Proof extends direct cb54101's truncated-divisor mean; the direction-divisor restrictions must be treated as a sieve on c, not assumed independent.

Let y=Kc^eta0, with sufficiently small fixed eta0>0, and write zc=Kc^(1/16). Since Kc>=log^gamma Y, the product of singular factors at primes >y dividing any nonzero polynomially bounded integer is uniformly bounded (Mertens product between y and log Y, then at most O(logY/loglogY) prime divisors >log Y). This also bounds large factors of J_H. Drop I restrictions at primes >y for upper bounds. For c!=0 expand J_small(c) over squarefree d of primes 5<=l<=y not dividing pqhA, with coefficients W(d)=prod 4/(l-4) and d|D(c). As in direct cb54101, normalize expansion weights: mean log d<=sum_(l<=y)4log l/l=O(log y). Choose eta0 so this is <=(log Kc)/8; hence at least half the weight is on d<=Kc^(1/4), pointwise. Thus J_small(c)<=2 sum_(d<=Kc^1/4,d|D(c)) W(d).

For each such d, D(c)=0 mod d has <=4^omega(d) residue classes, all coprime as moduli to the direction-divisor primes. On each residue progression in the c interval impose I_small, the two forbidden c residues at primes l|hA,5<=l<=y. In progression parameter these remain exactly two forbidden residues (d invertible). The one-dimensional Selberg sieve supported on squarefree k<=zc of those primes gives upper count
    << (Kc/d) prod_(5<=l<=y,l|hA)(1-2/l)
uniformly. For detail, diagonal denominator >=constant times full Euler product of inverse (1-2/l) factors on that prime set: normalize all squarefree weights, mean log k<=O(log y), choose eta0 so <=(log zc)/2, then truncate k<=zc. Rounding error in the quadratic form <=O(zc^6)=O(Kc^3/8), since root multiplicity <=l, |lambda_k|<=k, lcm<=k1*k2. This is absorbed in Kc/d>=Kc^3/4 times product >=c/log²(3Kc), uniformly. If c=0 is included by this upper count it only enlarges the truncated sum; no evaluation of J(0) is made. This proof also covers the empty direction prime set.

Multiply the upper count by J_H, cancel its small-prime product exactly and absorb its large factors. Summing d with W(d) 4^omega(d)/d costs a convergent Euler product prod_(l>4)(1+16/(l(l-4))). This proves (2). In particular the constant in (2) is independent of the choice of h,A or interval translation. A mere worst-case loglog loss on every direction coefficient would not suffice for the fixed-gap conclusion.

## 5. Large line-index intervals and the remaining short-index relation

For Kc>=log^gamma Y, equations (1),(2), and V Kc=O_K(tau U) give per ordered resonant pair and sides (excluding c=0)
    F_large-index << tau L/log^4Y.                    (3)
This is the SAME capacity as the nonresonant pair in XXXVII, now without the nonresonance restriction. It uses only L>=Y^(1+epsilon), polynomial Y, and fixed tau. Even if the interval contains no realized points it remains valid.

For Kc<log^gamma Y, take Kc as the padded full continuous c interval, with length >=D0 and <=D0+3 (empty a interval contributes nothing). Then
    h=O_K(tau^-1 log^gamma Y), |ell|=O_K((Y²/L) log^gamma Y).
For c!=0 use the pointwise bound J_H J(c)<< (loglog(3Y))^C for an absolute C (e.g. 20), and V Kc=O_K(U). Thus per ordered pair weighted count << L (loglog(3Y))^C/log^4Y. For fixed source p, possible h,A are O_K(tau^-2 log^(2gamma)Y), and for each h,A the possible integer ell have cardinality O(1+(Y²/L)log^gamma Y). The successor q=(hp-ell)/A is uniquely fixed. Therefore the outdegree of the short-index relation is at most
    O_(K,tau)(log^(2gamma)Y [1+(Y²/L)log^gamma Y]).      (4)
Certificates may be chosen arbitrarily reduced per pair; (4) covers their union and different side choices, and does not count each actual pair multiple times. This relation can still have large degree at L=X^.7 with Y~sqrt X. The proof has isolated the residual mechanism there, not eliminated it.

## 6. All-label fixed loss on sufficiently long bins

Add L>=Y²/log^beta Y for fixed 0<=beta<2 (fixed constant factors harmless). Choose fixed gamma>0 with 3gamma+beta<2. The outdegree (4) is O(log^(3gamma+beta)Y) for fixed tau. Summing the pointwise short-index bound over O(s_j log^(3gamma+beta)Y) edges and then bins gives o(NH) by the aggregate near-minimal support bound; loglog factors are absorbed by the strict power slack. The proportional c=0 part is o(NH) by section2. For nonresonant and large-index parts, discard bins with s_j>C1 log²Y at cost at most rho NH/4 as in XXXVI, then sum (3) and XXXVII's bound to obtain O(C1² tau NH) with constant independent of fixed tau (threshold may depend on tau). The same-label near part is o(NH) by XXXVI's one-progression bound at L>=Y^(1+epsilon). Last pair weight o(NH). Choose small fixed tau, so a fixed positive fraction of M has |d-4p|>tau Y. The exact XXXVI slack inequality then gives
    G_all-4M/3 >= c NH,   M <=3G_all/4-c' NH.           (5)
This removes ALL rational resonance exceptions on these long bins. At Y~sqrt X, L~H~X/log^.25 X satisfies beta=.25 up to constants; in fact any fixed beta>.25 and <2 works. For smaller Y polynomial the length condition may be easier. XXXVI covers lower scales with L>=Y^(2+epsilon). No low-relay bound, no consumer support bound, no fast-target or deficit multiplier cap. The result still assumes an actual macro ORDERED direct population and near-minimal LOCAL source support; cannot coarsen a short-core support assumption to these long bins without proving it. It does not give a fixed gap in the original overlap clock or prove direct saturation necessary.

## 7. Finite diagnostics

Run node research/min_unified_resonant_line_sieve_audit.mjs 4096 16384 65536. Extend XXXVII six actual prime-root runs and 48 controls. Verify primitive line direction, exact envelope V,D0 and line count, four collision determinants, constant-coordinate excluded fibers, total density across c residues, proportional arithmetic on actual qualifying lines, independent translated and forced-line controls including nontrivial hA factors. Finite tests do not establish the analytic mean (2), asymptotic sparsity or saturation. No independent Selberg numerical certification, full cumulative core/kernel or Lean verification. Main/direct unchanged.
```json
{
  "totals": {
    "controls": 48,
    "pairs": 29671,
    "M": 726042,
    "gapChecks": 6968,
    "nearMass": 8544,
    "resonantGroups": 14,
    "resonantMass": 2156,
    "lineControls": 14,
    "lineCount": 14,
    "lineChecks": 66,
    "lineMeans": 84,
    "lineConstants": 0,
    "lineCollisions": 84,
    "lineZero": 0,
    "lineZeroPoints": 0,
    "lineNonzero": 14,
    "actualZero": 0,
    "actualZeroMass": 0,
    "actualZeroPrimitive": 0
  },
  "independentLines": {
    "controls": 287,
    "lines": 3023,
    "checks": 25269,
    "localMeans": 1722,
    "constantFibers": 3359,
    "collisions": 14779,
    "zeroLines": 12,
    "zeroPoints": 65,
    "nonzeroLines": 3011
  }
}
```
Next: remove the short-index exception for actual short cores, or derive the macro ordered direct near-saturation and source support from the original overlap ledger. No final NT gap.
