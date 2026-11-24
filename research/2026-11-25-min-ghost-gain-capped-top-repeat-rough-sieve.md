# A gain-capped three-residue sieve for long waits at near-top repeated labels

2026-11-25 JST. Continues 36e95f2e13b1a779e5e43c343cb0a58df1339612 on the SAME research/min-cycle-forest-2026-11-24 branch. Original probability and sieve deductions, self-contained elementary Selberg quadratic majorant, finite common-CRT path audit. No external search, no Lean compilation. New unconditional removal of long-wait near-top returns before any positive peak; the intermediate-label repeat bank and global physical far-coalescence upper bound remain open.

## 1. Scope and exact first-to-repeat progression

Use the infinite independent CRT ghost, or a finite initial alphabet of all odd primes up to a given cutoff. Conditional on common initial time parity, each p has independent uniform initial horizon/time coordinates modulo p. Work at relative elapsed time s and nonnegative increasing even relative horizon gain g. Write w for the completed wait immediately preceding an executed event p (not the whole elapsed interval since the previous selection of p). Every eligible label has a matching clock within 2p from an attained state. Hence w<=2p and, more generally, w<=2r where r is the least eligible label at the preceding attained horizon. In the infinite alphabet r exists almost surely, simultaneously at all possible integer horizons. No physical height-nonnegativity assumption is used on this random phase rectangle.

Fix U tending to infinity, and a constant b with 0<b<3/2. Put
    z=ceil(U/(log U)^b).
We will bound the event that some repeated label p>=z executes by time U, with pre-event gain g1<=2U and completed wait w>p/4. This is a gain-capped event; no claim is made about repeats after the total gain has exceeded 2U.

Let g0 be the gain immediately before the FIRST selection of this same p. Both g0 and g1 have c_p+g_i congruent to +/-1 modulo p. Since that first event adds p-1 and all subsequent gains are positive,
    0<=g0, g1-g0>=p-1,
    g1 = g0 + m p + a, a in {-2,0,2}, 1<=m<=(2U+2)/p.
For p>=5 the lower bound m>=1 follows from g1-g0>2. This uses the first selection even if several other returns of p occurred between it and the specified return. There is no enumeration of the intermediate event sequence or its coefficients.

If w>p/4, then every available odd prime ell<=p/8 is ineligible at g1: otherwise its matching clock would have occurred within 2ell<=p/4 from the immediately preceding event. Thus
    c_ell + g0 + m p + a != +/-1 (mod ell)
for all such ell. These constraints concern horizon coordinates alone. Our argument will exploit them at the first-selection time, when p is still fresh and has a small conditional hazard. In a finite initial alphabet either p>=z is absent (then it cannot witness the event), or all smaller primes needed in the proof are available.

## 2. Uniform control of exceptional local roots before the path is run

Let L0=ceil((log U)^2), D=floor(U^(1/20)), and R=U^kappa, for a sufficiently small fixed absolute kappa>0 specified by the sieve argument below. Use the sieve primes L0<ell<=R. For all large U, R<z/8, z^2>=2U, and (2U+2)/z<L0. In particular every admissible m is nonzero mod every sieve prime.

Reveal all horizon and time coordinates of primes ell<=R initially, in addition to the common parity. Define the initial measurable good event Good that, for every integer v in [-2,2U+2], at most ceil(log U) sieve primes have
    c_ell+v == +/-1 (mod ell).
For any fixed v these indicators are independent with mean sum 2/ell=O(log log U), by the harmonic prime upper bound. For k=ceil(log U) the elementary exponential-moment/Chernoff bound is (e mean/k)^k, with the zero-mean case immediate. A union over O(U) v gives
    Pr(Good^c) <= exp(-Omega(log U log log U)).
In particular Good is an event about initially revealed coordinates, uniform over all adaptive g0 and offsets a. We do not condition on any future path success or impose independence between the selected labels and those coordinates.

For fixed v and positive admissible m, count candidate large primes x in [Q,2Q), Q>=z, satisfying
    c_ell+v+m x != +/-1 (mod ell)
at every sieve prime. Since x itself is prime and exceeds R, x mod ell is nonzero. Since m is invertible mod ell, the forbidden residues for x consist of 0 and the two distinct solutions to c_ell+v+m x=+/-1. Their union has cardinality nu_ell=3 except if c_ell+v==+/-1, in which case nu_ell=2. On Good at most ceil(log U) primes are exceptional, all exceeding L0. Thus their product correction relative to three forbidden residues is bounded by exp(O(log U/L0))=O(1). This is the third sieve condition (primality of the candidate label itself), in addition to the two rough-neighbor conditions. It is different from counting ordinary starting integers by a three-prime CRT modulus product.

## 3. Self-contained upper-bound sieve for the candidate primes

We record the sieve details so the needed uniformity in v,m and adaptive histories is explicit. The length of [Q,2Q) is Q up to rounding; replace it by an integer interval of length n<=Q+2. For squarefree d composed of the sieve primes, let nu(d)=product nu_ell and g(d)=nu(d)/d. The count of integers in the intersection of forbidden residue conditions for every ell|d is n g(d)+O(nu(d)), by CRT and counting residue classes in an interval. All ell are large, so 0<g(ell)<1.

For squarefree d<=D using only sieve primes, take real Selberg weights lambda_d supported on this divisor-closed finite set, lambda_1=1. For a surviving integer the sum of weights over its forbidden divisors is 1, so the square of that sum majorizes its indicator. Summing squares gives an upper bound
    n sum_(d,e) lambda_d lambda_e g(lcm(d,e))
      + O(sum_(d,e) |lambda_d lambda_e| nu(lcm(d,e))).
Define h(d)=product_(ell|d)(1/g(ell)-1), G(D)=sum_(d<=D) 1/h(d) on the same squarefree support. Since
    g(lcm(d,e))=g(d)g(e) sum_(l|gcd(d,e)) h(l),
the quadratic is sum_l h(l) y_l^2, where y_l=sum_(d:l|d) lambda_d g(d). Set y_l=mu(l)/(h(l)G(D)). Finite Möbius inversion gives weights with lambda_1=sum_l mu(l)y_l=1 and quadratic 1/G(D). It also gives |lambda_d|g(d)<=1: after inversion the absolute numerator is bounded by sum_(l:d|l)1/h(l)/G(D)<=1. Thus |lambda_d|<=d, since nu(d)>=1. As nu(lcm)<=lcm<=D^2, the entire error is O(D^6), using at most D^2 pairs and |lambda_d lambda_e|<=D^2. This coarse error suffices at D=U^(1/20).

To lower bound G(D), form the unrestricted divisor sum
    G_inf=product_(L0<ell<=R)(1+1/h(ell))
         =product_(L0<ell<=R)(1-g(ell))^-1.
Normalize these divisor weights to a probability on squarefree divisors of the sieve primorial. The inclusions are independent Bernoulli with probabilities g(ell), so the expectation of log d is
    sum_(L0<ell<=R) g(ell) log ell
       <=3 sum_(ell<=R prime) log ell/ell
       <=C0 log R
for an absolute C0, by partial summation and the elementary prime-count upper bound. Choose kappa sufficiently small that C0 kappa < 1/100 (and kappa<1/20). Then for all large U the expected log d is <=(1/2)log D. Markov gives at least half the divisor weight at d<=D, i.e. G(D)>=G_inf/2. On Good the product of local survival fractions is
    G_inf^-1 = product_(L0<ell<=R)(1-nu_ell/ell)
             <= O((log L0/log R)^3)
             = O((log log U)^3/(log U)^3).
Here the exceptional-factor correction is O(1) by section2, and the ordinary three-residue product estimate follows from the classical Mertens harmonic-prime estimate and absolutely summable quadratic errors. All constants are uniform in the allowed shifts and strides. Therefore
    #candidate primes in [Q,2Q)
      <= O(Q (log log U)^3/(log U)^3 + D^6)
      = O(Q (log log U)^3/(log U)^3)
for Q>=z, since D^6<=U^0.3 is negligible at that scale. This is a deterministic count conditional on Good, not a probabilistic independence claim about the future return. No distribution of primes in large-modulus arithmetic progressions is needed.

## 4. Apply the sieve at the first-selection tick

At any tick s<=U, condition on the initially revealed low coordinates, parity and entire selected-label/quiet-tick history before s. The horizon g0 at that tick is known. By the earlier exact history law, an unused p>=z has conditional probability of first selection at s at most 2/p^2, since p^2>=2U and its coordinate pair set has at least p^2-(s-1) allowed elements. Good is measurable in this past. On Good and g0<=2U, an actual future long-wait return before gain 2U requires p to satisfy the deterministic candidate test of sections1-3 for at least one a and m.

Partition z<=p<=2U+1 into dyadic bands [Q,2Q) starting at Q=z (the restriction p<=2U+1 follows already from the first jump and g1<=2U). In each band at most (2U+2)/Q possible positive m, and three offsets a. Apply the uniform sieve count to each pair (m,a) with v=g0+a. The number of candidate labels in the band is at most
    O(U (log log U)^3/(log U)^3).
Their conditional first-selection probability at this tick is at most this count times 2/Q^2. Summing bands geometrically, then all U ticks, yields
    Pr(some gain-capped long-wait repeat of p>=z by U)
       <= Pr(Good^c)
          + O(U^2 (log log U)^3/(z^2 log^3 U))
       = O((log log U)^3/(log U)^(3-2b)).
This is o(1) for every fixed b<3/2. We counted the necessary first selection of each possible witness, not the conditional probability of a known p firing at its later return (which could equal one). The first selection may itself have short wait or large negative drift. The result does not need the previous high-label coefficient enumeration, any LOW lifetime bound, or a cap on the number of repeats. It is only a long-wait exclusion before the gain cap, not a proof of absence of all near-top repeats.

A useful specific choice is b=5/4, giving error O((log log U)^3/sqrt(log U)). On the complement of this exceptional event every such repeated p has w<=p/4 and hence signed increment
    2w-(p-1) <=1-p/2.
Thus all near-top repeated labels before a positive attained peak have strictly negative drift. Indeed if a positive attained peak occurs at s<=U, then g(s)<2s<=2U, and all earlier gains are also <=2U by monotonicity. This addresses the relevant prefixes even when an unrestricted later path has enormous gain. No claim is made that a repeated label after that prefix has negative drift.

## 5. Consequence for the signed repeat bank and LOW-block surplus

Use the preceding fresh-wait theorem E F(U)=O(U/log U) and its signed block decomposition. Fix A=A(U) tending slowly to infinity, let L_A=2 product_(3<=p<A)p<=sqrt U, so z>=10L_A+2 eventually for the stated b. A block is a label p>=A and its subsequent executed labels <A up to the next such high event or horizon U. Let d_i be the nonnegative maximum signed increment in that low suffix (d_i<=5L_A), and w_i the completed wait of the entering event. The maximum nonnegative block gain is [2w_i-(p_i-1)+d_i]_+. Initial low-only peak is <=5L_A. All fresh high block surplus together is <=2F(U)+C_A, C_A=O(L_A^2/log(2L_A)). Define the intermediate repeat surplus
    E_mid(U)=sum_(repeated high block starts A<=p_i<z) [2w_i-(p_i-1)+d_i]_+,
using full observed blocks.

If D_infty(U)>0, truncate the path at a time attaining that positive peak. Every pre-gain in this truncated prefix is <=2U. On the good event of section4, any repeated high block with p>=z has 2w-(p-1)<=1-p/2, so its surplus including any low suffix is ZERO because 5L_A<=p/2-1. The truncated low suffix of the final block only decreases its maximum relative to the full observed suffix. Hence on that event
    D_infty(U) <= 5L_A + 2F(U) + C_A + E_mid(U).
The same bound is trivial if D=0. In particular for each fixed epsilon>0 and sufficiently large U,
    Pr(D_infty(U)>epsilon U)
      <= O((log log U)^3/(log U)^(3-2b) + 1/(epsilon log U))
          + Pr(E_mid(U)>epsilon U/2).
This uses Markov for F and the deterministic initial/fresh corrections; constants can depend on fixed b. Equivalently the remaining sufficient condition can be narrowed to sublinear positive repeated-block surplus for A<=p<U/(log U)^b. The exact bank Bmax of the preceding note still retains all negative gains and may be easier than this nonnegative sufficient majorant. The new sieve result is unconditional and removes the near-top repeated labels from the positive-peak analysis, but does not prove that the intermediate repeats have sublinear surplus. In particular it does not establish eta->0 or the physical far-pair upper bound.

## 6. Exact finite audit and persistence

Saved research/min_ghost_top_repeat_rough_sieve_audit.mjs and research/min_ghost_top_repeat_rough_sieve_results.json, exact remote readback at d20a6692184331850e1a8030dd447a5cc4079d6e. Sample independent common CRT coordinates with fixed seeds and finite alphabet p<=4U, U=256,1024,4096,16384,65536; 512 samples each except 256 at largest U. Diagnostic z=max(11,ceil(U/log(U)^1.25)), reveal all primes <=R=min(47,floor(z/8)) with minimum3. These R and the tested small prime range are NOT the asymptotic sieve choices: at finite U the sampled m can have factors in the small sieve set. No numerical evaluation of the analytic candidate count or implied probability constant. The finite model differs from the infinite process by the earlier O(1/log U) asymptotic coupling estimate, not a calibrated finite sample error.

For sampled v and m, enumerate x mod each small prime, test the exact union of forbidden residues. For invertible m verify two or three roots according to collision; for noninvertible m verify zero-slope case (excluded asymptotically by L0>m). At every executed top fresh event before gain 2U record whether its own p has any possible future gain g0+mp+a satisfying the diagnostic small-prime ineligibility test, with gain at most2U and at least g0+p-1; only even gains considered. For every actual top repeat at pre-gain<=2U verify the first-to-repeat progression, and when w>p/4 verify roughness and that the first-selection candidate test was positive. For short top repeats verify the negative signed bound, and for A5,L_A6,p>=62 verify their whole subsequent observed low-block surplus is zero. Check counts and actual clock waits. These are finite necessary-condition checks, not evidence that the asymptotic probability upper bound has a small numerical constant.

Results (top repeats counted only at pre-gain<=2U):
    U        z       fresh top   top repeats   long repeats   positive repeats
    256      31      647         15            11             5
    1024     92      606          7             4             2
    4096     290     567          1             0             0
    16384    957     476          0             0             0
    65536    3239    222          0             0             0
All 15 long-repeat incidences across the suite were covered by their recorded first-selection candidate test. At U65536, 57344 local residue-count checks (including 4011 zero slopes, 8105 collisions, 45228 distinct triples) and 16131 executed events. 129 of222 gain-capped top fresh events passed the conservative candidate test, but no top return occurred. Thus the candidate criterion substantially overcounts at these finite parameters. No claim of a measured vanishing fraction or direct verification of the probability bound. The small finite samples at the larger scales have no top-repeat witness; the small-scale samples test the nonvacuous implication. No Lean compilation.

## 7. Remaining work

The new proof uses a positive-peak gain cap to obtain a uniform three-residue sieve on possible FIRST-selected labels that could later repeat with large wait. It removes positive near-top repeated-block drift without assuming a small LOW-gain resource or a short intervening trajectory. It leaves the intermediate and smaller relative-scale repeated contributions, where the stride bound grows too large and the first-selection hazard accumulates over more candidates. Further work needs a different control of the signed repeat bank or a localized/restarted version of this sieve at smaller scales. The global weighted physical far-coalescence bound remains independently unresolved. No new branch, no main edit, no twin-prime proof.
