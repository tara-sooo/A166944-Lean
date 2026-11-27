# Negative MIN: necessary balanced roughness at 40%, and a variable-level/switching lower-sieve derivation

2026-11-28 JST; Issue #10. Continuation of 52773e062e8d3ab5f321c08b00b0da43d5f3f89f. User explicitly renewed the 4.85 research target, with primary target G_T/T<=0.40 at T=ceil(8 sqrt(2R+1)), alternate core-breakthrough routes, multistage deductions and GitHub persistence. Existing kernel-checked core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a (614 declarations) unchanged. No new Lean compile or independent human review. The analytic lower below is a paper-level derivation from literature, including a new application of special-factor factorization to appended-prime residual sieve weights; not an externally certified theorem or a claim of priority. No level 4.85 claim.

## 1. The time-exponent obstruction is intrinsic to subcritical gain

Let L=log R, S=sqrt(2R+1), A canonical in [R,2R], and T=o(R). Write G=G_T, W=sum of completed full waits, I=T-W, x=A-G, and q(x)=min(P^-(x-1),P^-(x+1)). We stay in positive centers x>2 by canonical gain. The earlier mod2310 certificate in c0e45b0 gives
    W <= 17G/8 + 395/12 - (1/8) sum_completed(p-281)_+ .   (1)
At the endpoint the next full wait is <=2q(x); since it has not completed, I<2q(x), including I=0.

For any fixed gamma<8/17, if G<=gamma T,
    q(x) > (1-17gamma/8)T/2 -395/24.                     (2)
In particular at T=ceil(8S), G/T<=.40 yields
    240 q(x) > 18 T-3950,
    q(x) > .6 S -395/24.                                (3)
The last inequality is an exact necessary bound (not a sufficient orbit criterion). Any composite neighbor is therefore a product of exactly two primes counted with multiplicity, both >=.6S-O(1). Every such factor is <=(2R+1)/(.6S-O(1))=O(S). A non-twin target may be a prime paired with a balanced semiprime OR two balanced semiprimes. For k<=2 completed labels all >=11, the fixed-depth bound from 52773e0 already makes a fixed .40 upper at this T a twin certificate for large R (non-twin thresholds .5 and 9/22).

Refinement: if a fraction f of the gain is in labels >=P>=282, their count is <=G_hi/(P-1), so the slack sum in (1) is >=G_hi(1-280/(P-1)). With G/T<=.40 and P tending to infinity this implies
    q(x) >= (.6+.2f) S-o(S).
For dominant high-label gain the necessary roughness constant increases to .8. This does NOT supply existence. At T>=14S, even the unrefined .40 bound certifies a twin for large R, but no construction at that longer horizon is proved.

Exponent equivalence: fix 0<theta<1 and 0<=gamma<8/17. The existence of unbounded canonical A and horizons T asymptotic up to positive constants to A^theta, with G_T<=gamma T, is equivalent to existence of unbounded even x with q(x)>=c x^theta for some c>0. The forward implication is (2), x=A-O(T)~A. For the converse, x divisible by 6 for large x since q(x)>3; use birth(x), horizon floor(c x^theta/4), and the checked height label bound p<=2 age+7 to prove no firing through that horizon. Thus the supremum of time exponents for these low-gain existence targets is exactly the static rough-pair supremum. This is not an equivalence of multiplicities, of fixed constants at theta=.5, or of the desired .40 target at 8S to the bare static bound. For theta>.5 both neighbors must be prime. For theta=.5 even a non-twin endpoint entails a difficult balanced-factor existence problem. If both are semiprimes, writing x+1=ad, x-1=bc yields ad-bc=2 with four prime entries all comparable to sqrt(x); this is a restricted instance of the prime-matrix problem discussed in Kontorovich, Levels of Distribution and the Affine Sieve, section 3.6.1, pp.956-957. No inference from higher-rank prime matrix results or bounded gaps between E2 numbers to this fixed-gap balanced problem is valid.

Consequence for research allocation: merely optimizing completed waits, increasing sequential depth or reducing gain at a fixed polynomial exponent cannot evade the static roughness frontier. Either improve that frontier by analytic arithmetic input, or find a different dynamic certificate not demanding subcritical G/T. This motivates the next sections.

## 2. Setup of a different lower sieve

We improve the prior BFI lower-sieve cutoff theta<2/7 (8aa47ea), not by asserting a stronger generic lower-weight level but by subtracting Buchstab sectors with different upper estimates.

Let X=R, L=log R, Acal={ell+2: ell prime in [R-1,2R-1]}. For an odd squarefree divisor d put
    E(d)=# {ell in interval: ell prime, ell=-2 mod d} - |Acal|/phi(d).
Write S(Acal,z) for the sifted count with no prime factor <z, odd primes (the elements are odd). Normalize by
    Pi_R=2 C2 R/L^2, C2=prod_{p>2}(1-1/(p-1)^2).
Mertens gives V(z)~2 C2 e^(-EulerGamma)/log z, |Acal|~R/L. The standard upper and lower linear sieve with Iwaniec remainder applies with g(d)=1/phi(d), and normalized main functions F(s)=2e^EulerGamma/s for 1<=s<=3, f(s)=2e^EulerGamma log(s-1)/s for 2<=s<=4. These are exactly the ranges used below. For Acal_q and residual d<q, its main size is |Acal|/(q-1) and remainder E(qd); actual E(q) need not separately be paid for each residual application, since the sieve inequality permits a prescribed main size.

Use the fixed parameters
    a=.144, b=.2845, c=.296, d0=4/7-.0001,
    e=.0001, switched sieve cutoff u0=.19, switched level dS=.56.
All exponent decimals in the certificate are exact rationals.
Buchstab gives
    S(Acal,R^c)=S(Acal,R^a)
      - sum_{R^a<=q<R^b} S(Acal_q,q)
      - sum_{R^b<=q<R^c} S(Acal_q,q).                    (4)
The BFI theorem for the well-factorable Iwaniec lower weights at D=R^d0 gives
    S(Acal,R^a)/Pi_R >= B - o(1) - O(eps_s),
    B=2/d0 * log(d0/a-1).
Here eps_s is the independently chosen sieve approximation parameter, fixed arbitrarily small before R tends to infinity. All distribution errors below are arbitrary log savings with constants allowed to depend on fixed parameters.

## 3. Appended-prime residual upper weights: special-factor transfer

Input: Pascadi, On the exponents of distribution of primes and smooth numbers, arXiv:2505.00653, Proposition 5.5, equations (5.3),(5.7), Proposition 4.4 and the proof of Theorem 5.4. For largest prime exponent t the available support-factorization exponent is
    vartheta(t)=min((1+t)/2,1-3t/2).
The factorization applies to Dwell(D), with every ordered prime prefix times the square of its next prime at most D, and D exponent <=vartheta(t)-2delta. It provides d=d1*d2*d3 with margins d1<=N R^-delta, N^2 d2 d3^2<=R^(1-delta), N^2 d2^5 d3^2<=R^(2-delta), for R^(2delta)<=N<=R^(1/3+delta). We use the *factorization proposition*, not Theorem 5.4 with an unsupported identification of different sieve weights.

More explicitly, for a fixed exponent bin [l,v] subset [a,b] (split at .25), set
    d=min_{t in [l,v]} vartheta(t)-e,  D_res=R^(d-v).
Take ordinary Iwaniec residual upper-sieve weights at level D_res and cutoff R^l, the same weights for all q in the bin R^l<=q<R^v. The desired remainder is
    sum_q sum_{m|P(R^l)} lambda_res^+(m) E(qm).            (5)
The following argument adapts the proof of Pascadi Theorem 5.4 to (5).
- First disregard the small smooth component of the residual Iwaniec weights. Its rough-box part has ordered prime factors in the upper sieve support, hence in Dwell at residual level (or within an arbitrarily small power enlargement when passing to box endpoints). This follows from Lichtman, A modification of the linear sieve, and the count of twin primes, arXiv:2109.02851v2, (5.14)-(5.17). In particular it is a finite sum of interval-product convolutions with fixed coefficients, and a small smooth component of support <=D_res^eps_s. The count of boxes is fixed once the approximation parameter is fixed.
- Append q as the first/largest prime factor; all residual primes are <R^l. For the first factor q^2<=R^d (verified for all bins). Each subsequent Dwell inequality holds because q times the residual prefix constraint is <=R^v D_res=R^d, allowing the tiny power enlargement mentioned above. Therefore the appended vector belongs to Dwell(R^(d+rho)) for arbitrary sufficiently small fixed rho>0, and its largest exponent is in [l,v]. Choose rho, delta and all box widths small enough that d+rho<=vartheta(t)-2delta. The factorization theorem applies. Further subdivide the appended prime interval for the remainder argument only, as finely as needed relative to delta; the main term bin remains [l,v].
- For each subbox choose one representative rough product and apply Proposition 5.5 for each Type II parameter N. Its partition of prime indices gives three convolutions of the corresponding prime interval indicators. All products in that box have factor supports enlarged by only an arbitrarily small power; append the small smooth component to the third factor. The margins in (5.3) survive. This is the same support-to-convolution step as Lichtman Lemma 5.3 and Pascadi section 5 (including the application of Proposition 4.4 in place of Maynard's Type II estimate). The appended prime is an independent interval indicator, not a coefficient correlated with the residual primes. In any implementation of the box convolutions with repeated prime indices, the equal-prime terms may be dropped at negligible cost: the repeated rough primes are >=R^rho' for a fixed rho'>0, and using |E(d)|<<R tau(d)/d for d<R^.625 and fixed divisor-power multiplicity gives total O(R^(1-rho'+o(1))). Coefficients from the usual grouping of equal intervals are fixed. The smooth component is on primes strictly below the rough boxes. Cutoff restrictions are independent interval restrictions on each prime.
- Apply Proposition 4.4 after the Heath-Brown decomposition of the prime indicator, with the other Type I/large-factor cases exactly as in Pascadi's proof of Theorem 5.4 (which explicitly invokes the proof of Lichtman Proposition 5.4 with these substitutions). The argument is a factor-support argument for each box convolution, not tied to the parity sign of the total modulus. It gives O_A(R L^-A) for (5) for every A, with parameters fixed. One may work on each endpoint of the prime interval or via subdivision into intervals [X,2X]; constant factors from endpoints are absorbed in the power margins. All moduli odd, residue -2 fixed. No application of BFI to an arbitrary prime-dependent residue or assumption of individual AP asymptotics at these levels is used.

This appended-weight transfer is the main new analytic step requiring specialist independent review. The proof is provided here rather than using a black-box theorem with a mismatched sign or support. The exact arithmetic certificate does not validate the analytic step.

Now S(Acal_q,q)<=S(Acal_q,R^l). The residual exponent s=(d-v)/l lies strictly between 1 and 3 on every chosen bin. The upper main constant for the bin, divided by Pi_R, is at most
    U(l,v)=2/(d-v) * log(v/l),
by partial summation of 1/(q-1). Error O(eps_s) summed over the finitely many bins can be made arbitrarily small. Use bins of width 1/100000 with a,b and .25 as exact endpoints. The elementary bound log(v/l)<= (v-l)/l gives a convenient exact rational upper on the aggregate U. The minimum margin d-2v is .00415. In particular no assertion of linear upper sieve at s<1 is made. The critical region where q^2 would exceed the available distribution level is handled in the next section, not by extrapolating (5).

## 4. Switch the remaining sector to products of primes

For q>=R^b and q<R^c, all prime factors of m=ell+2 are >=q and m~R; since b>1/4, m has either two or three prime factors counted with multiplicity. The repeated-factor population is O(R^(1-b)+sqrt R)=o(Pi_R), by summing R/p^2+1 for p>=R^b up to sqrt(2R+1). To upper-bound the remaining shifted-prime count, first enumerate the ordered-by-size distinct product population m=q*r or q*r*s, with least factor q in the desired exponent range, m in [R+1,2R+1], then sieve m-2 for odd primes <R^.19. The sequence is a multiset of product tuples with unique representation apart from already removed repetitions. Every such product is coprime to the sieve divisors since its factors exceed R^b.

Use Lichtman Corollary 5.6, equation (5.24), empty fixed prefix, at level .56<(3-.19)/5=.562. This is a distribution theorem for the product of prime variables in short relative boxes with Iwaniec weights. The empty-prefix interpretation is explicitly used in the author's switching proof at (6.17)-(6.20), b=1. This is not application of the single-prime BFI theorem directly to composite products. For the product domains, cover with boxes of relative width 1+L^-B0 for sufficiently large fixed B0, as in that proof, taking upper product endpoints as the theorem's X~R and hence exponent parameters summing to 1. Since all product factors have exponents >=.2845, the fixed sieve cutoff lies below every factor, and all level and support constraints have power slack for the constant factors X/R. One can use the *union of full boxes* covering the domains: its excess population is o(R/L) by partial summation/PNT in relative intervals of log-power width and the vanishing boundary layers, including order and product boundaries. Apply the upper sieve boxwise and use arbitrary log savings to pay the polylogarithmic number of boxes. Equivalently the usual subdivision in Lichtman's proof gives the aggregate remainder. The density for m-2 on the boxes is 1/phi(d), as the main coprimality restriction is automatic. The sieve parameter .56/.19 is between 1 and 3. Thus a product population of size (J+o(1))R/L contributes at most (2J/.56+o(1)+O(eps_s))Pi_R prime shifts.

The prime number theorem with partial summation gives the coefficients of the bare populations:
    J2(b,c)=integral_b^c dt/[t(1-t)],
    J3(b,c)=integral_b^c log((1-2t)/t) dt/[t(1-t)].
For the second, integrate the middle exponent v over t<=v<=(1-t)/2, giving the displayed logarithm. To count all triple products with least exponent >=b, replace c by 1/3. Endpoint strips caused by [R+1,2R+1] instead of a normalized product exponent exactly 1 have vanishing mass. No asymptotic for the *prime-shifted* product count is asserted: the factor 2/.56 is the upper sieve cost. This is why switching is useful beyond the middle-sector cutoff.

## 5. Certified positive margins and two analytic consequences

By (4), (5) and switching, the lower coefficient is at least
    B - U - (2/.56)(J2(b,c)+J3(b,c)).
A second lower, for ell+2 prime or semiprime with every prime factor >=R^.290, is
    B - U - (2/.56)(J2(b,.290)+J3(b,1/3)).
Here the entire triple population with least exponent >=b is subtracted, not just the triples below .290. These are lower bounds for the shifted-prime families, not for numbers with both sides prime. If only non-twin roots are wanted, an alternative with many twin centers must be retained.

The exact certificate research/lean/negative_min_variable_level_roughness_audit.mjs, commit 363b2b0fcb5dd32effde36c7fa13de2ed84a91e6, blob 95cfed971d28aab15437ce46152adfaade6a7309, uses integer units 10^-18 and outward rounding throughout. For logarithms log(n/d) with n>=d>0 use 32 terms of the positive atanh expansion, with explicit geometric tail upper. For J3 the integrand decreases on [b,1/3], and so does J2, since its denominator t(1-t) increases. Upper sums use left endpoints, including one final bin covering 1/3. In middle bins the exact upper bound 2(v-l)/(l(d-v)) is used. Results:
    B >= 3.807756027855275141
    U <= 3.517738060757154064
    switched all to .296 <= .272866490545467435
    all-triple switched upper <= .175234428562993330
    resulting lower coefficient for .296 >= .017151476552653642
    resulting lower coefficient for P2 at .290 >= .018838618680816545
The coefficient for P2 at .291 is also positive (.001510629355807614), but use .290 for larger slack. Choose sieve approximation parameters so that the sum of all fixed approximation errors is <.005, then R sufficiently large for the asymptotic errors. Conditional only on correctness of the analytic transfer above (which is argued, not independently reviewed), this proves the following two paper-level lower estimates without a prime distribution conjecture:
    # {ell in slab prime: P^-(ell+2)>=R^.296} >= .01 Pi_R,
    # {ell in slab prime: Omega(ell+2)<=2,
         P^-(ell+2)>=R^.290} >= .01 Pi_R.
The base, middle, and switch main constants use the same Pi_R. The certificate proves the numerical sign and level margins, not the truth of any new analytic input. We keep these as an unconditional proof draft awaiting independent checking of the special-factor transfer, not as a certified update to the previously accepted .285 exponent. No novelty or best-known worldwide exponent claim.

## 6. Return to the actual MIN dynamics

If the analytic lower in section 5 is accepted, x=ell+1 is canonical for large R and q(x)>=R^.296. The checked height-label bound gives stationary through H=floor(R^.295), since 2H+7<R^.296. This would extend the earlier unconditional exponent .285 to .295, with >=.01 Pi_R actual births in every sufficiently large slab. The second lower gives >=.01 Pi_R prime/at-most-two-factor centers with stationary time floor(R^.289). It removes the three-factor case from a family at exponent above 2/7.

The second family can be analyzed exactly after its first quiet phase. If x is not twin, write x-1=ell prime, x+1=q*r, q<=r, q>=R^.290. Both factors are odd and large; q=r cases may be dropped at negligible cost. The candidate first waits from birth(x) are
    w_q=((r mod 4)q-7)/2,
    w_r=((q mod 4)r-7)/2.
The x-1 prime's calendar wait is of order R and cannot win. The first winner minimizes (w,p); it is q except possibly when r=3 mod4, q=1 mod4 and r<3q, in which case r wins. Thus p<=3q, and postevent height is either 0 or p (the even-clock branch), and the destination is p*(other_factor-1). This is exact, not a guess based on least factor. It rules out the possibility that the first event waits for the large prime ell.

Reuse the four-form first-exit exclusion proved in 8aa47ea with theta=.290 (or .296 for the larger family). For any fixed 0<alpha<beta<theta and eps>0, all but o(R/L^2) rough non-twin roots have no R^alpha-rough center within even backward displacement L^(2-eps) of their first destination. Consequently these roots must gain more than L^(2-eps) within R^beta additional ticks after their first firing. Thus the new lower, if accepted, yields a dichotomy: either >=c R/L^2 twin centers, or >=c R/L^2 actual prime-semiprime starts with H~R^.289 initial quiet time, explicit first firing, and mandatory postfire movement. This uses the new family in the prior dynamic exclusion, but still gives no low-gain bound at the square-root horizon. The current gap is not the ability to concatenate a fixed number of events; it is the arithmetic roughness frontier itself, or the construction of a different dynamic certificate.

## 7. Source review and verification record

Primary sources inspected 2026-11-28:
- Alexandru Pascadi, On the exponents of distribution of primes and smooth numbers, https://arxiv.org/pdf/2505.00653, printed p24 equation (5.3), p28 equations (5.7), (5.8), Theorem 5.4 and Proposition 5.5, plus Proposition 4.4. PDF text and screenshots inspected. We use the special-factor factorization of Dwell and the proof's convolution mechanism; the theorem as printed concerns particular full sieve weights, hence the explicit adaptation in section 3.
- Jared Duker Lichtman, A modification of the linear sieve, and the count of twin primes, https://arxiv.org/pdf/2109.02851, printed p8 Theorem 2.10, pp22-24 (5.14)-(5.21), Lemma 5.3, pp25-26 Corollary 5.6 eq (5.24), p32 switching proof (6.17)-(6.20). PDF text/screenshots inspected. BFI fixed-shift well-factorable level 4/7 as in Theorem 2.2 (same as prior work). No unsupported 5/8 general lower-weight assertion.
- Alex Kontorovich, Levels of Distribution and the Affine Sieve, https://www.numdam.org/item/10.5802/afst.1432.pdf, section 3.6.1, printed p956, equation (3.30). PDF text/screenshots inspected. This is a connection to the both-balanced-semiprimes case, not a theorem resolving it.
- A recent alternative lead, Ratliff, A Roughness-Explicit Chen-type Theorem for Shifted Primes, Zenodo record https://zenodo.org/records/20383867 (v3), claims roughness .3844197. Inspected linked TeX https://zenodo.org/records/20383867/files/twin_rough_chen_acta_final_v9.tex?download=1, section Analytic estimates for the bad sectors, proposition Sub-1/3 semiprime-prime estimate. Its unit-constant upper relies on a stated standard asymptotic and a sketch of completion/Weil saving in every Type II block without a precise applicable theorem or complete error estimate. That input was not independently justified; the stronger claimed result is NOT used here. Latest version retrieval returned HTTP429 in the research session; no conclusion about the latest revision. No accusation of falsity, only no verified basis for using it.

Audit executed in ECMAScript, exact pinned remote readback. 14050 middle exponent bins with positive domain margins. All bounds at integer scale 10^18; no floating arithmetic enters the positivity assertions. Additional actual finite checks: 16567 canonical roots, 293549 completed events, 49701 horizons with slack/idle inequality checks, 26532 low-gain target instances at three time scales, of which 7075 non-twin endpoints; 14323 square-root-scale target instances (T=ceil(8 sqrt(A+1))), all twin endpoints in this finite range; 1430 exact prime-semiprime first-event calendar checks. These finite square-root data are not a non-twin asymptotic control and cannot establish existence at unbounded R. No new Lean compile, independent specialist review or 4.85 achievement.

Next concrete alternatives: independently review the appended-weight transfer (and switching box main/error ranges) before elevating .295 to accepted status; then explore stronger weighted Buchstab/Chen decompositions with multiple special factors, OR abandon the subcritical gain certificate for a different dynamic criterion. The 40% route requires balanced roughness even if it is weaker than twin infinitude, and no amount of small-scale orbit optimization alone changes that fact. Main/siblings unchanged.
