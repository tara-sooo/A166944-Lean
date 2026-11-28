# High-sector correction, mixed divisor correlation beyond product R, and isolated HIGH phase supply

2026-11-28 JST, Issue #10. Base 2db4af753f292d792c9e208c484cff23cc9419b8. Continuing the actual high-least-factor correction after the 1.09 Pi lower in the .16 route. This checkpoint gives: (i) a direct .208-cutoff identity with smaller sufficient residual coefficient, plus a tiny rigorous positive lower INSIDE the previous complementary high sector; (ii) a genuinely different mixed divisor distribution lemma from Bettin--Chandee, applicable to separate weights on opposite sides even when the modulus product exceeds R, with a worked vector-sieve consequence involving two specified prime factors above 5/24; (iii) isolated stationary-or-HIGH phase supply; (iv) a certified small refinement of the stationary exponent to .3347. The main .4 lower, meaningful density in the residual high-least sector, and unconditional twin infinitude are still open. No new Lean compile or independent specialist verification.

Notation: L=log R, Pi=2 C2 R/L², n=A-1,m=n+2 odd, U_a=1{P^-(n)>=R^a}, C_b=1{P^-(n)>=4R^b}, E_a=U_a-C_b. Slab n in [R-1,2R-1], A canonical multiple of 6 whenever both neighbors are polynomially rough. Fixed constant multipliers and O(1) shifts of endpoints do not affect limiting coefficients.

## 1. Reduce the complementary high-sector target without extrapolating the low-pin estimate

The previous checkpoint supplied >=1.09 Pi for E_.16(n)E_.16(m) with at least one least factor <R^.208. Its resulting sufficient target for the complementary square [R^.208,4R^.4) was 1.93 Pi. This was one sufficient identity, not an optimal necessary condition. Reusing the SAME high sector as the correction itself, choose a=.208 and b=.4 in the exact identity
    C_b(n)C_b(m)= C_b(n)U_a(m) - E_a(m)U_a(n) + E_a(m)E_a(n).
There is no need to use the low-pin contribution again (it is outside the new correction square).

In units Pi use previous factor-stratified lower P_b(a) for C_b U_a, and upper for E_a U_a. d0=4/7-.0001, dU=.5999, d2(t)=min((2+3t)/5,1-t)-.0001, B(d,a)=2 log(d/a-1)/d. Then
    P_b(a)=B(d0,a)+int_b^.5 B(max(d0,d2(t)),a)dt/[t(1-t)].
The upper baseline is 2/dU [M(a)-M(b)], M(a)<=.561522/a, M(b)=1+log((1-b)/b). Improve the rejected triple rows by the previous J3 over ordered anatomy, and the semiprime rows t>=1/3 by J2, capping every selected level at 3a-.0001=.6239. Thus all upper parameters remain on the 2/d plateau. Specifically the rejected triple row upper level can be max(dU,d2(t),d2(u),d2(1-t-u)) truncated at the cap; the other proof steps are unchanged. Finer inner rectangles and outward log bounds give
    upper(E_a U_a) - lower(C_b U_a) < 1.530577705 Pi
before arbitrarily small fixed approximation errors.

Hence an actual distinct count of
    E_.208(n)E_.208(m) >= 1.54 Pi                       (A)
on an unbounded sequence of slabs suffices for stationary M85. This is the SAME complementary square as the preceding target1.93, and does not count the 1.09 low sector twice. It is also slightly smaller than the previous alternative a=.206,target1.56, but excludes the additional lower strip [.206,.208); those two conditions are not equivalent. No lower near1.54 has been proved. This target choice can be further optimized by balancing threshold and sector size, not solely the numerical coefficient.

For motivation ONLY (no independence used): under a heuristic product of bare factor-anatomy masses the high correction coefficient would be (M(.208)-M(.4))². Numerical ODE integration of (u omega(u))'=omega(u-1) yields M(.208)≈2.69931905, M(.4)=1+log(1.5), heuristic square ≈1.67406. These exploratory values are not a theorem on actual shifted pairs, are not an input to any certificate, and do not say that the old1.93 target is impossible. They explain why lowering the target matters.

## 2. Actual positive lower inside the high-least complement

There is a thin genuine region of the complement in which the ordinary two-factor pinned lower has positive margin. Use semiprime source n=pv, short prime exponent t in [.373,.376], target least q exponent u in [.208,.2083]. Partition t at width .00002, u at width .00001. For source cell [l,r], take Q1 exponent x=l-.00001 and Q2 exponent y=min(1-2r,(2-2r)/5)-.00001. Q3 unit. Append q to Q1, residual lower level d=x+y-u_hi. For every cell with q fitting and d>2u_hi, use the previous exact pinned quotient method: the quotient m/q is sifted to R^u_hi, so q is its true least divisor; repeated squares are negligible. All strict Pascadi inequalities hold; all factors bounded, ordinary well-factorable lower in remaining capacities, source prime unrestricted. No use of three-factor upper support as a lower weight.

The coefficient lower per source/pin cell is
    log(r(1-l)/(l(1-r))) log(u_hi/u_lo) B(d,u_hi).
Sum disjoint cells; code checks 4500 capacities, of which 1965 positive. Certified total >5.90e-8 Pi (display truncated to 10 decimals; exact integer lower >1e-8 Pi). Usable lower 5e-8 Pi after fixing sufficiently small errors. All source least factors lie above .208 and below .4, all target least factors also in [.208,.2083). Thus this is an ACTUAL positive subset of E_.208 x E_.208 at least one side above .373, not simply a factor incidence with an unproved minimum. Reversing shift gives a disjoint orientation as the two least bands are disjoint, so both directions together even give >=1e-7 Pi if the two approximation errors are selected with strict margin. This is negligible compared with 1.54: the main complement is unsolved.

The total-level cap 5/8 implies d+u<5/8, d>2u forces u<5/24. Narrowing boxes cannot extend THIS ordinary pinned least-prime method to u>5/24. The next section changes the distribution input to one for opposite-side modulus factors rather than a single shifted product.

## 3. A mixed divisor distribution lemma with product above R

Primary source inspected: S. Bettin and V. Chandee, Trilinear forms with Kloosterman fractions, arXiv:1502.00769v1, 2015-02-03, https://arxiv.org/pdf/1502.00769, Theorem1 (1.2), printed p2 (PDF image index1), Corollary1 printed p4 (image index3), proof §9 printed p27 (image index26). Published Adv. Math. DOI 10.1016/j.aim.2018.01.026. Theorem1 allows arbitrary independent coefficients on the two dyadic variables and the frequency; specialization to a single frequency supplies a bilinear inverse-sum bound. No prime indicator may be inserted into the FREE variables of the determinant corollary. The following deduction instead places arbitrary convolution weights on the two modulus variables.

Let W be a fixed smooth compactly supported function on (1,2), and alpha_A,beta_B arbitrary independently supported on odd positive integers A,B <=R^(.512), with |alpha_A|,|beta_B| <= tau(A)^K,tau(B)^K for fixed K. For fixed shift Delta=1 or2, the weighted all-integer count
    T_Delta = sum_(A,B) alpha_A beta_B
                 sum_(n: A|n, B|n+Delta) W(n/R)
has coprime main term for odd A,B:
    R (int W) sum_((A,B)=1) alpha_A beta_B/(AB)
and error O_{K,W}(R^(1-delta0)), e.g. delta0=.0005. This is for a SEPARATED pair of coefficient sequences; it is not an absolute error for arbitrary joint coefficients alpha_(A,B).

Proof. For (A,B)>1 no solution since odd gcd cannot divide Delta. For coprime A,B use CRT and Poisson:
    sum W(n/R)= (R/(AB)) sum_(h in Z) W_hat(hR/(AB)) e(-Delta h Abar/B),
up to an irrelevant Fourier-sign convention. Here Abar is inverse of A mod B. The h=0 term is exact. In dyadic boxes A~X, B~Y, use Bettin--Chandee Theorem1 with frequency-support singleton and theta=-Delta h. The L² norms of the two coefficient sequences are O(R^eps sqrt X), O(R^eps sqrt Y). The two terms in that theorem give the common bound
    R^eps (XY)^(.85) (X+Y)^(.25)
       (1+|Delta h|/(XY))^(1/2).
Indeed the first term dominates the second after specialization, since (XY)^(.025) <= (X+Y)^(.125). For the smooth factor R/(AB) W_hat(hR/(AB)), two-dimensional partial summation on each box costs O_{W,J}(R/(XY)(1+|h|R/(XY))^-J), with derivatives in scaled A,B variables obeying the same bound after raising J. The truncated coefficients on subrectangles remain arbitrary 1-bounded/divisor-bounded sequences. Sum h≠0 with J sufficiently large; the product of this decay and the theorem's frequency factor has total O_W(1), uniformly for XY/R either large or small. The total error per dyadic box is therefore
    O(R^eps (XY)^(.85) (X+Y)^(.25)).
For both X,Y<=R^.512 the exponent is at most .85*1.024+.25*.512=.9984. Choose eps sufficiently small and absorb O(L²) boxes to get the claimed power saving. Very small modulus boxes (one variable bounded, or <=R^eps) also follow by the elementary O(1) progression remainder per pair, so no issue with the dyadic endpoint 1. The same bound with fixed smooth W and constants applies to n=2k, using scale R/2, shift1 and odd moduli. Subtract even n from all n at shift2. The ODD n version is consequently
    sum alpha_A beta_B sum_(n odd,A|n,B|n+2)W(n/R)
       = (R/2)(int W) sum_((A,B)=1) alpha_A beta_B/(AB)
          +O(R^(1-delta0)).                              (B)
Using cutoff exponent .512 minus any fixed slack is convenient if extra subpower factors are present. The modulus product can reach R^1.024; this is a direct two-sided correlation not derived from one-sided roughness tails. It is a paper application of a published theorem, not a new unconditional arbitrary-modulus distribution theorem. No statement about distribution of all four primes in the determinant equation follows.

## 4. Apply (B): simultaneous high PRIME FACTORS in actual rough pairs, not high LEAST factors

Here is a worked unconditional lower using (B), beyond the former one-sided pinned level condition. Choose both p,q prime in [R^.2085,R^.211], so p,q>R^(5/24). Require p|n and q|m, and both n,m rough to z=R^.11. Neither p nor q is claimed to be its side's least divisor. Use 0<=W<=1 supported in (1,2) with int W>=.9. We count weighted incidences before removing multiplicity.

Let z0=L^12 and split the sifting primes into the small odd primes <=z0, and the larger primes <z. Small-prime avoidance on both sides is one joint condition I_S, and I_1,I_2 are the respective large-prime avoidances. Use even Bonferroni upper U_S and odd lower L_S with truncation order K0=2 ceil((log L)^2). Expansion of the event ell|n(n+2) as 1{ell|n}+1{ell|n+2} is exact for odd ell (cannot divide both). Every term is an assignment of distinct small primes to two disjoint moduli d1,d2 with product <=z0^(K0+1)=R^o(1); number of terms R^o(1). In the uniform CRT reference their expectation upper/lower differ from V_S=prod_(2<ell<=z0)(1-2/ell) by O(L^-A) for any fixed A, because total violation mass O(log log z0) and factorial tail at K0. This is a genuinely joint small-prime sieve, not an assumption of independence at ell=3.

For each large-prime side use ordinary dimension-one linear sieve upper U_i and lower L_i with g(ell)=1/ell and support D=R^.30. Standard linear sieve extremal weights on these squarefree divisors have |lambda|<=1, and the dimension-one Mertens condition holds uniformly for the restricted prime set (removing primes only decreases its product). With s=.30/.11=30/11, their main expectations in the product reference satisfy
    U_i <= (F(s)+o(1)) V_L,  U_i >= V_L,
    L_i >= (f(s)-o(1)) V_L,
where V_L=prod_(z0<ell<z)(1-1/ell), F(s)=2 exp(gamma)/s and f(s)=F(s) log(s-1). Here lower/upper symbols in the display denote reference expectations; pointwise U_i>=I_i>=L_i, U_i>=0. These are ordinary linear-sieve polynomials, not triple-factorable lower weights. 

Use the exact vector lower polynomial
    L_S U_1 U_2 + U_S L_1 U_2 + U_S U_1 L_2 -2 U_S U_1 U_2
        <= I_S I_1 I_2.
This follows by telescoping the difference between product of nonnegative upper weights and product of indicators. For each fixed small assignment d1,d2, every expanded term of this polynomial has separated divisor weights on A=p d1 r1, B=q d2 r2, where r_i supported <=D. Because p,q>z, neither overlaps a sieve prime; after summing p and r_i the resulting coefficients are divisor-bounded. A,B <=R^(.511+o(1)) <R^.512, so (B) applies. The R^o small assignment count does not consume the fixed error margin. The diagonal p=q contributes no solutions; its reference reciprocal sum is o(1). For large-prime weights on opposite sides, their coprimality restriction cannot simply be dropped in general. Here dropping only the overlap of large r1,r2 has absolute reference error at most
    sum_(ell>z0) ell^-2 prod_(z0<r<z)(1+1/r)^2 << L²/z0.
After the small-assignment absolute sum <=prod_(ell<=z0,odd)(1+2/ell)=O((log z0)^2), this is o(L^-2), hence negligible in units Pi. Small and large primes are disjoint, so there is no other overlap. The small CRT main is V_S, not the square of a one-dimensional small product.

The resulting main lower coefficient for the vector polynomial is V_S V_L² times 2 f(s) F(s)-F(s)² up to relative o(1). To see the sign rigorously, the normalized U_i expectations are in [1,F+o(1)], L_i >=f-o(1), and f<=1. The expression f U1+f U2-U1 U2 is nonincreasing in each U_i there, so substitute their upper bound to get the desired lower. The small weights' relative error is o(1). Mertens yields
    V_S V_L² ~ 4 C2 exp(-2 gamma)/(log z)²,
since the finite small-prime ratio prod (1-2/ell)/(1-1/ell)^2 tends to C2. The odd-density factor R/2 in (B) is essential to the normalization Pi.

By prime reciprocal sums, sum_p 1/p ~ log(.211/.2085), and the same for q. Thus in units Pi the weighted incidence lower is at least, up to o(1),
    (int W) * 4/(.30²) * (2 log(19/11)-1)
                    * log(.211/.2085)^2.
The bracket 2log(19/11)-1 >.0930874. A number of size <=2R+2 has at most FOUR distinct prime divisors of size >=R^.2085 for large R. Hence divide incidences by at most16 for the distinct pair count; W<=1. The exact rational coefficient certificate after taking int W>=.9 is >.0000330611 Pi; a usable statement is
    # distinct actual odd n,m=n+2 with
      P^-(n),P^-(m)>=R^.11, and each containing a prime
      factor in [R^.2085,R^.211]    >= .00003 Pi
for every sufficiently large slab. Both selected primes are beyond 5/24 and below .4. This is an unconditional mixed-factor lower using a different analytic estimate, not a claim that the specified primes are least. The pairs belong to E_.11 x E_.11, not necessarily E_.16 or E_.208, so this count is NOT added to the 1.09Pi or the high complement lower in §2.

A quantitative reason this method does not yet solve the high complement: with both specified prime exponents ~.21 and both actual least cutoffs .208, residual levels .30 have linear sieve parameters only ~1.44, with zero ordinary lower. Even a symmetric vector lower with identical residual exponent d requires d/.208>1+sqrt(e) (~2.6487 in the first linear range). Including both pinned primes would require individual modulus exponent >.2085+.208(1+sqrt(e))≈.7594, not .512. This is a requirement of this particular product-of-linear-weights architecture, not an impossibility theorem for dimension-two beta sieve, extra factor constraints, or structured dispersion. The exact target (A) is still far beyond this quantitative input. The new mixed estimate provides a mathematically concrete test for other weight constructions, but we did not find one giving the required high-least lower.

## 5. Isolate the first HIGH phase with an opposite high-rough neighbor

Reuse previous asymmetric exchange, but accept ONLY the desired HIGH phase in the moving P2 range, rather than relying on a subsequent phase split. Let b>=.35, a<c<b, and on one side C_b as above. On the other define K_{c,b} to accept primes, semiprimes with least p>=4R^b (both phases), and semiprimes with 4R^c<=p<4R^b whose cofactor v is the HIGH class modulo4 (v=3 mod4 for plus, v=1 mod4 for minus). It excludes every P3+ number. The bare mass in units R/L is
    J=(M2(c)+M2(b))/2, M2(t)=1+log((1-t)/t).
This uses fixed-mod4 PNT only for the prime cofactor. Exact exchange
    C_b(n)K_{c,b}(m)=C_b(n)U_a(m)-C_b(n)(U_a-K_{c,b})(m).
Use the prior P_b(a) positive lower. On the negative source enumerate all rejected P3+ rows and semiprimes: below c all rejected, c..b one phase rejected, >=b none. For phase-constrained P2 choose least p as the unrestricted short prime and restrict only the long cofactor. For t<=1/3 the .5999 upper-level application with that choice is unchanged; t in [1/3,b] use d2(t). All P3+ rejected rows unfiltered: improve J3(a,1/3) exactly as before. Semiprime saving J2(b)/2 (all rows above 1/3 below b are half-rejected, since c<1/3 in the cases used). Thus new coefficient lower
    P_b(a) - 2/dU[M(a)-J] + J3(a,1/3)+J2(b)/2.
Certified pre-error lower and usable after deleting thin diagonal/near-deadline strips:
    a       c       b       net >         usable >=
    .208    .209    .400    .0025510892   .002
    .206    .207    .400    .0099938745   .009
    .211    .290    .350    .0913996548   .09
    .220    .250    .375    .0358632756   .035
This is different from the previously stronger minimum-label .28,.4 general two-sided phase family: now one opposite neighbor is always 4R^b-rough, the moving side necessarily has exactly two primes and the cofactor is a prime in the prescribed phase. These extra properties are useful for arithmetic conditioning, at the cost of smaller guaranteed first label exponents.

Take H=floor(R^b). High-rough opposite neighbor cannot fire before H because its least factor exceeds 2H+1. If the moving side is itself prime or high-rough then no first event; otherwise its least p>=4R^c is the only possible first label (the other prime v is >2H+1). Remove a thin exponent strip [b-eta,b+o(1)] on the moving side, cost O(eta)Pi by the inherited unrestricted semiprime upper (also bounds phase subrows). Thus every retained center either reaches first H with G=0 or makes an actual isolated HIGH first jump p with 4R^c<=p<R^(b-eta); no RESET alternative. The exact plus arrival is (p(v-1),p), minus (p(v-1)+2,p+3), previous prefire max about1.5p. This is a HIGH poststate, not an assertion of a new first-height record at p. Distinct physical HIGH arrivals have bounded reverse multiplicity via p|(x or x-2), p polynomial, x scale R. If stationary side insufficient, the surviving HIGH family has density scale. It fits the previously proved HIGH continuation hypotheses (v prime, opposite pv±2 rough R^b). In particular at c=.209 and b=.4 the existing separated stopped continuation applies with additional elapsed cap T=R^.025, gain threshold D=R^.15, since .15+2*.025=.20<.209, c_upper<.4<.5, as well as the common adaptive c0 L²-time theorem. Neither yields a lower on the proportion in the polynomial-time stop branch, nor positive polynomial height growth. This is a reusable isolated canonical source, not M85.

## 6. Refine the symmetric stationary exponent

The existing factor-stratified bilateral formula from 31613f25 at a=.206, c=.3347, no new analytic input, refined mesh .00005 (1D) and .00025 (2D) gives exact net lower >.0006984151 Pi before approximation errors. Use .0005 Pi for sufficiently large slabs. Thus the symmetric stationary frontier is .3347 in the current paper deduction, a small improvement from .3346. Both neighbors are 4R^.3347-rough, hence P1/P2, and all such canonical births hit H=floor(R^.3347) with zero gain. This is not the main mathematical advance in this checkpoint.

## 7. Executed checks and source ledger

research/lean/negative_min_high_sector_and_mixed_divisor_audit.mjs @4476a5c21240c9f153c4631820427b4870458f8d blob f5df9a377a13333d8e017703a52accd2e90ec37d. Initial source @3c30b5ba094dad1cecc13ed681d3b927a827c3fa had exploratory staticOk=false for overstrong .0008 margin; actual .0006984151, replaced with explicit >.0006 assertion and reran. All final assertions passed. Exact exponent units 1/2100000, 10^25 fixed point, 64-term atanh logs with outward tails, 11363 cached log arguments. .208 target gap upper 1.5305777042 (truncated), high-sector thin lower .0000000590 (truncated), 4500 exact capacity checks,1965 positive pin cells. BC .512 exponent check exact integer, vector lower .0000330611; 9261 finite pointwise vector inequalities incl negative lower weights,400 CRT normalization and400 odd-density controls including common moduli. No numerical experiment on actual asymptotic prime counts; exponent and coefficient certificates plus finite algebra only. Exact pinned and branch readback verified. Earlier pinned and factor-stratified proofs are inherited; no independent specialist review and no Lean build.

Web source trail: original Bettin--Chandee Theorem1, Corollary1 and proof read from PDF images above; search also found related partially-fixed-moduli and unbalanced convolution literature (not used as a theorem). No exhaustive or priority claim. Standard linear sieve inputs from prior notes; no assertion that a general arbitrary joint divisor-weighted remainder is controlled by Theorem1. Earlier high-sector coefficient from 2db4af75, stratified bounds from 31613f25, stopped HIGH and adaptive transcript notes reopened through their saved exact formulas. The proof does not use the heuristic independence estimate or numerical ODE as input. 

Current research status ~4.83 provisional. Symmetric stationary .3347, direct high-sector sufficient threshold1.54, actual thin positive high correction, new mixed opposite-side weighted distribution and high-factor incidences, stronger isolation of first HIGH phase. No .4 static lower, no dynamic M85 lower, no twin infinitude. Main/core/siblings unchanged. Next research: find a weighted/two-sided decomposition compatible with (B) that uses high-factor information to control actual low factors (or structured dispersion at much larger individual modulus levels); alternatively use the isolated opposite-.4-rough HIGH cohort to address real occupied transport. Do not add the .11 mixed-factor lower to the .16 correction.