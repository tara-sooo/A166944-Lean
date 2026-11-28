# Beyond 5/16: semiprime source, reverse Buchstab sectors, and a quantitative double-sieve bridge

2026-11-28 JST, Issue #10. User explicitly asks for exploration beyond the preceding 5/16 deduction during Astra reset. Base note 96859f46d2603f9e71e3e045a40a63ab0f40709e. New: an asymmetric two-prime source at the same roughness exponent; an explicit, strictly improved upper bound on a switched three-appended-prime Buchstab sector; a concrete sufficient correction for surpassing 5/16. No proven rough-pair density exponent >5/16 or M85. The analytic deductions use the same two-factor specialization of Pascadi Prop4.4 as the preceding note, including its constant-sized Q3=1 convention; independent specialist verification is pending. No new Lean compile or human review.

## 1. Literature delta and source review (2026-11-28 JST)

- Pascadi, arXiv:2505.00653v2 (29 June 2025), https://arxiv.org/pdf/2505.00653, printed pp20–23, Def4.3, Prop4.4, eqs(4.15)–(4.17), Prop4.5; p24 Iwaniec components. Re-read text and p21 screenshot. The weaker proof conditions (4.16) still imply total exponent <5/8 by (4.17); they do not bypass the ceiling. For a fixed alpha exponent nu, the two-factor slice (neglecting positive slack) is A<=nu, B<=min(1−2nu,(2−2nu)/5). Thus level at most nu+min(...)=.4+.6nu for nu<=3/8, 1−nu for nu>=3/8. The constant-sized third factor is as in the preceding note, not a new claim about arbitrary lower weights on the primes.
- Wu, original Acta Arith.114 (2004), https://www.impan.pl/shop/publication/transaction/download/product/82961, printed pp221–222 screenshots and §§3–4 text. Lemma2.5 level <=.6 over its table. Double sieve develops signed Buchstab comparisons for its particular sequence; its numerical improvements are not directly transferable to a shifted semiprime source. Lichtman, arXiv:2109.02851v2, https://arxiv.org/pdf/2109.02851v2, p8 screenshot Thm2.10 and eq(2.5): ordinary lower/upper components and f,F formulas.
- Zhiyuan Yang, arXiv:2608.13299v2 (3 Sep 2026), https://arxiv.org/pdf/2608.13299, printed pp2–4 screenshots, (1.2),(1.3), Thms1.1,1.2,1.4. Some levels exceed .625, but the sums have a plain integer variable l in (1.2),(1.3), not an arbitrary prime or rough l coefficient. Cannot replace l with the semiprime factor indicator and quote the exponent. A possible extension using explicit roughness decomposition of l would require a separate theorem (fixed residue/variable dependencies).
- Runbo Li, arXiv:2611.29075v1 (21 Nov 2026, math.GM preprint), https://arxiv.org/pdf/2611.29075, pp1–6, Thm1.4 and Cor1.5 screenshot p5. Arbitrary bilinear modulus weights, up to 8/15 for primes; new Type II near 1/2, with region N>=Q x^eps, N<=x^(1/2+eps/100) and N^(1/2)Q^(1/2)R^4 etc. Its cited maximum Type II modulus exponent ~223/396 is below 5/8. Useful for particular differently shaped modulus ranges, not an automatic higher uniform level. No reliance on its new proof.
- IMPORTANT correction to old lead: Marshall Ratliff, Zenodo v4 (22 Nov 2026), https://zenodo.org/records/24441524 (DOI 10.5281/zenodo.24441524), explicitly withdraws v3's 1/3 and .3844197214 claims and companion 1.9618; replaces them with a claimed .300816 prime/P2 roughness theorem. This supports excluding the old .3844 lead from our research, as already suspected in 627f57b. New record description reports signed Buchstab and finite certificates; original PDF download via Zenodo/API failed (400/inaccessible); new proof NOT independently inspected or used. The author's withdrawal is explicit on the version record itself.

## 2. A simpler, asymmetric seed with a large prime factor on one side

Let n=A+1=pv, p,v distinct primes, p in a fixed narrow exponent band [nu0,nu1] near and below 3/8, v>p, and n in [R+1,2R+1]. Unlike the previous three-prime seed, there is no attempt to force p to be the first winner. Its advantage is an independent one-prime coefficient on each side of the convolution and a much larger known least factor of n. Write L=log R, source count B_R, C2=prod_{ell>2}(1−1/(ell−1)^2), normalization M_R=4 C2 B_R/L. By PNT and partial summation,
  B_R ~ R/L * integral_{nu0}^{nu1} ds/[s(1-s)].
Representation is unique. For any fixed sigma<5/16, choose nu0,nu1 sufficiently close to 3/8, and fixed modulus exponents a<nu0, b<min(1−2nu1,(2−2nu1)/5) so d=a+b>2sigma. Use the earlier two-factor ordinary lower sieve/mask transfer on pv−2 with z=4R^sigma, density g(k)=1/phi(k) for odd squarefree k. Coprime corrections as in 96859f4, SW from unrestricted short p prime. All constants may depend on fixed sigma and exponent bands. Lower >>R/L², and P^-(A+1)=p>=R^nu0. Since pv odd and 3 divides neither pv nor pv−2, A=0 mod6. Every selected root is non-twin and reaches floor(R^sigma) with zero gain. This is the same exponent as the preceding seed but strengthens one-sided least-factor size to any fixed value below 3/8 (choose band accordingly). No density claim for p as first winner: an opposite smaller factor can fire before p. We do not transfer the earlier plus-only postfire theorem blindly.

The following switched estimates use the fixed rational band
  nu0=.374900, nu1=.374950,
  a=.374800, b=.249800, d=.624600, eps=.000010.
All (4.15) inequalities have fixed slack. Product source n in [R+1,2R+1] can be partitioned into multiplicative boxes of ratio 1+eta for arbitrary fixed eta, using the PNT uniform in endpoint and in fixed reduced APs; approximate product interval from inside/outside. There are O_eta(L^k) boxes for fixed number of factors; approximation errors in main terms can be made arbitrarily small by choosing eta, while arbitrary log-power distribution errors absorb the number of boxes. Alternatively use the standard variable-separation step cited in Pascadi Prop4.5 proof. No distribution theorem applied to a coefficient containing a coupled product condition without separation. 

## 3. Explicit reverse upper improvement for three appended primes

Use S_k(z) for the number of n in the semiprime source with k|n−2 and P^-(n−2)>=z. For distinct primes q1>q2>q3 use the ordered sector
  t1=log_R q1 in [.230000,.246000],
  t2=log_R q2 in [.170000,.182000],
  t3=log_R q3 in [.165000,.169900].
Set U=t1+t2+t3 in [.565000,.597900], w=1−U in [.402100,.435000]. Define the summed sector
  T = sum_{q1,q2,q3 in these bands} S_(q1 q2 q3)(q3),
  measure I=integral_box dt1 dt2 dt3/(t1 t2 t3).

**Forward elementary sieve upper:** insert q2 q3 in Q1 and q1 in Q2 of Prop4.4. Their exponents fit strictly: t2+t3<=.3519<a, t1<=.246<b. The remaining two capacities sum to d−U. For each multiplicative box take a well-factorable upper component of this residual level (a small slack is permitted) and split it at the two remaining capacities. Since each capacity is <.04, its divisors have prime factors much smaller than q_i, so the grouped coefficient with the appended large primes is 1-bounded by unique factorization. Restrict squarefree small factors as in 96859f4 via Mobius coprimality; the tail estimate remains valid after summation over q_i, with sum 1/(q1 q2 q3)=O(1) and uniqueness in the grouped factors. For absolute remainders |Delta(k)|<<RL/k, the small-e factor restriction is independent before grouping. Sieve at a cutoff close to R^(d−U), much smaller than q3, so ordinary upper at s close to1 gives coefficient 1/(d−U) in units M_R. Thus the obtainable forward bound is
  T/M_R <= integral_box 1/(d−U) dt1 dt2 dt3/(t1 t2 t3) + o(1)
in the usual limit with small fixed sieve/box errors, or with an arbitrarily small constant error. Its integrand is >=1/(.6246−.565)=16.7785... throughout the box. This is an upper-bound expression, NOT a lower bound for T.

**Reverse switch:** write n−2=q1 q2 q3 r. Then r has size R^w and is q3-rough. Since 2t3<w<3t3 uniformly, r is prime or product of two primes (allowing squares; negligible in main term). Use an unrestricted indicator of these rough r in its multiplicative box as alpha and the product of the three q_i as beta. The cutoff q3 may be replaced in each small multiplicative box by its lower endpoint for the upper; all such changes in exponents are o(1). Alpha is 1-bounded, polynomial rough, and SW: for primes use PNT in log-power progressions; for semiprimes fix the smaller prime u>=R^t3, apply the same theorem to the larger prime in its interval (with endpoints enforcing u<=v), sum with harmonic weights. Uniformity in log-power moduli follows by choosing PNT error exponent sufficiently large; remove factors dividing auxiliary integer d by O(omega(d)N/R^t3) (each such prime divides at most N/ell integers); large q moduli use N/q+1 and N/phi(q), as in the prior SW check. No AP restriction on alpha. Beta has unique representation in the disjoint q bands.

In reverse distribution use residue −2, N=R^w (within multiplicative constants), exponents
  a_r=w−.0005, b_r=1−2w−.0005, d_r=a_r+b_r=U−.001.
Since .4021<=w<=.435, all (4.15) inequalities have slack >=15eps and 40eps respectively. The source prime p of exponent nu can be appended inside Q1, because nu<=.37495<a_r. Split an ordinary upper remainder at capacities a_r−nu and b_r, then group p with its first factor (p larger than residual cutoff). The mask and tail work as above. This tests (n−2)≡−2 mod p*k, i.e. (n/p) divisible by k. The actual quotient v is prime of size R^(1−nu); upper sieve cutoff close to R^(d_r−nu) is smaller than v, and the upper with s close to1 costs 4 C2/[(d_r−nu)L]. All moduli are odd; p does not divide r in this domain (r prime has exponent w>nu, or both semiprime factors <=w−t3<nu); nor any q_i. Coprime corrections for the other factors of the reverse source are negligible: every prime factor exceeds R^.165, bounded multiplicity, and sum 1/phi(k) over squarefree k divisible by a source prime ell is O(L/ell); sum p reciprocal is O(1). This justifies the same g(k) model and Mertens constant.

By PNT the reverse base mass per q triple in the slab is
  R/[L q1 q2 q3] * omega(w/t3)/t3,
with omega(u)=(1+log(u−1))/u for 2<u<3. This formula can also be derived directly: prime term 1/w plus semiprime integral from t3 to w/2 of ds/[s(w−s)], giving (1+log((w−t3)/t3))/w. Sum p reciprocal with density dnu/nu; divide by B_R (whose p integral has 1/(1−nu)). The normalized upper integrand becomes the nu-weighted average of
  (1−nu) omega(w/t3) / [t3(d_r−nu)].
For the entire box omega(w/t3)<=5/8: log(u−1)<=u−2 and u<=.435/.165<8/3. Consequently this coefficient is <=
  (1−.3749)*(5/8)/[.165*(.565−.001−.37495)]
  =12.5247449... <13.
So, allowing the fixed slack in sieve and box approximation,
  T <= (13+o(1)) M_R I
or conservatively T<=13.1 M_R I for sufficiently large R after choosing approximations. This is a strict improvement over the specific ordinary forward upper integrand (>=16.77), of at least 21% even uniformly on this wider sector, with much larger gain near some edges. The proof estimates a sector of the actual source using a different source convolution and residue, not a numerical upper fit. It does NOT show a saving in the final signed lower expression until the appropriate branch is activated. It relies on the preceding two-factor Prop4.4 interpretation and has not received independent specialist review.

## 4. A precise double-sieve bridge for breaking 5/16

For an initial cutoff a0=.24 and target b0 between .3125 and .35, ordinary first-prime Buchstab is exact:
  S(R^b0)=S(R^a0)−sum_{R^a0<=q<R^b0} S_q(q).
All primes here are <R^a, so append q in forward Q1 and split the residual weights as in §3. S_q(q) can be upper-sieved at q when (d−t)/t>=1, or at smaller cutoff R^(d−t−slack) otherwise. For a0<=t<=b0 the usual s<=3 upper gives integrated coefficient 1/[t(d−t)]. Lower at a0 has 2<d/a0<4 and coefficient log((d−a0)/a0)/d. Thus ordinary one-level subtraction gives exactly
  (1/d) log((d−a0)/a0)− integral_{a0}^{b0} dt/[t(d−t)]
   = (1/d) log((d−b0)/b0).
It is nonpositive at b0>=d/2. This establishes why a straightforward first-prime subtraction cannot itself improve the ordinary level. The claim is only for this choice of standard F,f bounds, not an impossibility theorem for all signed decompositions.

For q exponent t in [.24,.28], insert a second Buchstab identity:
  S_q(q)=S_q(R^.13)−sum_{R^.13<=r<q} S_(qr)(r).
The ordinary upper for S_q(R^.13) has (d−t)/.13 between1 and3, so costs precisely the SAME coefficient as the original upper for S_q(q). Therefore we can keep ANY nonnegative subset of the correction. Define
  J_R=sum_{R^.24<=q<R^.28} sum_{R^.13<=r<R^.16} S_(qr)(r).
For fixed b0>=.28, exact identity plus the same analytic estimates prove
  S(R^b0)/M_R >= (1/d) log((d−b0)/b0) + J_R/M_R − error
where the error can be made arbitrarily small by fixed parameters and then large R. A positive fixed margin gives >>R/L² canonical stationary roots for every sigma<b0 (and H=floor(R^b0/4)); p source exponent exceeds b0. This is a concrete OPEN lower lemma on actual integers in the original semiprime sequence, not a generic request to improve the sieve. For every (t,r-exponent) in this J rectangle, residual level d−t−r<=.2546<2*.13. Thus the standard lower on S_(qr)(r) is zero. A genuinely improved two-prime-divided rough count is needed.

In the limiting d=5/8 normalization, the required J_R/M_R values are:
  b0=.313: >.0051200044
  b0=.315: >.0256005462
  b0=.320: >.0768147507
  b0=.325: >.1280683323
  b0=1/3: >.2136502282
  b0=.350: >.3858592909.
The fixed band in §2 uses d=.6246, so its exact thresholds use d=.6246, not these ideal limits. The thresholds in the actual fixed-band proof are:
  b0=0.313000000: >0.007177196
  b0=0.315000000: >0.027684113
  b0=0.320000000: >0.078965026
  b0=0.325000000: >0.130286472
  b0=0.333333333: >0.215984250
  b0=0.350000000: >0.388436857
One can make d arbitrarily close to .625 using smaller slack and a new fixed source band, but J_R normalization and lower must then be established for that band. No evidence that these corrections are already available. No comparison at b0>.35 is claimed for this particular bridge (p and modulus capacity are fixed, and its proof uses b0<=.35). The threshold calculation is a direct formula, not an assertion that a given improvement in §3 transfers to J. 

## 5. Exploratory signed recursion and audit

Executed audit research/lean/negative_min_reverse_buchstab_sector_audit.mjs @c43d9351816ba7fbfe9ae6d06092009eaf0eb412, blob2b4b23ac8479505365639be4463bfd03abf4173d. Exact integer exponent controls 11050 sector combinations; rational uniform bounds reverse 12.5247449368..., forward baseline16.7785234899...; finite semiprime-source sample27459, exact first Buchstab base10292, final5762, removed4530; second Buchstab base1150, final863, removed287, 3750 controls,103 nonvacuous triple quotient tests. All checks pass. Numerical exploratory recurrence (not interval-certified, no exponent margins, ideal d=.625, p=.375) uses the standard F,f and Buchstab omega, and for appended primes with exponent sum U allows reverse caps whenever the residual or a subset of q_i and residual can be grouped into an unrestricted SW variable of exponent min(U',1−U') in (.375,.5). Formula as §3, but with general omega(W/t), W=1−U. Recursively use lower=max(baseline, earlier lower−integral child upper), upper=min(baseline, earlier upper−integral child lower) on grid step .005 from .08 to .325, depths2,3. No U=1 exact-product hypersurface is crossed at these depths. Finite approximate grid and trapezoidal integration can show numerical artifacts (e.g. upper slightly below ordinary 1/d) and are NOT rigorous lower bounds. Depth3 has 23375 prefix arrays; reverse caps strictly improve 18322 finite ordinary upper entries and supply 203418 previously unavailable entries in this numerical model; final lower is still 0 at .315,.32,.325, with or without reversal. A separate scratch Python depth4 coarse run (.10 step .01) also gave no improvement at .32,.33; finer run exceeded time budget and was not used as evidence. Persisted JS depth2/3 only. This is a concrete negative result for that tested recursion, not a theorem that deeper or differently signed corrections cannot work. The next useful analytic task is to find a positive lower for the J rectangle (or a different rectangle with equivalent signed contribution), for example a switching lower with a different source that avoids having to sieve a prime cofactor all the way to its square root; or obtain a real upper saving on S_q(q) directly. Merely improving the deep negative upper terms is not sufficient in the tested model.

## 6. Status
New paper deduction for asymmetric seed and strict reverse-sector upper, plus precise sufficient bridge for >5/16. The >5/16 proof is NOT closed. M85 still open; independent review of the previous 5/16 and present deduction remains pending. Existing Lean core and all other research lanes untouched. New primary source correction to Ratliff should be included in next Astra handoff. 
