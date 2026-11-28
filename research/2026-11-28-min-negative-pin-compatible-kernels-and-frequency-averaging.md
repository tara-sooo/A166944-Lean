# Conditional-pin-compatible marginal obstructions, frequency averaging, and double-pin rough pairs

2026-11-28 JST, Issue #10. Base 598538ba1bf69699384e648dfc90292b38db4927. Continue the two-sided mixed-divisor direction and the high least-factor correction. Main results of this checkpoint:
1. Average all Poisson frequencies in Bettin--Chandee's trilinear theorem instead of applying it separately to each frequency: separated modulus range .512 -> .515, with a new explicit vector-sieve lower at rough exponent .114.
2. A separate classical dimension-two DHR argument gives true integer pairs with both sides R^.135-rough and each containing a prime in [.2085,.211] exponent band, quantitatively. These factors are not necessarily least.
3. Construct TWO continuous factor-anatomy kernels that obey all ideal one-sided tail inequalities at level 5/8 AND the entire ordinary conditional least-prime lower family; the stronger second model also obeys all ideal single-pin upper inequalities. Both have zero .4 pair mass. Thus the previous single-pin data, even greatly idealized, do not force the remaining high-sector correction. This is a precise obstruction for an information class, not an arithmetic counterexample and not an obstruction to all weighted/mixed congruence methods.
Current static frontier .3347 and sufficient high-sector target1.54Pi unchanged. No actual .208 high correction improvement of meaningful size; no M85, no twin infinitude, no new Lean build or independent specialist review.

Notation: L=log R, Pi=2 C2 R/L², n=A-1, m=n+2 odd. U_a least prime >=R^a, C_b least >=4R^b, E_a=U_a-C_.4. Fixed constants at polynomial cutoffs are immaterial to the limiting measures. The actual sufficient target from base note is >=1.54 Pi pairs both least in [R^.208,4R^.4). The .11 factor-pin lower of that note is outside that sector.

## 1. Average the Poisson frequency, rather than summing individual estimates

Reopened S. Bettin and V. Chandee, Trilinear forms with Kloosterman fractions, arXiv:1502.00769v1, https://arxiv.org/pdf/1502.00769, Theorem1 (1.2), printed p2, PDF image index1; also proof (7.1), printed p25, image24. The previous note used singleton frequency support and separated independent divisor coefficients. The theorem itself allows a third sequence on a dyadic frequency interval. Use this extra averaging.

Let odd A,B have independent divisor-bounded coefficients alpha_A,beta_B, |alpha_A|<=tau(A)^K, similarly beta, supported <=R^.515. W fixed smooth compactly supported in (1,2). For fixed shift Delta=1,2, apply CRT and Poisson for coprime A,B as in base note. Odd gcd>1 cannot divide Delta. In dyadic boxes A~X,B~Y, nonzero frequencies split into H<=|h|<2H, positive and negative separately. Use three-variable Abel partial summation to remove the smooth coefficient R/(AB) W_hat(h R/(AB)): its scaled derivatives on each box are bounded by O_{W,J}(R/(XY)(1+HR/(XY))^-J), for any fixed J. All truncated coefficient intervals still satisfy the original L² bound, and the frequency coefficient is 1 on the truncated interval. Write P=XY, K0=X+Y. Theorem1 gives, before the smooth factor,
    R^eps (1+H/P)^(1/2)
       [(PH)^(.85) K0^(.25) + P^(.875) H K0^(.125)].
Here norms contribute (PH)^.5, and the second theorem term contributes (PH)^.375 (H K0)^.125. This is the key distinction from treating each frequency independently.

If P>=R, let H0=P/R>=1. Summing dyadic H with decay, the two resulting bounds are
    R^eps [P^(.85) K0^(.25) H0^(-.15)
             + P^(.875) K0^(.125)]
  = R^eps [R^(.15) P^(.7) K0^(.25)
             + P^(.875) K0^(.125)].
Indeed before summing the first factor has H^(.85)/H0, second H/H0, both geometric sums are dominated near H0; take J large for H>H0, including (1+H/P)^.5. If P<R use the original singleton estimate with rapidly decreasing Fourier tail, bounded by R^eps P^(.85) K0^(.25); or trivial O(P) when well below R. With X,Y<=R^.515 the two exponents for P>=R are <=.99975 and .965625. For P<R the singleton exponent <=.97875. Choose eps and logarithmic box overhead to fit fixed margin (e.g. final error O(R^.9999)). Small dyadic endpoint variables can instead use elementary CRT remainder. Subtract even n via n=2k, shift1 and scaled W, since moduli are odd. Hence the actual separated mixed divisor lemma holds on the larger rectangle:
    sum alpha_A beta_B sum_(n odd,A|n,B|n+2) W(n/R)
      = (R/2) int W sum_((A,B)=1) alpha_A beta_B/(AB)
        + O_{K,W}(R^.9999),      A,B<=R^.515.
This reaches product R^1.03, instead of previous R^1.024. Limiting balanced exponent from this first term is 17/33 (strictly below). This is only the separated coefficient lemma. It does not permit arbitrary joint alpha_(A,B), nor does it prove dispersion for two prime cofactors. One-sided distribution input remains as before.

Use base note's vector lower construction with small joint primes <=L^12, large-prime separate dimension-one lower/upper weights, p,q in [R^.2085,R^.211], residual D=R^.303 on each side, z=R^.114. Then A,B<=R^(.514+o(1)), within .515. All previously checked support, small-prime overlap and odd normalization conditions remain valid; no change in proof. s=.303/.114, 2log(s-1)-1=2log(189/114)-1>0.01109713. int W>=.9, multiplicity<=16. Certified lower coefficient
    .9 * 4/(.303)^2 * [2log(189/114)-1] * log(.211/.2085)^2 /16
       >.000003863620 Pi
before arbitrarily small relative errors. Use >=.000003 Pi actual DISTINCT odd pairs with both least>=R^.114 and each containing a prime in the specified >5/24 band. The designated factors are not necessarily least. This is the improvement using the new mixed lemma itself.

## 2. Joint dimension-two sieve with both pins: extend roughness further to .135

A different method gives a stronger roughness exponent for the same two prime-factor pins. This classical argument is included because using the new mixed lemma is not itself a requirement for a stronger result.

Primary sieve input: Diamond--Halberstam--Richert dimension-two lower sieve, with sifting parameter beta_2<=4.2665 (upper bound on optimal sieve limit, not a claim of an optimality theorem). Checked Kevin Ford's 2023 Sieve Methods lecture notes, https://ford126.web.illinois.edu/sieve2023.pdf, printed p37 (PDF image36), definition of sieve limit and Table1. Also P.-H. Kao, Almost-Prime Polynomials with Prime Arguments, arXiv:1606.03505, https://arxiv.org/pdf/1606.03505, §4 Theorem2, equations (13)--(16), printed pp6--7 (PDF images5--6), including beta_2=4.2664... for DHR; §5 Lemma5.2 printed p11 (image10) for the dimension-two remainder shape. Kao cites Diamond and Halberstam, A Higher-Dimensional Sieve Method, Theorem6.1 and Lemma9.3. The journal DOI URL was inaccessible via direct fetch, so used author's arXiv copy. The standard DHR lower and upper remainder form allows factor 4^omega(d), harmless here.

Fix distinct primes p,q in [R^.2085,R^.211]. Count n odd in slab, p|n, q|n+2, sieve both n and n+2 against every odd prime below z=R^a, a<=.135. For squarefree odd d with all primes below z, d coprime pq. Exactly 2^omega(d) congruence classes modulo 2pqd obey the pin conditions and d|n(n+2); one class modulo 2pq before adding d. Thus
    count = R/(2pq) * 2^omega(d)/d + O(2^omega(d)).
Local sieve density g(ell)=2/ell for odd primes, dimension2, uniform Mertens condition and V(z)~4C2 exp(-2gamma)/(aL)^2. Apply lower DHR at residual level D=R^.577, fixed s=.577/a. Remainder sum per pin pair O(D L^7) by sum 8^omega(d). Summing all p,q costs at most R^.422, so total O(R^.999 L^7)=o(R/L²). Can alternatively apply lower uniformly to each fixed pair and then sum; local density and remainder constants uniform, no need for correlation or dispersion of prime pins.

The DHR normalized lower coefficient for s>beta_2 is at least
    f_2(s) >= 1-(beta_2/s)^2
because (s^2 f_2(s))'=2s F_2(s-1), F_2>=1, f_2(beta_2)=0. This weaker explicit bound suffices. In units Pi, after summing reciprocal prime pins and dividing by at most 16 incidences per integer pair,
    coefficient >= e^(-2gamma) * f_2(s)/a² * log(.211/.2085)^2 /16 - o(1).
Diagonal p=q has no solutions and reference reciprocal-square term o(1). Multiplicity <=4 choices on each side, because 5*.2085>1. Use e^-2gamma>1/4 (gamma<log2, e.g. gamma<=H_5-log5<log2). Exact rational log enclosures and beta_2 upper give:
    a      s                f2 lower >         coefficient lower >      usable
    .135   4.274074074      .0035410537         4.3129e-7                 4e-7
    .130   4.438461538      .0759859428         9.9805e-6                 9e-6
    .125   4.616            .1456970625         2.0698e-5                 2e-5
All usable constants hold for sufficiently large R. Thus both sides rough R^.135 and both containing a prime above 5/24 is genuinely established. This improves the previous actual .11 roughness in that specific mixed-factor problem, not the symmetric .3347 canonical stationary frontier. In particular these pairs are NOT proven to be in E_.16 or E_.208; do not add any of these coefficients to the previous 1.09Pi correction. The pin exponent is not the least-factor exponent. With this DHR architecture, two pins near .208 and cutoff .208 would require total exponent at least 2*.208+4.2665*.208≈1.3034, far beyond classical CRT level1 or the new balanced mixed rectangle. Even one such pin with two-sided .208 cutoff would need about1.0954 in this sufficient construction. These are requirements of the selected sieve design, not absolute lower bounds on distribution needed by every method.

## 3. Anatomy measure and ideal pin data: precise information class

The earlier continuous countermodel (31613f25) was excluded by an actual positive pinned lower. We now strengthen it. Define mu, the bare anatomy measure, on ordered factor exponents summing to1: prime atom mass1 at exponent1, ordered k>=2 simplex density dt1...dt_(k-1)/(prod t_i). Tail least exponent >=z has mass M(z)=omega(1/z)/z, as before. Locally finite for z>0. Continuous least-factor density for 0<u<.5 is
    a(u)=-M'(u)=omega(1/u-1)/u²
away from irrelevant breakpoints, by Buchstab's equation. Let d=5/8. The ideal one-sided linear sieve tail lower and upper on each fixed anatomy row (per unit mu row mass) are
    L_d(z)=e^-gamma f(d/z)/z,
    U_d(z)=e^-gamma F(d/z)/z.
On first lower range d/4<=z<=d/2, L_d=2/d log(d/z-1); above d/2 zero. U_d>=2/d at all z (for z>=d/3 use plateau). M(z) is between L_d,U_d, by ordinary integer sieve with level below R (g(p)=1/p). The ideal conditional least-pin density bounds at exponent u<d are
    l_d(u)=e^-gamma f((d-u)/u)/u²,
    h_d(u)=e^-gamma F((d-u)/u)/u².
The reciprocal prime-bin factor du/u times lower or upper quotient roughness coefficient gives exactly these formulas. The quotient of size R^(1-u) has enough ordinary integer distribution for those ideal residual levels; hence l_d(u)<=a(u)<=h_d(u) where defined. If cutoff exceeds an admissible upper-sieve range, use reduced cutoff on upper plateau; for u>=d/4 one obtains h_d(u)=2/[u(d-u)] as an upper, including when residual level smaller than requested cutoff. This is the useful ideal single-pin upper family. The prime atom at u=1 is not controlled by these divisor-pin formulas; one-sided tails still include it. Monotonicity in the level makes this the strongest of the ordinary lower/upper families at levels <=5/8. Pin lower vanishes for u>=d/3=5/24. Factor-specific source capacity restrictions only weaken this idealized family. We do NOT impose arbitrary joint congruences, two or more pinned factors simultaneously on one target, or all possible weighted lower/upper constraints.

We seek symmetric nonnegative joint measure nu on the pair anatomy space such that for arbitrary source anatomy restrictions, all these conditional inequalities hold by integration. A useful rank-one construction:
    dnu(x,y)=[1-F(x)F(y)] dmu(x)dmu(y),
    |F|<=1, integral F dmu=0.
All perturbations are supported at positive least exponents. Write C={least>=c=.4}, m=M(c)=1+log(3/2). Take F=1 on C, negative on a subinterval of [b0,c), zero below b0. If the negative integral equals m, the joint measure is nonnegative and all row tails below b0 equal the natural M(z). For z>=b0 define H(z)=integral_{least>=z} F dmu. H>=0, increases to m at c and then decreases; H(z)=0 at b0. Row tail for fixed x is M(z)-F(x)H(z), between M-H and M+H. Maximum M+H is a decreasing tail of the nonnegative row with F(x)=-1 and at b0 equals M(b0). Thus to prove all row bounds above b0 it is enough to have M(b0)<2/d=3.2 and certify M-H>=L_d on [b0,d/2]. For z>=d/2 the lower is zero. All exact partitions and repeated exchanges remain valid for nu, and nu(CxC)=0.

## 4. First new model: all ideal conditional pin lowers, zero high correction above 5/24

Set b0=.19, u0=d/3=5/24. Take F=-g on [.19,u0), F=-1 on [u0,c), F=1 on C, zero below .19. Solve integral zero:
    g=(2m-M(u0))/(M(.19)-M(u0)).
Rational interval evaluation gives
    2.9549868724 < M(.19) < 2.9551065654+1e-10,
    2.6949626560 < M(u0) < 2.6950412267,
    .4454803 < g < .4461224.
Hence M(.19)<3.2. For z∈[b0,u0], H(z)=g(M(b0)-M(z)); for z∈[u0,c], H=2m-M(z). The interval certificate of §6 verifies M-H>=L_d on 1226 cells of width at most .0001 over [b0,d/2], lower slack >.3020. This proves the full one-sided tail family for both orientations and every anatomy row. Below b0, the row is unchanged and hence valid.

For target least u<b0, F(y)=0, the density is natural a(u), which obeys ideal pin lower. For u∈[b0,u0), every row weight >=1-g>.5538. The ratio of ideal pin lower to natural density is
    r_L(u) = [2u/(d-u)] log(d/u-2) / omega(1/u-1).
Since 2u/(d-u)<=1 and omega(v)>=1/2 for v>=1 (base [1,2], induction using (v omega(v))'=omega(v-1)), the ratio <=2 log(49/38)<.508469. Thus w a(u)>=l_d(u) for every row. For u>=u0 the pin lower vanishes. This proves all ideal lower pin densities, not just a finite subset of pin boxes or their integrated lower coefficients.

The model has nu(E_hi x E_hi)=0, E_hi=[least in u0,.4), since F=-1 on both. Its high correction square E_.208 x E_.208 contains only cross terms involving the small strip [.208,u0); rational upper <.006309 (safe <.0064). In particular it does not force the target1.54 or even positive mass if both least exceed 5/24 and are below .4. This explicitly accommodates earlier actual pinned lower data that defeated the old countermodel.

Important scope: this first new model does NOT impose all ideal conditional pin upper inequalities; some C-to-E_hi densities near u0 can exceed those uppers. The next model incorporates them as well.

## 5. Stronger model: all ideal pin LOWER AND UPPER bounds

Choose b0=.185. Keep c=.4, u0=5/24. Take F=1 on C; on negative interval set F=-g(u) with
    g(u)=g0      for .185<=u<u0,
         3/4     for u0<=u<.22,
         9/10    for .22<=u<.23,
         1       for .23<=u<.4.
Below .185, F=0. Define
    J=(3/4)[M(u0)-M(.22)]+(9/10)[M(.22)-M(.23)]+M(.23)-m,
    g0=(m-J)/(M(.185)-M(u0)).
The exact enclosure gives .4779453<g0<.4794110. Again integral F=0, nonnegative kernel. M(.185)<3.2. On [b0,c], H(z)=integral_[b0,z) g(u) a(u)du. Lower for every row M-H exceeds L_d on all 1275 cells covering [b0,d/2], certified slack >.2598. Upper by M+H<=M(b0)<3.2 as above. Below b0 natural, above d/2 lower zero.

For u∈[b0,u0), ratio r_L as in §4. Now use actual Buchstab interval bounds for omega(1/u-1), rather than .5, on cells width <=.00005. The exact lower margin 1-g0-r_L(u) is >.0396 over all 467 cells. For u>=u0 lower zero. For conditional upper, use r_U(u)=2u/[(d-u)omega(1/u-1)] for u>=b0 to .5, since (d-u)/u<=3 and upper cutoff can be reduced to its plateau. For all rows w<=1+g(u) on negative bands, and w<=2 on C. The code bounds r_U from BELOW using the left endpoint of u and an upper interval bound on omega over the cell. In all 6301 cells over [.185,.5], r_U-(1+|F(target)|)>.0176. For u<b0 natural density obeys the ideal upper and lower. No continuous least density beyond .5; prime atom remains controlled only by row tails. Thus this stronger kernel satisfies the entire ideal single-pin lower AND upper family in both orientations, with arbitrary anatomy source partitions. This is a stronger information class than the first model, not a claim to satisfy all arithmetic remainders.

Nevertheless nu(CxC)=0, and also nu([.23,.4)x[.23,.4))=0, since F=-1 throughout that band. Its high correction coefficient for E_.208 x E_.208 is
    (M(.208)-m)^2 - (m-H(.208))^2 < .125358  (safe .126).
This is much smaller than the required1.54, despite allowing all the ideal single-pin upper and lower data. Neither model proves that the actual integers have this behavior; they prove non-implication in the indicated information classes. In particular any future argument deriving .4 solely from these constraints and exact identities (even repeated switches or arbitrary source row anatomy partitions) would fail on this explicit measure. More general mixed residue statistics or two-target-factor constraints can violate this model and are not ruled out. Even the previously established mixed-factor counts at .11/.114/.125/.13/.135 are far too weak to exclude these kernels; see below.

## 6. Compatibility checks and exact interval certificate

Use g_B(y)=y omega(y), equal1 for y∈[1,2], satisfying g_B'(y)=g_B(y-1)/(y-1) for y>2, and nondecreasing. For grid y_i=i/N, N=20000, fixed point scale 10^25, propagate rigorous lower and upper values for i>2N by
    G_i^- = G_(i-1)^- + floor(G_(i-1-N)^-/(i-N)),
    G_i^+ = G_(i-1)^+ + ceil(G_(i-N)^+/(i-1-N)).
This follows by bounding numerator and denominator monotonically on each integration interval; includes the scale in the stored G. For any z>0 in range, M(z)=g_B(1/z) lies between lower at floor(N/z) and upper at ceil(N/z). For omega(y) on an interval use g_B lower at lower endpoint divided by upper y, and upper at upper endpoint divided by lower y. Extend grid to y=7 for .16 mass. Logarithms enclosed by positive atanh series, 64 terms and rational geometric tail as previous audits. All assertions use BigInt outward bounds; decimal displays use Number and are explanatory only.

First model explicit aggregate checks:
- Low sector from previous .16 correction, at least one least below .208: total E_.16 square equals [M(.16)-m]^2-m², subtract high square. Certified >2.44348, so compatible with previous 1.09 lower (and in fact all individual pin lower constraints already hold).
- Both least [.20,.365): explicit cross-band lower >.14182, compatible with .00075 prior lower.
- Thin actual high sector source band .373..376, target least .208..2083: model density coefficient >.0000266 for rectangle, far above prior tiny actual lower5e-8.
- Symmetric stationary pair lower at exponent .3,.3125,.32,.324,.334,.3346,.3347: model lower 4m[M(c')-m] exceeds .98,.59,.375,.27,.015,.002,.0005 respectively. At .3347 model lower >1.5826. All aggregate checks pass.
The second model has the same stationary formula for c'>=.23. Its .16 low sector remains >2.32 since total E_.16 square identical and high square <.126. The lower-pin proof covers all earlier integrated pin lower inequalities (including their bilateral matrix max/sum combinations).

Both models leave unchanged the joint anatomy measure on pairs whose least factors are below .185. An explicit triple rectangle in each side with least [.11,.185], second prime [.2085,.211], last determined by sum1, has bare mass at least .075*.0025/(.185*.211*.6815). Square >.00004967. This alone meets the previous mixed .11 coefficient .00003. Restrict least to [.135,.185] instead, square >.00002379; meets all the new DHR lower coefficients at .125,.13,.135 and the new vector .114 lower. Thus these specific extra mixed-factor lower facts do not break either kernel. No claim that the models satisfy the full mixed divisor distribution lemma: that lemma concerns raw joint divisibility over actual integers including factors below all fixed exponent thresholds, not an anatomy measure alone. Bridging that information to high least-factor correlations remains open.

## 7. New concrete research target after this obstruction

The previous 1.54Pi sufficient target for actual E_.208 x E_.208 remains. The stronger model says even the full family of ideal conditional single-pin upper/lower and ordinary marginal tails cannot guarantee that target. A smaller, genuine qualitative breakthrough beyond this information class would be ANY density-scale actual lower with BOTH least exponents in [.23,.4), or a high-correction coefficient >.126 that excludes this specific stronger model. The first model also exhibits zero E_hi x E_hi with threshold5/24 when only lower pin data added. Excluding one model is not a proof of .4 and other models may persist. This identifies meaningful separate subgoals: obtain mixed correlations for TWO or MORE target factors on each side, a genuinely joint weighted lower with support not reducible to current marginal envelopes, or use the new isolated HIGH sources in dynamic transport. Merely increasing the number of marginal boxes and single-pin estimates at unchanged levels cannot force M85 in the idealized class above. No new lower for [.23,.4)^2 established here.

## 8. Execution and preservation

Audit research/lean/negative_min_pin_compatible_kernel_and_frequency_audit.mjs @09df67606192f617a9b285c8d346cec184deccb9 blob 094acb3e49202fb954a11e466d7eb4aa8cae7055. Final exact pinned and active branch content matched. It includes 140001 grid entries for Buchstab (including zero prefix), 1226+1275 tail cells, 467 lower-pin and6301 upper-pin cells, explicit prior-correction and stationary bound compatibility, mixed-box coefficient comparisons, exact frequency exponent and DHR coefficient bounds, 24 finite CRT two-root checks and823 finite odd disjoint pin cases. First exploratory run failed because a factor width .075 was mistakenly entered as75/10000 instead of750/10000; corrected in final code and all final assertions passed. Intermediate models and revisions retained in Git history (00bb65fa,715f0539,b1524f77). The numeric checks are certificates for inequalities and finite algebra, not independent proof of cited analytic theorems. Source trail: Bettin--Chandee original p2,p25 screenshots; Ford p37 screenshot; Kao arXiv p6,p7,p11 screenshots; journal DOI direct access unavailable, no new theorem taken from uninspected literature. No literature priority or exhaustive review claim.

Research status remains provisional ~4.83. No M85, 4.85, twin proof, independent specialist review or Lean build. Existing core/main/siblings untouched. New mixed separated estimate .515, actual double-pin rough .135, two rigorously checked obstruction kernels. The actual symmetric .3347 and high residual sufficient threshold1.54 unchanged.