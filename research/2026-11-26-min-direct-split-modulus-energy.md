# Split-modulus Fourier energy: power-scale smoothing and stronger occurrence bounds

Continuation of [f7c6f40](https://github.com/tara-sooo/A166944-Lean/commit/f7c6f400bb201f9f128c732dc5e38145d2086515) and [78b1212](https://github.com/tara-sooo/A166944-Lean/commit/78b1212d87663bbc8a7b137aa3e18375bc18885b). The previous mean-square estimate used the product of local coefficient maxima and a divisor average. Instead, on a suitable smaller primorial, sum the squared Fourier coefficients exactly by Parseval, and use coefficient maxima only on the complementary primes. This proves a fixed-power improvement of the smoothing scale, for BOTH horizon and deficit CRT barrier families. Applications here use disjoint horizon intervals and long low-label runs; no unjustified averaging of repeatedly visited deficit levels. No twin-prime contradiction or Lean kernel verification.

## 1. Finite split-modulus inequality

Let R>=11, P=P_R be the product of odd primes <=R, and r the number of these primes. In integer coordinate j=b/2 use either barrier family of f82180c. At p>=11 the local allowed set is a cyclic interval of length (p-1)/2 (horizon) or (p-3)/2 (deficit); p3,5,7 have their previously defined nonempty sets. Write A_p for the local set, a_p for its cardinality, alpha_P=prod(a_p/p). For any divisor Q of P put alpha_Q=prod_{p|Q}(a_p/p), using the SAME local sets of that family. Define normalized periodic indicator f=1_allowed/alpha_P on Z/P, and forward average f_l(j)=l^(-1) sum_{0<=a<l} f(j+a). Then
    fhat(k)=prod_{p|P} c_p(k),
    c_p(k)=(1/a_p) sum_{u in A_p} exp(-2pi i k v_p u/p),
where v_p is the inverse of P/p modulo p. All coefficients use the full-P CRT inverse, including the factors in the partial product. This matters: they need not be the coefficients with the inverse defined using Q instead of P. But v_p is a unit modulo p, so their squared sums are unchanged by that permutation.

Take Q=P_S for a prime S<R, 1<Q<=P/2. Let p_* be the first prime after S and let r_Q count the odd primes <=S. Put
    Kappa=max_{S<p<=R} kappa_p,
    kappa_p=1 for p=3,5,7,
    kappa_p=1/[((p-3)/2) sin(pi/p)] for p>=11,
    u=max(0,r-r_Q-floor(log Q/log p_*)).
Here u is a lower bound on the number of complementary primes not dividing any given positive k<=Q. Indeed if t different complementary primes divide k, their product is >=p_*^t and <=k<=Q. At every such nondividing prime |c_p(k)|<=kappa_p (local cyclic interval geometric-series bound); all other coefficients have magnitude<=1.

Now set B_Q(k)=prod_{p|Q}|c_p(k)|^2. By CRT and local Parseval,
    sum_{k=1..Q} B_Q(k)
      =prod_{p|Q} sum_{k mod p}|c_p(k)|^2
      =prod_{p|Q}(p/a_p)=1/alpha_Q.
This gives the finite, low-frequency energy bound
    sum_{k=1..Q}|fhat(k)|^2 <= Kappa^(2u)/alpha_Q.        (1)
The point is to use the exact sum over the smaller period Q, rather than bounding every coefficient there by the maximum. For the remaining frequencies, Parseval on P gives sum_{k mod P}|fhat(k)|^2=1/alpha_P.

For 1<=l<=P, the moving-average variance is
    sigma_l^2=mean_{j mod P}|f_l(j)-1|^2
             =sum_{k=1..P-1}|fhat(k)|^2
                    |l^(-1) sum_{a=0..l-1} exp(2pi i ka/P)|^2.
The squared kernel is <=1 always and <=P^2/(4l^2 min(k,P-k)^2) by sin(pi k/P)>=2 min(k,P-k)/P. Since P is odd, the low frequencies min(k,P-k)<=Q have two symmetric halves. The remaining terms have min(k,P-k)>=Q+1, and their energy is at most the full Parseval sum. Thus
    sigma_l^2 <= 2 Kappa^(2u)/alpha_Q
                     + (P/(2l(Q+1)))^2/alpha_P.          (2)
This finite bound is valid for arbitrary l, Q of the stated form; it may be minimized over Q and combined with the earlier 4V_R/l bound. No distributional assumption on CRT inverses, no large-sieve hypothesis, no trajectory independence.

## 2. Fixed-power smoothing theorem

Write c0=log(pi/2) (pi is the circle constant), and define
    delta_* = 2c0/(4c0+log 2) = 0.361... .
Fix any 0<delta<delta_*. Let l>=ceil(P_R^(1-delta)) with l<=P_R. Choose Q=P_S the smallest odd-prime primorial at least
    P_R^delta exp(r).
For all sufficiently large R, Q exists with Q<=P_R/2: using the prime number theorem (a standard unconditional theorem), log P_R~R and r~R/log R. The target log is delta log P_R+r, and the overshoot in log Q is at most log R. Consequently log Q=(delta+o(1))R, S=(delta+o(1))R and r_Q=(delta+o(1))r. These consequences follow directly by applying the prime number theorem to the primorial log sum and the prime-count function. Also log p_*=log R+O_delta(1), because S~delta R and Bertrand's postulate bounds the next prime by 2S. Therefore
    floor(log Q/log p_*) <= (delta+o(1))*r,
    u >= (1-2delta-o(1))*r.
All complementary primes grow uniformly, so log Kappa=-c0+o(1). For either family the densities have
    log(1/alpha_Q)=(log 2)*r_Q+O(log R),
    log(1/alpha_P)=(log 2)*r+O(log R),
since each large-prime local density is (1/2)*(1+O(1/p)) and the crude harmonic bound suffices. The first term of (2) is therefore at most
    exp((-2c0(1-2delta)+delta log 2+o(1))*r).
The second term is at most exp((log 2-2+o(1))*r), since l Q>=P exp(r). Both exponents are negative for delta<delta_*. In particular, for any fixed
    0<c_delta<min(2c0(1-2delta)-delta log 2, 2-log 2)
and all sufficiently large R,
    sigma_l^2 <= exp(-c_delta*r),
           ceil(P_R^(1-delta))<=l<=P_R.                 (3)
The sum of the two exponentials is absorbed by the strict choice of c_delta. The statement is uniform in l in this range and common to the two families. It uses PNT only for the asymptotic size of the split, not for any hypothesis about twin primes or MIN trajectories.

For delta=1/3, the first margin is (2c0-log 2)/3=0.0700...>0. Thus one can take, for example, c_delta=0.03, and use l=ceil(P_R^(2/3)). This is a fixed-power improvement over the earlier scale V_R=P_R exp(-(2c0+o(1))*r)=P_R^(1-o(1)). Neither (2) nor (3) asserts a pointwise discrepancy or maximum-gap bound of order l; the theorem concerns a complete-period mean square. The finite upper formula can be loose at small R and the asymptotic proof is not inferred from those samples.

## 3. Consequences for horizon coverage and far A1 counts

Use the same MIN notation as 78b1212 and 850c00f: crossed [X,lambda X], lambda>1 fixed, canonical infinite ray, total horizon gain G=(lambda-1)X+O_lambda(sqrt X), far gain G_f>=G/2-O(sqrt X), near count O(sqrt X), label bound C=floor sqrt(lambda X+1). Mark all A1 p>R>=47, with m_f counting the far marks; N counts actual canonical visits, B_R all far B p>R. Choose fixed rho with
    0<rho<min(1, 1/(2(1-delta))),
and R the largest odd prime with P_R<=X^rho. The next-prime bound and PNT give R~rho log X, P_R=X^(rho+o(1)), P_R=o(X), and l=ceil(P_R^(1-delta)) satisfies l log^A X=o(sqrt X) for every fixed A. No assumption on the density of twin primes is used. One may take any more conservative cutoff with these same bounds.

The horizon intervals of all high-label jumps p>R are disjoint and cover every R horizon barrier. The deterministic union-smoothing inequality of 78b1212, combined with the far-only recovery share bound of 850c00f, gives
    c/(1+c) G_f <= 2l*m_f+(C+2l)(N+1+B_R)
                  +2l*n_near+2P_R+err_l+2C/(1+c),
    c=9/5-O(X^(-1/4)),
    err_l=2 sqrt(n'*(n'+P_R))*sigma_l,
    n'=G/2+l-1.
By (3), err_l=o(X); all other standalone errors are o(X). We obtain
    9G/28-o(X) <= 2l*m_f+(C+2l)(N+1+B_R).             (4)
If along a sequence of crossed windows N=o(sqrt X) and B_R=o(sqrt X), then
    m_f >= (9*(lambda-1)/56-o(1))*X/ceil(P_R^(1-delta)).
                                                               (5)
This is a fixed-power improvement at the SAME cutoff R. For example at the original balanced cutoff rho=1/2 and delta=1/3,
    m_f=Omega_lambda(X^(2/3)).
In contrast the former mean-square V_R bound at the balanced cutoff was of scale X^(1/2+o(1)). The latter is a description of the former lower-bound scale, not an upper bound on m_f. The improvement here is in a necessary count. The permissible primorial exponent also increases: with delta=1/3 any fixed rho<3/4 is allowed, e.g. rho=7/10, whereas the former enlarged cutoff had P_R=X^(1/2+o(1)). With delta tending to delta_* from below, the fixed admissible rho can approach 1/(2(1-delta_*))=0.782... from below. At a larger cutoff the counted population changes.

Without either sparsity hypothesis the earlier joint theorem still follows at all these cutoffs. Choose the lower cutoff S0 as the largest odd prime with P_S0<=R, so the earlier uniform deficit barrier gap bound Bgap_S0=o(R) holds (f82180c). The far-only rounded level matching from 850c00f gives
    5m_f<=B_union+(N+2)L,  L=O(log X),
where B_union is all far B p>R plus far ordinary-decreasing nonreset B S0<p<=R crossing a dense S0 DEFICIT barrier downward. Since l log X=o(sqrt X), substitute in (4), using B_R<=B_union, to obtain
    N+B_union >= (9*(lambda-1)/(28 sqrt(lambda))-o(1))*sqrt X.
The leading constant is unchanged, but the cutoff range is genuinely larger. This does not force either sparsity hypothesis, nor imply a stopping theorem.

## 4. Weighted tail bound at the new power scale

Use the lower recovery-interval and precursor-exclusion theorem of f7c6f40. It allocates (p/5,p] to subsequent first downcrossings for each A1 p>R,p>=T; W_T is their sum of labels counting occurrences. For l integer, 1<=l<=P_R and 4l<=T/5, it proves the finite inequality
    (4/5)W_T <= G_long+(C+4l)(N+B_R+1)+2C,
where G_long is the total horizon gain of low-label runs (all p<=R) of gain at least4l. This holds at pre-horizons >=4097 and R>=47, T>=48. The key is that a short paying low run must follow a high reset or far high B, not A1 or a near nonreset. Each paying run has a distinct preceding event.

The sharper first inequality of 4777ea7 gives
    G_long <=4*(G/2+P_R)*sigma_l^2.
Indeed a long barrier-free run of index length >=2l contains at least half as many disjoint start positions where the forward average vanishes; each zero contributes 1 to the squared fluctuation. The runs are disjoint in H, so summing the positions is legitimate. Substitution of (3) now gives for every T>=max(48,20l) (with T>C simply an empty tail)
    W_T=O_lambda(X exp(-c_delta*r)+sqrt X*(N+B_R+1)).    (6)
Here l=ceil(P_R^(1-delta)) and the cutoff of section3 is used. This estimate does not need to apply any moving-average inequality directly to overlapping deficit intervals. In the sparse branch, already at the FIXED multiple T=24l, W_T=o(X), not merely at a multiplier tending to infinity. Since each tail mark has label>=24l, its count is o(X/l)=o(m_f) by (5). Thus all but o(m_f) occurrences of all high A1 lie below 24l, and the omitted weight is o(X). More precisely if m_all is the count of all marks, this also gives m_tail=o(m_all) since m_all>=m_f. At balanced rho=1/2, delta=1/3, the tail threshold is O(X^(1/3)), an actual weight restriction in addition to the count bound. Near A1 labels are of order sqrt X, so all marked near A1 have o(X) total weight. Neither the total A1 weight nor its fraction of G is forced to be positive; the additive o(X) error is not a relative o(W) statement for sublinear W.

The earlier completed-slab exceptional-count theorem also remains valid: bad count O(sqrt X log^2 X) under these sparsity assumptions. Below 24l their weight is O(l sqrt X log^2 X)=o(X); above it use (6). Therefore W_good=W-o(X) and the dense lower deficit-barrier budget of 850c00f holds on the good marks at the new cutoffs, with F+2E_S0*j>=(9/5-o(1))*W_good and F>=theta_S0*(9/5-o(1))*W_good. These are still necessary constraints, not an upper bound excluding the recovery supply at the new scale.

## 5. Diagnostics and persistence

[Split-modulus audit 669c892](https://github.com/tara-sooo/A166944-Lean/blob/669c892a954480be7dc047653a7386ee035670c6/research/min_direct_split_modulus_energy_audit.mjs), blob 2fe8b21f09b43e4b5bb5e1119a0b9be3831b0aa0, exact remote readback. Actual ECMAScript function executed in tool runtime. Complete periods R7/11/13/17/19, both families, l=ceil(P^(2/3)),ceil(P^(.75)),ceil(P^(.9)). 30,728,250 moving-average position checks, 40 Parseval checks including independent direct variance versus spectral computation, 120 partial-energy and 120 finite split-variance bounds. All passed. R19 P=4,849,845,l=28,652: exact-period numerical variances H0.006400932741419159 and d0.0015797135764047728, zero positions absent in both. The finite formula (2) was also evaluated in log-space at R100/200/500/1000/2000 for delta1/4,1/3,.35; these particular conservative formula bounds remain large at those cutoffs. They are not evidence that the asymptotic negative exponent is already effective at those R. The fixed-power theorem uses the proved inequality and PNT, not an extrapolation of sampled variances. Trigonometric/variance computations use floating-point tolerances; CRT set enumeration uses exact integer arithmetic.

[Application audit 8454dce](https://github.com/tara-sooo/A166944-Lean/blob/8454dceb43e879d22e4f6eaacb55d93073e76972/research/min_direct_power_smoothing_application_audit.mjs), blob 6b383c080b939f0b2a0a59ba6fb9868f44f94b97, exact remote readback. Derived from the earlier mean-square application audit with the three power lengths and exact complete-period variance in the Cauchy error (not the asymptotic bound). Run node research/min_direct_power_smoothing_application_audit.mjs 30000 180. 14,998 canonical odd roots M5..30000,243,497 events,1,899 A1,all stopped within180. 107,184 block/far-share checks,321,552 high-barrier coverage and joint capacity tests,327,552 convolution and Cauchy checks each incl6,000 synthetic unions,30,728,340 moment-position incidences,300,000 divisor averages. All passed. Low diagnostic R counts other high far events where appropriate rather than the asymptotic R>=47 classification. The tail consequence uses the previously verified finite precursor inequality and zero-start bound, not a claimed numerical instance of sparse macroscopic windows. No Lean kernel verification, no observed infinite ray, no historical novelty claim. Main/sibling branches unchanged.

Next: exploit the power-scale count and weighted tail to seek an actual frequency ceiling for low-label high-deficit recoveries, or sharpen the split-modulus low-frequency energy further. The present improvement changes the scale by a fixed power but remains compatible with abundant low-label recovery on a hypothetical infinite ray. Neither sparsity hypothesis follows from finite twins; no contradiction has been established.
