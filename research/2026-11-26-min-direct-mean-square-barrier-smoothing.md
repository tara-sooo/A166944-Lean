# Mean-square CRT barrier smoothing and a larger admissible cutoff

Continuation of [850c00f](https://github.com/tara-sooo/A166944-Lean/commit/850c00f2bac25d3c9eb49ef75993187ce054a995) and [f82180c](https://github.com/tara-sooo/A166944-Lean/commit/f82180c76e6c0db2570a063b7931544054c5b9db). Instead of paying a uniform interval-discrepancy bound on every jump, smooth the normalized barrier indicator and bound its global mean-square fluctuation. All high-label jump intervals on one ray form a disjoint family, so their aggregate barrier coverage is bounded by their total length, a smaller boundary-expansion cost, and one global error. This gives an exponentially improved A1 occurrence lower bound and permits a larger primorial cutoff. No twin-prime contradiction or Lean kernel verification.

## 1. Mean-square bound for either CRT barrier family

Use the integer coordinate j equal to the even horizon or deficit cut divided by 2. For cutoff R let P=P_R be the product of odd primes<=R. The horizon barrier family and the downward deficit barrier family are the two DIFFERENT periodic CRT sets defined in f82180c. Write A for the number of allowed residues, alpha=A/P for the density of the family under consideration, and
    f(j)=1_{allowed}(j)/alpha,
    f_l(j)=(1/l) sum_{0<=a<l} f(j+a)
for any positive integer l. Both have period P and mean 1. The moving average is forward in j.

As in f82180c, define for odd primes p>=11
    kappa_p = 1/[((p-3)/2)*sin(pi/p)] < 1,
    Lambda_R = product_{11<=p<=R} kappa_p,
    F_R(k) = product_{11<=p<=R, p|k} kappa_p^(-1)
(products over primes). Both families have normalized Fourier coefficients bounded by Lambda_R F_R(k) for 1<=k<P. The local Fourier bound follows from the finite geometric series for a cyclic interval; CRT factors the normalized coefficient into local coefficients at frequencies k times the respective CRT inverses. The local coefficient at a nonzero frequency has magnitude<=kappa_p and at zero frequency equals 1; use trivial bound1 for p3,5,7.

NEW define
    D2_R = product_{11<=p<=R} (1+(kappa_p^(-2)-1)/p),
    V_R = P_R Lambda_R^2 D2_R.
The nonnegative divisor expansion of F_R(k)^2 gives, for real M>=1,
    sum_{1<=k<=M} F_R(k)^2
       = sum_{a<=M, a|product_{11<=p<=R}p}
                  floor(M/a) product_{p|a}(kappa_p^(-2)-1)
       <= M D2_R.                                             (1)
For 1<=l<=P, Parseval and the finite interval exponential sum give
    sigma_l^2 = (1/P) sum_{j mod P} |f_l(j)-1|^2
       = sum_{1<=k<P} |fhat(k)|^2
                        |(1/l)sum_{a=0..l-1}exp(2pi i ka/P)|^2
       <= 2 Lambda_R^2 sum_{1<=k<=P/2}
                   F_R(k)^2 min(1,P^2/(4 l^2 k^2)).
Put K=P/l>=1. By (1), terms k<=K contribute <=K D2_R inside the last sum. Terms 2^j K<k<=2^(j+1)K, j>=0, contribute at most
    (1/(4*2^(2j))) D2_R*2^(j+1)K = 2^(-j-1) K D2_R.
Summing and including the leading factor2 proves the uniform mean-square theorem
    sigma_l^2 <= 4 V_R/l,        1<=l<=P.                     (2)
This is a deterministic complete-period average over the barrier locations, not a distributional hypothesis about MIN trajectories.

Write c0=log(pi/2), where pi here is the circle constant, and pi(R) for prime count. From kappa_p=(2/pi)(1+O(1/p)), elementary Chebyshev bounds, and the crude harmonic estimate sum_{p<=R}1/p=O(log R), we get
    V_R/P_R=exp(-(2*c0+o(1))*pi(R)),
    V_R/E_R=exp(-(c0+o(1))*pi(R)).                            (3)
Here E_R is the previous uniform normalized interval-discrepancy bound of f82180c. The second identity follows from that note's formula for E_R/P_R. In particular V_R/E_R beats every fixed negative power of R. V_R tends to infinity (each p*kappa_p^2>1 by a fixed factor for all sufficiently large p), while V_R/P_R tends to zero. The new estimate is not a uniform pointwise interval bound V_R; it controls aggregate coverage via (2).

## 2. Smoothed union capacity

Let J=[a,b) be an integer-coordinate interval of length n=b-a, and U be a union of m disjoint half-open integer subintervals of J. Write U^- for the set of integer positions j with [j,j+l) meeting U, i.e. the union of those intervals expanded by l-1 positions to the left. Then |U^-|<=|U|+(l-1)m, and U^- is contained in J'=[a-l+1,b) of length n'=n+l-1.

Every point k in U contributes f(k)/l to f_l(j) for all l starting positions j=k-l+1,...,k, all of which belong to U^-. Since f>=0, summing yields
    sum_{k in U} f(k) <= sum_{j in U^-} f_l(j)
       <= |U|+(l-1)m+sum_{j in J'} |f_l(j)-1|
       <= |U|+(l-1)m+sqrt(n'*(n'+P))*sigma_l.               (4)
For the last inequality apply Cauchy-Schwarz and periodicity: the sum of squares over any interval of n' positions is at most (n'+P) times the complete-period mean square, since the final partial period is nonnegative and bounded by one full period. This estimate is valid for arbitrary translates, for ANY disjoint intervals, and even if U was selected using all the barrier locations. No assumption of independent sampling of intervals is made. We can use an upper bound on m instead of its exact value.

In particular if U covers every barrier in J, its normalized mass equals sum_{J} f. The elementary period discrepancy gives sum_J f>=n-P. Thus
    n-|U| <= (l-1)m+P+sqrt(n'*(n'+P))*sigma_l.               (5)
For J formed by a contiguous block of MIN events and U the union of high-label p>R jump intervals, all H-barriers in J are covered by U, because low labels p<=R cannot cross one. Consequently the total horizon gain of low-label jumps is at most twice the RHS of (5). This is a new aggregate low-run supply constraint. In a long interval of order X, if P=o(X), l=o(X), V_R/l=o(1), it bounds low gain by 2l times the high event count plus o(X), rather than the earlier 2E_R times that count. The mean-square theorem is also true for deficit cuts, but (4) cannot automatically be summed over a trajectory's repeated deficit intervals; the disjoint horizon intervals are essential to the present application.

## 3. Far-only recovery and improved A1 count

Use the established adaptive MIN rule, ordinary deficit d and x=d+3, adjusted D=d'-6I. A1 means p>=47, p>=5d+15, D=2p; A0 the same low-deficit test with D=0; B all other events at p>=47. Far and near are the fixed square-band classes of 8b30078.

For a finite contiguous canonical event block with pre-horizon lower bound A0_min>=257, put k=floor((A0_min-1)^(1/4)), eta=2/k, c=9/5-2eta. Let G be its total horizon gain, G_f all far gain, C an upper bound on the labels, N the actual canonical visits in its tick interval (start,end], and n_near the number of all near events. Mark all A1 with p>R>=47, let F_f and m_f be the total gain and count of the FAR marks. Let B_R be the count of all far B with p>R, n_A0 the far A0 count above R, and D_nr the total ordinary deficit decreases of near decreasing resets.

Recall the finite theorem of 850c00f: a later near label s is >=(1-eta)p for a mark p, so it cannot pay nonreset recovery below 2(1-eta)p. Assign every level in (p/5,2(1-eta)p] to its next downward crossing. Nonreset payments are all far, per-event assigned length<=actual ordinary drop, and total pending length<=2C. Since marked A1 cannot decrease d, this gives
    (1+c) F_f <= G_f + D_nr + 2C.                            (6)
Near decreasing resets and high-far A0 resets are disjoint, and each corresponds to a distinct actual canonical visit within seven ticks before another label>=7 event, except possibly one pending at the block endpoint. Their combined count<=N+1; D_nr<=C times its own near reset count.

Take J=[H_start/2,H_end/2), n=G/2 and U all jumps p>R. Its absolute length 2|U| is <= G-G_f+F_f+C(n_A0+B_R), and its component count is <=m_f+n_A0+B_R+n_near. By (5),
    G_f <= F_f+C(n_A0+B_R)
       +2l(m_f+n_A0+B_R+n_near)+2P+err_l,
    err_l=2 sqrt(n'*(n'+P))*sigma_l.
Combine with (6) and the disjoint reset-count bound to obtain the finite joint inequality
    c/(1+c) G_f
       <= 2l*m_f+(C+2l)*(N+1+B_R)
                    +2l*n_near+2P+err_l+2C/(1+c).            (7)
In (7), sigma_l can be replaced by 2 sqrt(V_R/l) using (2). It is useful that the single error err_l is NOT multiplied by the number of high events.

Consider crossed [X,lambda X] with fixed lambda>1 on an infinite canonical ray. As before G=(lambda-1)X+O_lambda(sqrt X), G_f>=G/2-O(sqrt X), n_near=O(sqrt X), C=floor sqrt(lambda X+1), c=9/5-o(1). Assume cutoff R~log X satisfies P_R=o(X) and V_R log^A X=o(sqrt X) for every fixed A>0. Choose
    l=ceil(V_R*(log X)^2).
For the cutoff choices below l<=P_R eventually by (3), and l log^A X=o(sqrt X) for every fixed A>0. Then sigma_l=O(1/log X), err_l=o(X), and (7) gives
    9G/28-o(X) <= 2l*m_f+(C+2l)*(N+1+B_R).                  (8)
If N=o(sqrt X) and B_R=o(sqrt X), this implies
    m_f >= (9*(lambda-1)/56-o(1))*X/l.                      (9)
Compared to 850c00f, the denominator E_R is replaced by l=O(V_R log^2 X), an improvement of exp((c0+o(1))*pi(R)) when R~log X. In particular this is a lower bound specifically on far A1 occurrences.

A stronger order-of-magnitude result avoids the log^2 X factor. Instead set l=ceil(100 V_R). For sufficiently large R, l<=P_R and sigma_l<=1/5. As P_R,l=o(X), err_l<=(1/5+o(1))*G. Under the same sparsity hypotheses, (7) now yields
    (9/28-1/5-o(1))*G <= 2l*m_f,
    m_f >= (17*(lambda-1)/28000-o(1))*X/V_R.               (10)
The explicit coefficient is smaller than the coefficient in (9), but the asymptotic scale is stronger. No finite-sample fit supplies this coefficient: it comes from the analytic bound (2), the chosen factor100, and the far-gain residual.

There is also a simple new count upper bound on the moderately large marked-label tail: since total far mark gain<=G, at any t>1 its count at p>=t is <=G/(t-1). With (10), the proportion of far marks p>=t is O(V_R/(t-1)) under the sparse hypotheses. In particular at least half the far marks have label O(V_R), and for any diverging omega, all but o(m_f) have p<=omega V_R. At balanced R one may take t=sqrt(V_R E_R), exponentially smaller than E_R. This is an upper count, not a new upper bound on tail weight at that lower threshold. The previous deterministic weight bound W_T=o(X) at T~E_R from 850c00f remains available for the balanced cutoff.

## 4. Enlarging the prime cutoff beyond the balanced primorial

The balanced R of f82180c was the largest odd prime with P_R<=sqrt X. It satisfies the assumptions of section3 by (3). More generally, fix 0<=gamma<2*c0, and choose the largest odd prime R such that
    P_R * exp(-gamma*pi(R)) <= sqrt X.                      (11)
This exists for large X; along increasing primes the left side is eventually strictly increasing and tends to infinity. Elementary Chebyshev bounds on log P_R and pi(R) and Bertrand's postulate on the next prime show R=Theta(log X). Indeed the logarithm of the left side is Theta(R), and the next prime <=2R violates (11). Moreover
    P_R <= sqrt X * exp(gamma*pi(R)) = X^(1/2+o(1)),
    V_R <= sqrt X * exp(-(2*c0-gamma+o(1))*pi(R)).
Thus P_R=o(X) and V_R log^A X=o(sqrt X) for every fixed A>0. Both (9) and (10) apply. In particular under the sparse hypotheses
    m_f = Omega(X/V_R)
        >= sqrt X * exp((2*c0-gamma+o(1))*pi(R))
in the lower-bound sense (constant factors absorbed in o(1) in the exponent).

For c0<gamma<2c0 this range genuinely exceeds the former uniform-discrepancy regime E_R=o(sqrt X). To see this, violation of (11) at the next prime r<=2R gives P_R>sqrt X exp(gamma*pi(R))/O(R), so (5) of f82180c implies E_R/sqrt X tends to infinity for such gamma. The single global error in (7) avoids the need to assume E_R=o(sqrt X). The large-label weighted tail theorem that used uniform E_R in the deficit coordinate may become vacuous at these larger cutoffs; it is not being extended by an unjustified smoothing argument in that coordinate.

## 5. Unconditional-on-sparsity joint count at the enlarged cutoff

Let S be the largest odd prime with P_S<=R. Then S=Theta(log R), E_S=o(R), and the dense deficit gap bound Bgap_S=2ceil(E_S)+4=o(R) follows from f82180c. Define B_union exactly as in 850c00f: all far B with p>R together with far ordinary-decreasing nonreset B S<p<=R that cross a dense S DEFICIT barrier downward. For the FAR A1 marks p>R, choose rounded geometric levels with ratio beta=3/2+10Bgap_S/R and reference starting at R/5, selecting levels in (p/5,2(1-eta)p-Bgap_S] before rounding up to a shifted dense deficit barrier. For sufficiently large X each mark has at least five such levels, successive rounded levels are separated by factor>=3/2, and all lie in its far-only recovery interval. First-downcross matching is globally injective on nonresets by x/x'<3/2; such matches are far with s>S, and hence all belong to B_union. At most (N+2)L matches are lost to resets and pending endpoint, where L=O(log X) is the total reference level count. Therefore 5 m_f<=B_union+(N+2)L.

Use (8) with l log X=o(sqrt X) and B_R<=B_union. This proves, at EVERY cutoff (11) without either sparsity hypothesis,
    N+B_union >= (9*(lambda-1)/(28*sqrt(lambda))-o(1))*sqrt X. (12)
The leading coefficient is unchanged from 850c00f, but the admissible R is larger: now the high-far B band starts above R from (11), and the lower cutoff S is also chosen from that R. The populations of B_union change with the cutoff, so this is not an assertion that the same fixed set has a larger count. This strengthens the earlier cutoff scope; it still is not an upper bound on the supply of B_union and does not force canonical returns or high-far B sparsity individually.

## 6. Reproducible diagnostics

[Audit a31ae6b](https://github.com/tara-sooo/A166944-Lean/blob/a31ae6b50279d88915439db0a41a70aaea1897ce/research/min_direct_mean_square_barrier_audit.mjs), blob 4b05b620d2ad781d91a1802f2f8eb4364295d899. Exact remote readback. Run node research/min_direct_mean_square_barrier_audit.mjs 50000 180. Actual ECMAScript executed in tool runtime, not a separate Node process.

Complete periods R5/7/11/13/17/19 for both barrier families, at up to five smoothing lengths (1, floor sqrtP, floor P/4, floor P/2, P). 51,213,870 moving-average position incidences in the moment checks, 300,000 divisor-average tests, 7,500 synthetic union/cutoff/length tests. At R19, P=4849845 and l2202, actual full-period variances H0.09983426894065403 and d0.027592230225302293; analytic upper bound 1928.4953745894145. The small-cutoff bound is very loose; the proof does not identify these finite actual variances with the asymptotic upper formula.

24,998 odd canonical roots M5..50000, 452,868 events, 3,929 A1, all stopped within180. 180,668 full/suffix block-cutoff incidences with sufficiently large lower pre-horizon, 180,668 far gain-share checks, 677,505 high jump barrier coverage and joint capacity checks, and 685,005 convolution and Cauchy checks each including synthetic controls. For R5/7/11/13 the audit uses several finite l choices, exact integer interval/cut counts within safe range, floating-point moments/trigonometry and comparison tolerances; the low R values are geometry diagnostics, not empirical instances of the asymptotic B classification (other high far events are included in the diagnostic count). All assertions passed.

Formula-only evaluations of log10(E_R/V_R) at R100/200/500/1000/2000: 5.0110687 / 9.2359490 / 18.9972885 / 33.4469390 / 60.0706950. These are ratios of proved bounds, not observed maximum gaps or measured occurrence count improvements. The audit does not observe a macroscopic infinite-ray window, and the new stronger count follows from the symbolic argument. No external research or Lean kernel verification, no claim of historical novelty, main and sibling branches unchanged.

Next: exploit the stronger occurrence bound and O(V_R) typical marked labels to constrain actual low-label recovery supply, or obtain a small-discrepancy result applicable to repeatedly traversed deficit intervals without assuming disjointness. The new averaging argument is legitimate because horizon intervals are disjoint; transferring it blindly to deficit trajectories would be invalid. Neither the new joint count nor the sparse-branch constraints prove the finite-twins contradiction.
