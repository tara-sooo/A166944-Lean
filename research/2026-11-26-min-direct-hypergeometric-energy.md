# Hypergeometric subset averaging of Fourier energy

Continuation of [c3d46e7](https://github.com/tara-sooo/A166944-Lean/commit/c3d46e7c43e2452763f998137991f3e9d5588254). The previous proof used one fixed split of the primorial and charged every low frequency with the worst number of complementary prime divisors. Instead average over all fixed-size subsets of a collection of large primes. Exact local Parseval still bounds the partial energies, while the complement contributes a hypergeometric exponential moment. This proves uniform mean-square smoothing at length P_R^(14/25), improving the preceding fixed-power theorem. Applications retain the earlier finite MIN inequalities. No finite-twins contradiction or Lean kernel verification.

## 1. Finite subset-averaged low-frequency energy

Use either of the two CRT barrier families (H or d) and notation of c3d46e7. P=P_R is the odd primorial, alpha_P its family density, f=1_allowed/alpha_P in coordinate j=b/2. Write
    a_p(k)=|c_p(k)|^2,
    |fhat(k)|^2=prod_{p|P} a_p(k),
where c_p is the local normalized Fourier coefficient using the full-P CRT inverse. All a_p lie in [0,1]; a_p(k)=1 if p divides k, and for p>=11 with p not dividing k, a_p(k)<=kappa_p^2, where kappa_p=1/[((p-3)/2)sin(pi/p)]<1. The two families have the same upper bound because both large-prime local sets are cyclic intervals of lengths at least (p-3)/2.

Take a collection L of n distinct primes dividing P, all >=11. Put b=min L, Kappa=max_{p in L} kappa_p. Fix an integer q with 1<=q<n, and a positive integer frequency limit M<=P/2 such that b^q>=M. For every q-element subset U of L put Q_U=prod_{p in U}p, alpha_U=prod_{p in U} alpha_p (local densities), and B_U(k)=prod_{p in U}a_p(k). Then Q_U>=M, and partial Parseval/CRT gives
    sum_{k=1..M} B_U(k) <= sum_{k=1..Q_U} B_U(k) = 1/alpha_U.
The fact that the inverse is defined with respect to P rather than Q_U does not change the sum over each local residue.

Write t=t(k)=#primes in L dividing k. For 1<=k<=M, b^t<=k<=M<=b^q, so t<=q. Let J=|U intersect {p in L:p divides k}|. The complement L\U has n-t-q+J nondividing primes. Since all other factors have magnitude at most 1,
    |fhat(k)|^2 <= B_U(k) Kappa^(2(n-t-q+J)).
Equivalently B_U(k)>=|fhat(k)|^2 Kappa^(-2(n-t-q+J)). This uses multiplication by a strictly positive factor, not division by the possibly zero Fourier energy. Average over uniform q-subsets U. The law of J is hypergeometric with masses binom(t,j)binom(n-t,q-j)/binom(n,q). Put
    F(t)=sum_j [binom(t,j)binom(n-t,q-j)/binom(n,q)]
                           Kappa^(-2(n-t-q+j)).
Binomial coefficients outside their natural range are zero. F(t) is nonincreasing in t: couple nested sets of dividing primes of sizes t and t+1 and use the same uniform U; the number of nondividing primes in its complement cannot increase. Therefore F(t)>=F(q) for every low frequency, and
    F(q) |fhat(k)|^2 <= mean_U B_U(k).
Sum over k and use partial Parseval:
    sum_{k=1..M}|fhat(k)|^2 <= B/F(q),
    B=mean_{|U|=q} 1/alpha_U.                              (1)
This is the new finite bound. The subset averaging is an exact combinatorial identity and deterministic inequality; it is not an independence model for the frequency or trajectory.

For comparison Jensen's inequality alone gives F(q)>=Kappa^(-2(n-q)^2/n). The full hypergeometric moment is stronger and admits the single-term lower bound, for every feasible integer j,
    F(q)>=binom(q,j)binom(n-q,q-j)/binom(n,q)
                           *Kappa^(-2(n-2q+j)).           (2)
Both (1) and (2) are finite inequalities; one can optimize j and U's ambient prime collection. The choice of all q-subsets is used for the simple distribution and monotonicity argument.

As in c3d46e7, let f_l be the forward moving average of length 1<=l<=P. Parseval and the interval kernel bound, splitting at min(k,P-k)<=M, give
    sigma_l^2=mean_{j mod P}|f_l(j)-1|^2
       <= 2B/F(q) + (P/(2l(M+1)))^2/alpha_P.              (3)
One can take the minimum with the former single-split or divisor-average bounds. Equation (3) is a mean-square bound, not a uniform pointwise discrepancy.

## 2. Asymptotics and the explicit exponent 14/25

Let r=#odd primes<=R, c0=log(pi/2), with circle constant pi. Use the unconditional prime number theorem, so log P~R and r~R/log R. Choose L to contain all primes R/log R<=p<=R (for R sufficiently large all are >=11). Then n=(1-o(1))r, log b~log R, and log Kappa=-c0+o(1), uniformly since b grows. The omitted small primes cause no difficulty: only their coefficient upper bound 1 is used in (1).

Fix delta in (0,1/2), and set M=ceil(P^delta exp(r)), q=ceil(log M/log b). For large R, M<=P/2, q<n, b^q>=M, q/n=delta+o(1). Uniformly on L the local densities are 1/2+O(1/b); hence
    log B <= (delta log 2+o(1))*r.
Also log(1/alpha_P)=(log 2)*r+O(log R) for either family. Define binary entropy h(v)=-v log v-(1-v)log(1-v), with the continuous endpoint values. For a fixed real j0 satisfying max(0,2delta-1)<j0<delta, choose j=floor(j0*n). It is feasible in (2) for all sufficiently large R. Stirling's formula applied to the three binomial coefficients gives
    log F(q) >= (J(delta,j0)+o(1))*r,
    J(delta,j0)=2c0(1-2delta+j0)
                 +delta h(j0/delta)
                 +(1-delta)h((delta-j0)/(1-delta))-h(delta). (4)
The entropy losses in (4) quantify the cost of selecting atypically many dividing primes inside the partial modulus, leaving more nonzero local coefficients outside. Jensen would use only the typical intersection j0=delta^2.

If J(delta,j0)>delta log 2, then for l>=ceil(P^(1-delta)) the first term in (3) decays exponentially in r. The second does too, since l M>=P exp(r):
    sigma_l^2 <= exp(-c_delta*r)
for every fixed positive c_delta strictly below min(J(delta,j0)-delta log 2,2-log 2), all sufficiently large R, uniformly in l<=P. Constants in o(1) are for fixed delta,j0.

Take delta=11/25=.44 and j0=1/4. The margin is the explicit expression
    J-delta log2
      = .74 log(pi/2)
        -.25 log(25/44)-.19 log(19/44)
        -.19 log(19/56)-.37 log(37/56)
        +.44 log(.44)+.56 log(.56)-.44 log 2
      > .0028.                                            (5)
The strict numerical inequality is certified by the accompanying integer interval-arithmetic audit: replace pi by 3.14159 (a lower bound), use the positive coefficient .74, and bound each logarithm via the first 300 terms of log x=2 sum_{i>=0} z^(2i+1)/(2i+1), z=(x-1)/(x+1), with rational remainder bound 2|z|^601/[601(1-z^2)] and outward fixed-point rounding. The resulting lower bound exceeds .00285100. The displayed margin at actual pi is approximately .00285163. The proof does not require optimizing delta or claiming the maximal possible exponent.

Consequently we may take c_delta=.001 and obtain
    sigma_l^2 <= exp(-.001*r),
    ceil(P_R^(14/25))<=l<=P_R                             (6)
for all sufficiently large R, for BOTH barrier families. This improves the prior explicit exponent 2/3 and its limiting admissible exponent 1-delta_* (~.639). At this stage no uniform bound on individual gaps is asserted.

## 3. Consequences for the established MIN inequalities

Use crossed horizon windows [X,lambda X] of an infinite canonical ray, fixed lambda>1. As established in 850c00f and 78b1212, G=(lambda-1)X+O(sqrt X), far gain G_f>=G/2-O(sqrt X), near count O(sqrt X), label bound C=floor sqrt(lambda X+1). Mark all A1 p>R>=47; m_f is the count of far marks; N counts actual canonical visits; B_R counts all far B p>R. Choose fixed 0<rho<25/28 and R the largest odd prime with P_R<=X^rho. PNT and the next-prime bound give R~rho log X, P_R=X^(rho+o(1)), P_R=o(X). With l=ceil(P_R^(14/25)), l log^a X=o(sqrt X) for any fixed a, because (14/25)rho<1/2.

The earlier disjoint horizon-union smoothing and far-only recovery inequalities, with the new bound (6), give
    9G/28-o(X) <= 2l*m_f+(C+2l)*(N+1+B_R).               (7)
Indeed the global smoothing error 2sqrt(n'*(n'+P_R))*sigma_l is o(X) since n'=G/2+l-1=O(X), P_R=o(X), and sigma_l tends to zero; the other standalone terms are O(l sqrt X+P_R+C)=o(X). No new trajectory independence or finite sampling assumption has been added.

Under N=o(sqrt X), B_R=o(sqrt X), (7) yields
    m_f >= (9(lambda-1)/56-o(1))*X/l.                     (8)
At the balanced cutoff rho=1/2, l<=X^(7/25)+1, hence m_f=Omega_lambda(X^(18/25)). This is a lower bound on occurrences, not distinct labels or an upper estimate on the actual count. The earlier fixed-power explicit bound was Omega(X^(2/3)) at the same cutoff. The admissible primorial exponent now reaches any fixed rho<25/28 (~.892857), versus <3/4 for the preceding explicit 2/3 scale. At different rho the B_R and A1 populations differ.

Without sparsity, choose S0 as in 850c00f, the largest odd prime with P_S0<=R. Its previous deficit barrier gap bound is o(R), so rounded geometric matching still gives 5m_f<=B_union+(N+2)L with L=O(log X), B_union all far B p>R plus far ordinary-decreasing nonreset B S0<p<=R crossing a dense S0 DEFICIT barrier down. Substitute in (7), since l L=o(sqrt X). The earlier joint count
    N+B_union >= (9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X
therefore holds throughout the expanded cutoff range without either sparsity hypothesis. It is a lower count, not a stopping invariant.

The weighted tail inequality from f7c6f40 allocates (p/5,p] to the next downward crossings, and gives
    (4/5)W_T <= G_long+(C+4l)(N+B_R+1)+2C
for W_T=sum of A1 labels p>R,p>=T and T>=max(48,20l). Long low-label runs have gain>=4l; as in 4777ea7, their disjoint horizon intervals give G_long<=4(G/2+P_R)*sigma_l^2. Apply (6) to obtain
    W_T=O_lambda(X exp(-.001*r)+sqrt X*(N+B_R+1)).         (9)
In the sparse branch, at T=24l the tail already has o(X) weight and o(X/l)=o(m_f) occurrences. At balanced rho=1/2, this threshold is O(X^(7/25)), improving the explicit X^(1/3) threshold of c3d46e7. The earlier good-slab count O(sqrt X log^2 X) of exceptional marks, split at 24l, again has o(X) weight using l log^2 X=o(sqrt X) and (9), giving W_good=W-o(X). This does not imply a relative o(W) error when W=o(X). Neither sparsity assumption follows from finite twins, and the lower-band recovery supply is not yet upper-bounded sufficiently for a contradiction. The new Fourier proof is also valid for deficit barriers, but its applications here use disjoint horizon intervals; it is not a direct averaging theorem for repeated deficit crossings.

## 4. Diagnostics and preservation

[Audit 74e498a](https://github.com/tara-sooo/A166944-Lean/blob/74e498a4b85d45d7f724dd6c8b977c2c0cc65a68/research/min_direct_hypergeometric_energy_audit.mjs), blob 2ae444e5d0c23ff218fe8455658820db1ea51e08, exact remote readback. Run node research/min_direct_hypergeometric_energy_audit.mjs. Actual ECMAScript executed in the tool runtime. Complete periods R13/17/19 for both families, ambient primes >=11, all nonempty proper subset sizes, M=min product of q smallest ambient primes, and lengths ceil(P^.56),ceil(P^.75). 22,220 pointwise subset inequalities, 5,500 hypergeometric coefficient inequalities, 44 partial Parseval sums, 12 summed low-frequency energy inequalities, 40 monotonicity checks, 24 variance bounds, 60,300,240 direct moving-average position checks. All passed. At R19, P=4,849,845, q=2, M=143, l=5547, measured full-period variance H=.041880676741157224, d=.00785920691416714. The finite formula bound at those small cutoffs is loose (3456.088... and1488.128... respectively); these are diagnostics of inequalities, not evidence of an effective asymptotic R threshold. Floating trigonometric checks use tolerance; the entropy margin is separately certified by exact BigInt interval arithmetic with 10^40 fixed-point scale and remainder as in section2. No fresh MIN trajectory scan is claimed this turn: the applications are algebraic substitutions into previously proved and audited finite inequalities (850c00f, 78b1212, 4777ea7, f7c6f40). No infinite-ray observation, external novelty claim or Lean kernel verification. Main and sibling branches unchanged.

Next: investigate sharper control of low-frequency energies by local higher moments, or a second subset averaging stage, and use the smaller power scale to seek an actual upper bound on low-label recovery supply. The present theorem strengthens the necessary occurrence and weighted tail constraints but establishes no contradiction with finite twins.
