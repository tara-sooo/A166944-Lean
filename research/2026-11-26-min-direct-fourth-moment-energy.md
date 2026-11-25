# Weighted fourth-moment subset energy and smoothing exponent 17/32

Continuation of [9007b46](https://github.com/tara-sooo/A166944-Lean/commit/9007b46b95ddb3bebcf9e72b2d3b075820c7848e). Replace the previous partial second moments with weighted fourth moments. An exact local additive-energy formula gives a smaller partial Parseval cost; conditional arithmetic-geometric mean on subsets of the nondividing primes supplies the corresponding lower bound. A concavity argument controls every possible divisor count, without assuming its worst value occurs at the endpoint. This yields a fixed-power smoothing exponent 17/32 for both barrier families. The target exponent <=1/2 is not yet achieved. No contradiction with finite twins or Lean kernel verification.

## 1. Exact local fourth moment

Use the odd primorial P=P_R, the H or d CRT barrier family, normalized indicator f on the integer coordinate j=b/2, and local Fourier coefficient c_p(k) with full-P CRT inverse as in c3d46e7 and 9007b46. Write a_p(k)=|c_p(k)|^2, so |fhat(k)|^2=prod_{p|P}a_p(k), and a_p(k)=1 for p|k. All a_p<=1. For p>=11 the local allowed set is a cyclic interval of cardinality a=(p-1)/2 for H, (p-3)/2 for d. Thus a<=p/2, and after translation it is {0,...,a-1}.

The fourth moment of a normalized Fourier coefficient is p/a^4 times the number of quadruples in the interval satisfying u+v=w+x modulo p. The integer sum ranges from0 to2a-2<p, so modular equality here is integer equality. The number of representations of a sum is triangular, with counts1,2,...,a-1,a,a-1,...,1. Hence
    sum_{k mod p} |c_p(k)|^4
      = p/a^4*(a^2+2 sum_{j=1}^{a-1}j^2)
      = p*(2a^2+1)/(3a^3).                              (1)
The full-P CRT inverse permutes the frequency residues, and translating the interval only changes the phase, so the identity is independent of both. In particular the nonzero-frequency fourth-moment sum is 1/3+O(1/p), uniformly in both families. This replaces the nonzero second-moment sum 1+O(1/p).

## 2. Finite weighted subset inequality

Take an ambient collection L of n primes>=11 dividing P, b=min L, Kappa=max_{p in L} kappa_p, where kappa_p=1/[((p-3)/2)sin(pi/p)]<1. For p not dividing k, a_p(k)<=Kappa^2. Choose 1<=q<=n/2, M<=P/2 a positive integer with M<=b^q. For every q-subset U of L its product Q_U>=M.

Fix z>0, and define
    g_p(k)=z if p divides k, and a_p(k)^2 otherwise.
For each U the partial product G_U(k)=prod_{p in U}g_p(k) is Q_U-periodic. CRT and (1) imply
    sum_{1<=k<=M} G_U(k)
       <= prod_{p in U} m_p,
    m_p=z-1+p*(2a^2+1)/(3a^3).
Let B=mean_{|U|=q}prod_{p in U} m_p.

For a fixed 1<=k<=M, put t=#primes in L dividing k, so t<=q. Among uniform q-subsets U, condition on exactly j dividing primes selected, with j feasible and 2(q-j)<=n-t. The conditioning probability is
    H_t(j)=binom(t,j)binom(n-t,q-j)/binom(n,q).
Let A=prod_{p in L,p not dividing k}a_p(k). If A=0 then full energy is zero and the desired inequality is immediate. Otherwise AM-GM over all (q-j)-subsets of the n-t nondividing primes gives
    E[G_U(k) | J=j] >= z^j A^(2(q-j)/(n-t)).
Indeed each nondividing prime is present in fraction (q-j)/(n-t) of the subsets. Since the exponent e=2(q-j)/(n-t)<=1, and A<=Kappa^(2(n-t)), we have
    A^e = A*A^(-(1-e))
       >= A*Kappa^(-2(n-t-2(q-j)))
       >= |fhat(k)|^2*Kappa^(-2(n-t-2(q-j))).
The last inequality uses the omitted small-prime factors <=1. Thus for any choice of feasible j=j(t) satisfying 2(q-j)<=n-t,
    E[G_U(k)] >= |fhat(k)|^2 H_t(j) z^j
                                     Kappa^(-2(n-t-2(q-j))).
Define
    F=min_{0<=t<=q} H_t(j(t)) z^j(t)
                                 Kappa^(-2(n-t-2(q-j(t)))).
All factors are positive for feasible j. Summing over k and using the partial-period bound yields
    sum_{k=1..M}|fhat(k)|^2 <= B/F.                       (2)
Unlike the preceding second-moment method, no monotonicity of F(t) is assumed. One can maximize the lower bound separately over feasible j for each t. This is a deterministic subset average, not a trajectory probability model.

The forward moving average of length l, 1<=l<=P, has variance sigma_l^2=mean|f_l-1|^2. The interval kernel bound and full Parseval sum1/alpha_P as in c3d46e7 imply
    sigma_l^2 <= 2B/F + (P/(2l(M+1)))^2/alpha_P.         (3)
The finite theorem is valid at all stated parameters, with exact m_p and binomial coefficients; no asymptotic argument or independence is needed for (2)-(3).

## 3. Uniform entropy bound and the new power exponent

Write r=#odd primes<=R, c0=log(pi/2), and use the unconditional PNT as in 9007b46. Take L={primes R/log R<=p<=R}, n~r, b=min L, log b~log R, log Kappa=-c0+o(1). Fix
    delta=15/32, a0=5/8, z=3/5,
    M=ceil(P^delta exp(r)), q=ceil(log M/log b).
Then q/n=delta+o(1), M<=P/2, q<n/2 eventually. The local moments (1) give uniformly m_p=z+1/3+O(1/b)=14/15+O(1/b), and hence
    log B <= (delta log(14/15)+o(1))*r.                   (4)
This partial-period cost actually decays exponentially.

For every integer 0<=t<=q choose j=floor(a0*t). It is feasible for all sufficiently large R: j<=t,q and 2(q-j)<=n-t, since n-t-2(q-j)>=n-2q+(2a0-1)t-2, which is positive for large R because 1-2delta=1/16. Also q-j>=0. In the finite audit the choice is raised if necessary for very small n.

Put v=t/n and h(u)=-u log u-(1-u)log(1-u) with continuous endpoint values. Stirling's binomial entropy estimate has error O(log(n+1)) uniformly over integer parameters including endpoints (or use the elementary binomial entropy upper/lower inequalities). The entropy expression is continuous on the feasible triangle, so the rounding and q/n=delta+o(1) induce o(r) uniformly for all t. The logarithm of the term inside the minimum defining F, minus log B, is bounded below by
    r*(L_delta(v)+o(1)),
    L_delta(v)=2c0*(1-v-2(delta-a0*v))
                +a0*v*log z +v*h(a0)
                +(1-v)*h((delta-a0*v)/(1-v))
                -h(delta)-delta*log(z+1/3).             (5)
The error is uniform over 0<=v<=q/n, so it suffices to evaluate the limit on [0,delta]. The entropy perspective (1-v)h((delta-a0*v)/(1-v)) is concave in v, since h is concave and both arguments in its perspective are affine functions of v. All other terms in (5) are affine or constant. Therefore
    L_delta(v)>=min(L_delta(0),L_delta(delta))
for all 0<=v<=delta. Uniform continuity covers the o(1) extension of this interval when q/n>delta. This endpoint argument is essential; a numerical scan of divisor counts is unnecessary.

At the chosen rational parameters,
    L_delta(0) = (1/8)log(pi/2) -(15/32)log(14/15)
                 = .08878824667...,
and
    256 L_delta(delta)
       = 92 log(pi/2)+75 log(3/5)
          -75 log(5/8)-45 log(3/8)
          -45 log(45/136)-91 log(91/136)
          +120 log(15/32)+136 log(17/32)
          -120 log(14/15).
The latter divided by256 is .00112541170... . The audit below proves lower bounds .08878814108 and .00112510815 respectively, using pi>3.14159 and exact BigInt log intervals. In particular the minimum exceeds .001.

By (4)-(5), B/F<=exp(-(.001+o(1))*r) (the actual margin is larger). For l>=ceil(P^(1-delta)), l<=P, the high-frequency term of (3) is <=exp((log2-2+o(1))*r), since l M>=P exp(r) and log(1/alpha_P)=(log2)r+O(log R) for both families. Absorb the factor2 and the o(1) losses to obtain the new theorem:
    sigma_l^2 <= exp(-.0005*r)
    for ceil(P_R^(17/32))<=l<=P_R,                    (6)
for all sufficiently large R. It is a uniform complete-period mean-square theorem, not a maximum-gap or pointwise discrepancy theorem. The exponent17/32=.53125 improves14/25=.56; the target1/2 has not been reached. This particular proof does not establish an optimal exponent.

## 4. Consequences for MIN at the new power scale

Apply (6) to the finite MIN theorems already established in 850c00f, 78b1212, 4777ea7 and f7c6f40, exactly as in 9007b46. In crossed [X,lambda X], fixed lambda>1, G=(lambda-1)X+O(sqrt X), far gain>=G/2-O(sqrt X), near count O(sqrt X), C=floor sqrt(lambda X+1). Let N be canonical visits, B_R far B count with p>R, m_f far A1 count with p>R. Take R largest odd prime with P_R<=X^rho, any fixed 0<rho<16/17, and l=ceil(P_R^(17/32)). PNT and Bertrand give R~rho log X, P_R=X^(rho+o(1))=o(X), l log^A X=o(sqrt X) for every fixed A, because (17/32)rho<1/2.

The previous finite smoothed horizon union and far-only recovery joint inequality has global error 2sqrt(n'*(n'+P_R))*sigma_l, n'=G/2+l-1. This is o(X) by (6), and the other standalone terms O(l sqrt X+P_R+C) are o(X). Hence
    9G/28-o(X) <= 2l*m_f+(C+2l)*(N+1+B_R).
Under N,B_R=o(sqrt X) this yields
    m_f >= (9(lambda-1)/56-o(1))*X/l.                  (7)
At the balanced cutoff P_R<=sqrt X (rho=1/2), l<=X^(17/64)+1, so
    m_f=Omega(X^(47/64)) = Omega(X^(.734375)).
This improves the explicit .72 lower-bound exponent from 9007b46 at the same cutoff. The permissible primorial exponent is now any fixed rho<16/17=.941176..., compared to the preceding25/28=.892857... . At different rho the marked populations change.

As before S0 largest odd prime with P_S0<=R gives a dense deficit gap bound o(R) and rounded matching of at least five later far decreasing nonreset events (except reset/end slots) per far A1. Define B_union as all far B p>R plus far ordinary-decreasing nonreset B S0<p<=R crossing a dense S0 deficit barrier down. The previous 5m_f<=B_union+(N+2)L, L=O(log X), together with (7)'s preceding joint inequality and lL=o(sqrt X) gives
    N+B_union >= (9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X
without either sparsity assumption, at all these cutoffs.

For W_T=sum of A1 labels p>R,p>=T, the finite precursor inequality
    (4/5)W_T <= G_long+(C+4l)(N+B_R+1)+2C
holds for T>=max(48,20l). Disjoint long low-run intervals in the horizon coordinate give G_long<=4(G/2+P_R)*sigma_l^2. Thus
    W_T=O_lambda(X exp(-.0005*r)+sqrt X*(N+B_R+1)).
At T=24l under the sparse assumptions this is o(X) weight and o(m_f) occurrences. At balanced rho1/2 the threshold is O(X^(17/64))=O(X^.265625), compared to previous O(X^.28). Splitting the earlier O(sqrt X log^2 X) exceptional good-slab mark count at24l again yields bad weight o(X), not necessarily a relative o(W) error for sublinear W. All these applications are substitutions into previously proved finite inequalities, and do not average repeatedly traversed deficit intervals directly. The lower-band recovery supply is still not capped sufficiently for a finite-twins contradiction; neither sparsity condition follows from finite twins.

## 5. Diagnostics and preservation

[Audit ecd13d3](https://github.com/tara-sooo/A166944-Lean/blob/ecd13d35473916b0f65028fcee3427c8df18bfe1/research/min_direct_fourth_moment_energy_audit.mjs), blob 892b2ec9255fac073adabf087c43f778faead54a. Exact remote readback. Run node research/min_direct_fourth_moment_energy_audit.mjs. Actual ECMAScript execution in the tool runtime. Both families: 84 local fourth-moment identities (primes11..199),30 partial weighted fourth-moment sums,352 frequency inequalities,8 low-frequency summed-energy inequalities,8 variance bounds,19,939,920 full-period moving-average position checks. Complete periods R13/17/19, ambient primes>=11, all q<=floor(n/2), M=product of q smallest ambient primes, l=ceil(P^(17/32)). At R19,q2,M143,l3563, actual variances H .061758094336955546, d .014003046909169375; the finite formula upper bounds at such small R are loose (8364.9446 and3591.6489). Floating trigonometric checks use tolerance, exact integer period counts. Separate exact fixed-point BigInt log intervals at scale10^40, using 300 terms of log x=2 sum z^(2i+1)/(2i+1), z=(x-1)/(x+1), outward rounding and remainder 2|z|^601/[601(1-z^2)], certify endpoint margins >.088788141 and >.001125108 (strict comparisons in code >.088 and >.001). All passed. No new MIN trajectory scan this turn; the application uses existing finite theorems and their audits. No observed infinite ray, historical novelty claim or Lean kernel verification. Main and sibling branches unchanged.

Next: to reach <=1/2 one would need a further saving beyond this weighted fourth-moment subset method at its current parameters (e.g. sharper conditioning on nonzero coefficient sizes, other fractional moments, or genuinely different estimates). Alternatively use the stronger occurrence and weight constraints to seek a supply upper bound for low-label recovery; no stopping invariant yet.
