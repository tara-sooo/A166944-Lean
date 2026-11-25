# Residue-code shortening and a smoothing exponent below one half

Continuation of [3c3eb3e](https://github.com/tara-sooo/A166944-Lean/commit/3c3eb3edc45f35969133736c0453bb43f01080a3). The previous partial-modulus proofs required each selected product to exceed the frequency range. For frequencies having a fixed number of prime divisors, even a smaller partial modulus has bounded multiplicity by a Plotkin-type agreement count. Combining this with second/fourth moments and a conditional subset average gives smoothing at P_R^(12/25), below 1/2. This is a new deterministic upper bound on low-frequency energy, not a stopping theorem.

## 1. Shortened residue-code multiplicity

Use either H or downward-d CRT barrier family, odd primorial P=P_R, and normalized Fourier energy |fhat(k)|^2=prod_{p|P} a_p(k), where a_p(k)=|c_p(k)|^2, c_p uses the full-P CRT inverse. All a_p in [0,1], a_p(k)=1 if p|k. For p>=11 and p not dividing k, a_p(k)<=kappa_p^2, kappa_p=1/[((p-3)/2) sin(pi/p)]<1.

Let ambient L be n distinct primes>=11 dividing P, b=min L, Kappa=max kappa_p over L. Fix integer 1<=M<=P/2 and q=floor(log M/log b), so b^(q+1)>M. Distinct integers k,k' in [1,M] can agree in residues modulo at most q ambient primes: the product of every agreeing prime divides the nonzero difference of magnitude<M. Also each k is divisible by at most q ambient primes. Assume q<n.

Fix divisor count t<=q and choose h ambient primes U. Prescribe their residues, with exactly j of them zero. Consider the fibre of integers k in [1,M] with this prescribed projection and exactly t ambient prime divisors. If h>q the fibre contains at most one integer. Otherwise h<=q<n. If the fibre contains L0>=1 integers, each has t-j zero residues among the remaining n-h primes. Write Z_p for the count of zero residues there, so sum Z_p=L0(t-j). Every pair in the fibre agrees at most q-h times outside U. Count just agreements between two zero residues, using Cauchy:
    sum_{p outside U} binom(Z_p,2)
      >= [L0^2*(t-j)^2/(n-h)-L0*(t-j)]/2
      <= binom(L0,2)*(q-h)
where the lower expression is <= the upper expression (the actual sum is between them). Thus
    L0*((t-j)^2/(n-h)-(q-h)) <= t-j-(q-h).             (1)
If the coefficient of L0 is positive, every nonempty fibre has size at most
    floor(((t-j)-(q-h))/((t-j)^2/(n-h)-(q-h))).
We may take its maximum with1 as a uniform bound Lmax; empty fibres need no special treatment. In particular a gap >=epsilon*n in the coefficient implies Lmax<=1/epsilon, since numerator<=n. This is the shortened-projection bound. It does not require Q_U=prod_{p in U}p>=M. It uses only the exact agreement constraint and the fixed divisor count, not independence of the prime divisors.

## 2. Weighted energy with bounded fibres

For a fixed class t choose h,j with 1<=h<=n, max(0,h+t-n)<=j<=min(h,t), and an integer s in {1,2} such that s(h-j)<=n-t. Assume either h>q or the gap in (1) is positive, and use Lmax from section1 (1 in the injective case). Define
    m_s=max_{p in L} sum_{k mod p,k !=0} a_p(k)^s,
    H_t(j)=binom(t,j)binom(n-t,h-j)/binom(n,h).
For each U of size h, sum only over frequencies in class t with exactly j zero residues in U, weighting by prod_{p in U,p not dividing k} a_p(k)^s. The number of frequencies at each specified projection is <=Lmax. Hence the total weighted sum is at most
    B=Lmax*binom(h,j)*m_s^(h-j).                      (2)
Indeed each choice of the j zero positions contributes at most the product of the nonzero local moment sums, bounded by m_s^(h-j). The omitted zero factors are exactly1. This is the CRT partial-moment sum with a multiplicity correction rather than a period-length constraint.

For a fixed k in the class, let A=prod_{p in L,p not dividing k} a_p(k). If A=0, full energy is zero. Otherwise conditioning a uniform h-subset U on J=j zero positions and using AM-GM over the nondividing subsets gives mean weight conditional on J=j at least A^(s(h-j)/(n-t)). Since this exponent is <=1 and A<=Kappa^(2(n-t)),
    mean_U [1_{J=j} prod_{p in U,p not dividing k}a_p(k)^s]
       >= |fhat(k)|^2 H_t(j) Kappa^(-2(n-t-s(h-j))).
Sum this over class t and use (2). We obtain the finite energy bound
    sum_{1<=k<=M, #divisors in L=t}|fhat(k)|^2
        <= Lmax binom(h,j) m_s^(h-j)
                 /[H_t(j) Kappa^(-2(n-t-s(h-j)))].     (3)
One may optimize independently for each t. There is no assumption on the locations of the nonzero Fourier coefficients. For s=1, local Parseval gives nonzero sum p/a-1; for s=2, the local additive-energy identity of 3c3eb3e gives p(2a^2+1)/(3a^3)-1. For the cyclic interval lengths a=p/2+O(1) of both barrier families these are 1+O(1/p) and 1/3+O(1/p).

Let E_low be the sum of the right sides of (3) over t=0..q (or any sharper valid bounds for some classes). For normalized moving averages of length 1<=l<=P, the symmetric low-frequency and high-frequency split of c3d46e7 gives
    sigma_l^2 <= 2 E_low+(P/(2l(M+1)))^2/alpha_P.      (4)
Here alpha_P is the density of the chosen barrier family. Full Parseval gives total Fourier energy1/alpha_P. Equation (4) is a mean-square estimate, not a pointwise discrepancy bound.

## 3. Explicit fixed power 12/25

Write r=#odd primes<=R, c0=log(pi/2), and use the unconditional prime number theorem. Choose L={primes R/log R<=p<=R}. Then n~r, log b~log R, log P~R, log Kappa=-c0+o(1). Set
    delta=13/25=.52,
    M=ceil(P^delta exp(r)),
    q=floor(log M/log b).
Then q/n=delta+o(1), M<=P/2, q<n eventually. For a frequency divisor class t put v=t/n. Choose h=floor(H*n) and j=floor(h*t/n), with H and moment s selected by the following four ranges (boundary choices arbitrary):
    v in [0,.25]    : H=.521,s=1
    v in [.25,.35]  : H=.490,s=2
    v in [.35,.44]  : H=.460,s=2
    v in [.44,.52]  : H=.410,s=2.
Extend the last range to q/n when q/n>.52; the excess is o(1). These choices satisfy all integer feasibility inequalities for sufficiently large n: j<=min(h,t), h-j<=n-t (rounding a typical intersection; the latter has a uniform positive slack because H<1,v<=.52+o(1)), and s(h-j)<=n-t since sH<1. In the first range h>q eventually. In the remaining ranges the coefficient in (1) divided by n is
    (1-H)*v^2-(delta-H)+o(1).
At the respective lower endpoints .25,.35,.44 its main-term values are .001875,.00615,.004224. The main term is increasing in v, so the gap is uniformly positive. Hence Lmax=O(1) in all ranges. This is the improvement over fixed-period arguments: e.g. in the final range a .41 fraction of primes controls the multiplicity even though the frequency length corresponds to .52 of the primes.

The conditional probability H_t(j) has logarithm o(n), uniformly in t, by the binomial entropy estimate with O(log(n+1)) error and uniform continuity at endpoints. Indeed j/n=Hv+O(1/n), so its leading entropy is v h_bin(H)+(1-v)h_bin(H)-h_bin(H)=0, where h_bin is binary entropy (including continuous endpoint values). Also log binom(h,j)=n*(H h_bin(v)+o(1)) uniformly. Since the ambient primes grow, m_1=1+o(1), m_2=1/3+o(1).

Consequently the class upper bound (3) is <=exp(-n*(L_s,H(v)+o(1))), where the notation L_s,H(v) is a function, unrelated to the fibre L0 or ambient set L:
    L_s,H(v)=(1-v)*(2c0*(1-sH)-H log m_s^*)-H h_bin(v),
    m_1^*=1, m_2^*=1/3.                               (5)
All errors are uniform over the indicated divisor classes. Write A0=2c0(1-sH)-H log m_s^*>0. The derivative of (5) is -A0-H log((1-v)/v), increasing in v. It is strictly negative at each respective right endpoint (see exact numerical certificates below), hence the minimum in each range is at that endpoint. The following are certified strict lower bounds, using pi>3.14159 and rational logarithmic interval arithmetic:
    H=.521,s=1,right=.25 : margin > .03148495
    H=.490,s=2,right=.35 : margin > .04440028
    H=.460,s=2,right=.44 : margin > .00793655
    H=.410,s=2,right=.52 : margin > .01037798.
The corresponding lower bounds for the negative derivatives exceed 1.00499,.85971,.68854,.58018. The small o(1) extension of the last range is covered by continuity. Thus all class exponents are at least .007+o(1). Summing at most n+1 classes preserves the exponential saving. For l>=ceil(P^(1-delta))=ceil(P^(12/25)), the high-frequency term of (4) is <=exp((log 2-2+o(1))*r), since l M>=P exp(r) and log(1/alpha_P)=(log2)*r+O(log R). Absorbing constants and using n~r proves the uniform theorem
    sigma_l^2 <= exp(-.003*r),
    ceil(P_R^(12/25)) <= l <= P_R,                    (6)
for all sufficiently large R and for BOTH barrier families. This proves an exponent .48, strictly below .5, without an unproved distribution conjecture. The proof is not claimed optimal.

## 4. Consequences for MIN

Apply the previously proved disjoint-horizon smoothing, far-only recovery, and precursor-exclusion finite inequalities (78b1212,850c00f,4777ea7,f7c6f40). On a crossed [X,lambda X] window of an infinite canonical ray, fixed lambda>1, G=(lambda-1)X+O(sqrt X), G_far>=G/2-O(sqrt X), near count O(sqrt X), C=floor sqrt(lambda X+1). Let N count canonical visits, B_R far B with p>R, m_f far A1 with p>R. For any fixed 0<rho<1 choose R largest odd prime with P_R<=X^rho; then R~rho log X, P_R=o(X), l=ceil(P_R^(12/25)) obeys l log^a X=o(sqrt X) for every fixed a. The finite joint inequality's smoothing error 2sqrt(n'*(n'+P_R))*sigma_l=o(X), n'=G/2+l-1, by (6). Its standalone errors O(l sqrt X+P_R+C)=o(X). Therefore
    9G/28-o(X) <=2l*m_f+(C+2l)*(N+1+B_R).              (7)
Under the same sparsity assumptions N,B_R=o(sqrt X),
    m_f >= (9(lambda-1)/56-o(1))*X/l.                 (8)
At the balanced cutoff P_R<=sqrt X this is Omega(X^(19/25))=Omega(X^.76), improving47/64=.734375. The weighted tail from the finite precursor inequality (4/5)W_T<=G_long+(C+4l)(N+B_R+1)+2C and G_long<=4(G/2+P_R)*sigma_l^2 becomes
    W_T=O_lambda(X exp(-.003*r)+sqrt X*(N+B_R+1)),
    T>=max(48,20l),                                  (9)
where W_T sums A1 labels p>R,p>=T. At T=24l in the sparse branch the weight is o(X), and the count is o(X/l)=o(m_f). The balanced tail threshold is O(X^(6/25))=O(X^.24), improved from O(X^.265625). Earlier good-slab exception weight is again o(X), by splitting O(sqrt X log^2 X) bad occurrences at24l, using (9). This is macroscopic weight, not a relative error for sublinear total W.

The new cutoff range covers EVERY fixed rho<1, rather than rho<16/17. It even permits R largest odd prime with P_R<=X/log^2 X: P_R=o(X), R~log X and l<=X^.48+1 so all the same error estimates hold. This is possible because the new smoothing exponent is strictly below one half. At this near-X primorial cutoff the lower bound in (8) is at least Omega(X^.52*(log X)^.96) under sparsity, but it counts a different population from the balanced cutoff.

Without either sparsity assumption, choose S0 largest odd prime with P_S0<=R. Previous uniform deficit gap bound o(R) and rounded far-only level matching give 5m_f<=B_union+(N+2)L0, L0=O(log X), where B_union is all far B p>R plus far ordinary-decreasing nonreset B S0<p<=R crossing a dense S0 deficit cut downward. Substitute in (7), with l L0=o(sqrt X), to retain the unconditional-on-sparsity joint count
    N+B_union >= (9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X
throughout this enlarged cutoff range. This is a necessary lower bound on a changed population, not an upper supply bound. None of these inequalities shows either sparsity condition follows from finite twins. The Fourier theorem for deficit barriers is valid, but its trajectory applications here still use disjoint horizon intervals; repeated deficit visits are not treated as disjoint.

## 5. Diagnostics and preservation

[Audit 4ab6176](https://github.com/tara-sooo/A166944-Lean/blob/4ab61764b5bde2d4ee264dbdce0e4de86e1474f8/research/min_direct_residue_code_energy_audit.mjs), blob b1952d54c2d0f59dbc64d1d52f11d6dc14a1b9b9. Exact remote readback. Run node research/min_direct_residue_code_energy_audit.mjs. Actual ECMAScript executed in tool runtime. Both families, R13/17/19/23/29/31, frequency limits40/160/400/5000/20000/50000; enumerate eligible h,j choices, use s2 when feasible else s1. 3,891,502 fibre checks, 216 nontrivial fibres (all in shortened cases, max size2),78 shortened class/parameter tests,2,284 partial weight checks,548,560 pointwise weighted-AMGM checks,200 summed energy inequalities. Six full-period variance bounds at R13/17/19,10,240,230 moving-average positions. R19,P4849845,l1619,M400 measured variance H .1159734332733,d .0433992708491. Finite upper formula loose at these small scales; asymptotic proof relies on PNT, agreement bound, entropy and analytic endpoint margins, not numerical extrapolation. Exact integer fibre and period counts, floating trigonometric/energy checks with tolerance. Exact BigInt outward log bounds scale10^40,300 atanh terms and rigorous remainder, verify four positive margins >.007 and negative derivatives, plus rational positive shortening gaps. All assertions passed. No fresh MIN trajectory scan; application is substitution into previous audited finite inequalities. Main/sibling branches unchanged; no observed infinite ray, Lean kernel verification or historical novelty claim.

Next: the residue-code argument allows other shortening rules (e.g. agreements in large nonzero coefficient classes or further conditional higher moments) and could improve the power further. More importantly, at the new cutoff one can explore deterministic upper supply bounds for the abundant far A1/low-band recovery population. No contradiction with finite twins.
