# Three-class residue-code energy and smoothing at P^(2/5)

Continuation of [0573fdd](https://github.com/tara-sooo/A166944-Lean/commit/0573fdde94b9cdf31086dc5f806ffaa8ebcf4612). The previous shortened-projection bound counted agreements only at zero local frequencies. Count agreements also at the two largest nonzero local frequencies, and apply separate moment sums to those frequencies and the remaining ones. A finite rational certificate of the resulting two-dimensional entropy inequalities gives smoothing at P^(2/5) for both barrier families. No stopping theorem or finite-twins contradiction.

## 1. Three local classes

Use P=P_R, the odd primorial, and either H or downward-deficit barrier family. In integer coordinate j=b_cut/2 let f be its normalized periodic indicator. The global squared Fourier magnitude is product_{p|P} a_p(k), where a_p=|c_p|^2 is the normalized local coefficient, evaluated at local frequency k v_p mod p with v_p=(P/p)^(-1) mod p. The local sets at p>=11 are cyclic intervals of length a=(p-1)/2 or (p-3)/2. Classify the local frequency as
    0: zero;
    1: +1 or -1 modulo p;
    2: every other residue.
This class definition uses the full-P inverse; for each p class1 still has exactly two distinct residues of k mod p. It is not a classification of k mod p as +/-1 without the inverse.

By the geometric-series formula for the local normalized coefficient, class1 squared magnitude tends to A=4/pi^2 as p grows. For class2 the maximum squared magnitude has limsup <= A/9. Indeed for local frequency of absolute least representative 2 the numerator sin(2*pi*a/p) tends to zero, and for representative 3 the magnitude tends to 2/(3*pi). For representatives from4 to(p-1)/2 use the bound 1/(a sin(4*pi/p)), tending to 1/(2*pi), strictly smaller than 2/(3*pi). All estimates hold for both local interval lengths.

For s=1,2, write m_{s,i}(p) for the sum of a_p(k)^s over class i, k mod p. Class1 limits are 2A^s. By local Parseval and the exact fourth-moment identity of 3c3eb3e, class2 limits are 1-2A for s1 and 1/3-2A^2 for s2. Class0 sum and coefficient are 1. Therefore for every sufficiently large p, simultaneously for both families,
    a_p(k)<=A1=.406 on class1,
    a_p(k)<=A2=.046 on class2,
    m_{1,1}(p)<=.812, m_{1,2}(p)<=.191,
    m_{2,1}(p)<=.330, m_{2,2}(p)<=.006.                (1)
All six upper constants strictly exceed the limiting values (or limsup). In particular the class2 fourth-moment sum is small because the two class1 terms have been removed from the nonzero fourth-moment sum. The local inequalities for large p follow analytically, not from the small-p audit. For use below, conservative logarithmic bounds are
    -log A1>.90, -log A2>3.07,
    -log .812>.20, -log .191>1.65,
    -log .330>1.10, -log .006>5.10.
These comparisons and the strict limiting-constant comparisons are checked in the exact certificate.

## 2. Agreement bound with three classes

Take an ambient set of n primes >=11 dividing P, b=min ambient prime, integer 1<=M<=P/2, q=floor(log M/log b)<n. Any two distinct positive frequencies k,k'<=M agree on at most q ambient residues, since b^(q+1)>M and the product of agreeing primes divides their difference. Each frequency has at most q zero residues.

Fix a class-count vector t=(t0,t1,t2), sum n, and a projection onto h ambient primes with prescribed residues, containing j_i positions of class i, sum h. Put u_i=t_i-j_i, the class counts outside the projection. For h>q the fibre (frequencies with the prescribed projection and class-count vector) is injective. For h<=q, let its size be L0>=1. Each frequency has u0 zeros and u1 class1 residues outside the projection. Counting just agreements within the zero class, and within either of the two individual class1 symbols, gives by Cauchy-Schwarz
    2*number of counted agreeing pairs across outside positions
       >= L0^2*(u0^2+u1^2/2)/(n-h)-L0*(u0+u1).
To see the class1 term, sum the occupancies of its two residues at each of the n-h positions, a total of L0*u1. There are 2(n-h) such slots, so the sum of squared occupancies is at least (L0*u1)^2/[2(n-h)]. The zero class has n-h slots and a separate Cauchy bound. These count disjoint agreements. On the other hand every pair agrees in at most q-h outside positions, including all three classes. Thus
    L0*((u0^2+u1^2/2)/(n-h)-(q-h))
         <= u0+u1-(q-h).                               (2)
If the coefficient is positive, the fibre size is bounded by the floor of the ratio of the right side to that coefficient (max with1 is a convenient bound for empty fibres as well). If the coefficient is >=epsilon*n, the bound is O(1). Call a valid bound Lmax. This is the two-class agreement improvement over the zero-only shortening of 0573fdd.

## 3. Conditional partial-moment energy

For each fixed t choose integers h,j_i feasible (0<=j_i<=t_i,sum j_i=h), and s in {1,2} with s*j_i<=t_i for i=1,2. Assume the fibre bound of section2 applies. Write A_i for the maximum squared local coefficient in class i over ambient primes (i1,2), m_{s,i} for the maximum of the corresponding local moment sum. In the small finite theorem these are actual finite maxima rather than the large-prime bounds (1). Put
    H_t(j)=prod_i binom(t_i,j_i)/binom(n,h),
    B=Lmax*multinomial(h;j0,j1,j2)*m_{s,1}^j1*m_{s,2}^j2.
For each h-subset U, sum partial weight prod_{p in U}a_p(k)^s over frequencies of class-count vector t and selected counts j. This sum is <=B by the fibre bound: choose class positions then sum over all local residues of those classes, using their local moments. Zero factors equal1.

Now fix a frequency in the class, average over uniform h-subsets and condition on selected class counts j (probability H_t(j)>0). Let D_i be the product of a_p(k) over the ambient positions of class i. If global energy is zero the desired lower bound is trivial. Otherwise all factors are positive. Within each class the chosen subset is uniform, so AM-GM over all such subsets gives conditional mean weight >=prod_{i=1,2}D_i^(s*j_i/t_i). An empty class contributes1. Since exponents <=1, D_i<=A_i^t_i and omitted primes have squared magnitude<=1, the unconditional mean weighted indicator for this selected-count condition is >=
    |fhat(k)|^2 * H_t(j) * prod_{i=1,2} A_i^(-(t_i-s*j_i)).
Sum over the frequency class and compare to B. The finite energy bound is
    E_t <= B / [H_t(j)*A1^(-(t1-s*j1))*A2^(-(t2-s*j2))].  (3)
It is valid for independently chosen parameters in each t-class. No claim of a random distribution of k or its residues is used: the average is over subsets only. With E_low the sum of valid bounds over all nonempty classes, the previous symmetric low-frequency/high-frequency split and full Parseval give
    sigma_l^2 <= 2 E_low+(P/(2l(M+1)))^2/alpha_P         (4)
for forward moving averages of lengths 1<=l<=P.

## 4. Uniform asymptotic certificate

Use unconditional PNT, r=#odd primes<=R, L={primes R/log R<=p<=R}, n~r, log b~log R, log P~R. Choose
    delta=3/5, M=ceil(P^delta exp(r)), q=floor(log M/log b).
Then M<=P/2, q/n=delta+o(1). Put v=t0/n,w=t1/n,u=t2/n=1-v-w. We have v<=.6+o(1). Choose a constant H in (0,1), h=floor(H*n), j_i=H*t_i+O(1) summing h. For example take floors of h*t_i/n and distribute the residual to largest fractional parts, without exceeding t_i. Then j_i<=t_i. If s=2 and 2H<1, for each class with t_i bounded it may be necessary to take j_i<=floor(t_i/2) rather than round up. One can impose this for both nonzero classes while still maintaining j_i=H*t_i+O(1): if all three counts large, slack from 2H<1 suffices; if some are small, round those down and put the O(1) residual in a class with count >=n/3 and available slack (the zero class is subject only to j0<=t0). More explicitly start with floor(h*t_i/n), whose sum is at most h with residual <=2, and add the residual to a largest class; its available capacity is linear in n since H<1 and sH<1. This meets s*j_i<=t_i for i1,2 eventually uniformly. For s=1 the same construction suffices.

The coefficient in (2), divided by n, is
    (1-H)*(v^2+w^2/2)-(delta-H)+o(1),                   (5)
uniformly for fixed H and all counts. When h>q use injection instead. The hypergeometric log probability log H_t(j)=o(n) uniformly, by the binomial entropy bounds with O(log(n+1)) errors, because j_i/n=H*t_i/n+O(1/n). Let E(v,w,u)=-sum_{x=v,w,u}x log x with 0 log0=0. The log multinomial divided by n is H E(v,w,u)+o(1) uniformly. Thus, using (1), the saving exponent of (3) divided by n has lower bound
    (1-sH)*(.90*w+3.07*u)
       -H*(E(v,w,u)-b_{s,1}*w-b_{s,2}*u)+o(1),        (6)
where (b_{1,1},b_{1,2})=(.20,1.65) and (b_{2,1},b_{2,2})=(1.10,5.10). These constants deliberately weaken the exact limiting constants.

Here is a finite, reproducible certificate that both (5) and (6) have uniformly positive main terms, using a mesh of size1/100. For i=0..61, j=0..99-i cover the feasible points with
    v in [i/100,(i+1)/100], w in [j/100,(j+1)/100],
    u in [max(0,98-i-j)/100,(100-i-j)/100].
This covers every point v<=.61, v,w,u>=0, sum1; boundary w=1-v is covered by a closed last cell (and endpoints may have several cell choices). For large R the feasible v range is inside it. Put S=(2i^2+j^2)/20000 and choose
    H=max(1,ceil(1000*(.6-S)/(1-S))+1)/1000.
For every cell, H<=.601 and (1-H)S-(.6-H)>0. The exact rational checks give minimum gap .0005805. In each cell choose s=1 or2 satisfying sH<1 which maximizes the following certified lower bound: replace w,u in every positive linear term of (6) by their lower endpoints, and E by the sum of three upper bounds for -x log x on the respective component intervals. An upper bound is its value at the upper endpoint if <=.36, its value at the lower endpoint if >=.37, otherwise .368 (since 1/e lies in (.36,.37) and is <.368). Use outward rational log intervals for the endpoint values. For all 4,309 cells the resulting rational bound exceeds .01; the smallest certified bound is .01838451234... (cell i51,j47,H=.366, with s1 in the audit; conservative bounds for s1/s2 can tie). The choices are s1 in2436 cells and s2 in1873. All H choices form a finite set, so the uniform o(1) terms in (5)-(6) apply without dependence on an unbounded parameter choice. This is a finite proof certificate of the entropy inequalities, not numerical extrapolation from the asymptotic or finite MIN data.

Consequently all class energy bounds are <=exp(-(.01+o(1))*n), with Lmax=O(1) by the uniform gap and (2) (or injection). There are at most (n+1)^2 classes, so the polynomial number of classes is absorbed in the exponential. For l>=ceil(P^(2/5)), l M>=P exp(r). The high-frequency term in (4) is <=exp((log2-2+o(1))*r) because log(1/alpha_P)=(log2)*r+O(log R). Hence for both families, sufficiently large R and all indicated l,
    sigma_l^2 <= exp(-.005*r),
    ceil(P_R^(2/5)) <= l <= P_R.                        (7)
The margin .005 is chosen strictly below .01 and absorbs constants and uniform o(1) errors. This is a mean-square theorem, not a uniform maximum-gap bound of that power scale.

## 5. Applications to MIN

Use the established crossed horizon window [X,lambda X] on a hypothetical infinite canonical ray, fixed lambda>1, gain G=(lambda-1)X+O(sqrt X), label bound C=floor sqrt(lambda X+1), canonical visits N, far B count B_R with p>R, far A1 count m_f with p>R. Set l=ceil(P_R^(2/5)). For any fixed 0<rho<1 choose R largest odd prime with P_R<=X^rho; alternatively use the near-X cutoff P_R<=X/log^2 X of 0573fdd. Then R~rho log X in the fixed case (R~log X in the near-X case), P_R=o(X), and l log^A X=o(sqrt X) for every fixed A. Apply the previous disjoint-horizon smoothed union and far recovery joint theorem: its global error is 2sqrt(n'*(n'+P_R))*sigma_l=o(X), n'=G/2+l-1. Other standalone errors O(l sqrt X+P_R+C) are o(X), giving
    9G/28-o(X) <=2l*m_f+(C+2l)*(N+1+B_R).               (8)
Under N,B_R=o(sqrt X), m_f>=(9(lambda-1)/56-o(1))*X/l. At the balanced cutoff P_R<=sqrt X this is Omega(X^(4/5)), improving Omega(X^(19/25)). At the near-X cutoff it gives Omega(X^(3/5)*(log X)^(4/5)), a different counted population. No assumption of the sparsity conditions following from finite twins is made.

Apply the previous short-run precursor inequality (4/5)W_T<=G_long+(C+4l)(N+B_R+1)+2C for W_T the sum of A1 labels p>R,p>=T, T>=max(48,20l). Long low runs have total gain <=4(G/2+P_R)*sigma_l^2 by disjoint horizon zero-start counting. Thus
    W_T=O_lambda(X exp(-.005*r)+sqrt X*(N+B_R+1)).
At T=24l under the sparse conditions, weight o(X), count o(X/l)=o(m_f). At balanced cutoff this tail threshold is O(X^(1/5)), improving O(X^(6/25)). Earlier good-slab exception weight o(X) follows by splitting its O(sqrt X log^2 X) exceptional occurrences at24l. This is a macroscopic weight statement, not relative error when W=o(X).

As previously, take S0 largest odd prime with P_S0<=R, and B_union the count of all far B p>R plus far ordinary-decreasing nonreset B S0<p<=R crossing a dense S0 deficit barrier downward. The prior rounded matching 5m_f<=B_union+(N+2)L, L=O(log X), and (8) imply the same joint count N+B_union>=(9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X without either sparsity assumption. The cutoff range P_R=o(X) remains as in 0573fdd, but the smoothing length is smaller. The repeated deficit intervals are not averaged as disjoint horizon intervals. No finite-twins contradiction or sufficient upper supply bound on low-label recoveries is obtained.

## 6. Diagnostics and persistence

[Audit 3bea1a4](https://github.com/tara-sooo/A166944-Lean/blob/3bea1a4290b634606a07c7fe284563505b2c49d5/research/min_direct_three_class_energy_audit.mjs), blob 80b8d08d4cd6929232119c0ff56fcab3d105e7e6. Exact remote readback. Actual ECMAScript function executed in tool runtime; run node research/min_direct_three_class_energy_audit.mjs. The rigorous certificate uses pi in (3.14159,3.14160), integer comparisons for the six limiting constants, 10^30 fixed-point outward log intervals with 1000 atanh-series terms and remainder 2|z|^2001/[2001(1-z^2)], exact rational shortening gaps, and exact BigInt comparison of the margin with .01. The choice of H by floating ceil is also checked directly for positive exact rational gap in each cell, so the proof does not depend on floating correctness of the ceil. 4309 cells, min gap .0005805, min margin .01838451234... . Separately finite diagnostics for both families at R13/17/19/23 with frequency ranges100/400/1200/5000: 76 classes, 113688 fibre checks, 1768 nontrivial shortened fibres, 49638 pointwise weighted checks,388 energy inequalities. Six full-period variance checks R13/17/19, 10240230 moving-average positions. R19 P4849845,l473: measured variance H .60783545,d .22558518; finite upper formulas loose at these small parameters. Finite trigonometry uses floating tolerance; exact rational certificate is separate. All assertions passed. No new MIN scan this turn; application is substitution into previously proved/audited finite inequalities. No observed infinite ray, Lean kernel verification or historical novelty claim. Main and sibling branches untouched.

Next: further split the nonzero frequencies by magnitude or use more complete agreement counting, and apply the improved polynomial-scale restrictions to actual low-label recovery supply. No stopping invariant has been established.
