# Modular hyperbola three-condition sieve for first high successors, uniformly in the label scale

Continuation of [240e3de](https://github.com/tara-sooo/A166944-Lean/blob/240e3dea344526cac575e612ba4d538f42bd2a57/research/2026-11-26-min-direct-fast-pair-odd-shift-and-quadratic-escape.md). Instead of capping or localizing the deficit multiplier, count the target prime and cofactor on a modular hyperbola. The source gives two roughness constraints and the target prime gives a third. An elementary p^(3/4) exponential-sum bound is sufficient for a dimension-three upper sieve, including near-square-root scales and long rectangles when T is much smaller. No outside exponential-sum theorem is assumed. All analytic statements below are paper deductions, not Lean-verified. No novelty or final open-problem claim.

## 1. Exact product relation and three local exclusions

On one actual canonical MIN block, pre-horizons in [X,Y], Y=lambda X, fixed lambda>1, let C=floor sqrt(Y+1), T->infinity, T<=C. Fix K>=1. Consider actual first high pairs p,r in [T,KT] (also <=C), with upward first event, and the next actual event of label >=T. All intervening labels are <T. Let E be their total gain, e,f the two signs, H_s=pq+e, H_t=rs+f. For integer 0<=E<=B<T-3,
    H_t-H_s=p-1+E,
    rs=p(q+1)+a, a=E+e-1-f.                           (1)
The odd a is nonzero and |a|<=B+3<T<=p. Thus rs=a mod p is a nonzero modular hyperbola, and p!=r. Here s is the second cofactor, not a firing tick. Neither s nor q is assumed prime. Upward means 2w_s>p-1, so both source neighbors avoid odd primes l<(p-1)/4 by the eligible competing-clock rule. Consequently for every prime 3<l<T with l<(p-1)/4,
    r!=0 mod l,
    rs!=p+a mod l,
    rs!=p+a-2e mod l.                                 (2)
The first follows from target primality and l<T<=r. The last two follow from source roughness, using q=(rs-a)/p-1. This use of target primality does NOT require a long target wait.

Fix p,e,f,E. For a prime l>3, the two product residues in (2) differ by 2e, nonzero mod l, including when one product residue equals zero. For r=0, all l choices of s are forbidden. For each nonzero r, exactly two s residues are forbidden, including the zero choice if one product residue is zero. Thus the number of forbidden pairs in F_l^2 is EXACTLY
    rho(l)=l+2(l-1)=3l-2,
    g(l)=rho(l)/l^2=3/l-2/l^2.                        (3)
There is no exceptional discriminant factor even when l divides p+a or p+a-2e. This is because the entire r=0 fiber is already forbidden. The equality, not merely a generic-prime bound, is important: fixed E (even E=0) needs no averaging. The modulus p is not included in the sieve.

## 2. Elementary exponential-sum estimate

For an odd prime p write e_p(x)=exp(2 pi i x/p) and
    K_p(A,B)=sum_(x in F_p^*) e_p(Ax+B/x).
For (A,B)!=(0,0) we show |K_p(A,B)|=O(p^(3/4)), with an absolute constant. If B=0, A!=0 the sum is -1. If B!=0, expand the square and put h=x-y. The diagonal h=0 contributes p-1. For h!=0 write x=h z,y=h(z-1), where z!=0,1. Then
    |K_p(A,B)|^2=p-1+sum_(h!=0)e_p(Ah) S(h),
    S(h)=sum_(z!=0,1)e_p(-B/[h z(z-1)]).
Sum the second moment over h!=0 using orthogonality after h is replaced by its inverse:
    sum_(h!=0)|S(h)|^2=p M-(p-2)^2,
where M counts z,t!=0,1 with z(z-1)=t(t-1). Each z has at most two such t (the factorization is (z-t)(z+t-1)=0). Hence M<=2(p-2), the second moment is <=2p^2, and Cauchy-Schwarz gives
    |K_p(A,B)|^2 <= p-1+sqrt(2p^2(p-1)).
This proves the asserted elementary bound; no Weil estimate is needed. Also K_p(0,0)=p-1.

## 3. Uniform congruence count on a modular hyperbola in a long rectangle

Enlarge the target domain to integer intervals I=[ceil T,floor(KT)] and J=[1,ceil((Y+1)/T)], write L1=|I|=O_K(p), L2=|J|=O_lambda(X/T), N=ceil((Y+1)/T)+1. Every actual candidate lies there. In particular N>=T and N>>_K p. We do NOT require L2=O(p); for T subpolynomial in X this rectangle can be very long. If I is empty the result is trivial.

For squarefree d coprime to p, each residue pair (b,c) mod d restricts r,s to arithmetic progressions inside I,J. Write R_b(x),S_c(x) for their multiplicities in F_p, and use the unnormalized Fourier transforms hat R(k)=sum_x R(x)e_p(-kx), similarly S. The geometric sum for a progression of step d gives at nonzero k
    |hat R(k)|,|hat S(k)| <= 1/|sin(pi k d/p)|.
Since multiplication by d permutes nonzero residues, the sums of these bounds divided by p are O(log(2p)). This is independent of the progression length; full periods do not contribute at nonzero frequencies. The zero coefficient is the progression cardinality. Hence normalized total Fourier l1 norms are O_K(log(2p)) for R and O(log(2p)+N/p) for S, since their lengths are at most L1 and L2 respectively. No restriction on rectangle translation is needed.

Fourier inversion on (x,a/x), x!=0, yields
    # {(r,s) in I x J : rs=a mod p, r=b mod d, s=c mod d}
      = (p-1)/p^2 * (#I_b)(#J_c)
        + O_K(p^(3/4) log(2p) (log(2p)+N/p)).
The nonzero frequency pairs use K_p(A,aB), and a!=0 mod p, so section 2 applies. Since N>>_K p, the error is O_K(N p^(-1/4) log^2(2p)). Replacing the progression cardinalities by L1/d,L2/d costs at most O_K(1+N/p), absorbed by the same error. Thus uniformly in b,c and d coprime to p the count is
    N0/d^2 + O_K(N p^(-1/4) log^2(2p)),
    N0=(p-1)L1 L2/p^2=O_K(N).                        (4)
Even if d is larger than a side length, the O(1) rounding in each progression is covered. This derivation includes both zero/nonzero mixed frequency terms; no assumption of uniformly small zero coefficients in the long side is used.

## 4. Selberg sieve on the integer pairs

Choose z=floor(T^(1/64)) and use primes 3<l<=z, which are below T and (p-1)/4 eventually. For squarefree d of such primes, let A_d(r,s) indicate that a forbidden condition in (2) holds at each l|d, with A_1=1. By CRT on both coordinates there are rho(d)=prod_(l|d)(3l-2) forbidden residue pairs modulo d. Multiplying (4) by this number gives on the integer hyperbola domain
    sum A_d = N0 g(d) + O_K(rho(d) N p^(-1/4) log^2(2p)),
    g(d)=rho(d)/d^2.
Also A_d A_e=A_lcm(d,e) and g multiplicative. Use the exact Selberg quadratic diagonalization from [global sieve](https://github.com/tara-sooo/A166944-Lean/blob/240e3dea344526cac575e612ba4d538f42bd2a57/research/2026-11-26-min-direct-global-sieve.md). On the divisor-closed squarefree d<=z set, define h(d)=prod_(l|d)(1-g(l))/g(l) and G(z)=sum_(d<=z)1/h(d). Its explicit weights lambda_1=1, |lambda_d|<=prod_(l|d)(1-g(l))^-1<=d have main quadratic form 1/G(z). The error after expanding the square is bounded by
    O_K(N p^(-1/4) log^2(2p) sum_(d,e<=z) d e rho(lcm(d,e)))
    = O_K(N p^(-1/4) log^2(2p) z^8),
using rho(k)<=k^2, lcm(d,e)<=de and sum_(d<=z)d^3=O(z^4). The product lcm is coprime to p, so (4) applies to the needed moduli, not just d<=z. The choice of z and p>=T gives error O_K(N T^(-1/8) log^2(2T)).

For completeness the lower bound G(z)>>log^3 z is the same truncated Euler-product argument as the earlier fixed-dimensional sieve. Take primes 3<l<=y=z^eta, fixed sufficiently small eta>0. The product of the total squarefree weights 1/h(d) over these primes is
    W=prod_(3<l<=y)(1-g(l))^-1 >> (log y)^3,
using g(l)=3/l+O(l^-2), the elementary Mertens product order and a convergent quadratic correction. Equivalently use the earlier dimension-three Euler-product lemma with this O(l^-2) correction. Normalize these weights; each prime occurs with probability g(l). The mean log d is sum g(l) log l=O(log y) by Chebyshev and partial summation. Choose eta to make it <=(log z)/2. At least half the weight has d<=z by Markov, hence G(z)>=W/2>>log^3 z. The use of elementary Mertens/Chebyshev is identical to the existing fixed-dimensional sieve; no prime-pair asymptotic is required.

The surviving integer pairs thus number
    O_(K,lambda)(N/log^3 T)=O_(K,lambda)(X/(T log^3 T)). (5)
All three exclusions are imposed simultaneously. In particular neither a singular-factor average over E nor a polynomial lower bound on X/(pr) is used. The upper sieve cannot be used for a lower bound on actual successors.

## 5. Actual first-pair supply and consequences

Each fixed p,e,f,E and integer pair (r,s) fixes q by (1), hence fixes H_s=pq+e and H_t. On a single actual monotone ray a source pre-horizon occurs at most once, and its first high successor is unique. Thus (5) counts all actual first pairs of that tuple. The count remains valid for any subset and with arbitrary nonnegative weights <=K_w T. If counting bounded high words of length <=J0 with that first pair, multiply by the fixed maximum J0 of prefix extensions. With S distinct source primes and E<=B<T-3, summing the two signs and E gives
    F_first(B) << X S (B+1)/log^3 T.                  (6)
All constants depend only on fixed lambda,K,K_w,J0. There is no multiplier cap, total-variation cap, narrow-height assumption, target wait restriction, prime target cofactor assumption, or finite-twins hypothesis. T may grow arbitrarily slowly or be comparable to sqrt X; the long-side Fourier estimate is what removes a lower scale restriction. At B=0 this improves the earlier per-source two-root sieve by a full logarithm for these actual first pairs, with no exceptional-prime loss. It is a counting upper bound rather than an assertion of reachability.

For a disjoint macroscopic word/pair population of total weight F>=rho X, all with upward source and comparable labels, let G_low be the entire physical gain of p<T. Since disjointness pays every strictly intervening low event at most once,
    F <= C_* X S (B+1)/log^3 T + K_w T G_low/(B+1)
    for each integer 0<=B<T-3.                       (7)
The first term pays the low-relay population and the second is the Markov tail for relay gain >B. Thus:
- If S<=D0 log^2 T with fixed D0, choose B=floor(c log T), with sufficiently small fixed c>0 depending on rho,D0 and C_*. The first term is <=rho X/2 eventually, forcing G_low=Omega((X/T) log T).
- If G_low=O(X/T), choose sufficiently large fixed B to make the tail <=rho X/2, forcing S=Omega(log^3 T).
- More generally set u=T G_low/X. If u=o(T), choose B+1 comparable to a sufficiently large fixed multiple of (1+u), satisfying B<T-3 eventually and making the tail <=rho X/2. Then S(1+u)=Omega(log^3 T). If u is not o(T) the earlier low-gain scarcity regime already fails along that subsequence; the exact cutoff statement (7) is always available.

This strengthens the earlier long-CRT word source-support/relay obstruction to all label scales, and to the unbounded multiplier branch of direct pairs. In particular near-minimal global source support and G_low=o(X log T/T) are incompatible with a macroscopic disjoint comparable high-word population, even if its deficits escape every subquadratic cap as in 240e3de. This conclusion does not require the previous four-form first-successor reduction: even long first successors are counted. The stronger low-relay assumption here is NOT forced by G_low=o(X log^2 T/T) in 240e3de. The range between logarithmic and squared-logarithmic relay, larger source support, and general low/middle crossing and macro upward supply remain. The narrow-guard/fast-dominance conditions used to produce the disjoint words are still conditional. This is not a proof of twin infinitude.

## 6. Diagnostics and persistence

[Final audit a98ccdf](https://github.com/tara-sooo/A166944-Lean/blob/a98ccdf8b22d44a5911997fc4dcaf3faa621cf81/research/min_direct_modular_hyperbola_source_sieve_audit.mjs), blob bc4aa3dfeb3dff784c7793f2a432790839671b11. Exact remote readback. Run node research/min_direct_modular_hyperbola_source_sieve_audit.mjs 40000. Actual ECMAScript executed in tool runtime. 19998 canonical odd roots through40000,352451 actual MIN events,0 unresolved cap180;79992 controls T11/17/31/61, comparable band [T,6T], B=min(T-4,ceil(log^2 T)).37760 actual upward-first pairs and product congruences,66759 three-condition roughness controls (42074 both product residues nonzero,24685 one zero),25775 finite box checks,27589 extended target waits and10171 short,32829 prime source cofactors and10246 composite target cofactors,31501 greedy disjoint low-budget checks. Independent finite exact tests:2260 local densities incl zero product residue cases,3 composite CRT densities,1600 translated hyperbola boxes (49757 integer solutions counted),36 long rectangles (7445 solutions) with length up to 100p+17 and1800 nonzero Fourier geometric bounds. Numerical complex arithmetic checks:48 second moments,768 complete exponential-sum inequalities,6 full Fourier identities; largest observed |K|/p^.75 about0.951, not the analytic constant. Example p23,r17,q41,s57,E6,a3,H942->970,target wait4; composite target cofactor permitted. Initial audit aborted because it checked l>=T, potentially including r itself, despite requiring r!=0 mod l. The final audit uses l<T as in the analytic proof; no failed partial commit. All final assertions passed. Counts overlap across thresholds and roots; finite tests do not verify the asymptotic sieve or macroscopic hypotheses. Main and sibling branches unchanged. No Lean kernel verification, external novelty claim or final contradiction.
