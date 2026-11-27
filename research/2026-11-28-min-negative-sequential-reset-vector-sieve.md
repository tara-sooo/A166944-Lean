# Negative MIN: polynomial-label sequential reset chains by a split sieve

2026-11-28 JST. Issue #10, continuation of 8aa47eadc352787233e55733ece76c9e5eb46eb9. Checked core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a, 614 declarations unchanged. User goal 4.85 intermediate and unconditional twin infinitude ultimate. This checkpoint constructs actual histories with arbitrarily many completed long waits and firings, followed by a longer quiet tail. Unlike the earlier direct fans, the labels are used sequentially on the SAME path and can be polynomial in R for each fixed depth. Paper proof using published sieve results plus exact finite controls; not new Lean kernel verification.

## 1. Statement

Write L=log R. For every fixed integer k>=1 and every fixed 0<theta<1/4, there exists a fixed delta=delta(k,theta)>0, delta<theta, such that for all sufficiently large R there are
    >>_(k,theta) R/L^(2k+2)                                  (1)
distinct canonical initial centers A in [R,2R] with the following properties at age H=floor(R^theta):
- exactly k completed firings, in their prescribed order, with distinct prime labels p_1,...,p_k in [R^(delta/2),R^delta];
- every firing is the true least-prime event, at the end of a canonical wait (p_j-7)/2 from the corresponding reset birth; three additional idle ticks attain the next canonical birth;
- at time G/2, G=sum_j(p_j-1), the actual state equals birth(x) for x=A-G; from then through age H it is stationary, since x-1 is prime and x+1 has all prime factors >=4H+8;
- k(R^(delta/2)-1)<=G_H(A)=G<=k R^delta=o(H).
In particular the first quiet phase, AND each quiet phase between successive events, grows polynomially, even though all are short relative to the final quiet tail. Neither (1) nor the following diagonal result requires twin primes. Some final centers may be twins; we do not assert that they are not.

## 2. CRT construction without nested label congruences

Fix k. Let B0 be a fixed multiple of 12 containing every prime <=2k+3 (e.g. 12 times the product of primes 5 through 2k+3). Let P=R^delta and P0=R^(delta/2). Take ordered distinct prime labels p_1,...,p_k in [P0,P], all 1 mod B0. Define D_i=sum_(j=i+1)^k(p_j-1) for 0<=i<=k, so D_k=0, x_i=x+D_i, A=x_0. All x_i are canonical if x=0 mod B0. To reset x_(j-1) to x_j impose x_j=0 mod p_j, hence x_j=0 mod4p_j. Equivalently choose x=-D_j mod p_j. These are independent CRT constraints because labels are distinct and coprime to B0. They do NOT impose p_j=1 mod other labels.

We restrict to tuples such that for every pinned prime p_j,
    D_i-D_j+s !=0 mod p_j  for all 0<=i<=k, s in {-1,+1},
    EXCEPT (i,s)=(j-1,+1).                                  (2)
At the exception divisibility is automatic since D_(j-1)-D_j=p_j-1. For i=j the residues are +/-1, and for i=j-1,s=-1 the residue is -2. For every other i, the difference of suffix sums contains at least one OTHER label with coefficient +1 or -1; after fixing all labels except that other label, violation of (2) pins one residue mod p_j. The bound
    sum_(P0<=m<=P, m=a mod p_j) 1/m
          <= O(1/P0 + log(P/P0)/p_j) = O(L/P0)
holds for any residue (sum over all integers, grouping into p_j-blocks or integrating the arithmetic progression; first term <=1/P0). Repeated labels similarly cost O(1/P0) in harmonic weight. For fixed k the sum over all other label variables is bounded since
    sum_(P0<=p<=P, p=1 mod B0) 1/p -> (log 2)/phi(B0)>0
by PNT in a fixed AP and partial summation. Thus the total product-reciprocal weight of inadmissible or repeated tuples is O_k(L/P0)=o(1), and
    sum_(admissible ordered tuples) prod_j 1/p_j >>_k 1.   (3)
Here and below k,theta,delta are fixed before R tends to infinity. This broad polynomial label interval, rather than one dyadic band, avoids a factor L^-k in the lower bound.

For each admissible tuple let B=B0 prod_j p_j and take the unique class x mod B from the CRT above. By (2), x-1 and x+1 are coprime to B; all other x_i neighbors avoid primes dividing B except the intended label dividing x_(j-1)+1. For primes dividing B0, x_i=0 mod B0 because every label is 1 mod B0. If all x_i neighbors avoid free primes q<=P except intended pins, every source x_(j-1) is p_j-rough and every target x_j is 11-rough, for all sufficiently large R. With final target rough up to z=4H+8, the checked lemma shortReset_merge_birth applies at each step: first firing p_j at elapsed (p_j-7)/2, target x_j, followed by 3 idle ticks to birth(x_j). Actual deterministic suffix equality then composes these resets, and the height pin excludes a firing at final center through at least age H after its birth. The total reset duration is sum (p_j-1)/2=G/2. Use x in [R,2R-kP-10] so all births are in [R,2R]; this trimmed interval has length asymptotic to R. The local conditions in this section suffice independently of all analytic estimates.

## 3. Separate small-label constraints from final long roughness

Use a prime variable a=x-1 in that trimmed interval shifted by -1, and a in its single reduced class b mod B. For each admissible tuple make two disjoint prime groups:
  P_small = free primes q<z0=2P, q does not divide B.
  P_large = primes z0<=q<z=4H+8.
At small primes forbid a+D_i and a+D_i+2 from vanishing for all i=0,...,k. For the last i=k, a itself is already prime of order R, so among reduced residues there are at most kappa=2k+1 forbidden classes. Let nu(q) be their actual count, omitting residue 0 and deduplicating. For q not dividing B0, q>2k+3 so nu(q)<=2k+1<q-1; positivity and a uniform dimension-kappa product bound follow from g1(q)=nu(q)/(q-1)<=kappa/(q-1), Mertens, and convergence of the O_k(1/q^2) correction. In particular
    V1=prod_(q in P_small)(1-g1(q)) >>_k (log z0)^(-kappa).
This bound is uniform in the tuple, with no assumption of independent shifted forms at a given prime. All primes dividing B are handled by the exact pinned congruences, not by these free sieve weights. At large primes only forbid a+2; g2(q)=1/(q-1), independent of tuple. The one-sided dimension-one product condition holds with a fixed constant by Mertens (omission of small primes only decreases the product). Here
    V2=prod_(z0<=q<z)(1-1/(q-1)) ~ log z0/log z -> delta/theta>0.
It is essential to use a linear sieve that permits the ONE-SIDED product hypothesis for this truncated group, not to assume the two-sided formula for every w below z0.

Choose b2 with 2theta<b2<1/2; choose b1>0 so b1+b2<1/2. Then choose delta>0 sufficiently small that
    delta<theta, k delta+b1+b2<1/2, and b1/delta is as large as needed.
Put D1=R^b1, D2=R^b2. At small primes use upper and lower combinatorial beta-sieve weights lambda1^+,lambda1^- with |lambda|<=1 and support d1<=D1. The fundamental lemma gives their main sums A1^+,A1^- = V1(1+O_k(exp(-s1))) (or O_k(s1^-s1/2)), s1=log D1/log z0. By making delta sufficiently small, for any fixed eta>0 we have |A1^+-V1|,|A1^--V1|<=eta V1 uniformly. Denote the pointwise sums on an individual a by U1,L1, and I1 its small-sifted indicator. Then L1<=I1<=U1; U1 and U1-L1 are NONNEGATIVE pointwise. No assertion L1>=0 is used.

Instead of applying a lower sieve to a signed sequence, form TWO nonnegative weighted sequences (indexed by n=a+2 and summed over all admissible tuples, with multiplicity):
    Aplus: weight U1(a),
    Adiff: weight U1(a)-L1(a).
Both satisfy the same large-prime density g2(d2)=1/phi(d2). Their respective main totals are
    Xplus=sum_tuple X_B A1^+,
    Xdiff=sum_tuple X_B(A1^+-A1^-),
    X_B=pi(interval)/phi(B),
because the CRT moduli B,d1,d2 are pairwise coprime and the reduced residue counts factor. Set Xstar=sum_tuple X_B V1. By (3), phi(B)=phi(B0) prod_j(p_j-1), and PNT,
    Xstar >>_(k,delta) R/L^(kappa+1),
    Xplus >=(1-eta) Xstar,    0<=Xdiff<=2eta Xstar.          (4)
Nonnegativity of the main difference also follows by taking expectation of U1-L1 under independent Bernoulli bad-prime indicators with probabilities g1(q). This is a statement about the formal main term only, not probabilistic independence of actual primes.

## 4. Uniform BV error for polynomial growing moduli and ordered tuples

For each d2<=D2 supported on P_large, expand U1 or U1-L1 as small-divisor sums. For each tuple and each d1<=D1 supported on P_small there are nu(d1)=prod_(q|d1)nu(q) reduced CRT classes modulo m=B d1 d2. Large-prime condition is the one class a=-2 mod d2. The prime count in each complete class is pi(interval)/phi(m)+O(E(m)), where E(m) is the sum of the two endpoint maximum reduced-class errors. Its main terms sum to exactly X_B g1(d1)g2(d2). Total weighted error over d2 is bounded by
    O_k(sum_(m<=B0 R^(k delta+b1+b2)) tau(m)^C_k E(m)).
Indeed B0 is fixed; choosing the ordered distinct tuple from the prime divisors of m costs at most k! tau(m)^k (a deliberately loose bound); after tuple removal the disjoint prime-range split determines d1,d2 uniquely. The factor nu(d1)<=kappa^omega(d1) is at most a fixed power of tau(m). Small weight magnitudes are <=1 (or 2 for their difference). No uniform asymptotic for primes in each individual growing modulus is being asserted.

Classical BV at any fixed level strictly below R^1/2 gives sum E(m)<<_A R L^-A for arbitrary fixed A. The weighted version follows directly by Cauchy-Schwarz: elementary E(m)<<R tau(m)/m for m<=R^1/2 (count all integers in a class, bound 1/phi(m)<=tau(m)/m). Thus sum tau(m)^(2C_k) E(m)<<_k R L^C'_k by the elementary fixed divisor moments, obtainable from their Euler products. Combining the two estimates with arbitrary A gives weighted error O_k,A(R L^-A) for every fixed A. Both endpoints are of order R, so BV applies with the same fixed margin. This is the reason polynomially growing p_j are now permitted, whereas previous fixed-class arguments did not establish a uniform claim of this kind.

## 5. Positive simultaneous lower sieve and actual histories

Apply the ordinary Rosser-Iwaniec linear lower sieve to Aplus on P_large at level D2 and the ordinary linear upper sieve to Adiff. The common s2=log D2/log z -> b2/theta>2, so f(s2)>0 and F(s2) finite. Standard one-sided dimension-one hypothesis suffices (Ford Theorem LS, verified below); the remainders are O(R L^-A) by section 4. If a main total is zero its contribution can be bounded directly by the remainder or by adding a vanishing positive main parameter. Since I1>=L1=U1-(U1-L1), the actual joint sifted count is at least the difference of these two large-sifted sums. Hence
    joint count >= V2 [Xplus(f(s2)-o(1))
                      -Xdiff(F(s2)+o(1))] - O(R L^-A)
                >> Xstar V2 >> R/L^(2k+2),
choosing eta first sufficiently small relative to f(b2/theta)/F(b2/theta), then delta to make the small sieve approximation hold, then R large. This is a vector-sieve argument with different dimensions and disjoint ranges, NOT a lower sieve for a single dimension-2k+2 problem at z=R^theta. No factorability assertion beyond BV is needed. The pointwise inequality can also be written I1 I2 >= L1 U2+U1 L2-U1 U2 for upper/lower indicators of both groups.

Each surviving tuple/a meets all local conditions of section 2 and gives a canonical root A=x+D_0. The count is over ordered tuple/prime pairs. It is ALSO a count of distinct initial centers: if two pairs produce the same A, the deterministic recurrence forces the same first k actual prime labels in the same order; hence the tuple is the same and x=A-D_0 is the same. This injectivity is crucial; no extra division by possible fan multiplicity is required. The k resets occur before H since delta<theta, then no further event through H. This proves (1).

## 6. Use the fixed-depth lower to get unbounded true event count

For every fixed theta<1/4, choose delta_k from the proof also <min(theta/2,1/(2k)). For each k choose a threshold R_k, strictly increasing unboundedly, so for all R>=R_k the above lower holds and:
    c_k>=R^(-1/k), L^(2k+2)<=R^(1/k),
    k R^delta_k<=R^(1/k), (R^(delta_k/2)-7)/2>=L^k.
These are possible for each fixed k, using the positive constants and powers. For R_k<=R<R_(k+1), use the k-th construction. Then k(R)->infinity, and there are at least R^(1-o(1)) distinct actual canonical roots which at age floor(R^theta)
- have k(R) distinct completed firing labels,
- have every canonical inter-reset wait at least L^k(R),
- have 0<G_H<=R^(1/k(R))=R^o(1), hence G_H/H->0,
- have exact reset state at age G/2 followed by the long quiet tail.
No explicit growth rate of k(R) or effective R_k is provided. This diagonal uses fixed-k BV estimates only, not a uniform increasing-dimensional sieve theorem. This construction is for sequential histories, not growing fan multiplicity. It also does not assert a density lower by a fixed power of L when k grows.

One may use theta=.249, as in the previous one-reset construction, but now the event count is unbounded and the completed waits themselves grow. The earlier .285 zero-gain exponent is unchanged. This is a new dynamic low-gain construction at polynomial horizon, rather than an increase of the best time exponent or a near-square witness. It is consistent with the previous first-exit exclusion: for k=1 the lower size R/L^4 is below the earlier exceptional bound, and in the present chains the first jump and the later waits may be polynomial. The remaining gap to sqrt R is polynomial. In particular the density/semiprime obstruction to the final long quiet tail remains; taking k large does not change the exponent theta<1/4 because each chain uses only o(H) completed time.

## 7. Independent finite checks and sources

Audit research/lean/negative_min_sequential_reset_vector_sieve_audit.mjs @c05eda7db538db3bc404697c9e41d7acca5978ed blob d0db128556e5ce231b847d2890c02c49847edb0c. ECMAScript executed, exact pinned remote readback. Finite proxy labels 13,37,61,73,97,109,157, fixed modulus 12 (with direct free-prime local admissibility checks; not the asymptotic B0 for all k). Enumerated 1099 ordered distinct tuples of length1..4, 817 pass pinned tests, 282 rejected, 2986 CRT target pin checks, 5028 local reduced-class checks. Constructed 55 prime-rough final-target examples, independently factor-calendar vs literal tick replay of 151 actual firings and reset invariants, 15300 literal ticks; 1600 pointwise vector sieve inequality controls. All checks passed. Example: labels (13,61,73,97), A=34571141292, final x=34571141052, total gain240, reset elapsed120, terminal quiet204 more ticks. Trial division covers all finite values (<=5e11); integer arithmetic exact in this range. These tests do not evaluate BV or asymptotic counts.

Sources inspected 2026-11-28, with PDF text and screenshots:
- Terence Tao, 254A Notes 4: Some sieve theory (2015-01-21), https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/ Lemma17/Cor19 and composition discussion: combinatorial fundamental lemma for fixed dimension, small-sieve main sums. 
- Pär Kurlberg, Stephen Lester, Lior Rosenzweig, Superscars for arithmetic point scatterers II, https://kurlberg.github.io/eprints/2dscar.pdf section2.1 printed pp8-9, (2.4)-(2.7), Theorems2.1-2.2: one-sided dimension product, pointwise upper/lower beta weights with magnitude<=1, main-sum fundamental lemma. Their Lemma2.2 is a precedent for composing small and large sieves, not a result about MIN. Standard source [15] Friedlander-Iwaniec, Opera de Cribro.
- Kevin Ford, The linear sieve, https://ford126.web.illinois.edu/Sieve_methods_notes_part6.pdf Theorem LS printed p3 and f(s) formula printed p1, one-sided dimension-one product and ordinary two-sided bounds with absolute remainders, f(s)>0 for s>2. Theorem LS screenshot checked; this is used on truncated P_large, not Lichtman's two-sided product hypothesis.
- Jared Duker Lichtman, A modification of the linear sieve, and the count of twin primes, arXiv:2109.02851v2 (2024), https://arxiv.org/pdf/2109.02851 printed p2 eq(1.2) for ordinary BV with max over reduced classes and arbitrary log saving. Previous shifted-prime .285 uses separate BFI result; no BFI variable-class assumption made here.
No novelty claim for the analytic input, no new Lean run or independent human review. 4.85 not claimed. The next direct route should examine a way to go beyond the final-roughness cutoff, rather than only increase the fixed number of completed resets. Main/siblings unchanged.
