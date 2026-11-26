# Fixed-depth ancestry moments and the two singular deficit lines

2026-11-26 JST. Continuation of 4e4c38c5a406f3b7e33b0fc7fb99256823d3f17a, research/2026-11-26-min-primorial-reset-merger-moments.md. Paper deductions and executed finite audits for the ordinary uncut offset MIN. No Lean verification, novelty claim, or proof of twin infinitude. No canonical branch or formal target changed.

## 1. Complete classification of one-event mergers from integer resets

At a seed (u,v)=(12k,6k+3), the deficit is 6. Suppose its next event has odd prime p, wait w, and arrival (U,V)=(u+p-1,v+w), deficit d'=2V-U. Then

    d'=2w-p+7, 1<=w<=2p.

The even arrival clock gives p|gcd(U,V), hence p|d'. The odd arrival clock gives p|gcd(U+2,V-2), hence p|(d'-6). Since d' is even and nonnegative, in the even case d'=2h p, 0<=2h<=3+7/p, so h=0,1,2, with h=2 possible only for p<=7. In the odd case d'-6=2h p; the bounds 3-p<=d'-6<=3p+1 imply h=0,1. Thus

    V even: d' in {0,2p,4p}, with 4p requiring p<=7;
    V odd:  d' in {6,6+2p}.

For any nonsingular arrival (d' not in {0,6}), the odd part of d'/2 (even V) or (d'-6)/2 (odd V) determines p uniquely. Then u=U-p+1 and v=u/2+3 recover the only possible reset origin. Even-arrival d'=6 would require p=3, impossible at u=0 mod12; odd-arrival d'=0 is impossible. Consequently all one-event collisions of different integer reset origins occur at d'=0 with even V or d'=6 with odd V. No upper bound on p relative to the seed threshold is needed for this injectivity statement.

For an incoming PRE-FIRST-RECORD edge, p<=u/2+1. At a singular arrival define N=U for d'=0, N=U+2 for d'=6. Then p|N and the selected source neighbor is p(N/p-1), the other neighbor is p(N/p-1)+2 for d'=0 or -2 for d'=6. For p>=5 the selected neighbor is composite, since u>=2p-2 and u±1>p. Thus N/p-1 is an odd integer >=3. The waits are respectively (p-7)/2 and (p-1)/2. For all sufficiently large p, every neighboring prime factor is >=p/8 (using w<=2q for each factor q), and p<=8 sqrt(u+1). The two-form upper sieve from the previous merger paper therefore applies to both singular lines, not just the d'=6 line at integer reset offsets. In particular for U in [Y,2Y], the number of distinct label/arrival pairs on either line with p>=T is O(Y/log^2 T). This also follows as the d=6-source subcase of section 3 below. No large multiplicity is possible away from these two singular lines in one event from a reset.

## 2. Exponential tail in the limiting direct-reset indegree law

Let D(r) be the direct pre-record reset indegree from the previous note. Its limiting distribution exists and all fixed moments converge by the previous theorem. We strengthen its limiting tail using exact finite CRT densities.

Fix distinct candidate primes p_1<...<p_j=p, all 1 mod12. Write P=product p_i. For all to be direct incoming labels at r, one needs P|r. The largest label p requires the two forms 2r/p-1 and 2r-p-2 to avoid every odd prime ell<=p/8 for large p. For ell not dividing P, these give exactly two excluded residues of r modulo ell; omit primes dividing P. Conditional on r=1 mod6, the finite congruence density is at most

    C/(P log^2 p) * product_(q in {p_1,...,p_(j-1)}) (1-2/q)^(-1).

Indeed the full product over 5<=ell<=p/8 of (1-2/ell) is O(1/log^2 p) by the ordinary Mertens product, and omission of the other selected primes costs at most the displayed product. Bounded p can be handled by an absolute constant. This bound holds for the limiting probability of any fixed tuple; no uniform large-product progression estimate is required in this limiting argument.

For t in (0,2), expand the nonnegative factorial generating function of the limiting random variable D. Group nonempty finite subsets of incoming labels by their largest p. For each p the sum of their contributions is bounded by

    C t/(p log^2 p) * product_(q<p, q prime, q=1 mod12) (1+t/(q-2))
    <= C_t /(p (log p)^(2-t)).

For the last inequality enlarge the prime set to all primes >=5 and use the elementary reciprocal-prime Mertens bound; sum 1/(q-2)-1/q converges. The sum over p converges by Chebyshev's bound in dyadic intervals since 2-t>0. Nonnegative monotone convergence from finite truncations justifies the expansion. Therefore

    E[(1+t)^D]<infinity for every 0<t<2.

In particular for every 1<b<3, the limiting law satisfies Pr(D>=m)=O_b(b^(-m)). This is a limiting-distribution statement; it does NOT assert uniformly bounded exponential moments of the finite-Y distributions. The fixed-power finite-Y moments already established in the previous paper remain available. The same factorial-generating argument will apply to high incoming LABEL counts on the two singular lines below, because the only arithmetic ingredients are divisibility by N and the two rough forms. It does not require labels to lie in the progression 1 mod12 when bounding the product above.

## 3. One-step incoming moments in the entire bounded-deficit strip

Fix an even D0>=6. Use all envelope-valid states with u even, u>=12, v=(u+d)/2 and d even, 0<=d<=D0. This is a larger state class than actual reset-origin reachability. Include an edge exactly when the genuine first-clock MIN event has p<=u/2+1 and its destination remains in this strip. The cut includes every actual pre-first-record edge from an integer reset that stays in the strip, since p<=r_seed<=u/2+1. Each vertex has at most one outgoing edge and u strictly increases.

Let I(U,V) be the indegree of a vertex. Put c=0 for even V and c=6 for odd V. Every incoming prime satisfies p|(d'-c), d'=2V-U. If d'!=c, then p<=D0+6 and the origin offset is forced by p, while its deficit has at most L=D0/2+1 choices. Thus I is bounded by a constant depending on D0 off the singular lines. For d'=c, p divides N=U+c/3 (i.e. U or U+2), and still each p has at most L possible source states. For p>=max(17,2D0+2),

    w=(p-1+d'-d)/2 >= p/4.

Every prime factor of the source neighbors is >=w/2>=p/8; the selected source neighbor is p(N/p-1), necessarily composite by the source-label cut, so p<=8 sqrt(u+1). Its other neighbor is this product plus or minus 2. For U in [Y,2Y], the previous two-form upper sieve, with fixed p and variable k=N/p-1, bounds the number of candidate arrivals by O(Y/(p log^2 p)). The parameter length O(Y/p) is at least a constant times p, by the scale bound. Hence, summing over primes p>=T, the number of high-label edges into the slab is

    O_D0(Y/log^2 T)            (T sufficiently large depending on D0).

This counts all allowed strip sources, not only states reached from some seed.

Let J(N) count distinct incoming labels above the fixed threshold on a singular line, so I<=C_D0+L J(N). We have J<=omega(N). For fixed integer k>=1 the uniform kth moment of J follows by the same argument as section 4 of the previous merger note: exceptional targets with any incoming p>Y^(1/(2k)) have proportion O_D0,k(log^-2 Y), and Cauchy-Schwarz with E[omega(N)^(2k)] gives o(1) contribution. For tuples of at most k distinct smaller labels, their product P<=sqrt Y. Substitute N=P h. The largest p requires the two forms (P/p)h-1 and P h-p +/-2 to be rough at primes <=p/8. These have two distinct roots at all odd sieve primes not dividing P. The same explicit two-form Selberg upper sieve gives O_k(Y/(P log^2 p)) candidates; omitting at most k prime divisors of P costs only a k-dependent constant, and the available progression length is >>p. Sum the bound over tuples using convergence of sum_p (1+log log(3p))^(k-1)/(p log^2 p). This proves

    sum_(strip vertices U<=Y) I(U,V)^k = O_D0,k(Y).

We used dyadic decomposition for the sum up to Y. The same proof also bounds one-step integer-reset-origin indegrees at singular destinations outside the reset-offset congruence class, by taking only source deficit 6. In that separate one-step problem, nonsingular destinations need no moment estimate beyond the injectivity of section 1, and the number of one-step arrivals up to Y is O(Y).

For any fixed label cutoff T, incoming tests are eventually periodic in U on each fixed deficit row. Indeed for each fixed p,d,d' the source and wait are forced; all intervening raw gcd prime divisors are determined by the odd nonzero relative defects d+2j+1 on even ticks and d+2j-5 on odd ticks, where 1<=j<=w. The parity and residues repeat under a sufficiently divisible even translation of U, and the threshold p<=u/2+1 becomes automatic for large U. This also proves eventual periodicity of bounded-depth incoming counts with bounded labels.

For fixed cutoff T, the limiting CRT density of a tuple of high labels at a singular line is bounded as in section 2 (with N instead of r, and harmless constants for restricting parity). The largest label imposes the rough forms N/p-1 and N-p +/-2, with two forbidden residues at each odd prime not dividing P. Thus the limiting J has exponential moments E[b^J]<infinity for 1<b<3. Existence of the limiting law follows from periodic truncations and the O_D0(log^-2 T) high-label tail. Since I<=C_D0+L J and the nonsingular indegrees are bounded, the limiting law of I has an exponential tail, with exponent depending on D0. Finite-Y power moments and convergence of these moments follow from the preceding uniform bounds and truncation. No uniform estimate as D0->infinity is claimed.

## 4. Propagation to every fixed ancestry depth without independence

The following finite graph inequality applies to either the direct-reset graph or the strip graph above, truncated at target horizon Y. The graphs are acyclic and have outdegree at most one; all ancestors of a target in the truncated domain are also in that domain (apart from the fixed lower boundary). Let Lf(y)=sum_(x->y) f(x), for nonnegative f, and I(y) the indegree. For integer k>=1, Holder's finite-sum inequality and Cauchy-Schwarz across directed edges give

    sum_y (Lf(y))^k
      <= sum_(x->y) I(y)^(k-1) f(x)^k
      <= [sum_y I(y)^(2k-1)]^(1/2)
         [sum_x f(x)^(2k)]^(1/2).

The last factor uses OUTDEGREE AT MOST ONE; the first factor counts each target exactly I(y) times. Divide both sides by the vertex count, which is Theta(Y) for fixed strip width or for the direct reset graph.

Let A_h(y) count ancestors at exactly h edges (A_0=1), B_h=sum_(i=0)^h A_i. Since A_(h+1)=L A_h, induction on h using the uniform finite-Y moments of I proves

    E_Y[A_h^k]=O_(h,k,D0)(1),
    E_Y[B_h^k]=O_(h,k,D0)(1)

for every fixed h,k, with D0 dropped for the direct reset graph. Strict increase of u and outdegree at most one imply no origin is counted twice at different depths for the same endpoint. This is a true multi-step ancestor bound, with no independent-branching assumption.

Truncate incoming edges at label T. If the depth-h ancestry of an endpoint changes, some high-label edge lies within h steps backward from it. The target of each high-label edge has at most h forward descendants including itself within that depth, because forward edges are unique. Thus the number of endpoints whose B_h differs after truncation is at most h times the number of high-label edges, i.e. O_D0(hY/log^2 T). Together with eventual periodicity at bounded T, this proves the existence of a limiting law for every fixed B_h. The uniform moment bound at order 2k and Cauchy-Schwarz show that moments also converge (the contribution from altered endpoints is O_(h,k,D0)(1/log T)).

There is a stronger tail in this limiting law. If all vertices in the depth-h incoming tree have indegree <=m, m>=1, then B_h<=(h+1)m^h. Consequently a vertex violating this bound must be a forward descendant within h steps of a vertex of indegree >m. Each such vertex can account for at most h+1 endpoints. Passing to densities and using the exponential indegree tail gives, for fixed h>=1,

    Pr(B_h>b) <= C_(D0,h) exp(-c_(D0,h) b^(1/h))

for b large. This also holds on the direct-reset graph. The finite-Y uniform power moment result is separate from this limiting tail.

A useful consequence: for fixed h,D0, any family of o(Y) vertices in the strip can collect only o(Y) different seed origins within h edges staying in the strip. Indeed the sum of B_h over that family is bounded by the square root of its size times the square root of sum B_h^2=O(Y). This is an actual small-set transport estimate for bounded-depth, bounded-deficit ancestry. It is not applicable directly to the previous high-rational-slope crossings, whose deficit is proportional to Y.

## 5. Arbitrarily long direct-reset chains

Fixed-depth analysis cannot be replaced by a uniform finite depth. For any m choose successively distinct primes p_i=1 mod12, all 1 modulo every odd prime <=2m and all earlier selected primes, with p_i>2E_(i-1)+3 where E_i=sum_(j<=i)(p_j-1)/2, E_0=0. Dirichlet applies to the resulting reduced progressions. Seek consecutive reset parameters r_i=r_0+E_i and impose r_i=0 mod p_i.

For a selected p_i, at the intended source 2r_(i-1)=1 mod p_i. At earlier sources 2r_j=1-2(E_(i-1)-E_j) mod p_i, which is neither 1 nor 3 by the size bound and positive even gain. At later sources r_j=0 mod p_i by nested congruences. Thus p_i is excluded from both neighbors at every other source. For every unselected odd prime q<=max p_i+6 exclude r_0 residues with 2(r_0+E_j)=1 or 3 mod q for 0<=j<m. If q<=2m choose r_0=1 mod q (all gains divisible by q); otherwise at most 2m residues are forbidden. Combine with r_0=1 mod6 by CRT.

The same relative-defect check as in the previous direct-merger construction excludes every possible earlier clock and yields first event p_i, w_i=(p_i-1)/2. All sufficiently large r_0 in the progression have p_i<=r_0 and these are genuine pre-first-record edges of the original seed, not merely edges under a changing threshold. Thus direct chains of every finite length exist, on a positive-density progression for each length. This does not establish an infinite direct chain, nor a density bound for chain lengths growing with Y. It proves that the full direct-forest ancestor depth cannot be uniformly bounded.

## 6. Executed diagnostics

Source research/min_primorial_direct_forest_audit.py, commit df3bf2a59722c7d86742a05184ec34b0c0443097, exact remote blob c3de70f4f87c0b9ce8331c8169b950250d659133 equals the locally executed git hash-object. Run:

    python research/min_primorial_direct_forest_audit.py 1000000

Dependencies: SymPy and sibling min_primorial_record_supply_audit.py.

- Complete direct reset graph for r<=10^6: 166666 vertices, 13268 edges, max indegree 3, max full basin including target 5, max depth 4. Counts of sources with at least 1,2,3,4 edges inside cap: 13268,586,24,2. A longest chain is 399211->399217->399337->399367->399373 (labels 13,241,61,13). Full basin sizes 1,2,3,4,5 occur 153588,12336,691,42,9 times respectively. The identities for exact depths, degree-tree tail, high-edge endpoint count, and operator inequalities for k=1,2,3 all passed.
- CRT chain labels (13,157,4093), seed has 1753 digits, relative reset-parameter gains 0,6,84,2130. All 2130 raw GCD ticks replayed; this explicit compatible tuple is not claimed to satisfy the recursive prime-selection scheme. Arbitrary length is established by the paper construction.
- One-event integer-reset-origin graph with source r<=10^6 and arrival U<=1999998, excluding first-record edges: 159162 edges to 155349 distinct states. 73653 nonsingular destinations all have exactly one origin. Deficit-0 singular line: 27695 edges to 27064 states, 629 merger states, max indegree 3, e.g. (776968,388484) with seed parameters 388387,388471,388477 and labels 197,29,17. Deficit-6 singular line: 57814 edges to 54632 states, 3081 merger states, max indegree 3, e.g. (14788,7397) with seed parameters 7381,7387,7393 and labels 29,17,5. All phase classifications passed.
- Full envelope-valid strip graphs at u<=100000, source cut p<=u/2+1, including arbitrary local states, not restricted to reset origin: D0=6: 199980 states, 136298 edges, max indegree 19, max B_3=56. D0=24: 649920 states, 528540 edges, max indegree 35, max B_3=169. All large-label singular-line and roughness-scale checks, and the operator inequality for depths 1,2,3 and k=1,2,3, passed.

## 7. Open target

The earlier whole-basin moment problem is now solved at the paper-deduction level only for fixed ancestry depth in the direct-reset graph or a fixed bounded-deficit strip. The full ancestry can leave every fixed strip, and even direct-reset chains have unbounded depth. Controlling constants when depth and strip width grow, or bounding the total mass transported through successive exit levels, remains open. In particular the previous high-rank crossing supply estimate does not yet imply a positive density of good seeds. No upper bound on first-record displacement or Lean-verified theorem was obtained. No assigned child issue is claimed completed.
