# Averaged four-form sieve for local upward returns and the log-squared recycling scale

Continuation of [7b426da](https://github.com/tara-sooo/A166944-Lean/blob/7b426daaea1e966b1ee35414baa036e5ce3c6092/research/2026-11-26-min-direct-time-height-localized-upward-source-capacity.md). The previous time-height theorem forces positive sources at intermediate scales under localized fast-drop hypotheses. Here study repeated visits of one such upward label, using both endpoints' roughness. Unlike the older pointwise discriminant estimate, averaging the exceptional-prime factor over the cofactor gap removes the loglog loss. In the regime of near-minimal weighted local label support this places most positive flux on returns with half-gap of order log^2 T. This is a necessary spacing condition, not a universal upper bound on source flux or a twin-infinitude contradiction.

## 1. Four forms and exact collision polynomial

Take a canonical contiguous block with pre-horizons in [X,Y], Y=lambda X, C=floor sqrt(Y+1), partition into half-open bins of integer length L as in 7b426da, with C T^epsilon<=L<=X and T->infinity, fixed epsilon>0. For each bin choose any finite guard union E (in ordinary deficit space) and any subset of actual upward events p in [T,R], T<=R<=C and R<=K0 T^b with fixed K0,b>=1. The guard can depend on the actual trajectory. Retain only events with positive localized flux, i.e. length(E intersect (d,d'])>0. Write M=length(E), assume finite; empty guards are vacuous. The selection can omit events arbitrarily. Write e=1-2I and q=(H-e)/p. At an upward event 2w>g=p-1; thus both H+-1 avoid every odd prime l<g/4, by the strict future competitor clock. No assumption that q is prime.

For fixed p>=T, order the selected source visits in the bin by horizon. Their odd q strictly increase: two distinct same-p visits have horizon difference at least p-1 and the sign difference is at most2. For any pair, q2=q+2m, m>=1 integer, and H2-H1=2mp+e2-e1. The simultaneous roughness conditions at the two endpoints give the four linear forms
    q, q+2m, pq+2e1, p(q+2m)+2e2.
For an odd prime l>4, l!=p, the four forbidden roots coincide in some pair if and only if l divides the nonzero integer
    D_p(m)=m (pm+e2)(pm-e1)(pm+e2-e1).               (1)
Indeed the roots are 0,-2m,-2e1/p,-2m-2e2/p. The comparisons within one event never coincide; the four cross comparisons give exactly (1). All factors are nonzero since m>=1,p>=7. With p and m polynomially bounded in T, abs(D_p(m))<=T^O(1). This sharper collision product is independent of the absolute horizon or deficit.

Define
    J_p(m)=prod_(l|D_p(m), l>4 prime, l!=p) (1-4/l)^(-1).
At a fixed gap the old fixed-dimensional Selberg argument gives a factor J_p(m). In particular it is not necessary to use a uniform worst-case O((loglog X)^4) bound; we average this factor below.

## 2. Uniform mean of the collision factor on logarithmically long gap intervals

Fix a>0,d0>0. For integer K with (log T)^a<=K<=T^d0, uniformly in p in [T,K0 T^b] prime and both signs,
    sum_(1<=m<=K) J_p(m) <<_(a,b,d0,K0) K.             (2)
Proof. Put y=K^eta with a sufficiently small fixed eta>0. Split J_p into its factors with l<=y and l>y. For all sufficiently large T, the product of the larger factors is bounded by a constant depending only on the fixed parameters. To see this, primes y<l<=log T have product bounded by O((loglog T/log y)^4) if the interval is nonempty, by Mertens' product and convergence of the quadratic correction. Since log y=eta log K>=eta a loglog T, this is O_(eta,a)(1). If y>=log T that portion is empty. Prime divisors of D_p(m) above log T number O_(b,d0,K0)(log T/loglog T), each log contribution O(1/log T); their product is bounded. This is uniform even when D_p(m) has unusually many small prime factors.

For the small part J_small(m), expand the finite Euler product
    J_small(m) = sum_(d|D_p(m)) W(d),
where d is squarefree, only primes 4<l<=y,l!=p occur, and W(d)=prod_(l|d) 4/(l-4). For a fixed m normalize these weights to a probability distribution on divisors of D_p(m) built from the eligible small primes. Each included prime has probability 4/l. Thus the mean of log d is
    sum_(l|D_p(m),4<l<=y,l!=p) 4 log l/l
      <= O(log y)
by the elementary Chebyshev bound and partial summation. Choose eta so this is <=(log K)/2 for all sufficiently large K. Markov's inequality then shows at least half the weight is on d<=K, so pointwise
    J_small(m) <= 2 sum_(d<=K,d|D_p(m)) W(d).
For each such squarefree d, the congruence D_p(m)=0 mod d has at most 4^omega(d) roots: every l|d is coprime to p, and (1) consists of four nonzero linear polynomials mod l. Over 1<=m<=K its count is <=4^omega(d)(K/d+1)<=2K*4^omega(d)/d. Summing the truncated divisor expansion and extending the positive sum to all squarefree products of primes >4 gives
    sum_m J_small(m)
       <= 4K prod_(l>4 prime) [1+16/(l(l-4))] = O(K).
The Euler product converges. Combined with the uniform large-prime bound this proves (2). This argument uses a pointwise weighted divisor truncation, not an assumption of uniformity of all roots over a full enormous CRT period. It is valid for K growing as an arbitrarily small fixed power of log T, not for arbitrary bounded K with a uniform asymptotic constant. The constants can depend on a,b,d0. This average singular-factor lemma is the main new analytic ingredient.

## 3. Local short-return capacity without a loglog loss

For fixed p, sign pair and gap m, the first q lies in a translated interval padded to N=ceil(L/p)+2. Both events need the four roughness tests above; the sieve can omit the bad primes in (1). Use the fixed-dimension Selberg argument in [9e3203a](https://github.com/tara-sooo/A166944-Lean/blob/7b426daaea1e966b1ee35414baa036e5ce3c6092/research/2026-11-26-min-direct-repeated-cofactor-cluster-sieve-and-stratum-capacity.md), taking cutoff z=floor(min(p,L/p)^(1/12)). The cutoff is below p and (p-1)/4 for sufficiently large T. Its log is comparable to log T from below, because p>=T and L/p>=T^epsilon, and it has z^6<=sqrt(N). Thus the number of candidates is O_epsilon(N J_p(m)/log^4 T); the error sqrt(N) is absorbed since N>=T^epsilon. For every fixed q and sign pair and gap there is at most one actual ordered pair, even if it is not consecutive in the chosen p-list, because each horizon occurs at most once on a monotone trajectory. Sum m<=K and the four sign pairs, using (2):
    number of actual short pairs with fixed p
        << L K/(p log^4 T).                            (3)
This applies to the entire upward subset and in particular to positive localized sources. We did not use a bound on the absolute multipliers or total variation. Neither q needs to be prime. The earlier global short-cluster estimate with a worst-case loglog factor does not imply (3) uniformly in the present range of T,L,K without the new mean estimate and the label-adapted cutoff.

For a source visit, its localized positive increment is at most min(M,3p+1)<=4 min(M,p). Let S be its actual distinct source label set in the bin and D=sum_(p in S) min(1,M/p). In each p-list classify the ending flux of every visit as FIRST (first visit of p in this bin), SHORT (its predecessor in this selected p-list has half-gap m<=K), or LONG (m>K). These classes partition the actual localized flux P; no flux is counted twice. Equations (2)-(3) give
    P_short(K) << L K D/log^4 T.                       (4)
For the first visits,
    P_first <=4 R D.                                   (5)
For the long visits we need no sieve. The sum of successive half-gaps on a fixed p-list is at most (L+2)/(2p), because its first-to-last pre-horizon span is <L and the sign correction has size <=2. Thus their number with m>K is at most (L+2)/(2p(K+1)). Weight by the maximum flux and sum over p:
    P_long(K) << L D/(K+1).                            (6)
Equation (6) holds for every integer K>=0; (4) requires the stated logarithmic-to-polynomial gap range. Together they bound both tails of the flux-weighted return-gap distribution. The upper tail uses the actual ordered p-list, not an assumption that all candidate pairs can be realized, and the lower tail counts all possible qualifying pairs, which only enlarges the count of actual consecutive ones.

## 4. Near-minimal local support forces a log-squared return scale

Suppose a bin has P>=rho L for a fixed rho>0 and D<=D0 log^2 T with fixed D0. From the preceding source-capacity theorem P<< L D/log^2 T, so this is the near-minimal weighted-support regime, not an assumption of small absolute number of prime labels when M/p is tiny. Since R<=C<=L/T^epsilon, (5) gives P_first=o(L). For any fixed tolerance tau>0 choose a sufficiently small fixed A>0 and a sufficiently large fixed B>A, depending on tau,rho,D0 and the fixed sieve parameters. Take K1=floor(A log^2 T), K2=ceil(B log^2 T). For large T both satisfy e.g. a=1,d0=1 in (2). From (4) and (6),
    P_short(K1) <= O(A D0 L),
    P_long(K2) <= O(D0 L/B).
Choose A,B so the sum of those bounds is <=tau rho L/2; the first-visit term is <=tau rho L/2 eventually. Hence at least (1-tau)P of the localized positive flux is supplied by non-first visits whose preceding selected same-label half-gap satisfies
    A log^2 T < m <= B log^2 T +1.                     (7)
(For the strict lower inequality use m>floor(A log^2 T), which implies m>A log^2 T unless equality at an integer, in which case m exceeds it too.) In horizon units H2-H1=2mp+O(1), so the required separation is of order p log^2 T. This is a flux-weighted two-sided scale conclusion: it does not assert that every repeated visit has such a gap, nor that adjacent physical events have it. In particular it does not imply q2-q1=2 or prime cofactors.

There is an aggregate version with arbitrary different guards and source subsets in the bins. Suppose sum_j P_j>=rho X, sum_j D_j<=D0 (X/L) log^2 T, and all selected source labels lie in [T,R] with the same polynomial upper bound. The first, short and long inequalities sum over bins without overlap of physical events. The first term is O(R sum D_j)=o(X), the short term at K1 is O(A D0 X), and the long term at K2 is O(D0 X/B). Hence at least (1-tau)sum P_j is supplied by returns in (7). For tau=1/2 this is Omega(X) actual localized flux across Omega(X/L) bins, because each bin has physical gain <=L+C<=2L and positive flux <=5 times its gain. This conclusion can be applied to the intermediate source subset forced by 7b426da if its local weighted support sum also has the stated upper bound and its labels are polynomially bounded in T. For example in the polynomial-scale case T=X^a and R<=sqrt(lambda X+1), that last bound holds. No inference that the support upper bound is forced by the earlier lower bound is made.

The new result removes the loglog loss in short pairs, and identifies the repetition scale when weighted support is near minimal. It does not exclude that scale; a trajectory can in principle spread over substantially more source labels, or provide its flux through gaps comparable to log^2 T, or fail the preceding fast-drop hypotheses. Small/middle crossing supply, general macro upward supply and a direct twin witness are still unresolved. The next useful direction is to exploit the exact MIN clock and intervening deficit recovery over these actual same-label return intervals, or prove a contradiction to the required support and gap distribution. The arithmetic estimate here is not an upper bound of o(X) for unrestricted source populations.

## 5. Diagnostics and preservation

[Audit 5c25d58](https://github.com/tara-sooo/A166944-Lean/blob/5c25d58ea9957c16765a07572bd15b2ec31f17e2/research/min_direct_local_upward_return_average_audit.mjs), blob bb397f5d8ad79b4c35b73484774df75b050ac7bf. Exact remote readback. Run node research/min_direct_local_upward_return_average_audit.mjs 40000. Actual ECMAScript execution in tool runtime. 19998 canonical odd roots through40000,352451 actual MIN events,0 unresolved cap180. 159984 controls with T9/17/31/61, L4T^2 and fast guard subsets all or near first ending height;44750 nonempty guard bins.58841 positive source incidences p>=T,56595 distinct (bin,label) incidences,2246 actual successive selected same-label pairs,1669 short with finite K=4,577 long.1978 actual four-root roughness/collision checks,44750 flux partition and guard width checks,56595 span/first-visit budget controls.2880 independent gap/sign/label patterns,47040 exact root collision tests;48 finite singular-factor average controls,21504 small-factor expansions,72632 weighted subset terms; maximum observed finite mean about8.5224, not a uniform analytic constant. The divisor-subset tests verify the Euler weights, weighted mean and conditional Markov bound; the proof of the uniform mean and its asymptotic tails is analytical. Example finite p13,q557->559,H7242->7266,e1=+1,e2=-1, local ending flux2: the second q is composite, so this is not a twin witness. Counts overlap across selections, thresholds and roots. Finite runs do not realize the asymptotic near-minimal-support hypothesis or verify its constants. All assertions passed. No Lean executable/kernel verification, external novelty claim or final contradiction. Main and sibling branches unchanged.
