# Dense source-only pair sieve and transport through consecutive high singular returns

2026-11-26 JST. Continuation of 559544a638c8e35301170b759c714dd4be65c1d0 (growing-depth transport), using the earlier ordered-descent pair sieve and rational-line crossing notes. Paper deductions and executed finite arithmetic audit; not Lean verified, no claim of novelty or twin infinitude. No formal target or canonical branch changed.

## 1. Two rough offsets, fixing only the source label

Consider offsets in [12,CY], C>1 fixed, and thresholds T1>=T2>=17 tending to infinity, with 0<=B<=T1/2. Count tuples (x,p,e,E) with odd prime p>=T1, p<=8 sqrt(CY+1), e in {-1,1}, x even, x=p k+e, 0<=E<=B even, y=x+p-1+E<=CY. Require all odd prime factors of both x-1,x+1 to be >=p/8 and all odd factors of both y-1,y+1 to be >=T2/8. The second offset need not have a specified selected label or even a specified time. No restriction on the size of the set of labels used by the paths is imposed.

Put D=p+E-1. For fixed p,e,E, the four integer forms in k are

    k, p k+2e, p k+e+D-1, p k+e+D+1.

The first two are rough at odd primes <p/8 and the last two at odd primes <T2/8. At ell>5, ell!=p, the first two forms have two distinct roots. For the four forms the distinct root count is exactly 4-nu_ell, with

    nu_ell=2*1_(ell|D)+1_(ell|D-2)+1_(ell|D+2).

This follows by the invertible change from k to x mod ell: the roots in x are +/-1,-D+/-1. Define S(p,E)=product_(ell>5)(1-1/ell)^(-nu_ell), the same finite singular factor as in the earlier ordered-pair note. D,D-2,D+2 are positive for our p and their product is O(p^3).

Here we do not fix a target label r, and do not impose a modulus pr. Consequently the variable k has available interval length O_C(N), N=Y/p >>_C p even at the square-root scale. Enlarge to a positive integer interval of length ceil(CY/p)+O(1) if needed. Choose z=floor(p^(1/10)); for sufficiently large p it lies below p/8. Use sieve primes 5<ell<=z. For ell<T2/8 use all four forms with g(ell)=(4-nu_ell)/ell, and for the other primes use just the first two with g(ell)=2/ell.

The explicit Selberg quadratic form in research/2026-11-26-min-primorial-record-displacement-and-supply.md gives weights |lambda_d|<=d, main term interval length/G(z), G(z)=sum_(d<=z) product_(ell|d) g(ell)/(1-g(ell)). Squarefree congruence counts have error O(rho(d)), rho(d)<=d; expanding the square gives error O(z^6)=O(p^(3/5)). To lower bound G, truncate the Euler product to primes <=z^eta for a sufficiently small fixed eta>0. The normalized squarefree product weight has mean log d = sum g(ell) log ell <=4 sum (log ell)/ell = O(log(z^eta)); at least half lies at d<=z by Markov. By Bernoulli's inequality, (1-g(ell))^(-1)>=(1-1/ell)^(-2) at all these primes and has the extra factor (1-1/ell)^(-(2-nu_ell)) at the four-form primes. The omission from the generic extra product costs at most S(p,E). The second product extends to min(z^eta,T2/8) up to a strict endpoint; since p>=T2, the log of that minimum is >> log T2. Mertens therefore gives

    G(z) >> log^2 p log^2 T2 / S(p,E).

Absorb the O(p^(3/5)) error into N/(log^2 p log^2 T2), since N>>p and T2<=p. For each fixed tuple p,e,E the candidate count is

    O_C(Y S(p,E)/(p log^2 p log^2 T2)).               (1)

The argument requires only the earlier elementary Selberg construction and the standard Chebyshev/Mertens estimates; no equidistribution of the MIN orbit and no modular hyperbola estimate. Bounded cutoffs can be absorbed by enlarging constants.

## 2. Average the exceptional factors over the source primes

We show, uniformly in dyadic source bands P<=p<2P and in fixed even E<=P/2,

    sum_(P<=p<2P, p prime) S(p,E) << P/log P.           (2)

This removes all log-log losses from the all-label count. For each p, the contribution of ell>log(3P) to S is bounded absolutely: the product D(D-2)(D+2)=O(P^3) has at most O(log P/log log P) such prime divisors, each reciprocal at most 1/log(3P), and exponent <=2. Retain ell<=log(3P), ell>5. Write each factor as 1+b_ell(p), a nonnegative function supported on three residue classes of p. Its sum over the residue classes is

    A_ell=((1-1/ell)^(-2)-1)+2*((1-1/ell)^(-1)-1)
         =4/ell+O(ell^(-2)).

Expand the product over squarefree d composed of retained primes. The nonnegative coefficient b_d(a) on a class mod d has total over a equal to product A_ell by CRT.

For d<=sqrt P, each reduced class a mod d contains O(P/(phi(d) log P)) primes of [P,2P]. For completeness this upper bound follows from the same one-dimensional Selberg form applied to a+d k on an interval of length P/d+O(1): use sieve primes <=z=P^(1/24) not dividing d, density 1/ell, truncated Euler-product lower bound G(z)>>log P * phi(d)/d, and error O(z^6)=O(P^(1/4)), absorbed since P/d>=sqrt P. The lower bound on G follows by the same normalized-weight argument in section 1, and omitting prime divisors of d costs at most d/phi(d). A nonreduced class contributes no prime because all prime divisors of d are <P. Thus the total small-d contribution is at most

    O(P/log P) product_(5<ell<=log(3P)) (1+A_ell/(ell-1))
    = O(P/log P),

since the infinite product converges.

For d>sqrt P use the count of ALL integers in each class, <=P/d+1<=sqrt P+1. The sum of all coefficients over all d and a is product(1+A_ell)=O((log log P)^4) by Mertens. The resulting contribution O(sqrt P (log log P)^4) is negligible. This proves (2), uniformly in E and the band. It uses prime primality only on the SOURCE label, not target distribution.

Summing (1) over p in a dyadic band and using (2) costs O_C(Y/(log^3 P log^2 T2)) for each fixed E and sign. The dyadic sum starting at T1 is O(1/log^2 T1) for the log^-3 P part. Summing E and signs gives the full count

    # (x,p,e,E) <<_C Y (B+1)/(log^2 T1 log^2 T2).       (3)

Since B<=T1/2 the average proof is uniform in every contributing band. In particular equal thresholds T1=T2=T give O_C(Y(B+1)/log^4 T), independent of source support, target support, label ratio, or proximity to sqrt Y. The object counted is a tuple of offsets/first label/relay, not the number of all possible source or target times. It is not a physical-gain bound on one ray: multiplying by large labels could remove the saving.

## 3. Application to consecutive singular returns in a low-deficit strip

Use the strip graph of the preceding note with 0<=d<=D0, D0 even >=6, u<=CY and genuine events cut by p<=u/2+1, keeping only edges whose endpoints remain in the strip. Write L=D0/2+1 and Q=2 product of odd primes <=max(3,D0/2). A singular arrival means d'=0 with even arrival time, or d'=6 with odd arrival time. The prior nonsingular-excursion lemma gives a physical gain <=Q between a singular state and the source of the next singular-arrival event, if that next arrival exists.

Let T>=max(17,2D0+2,2Q). A strip event with p>=T has w>=(p-1-D0)/2>=p/4 by nonnegative post-deficit. Consequently all neighboring prime factors are >=p/8. The source-label cut implies the selected neighbor is composite and p<=8sqrt(u+1). Such an event must have a singular arrival by the exact arrival divisibility 2p|(d'-c), c in {0,6} according to parity.

Mark an event with p>=T whose singular arrival is followed by a next singular arrival with label r>=T. The relay consists solely of nonsingular arrivals and its physical gain E is <=Q. Apply (3) with B=Q and T1=T2=T. For each candidate source offset there are at most L source time choices. Hence the set S of distinct marked first-event source states has

    |S| <<_C L Y (Q+1)/log^4 T.                       (4)

This bound is across the ENTIRE local graph, not a separate sum over different reset rays. No assumption of sparse labels or comparable scales is needed. Both high events must be before first record when this is applied to a true reset path.

Let S' be the singular states whose next singular arrival is by an event in S. Such an origin lies within Q behind the source event and at most two singular states exist per even offset, giving

    |S'| <= (Q+2)|S| <<_C L (Q+2)^2 Y/log^4 T.        (5)

Thus a path from a deficit-6 integer reset encountering two consecutive high singular returns must first reach S' on the compressed singular-state graph. This does not imply that high returns generally occur consecutively: lower-label singular returns can intervene and can themselves carry significant physical gain.

## 4. Growing-width, growing-return transport

Here is a quantitative application even allowing D0 to grow, with D0=o(log log log Y), D0 even >=6. The elementary Chebyshev upper estimate for prime logarithm sums gives log Q=O(D0). Thus Q=(log log Y)^{o(1)}, L=(log log Y)^{o(1)}. Set T=exp((log Y)^theta), 0<theta<1, or T=Y^epsilon for fixed epsilon>0 (write theta=1 in the latter case). All hypotheses of section 3 hold eventually. Equation (5) gives |S'|=O(Y/(log Y)^b) for every b<4theta.

On the induced singular graph J(y)<=(Q+2)I(y) by the previous note. Put M=L ceil(K log log Y), M'=(Q+2)M with K a sufficiently large fixed constant. The previous elementary exceptional-mass estimate gives

    sum_(J>M') (1+J)
        <=(Q+2) sum_(I>M)(1+I)
        <<_C (Q+2) L Y (log Y)^(1-K log 2/2).

For h<=gamma log log Y/log log log Y, log M'=(1+o(1))log log log Y and (h+1)(M')^h<=(log Y)^(gamma+o(1)). Apply the first-bad transport inequality to the induced graph and S'. For any gamma<4theta, choose b strictly between gamma and 4theta and K with K log2/2>1+gamma. It follows that

    |Anc_{<=h}^{singular}(S')|=o(Y).

In words, among integer reset seeds with initial offset in [Y,2Y], C>=2, all but o(Y) cannot start a pair of consecutive high singular returns after at most h preceding singular returns, provided the whole prefix and pair remain in the strip, below CY and before first record. The pair adds two more singular returns. The estimate permits slowly growing strip width and a growing count of returns. For fixed strip, the corresponding exponent threshold for a single high departure from the earlier paper was 2theta, rather than 4theta for these pairs. This is an exclusion of a particular two-return pattern, not a bound on all high departures or on strip escape.

## 5. A second application without a low-deficit strip

Consider a non-twin upward crossing of a fixed rational line A u-K v=0 with coprime A,K, K odd, 1/2<A/K<1, in the sense of research/2026-11-26-min-primorial-rank-lines-and-crossing-mergers.md. It has w>(p-1)/2, so all neighbor prime factors are >=p/8 for p sufficiently large and p<=8sqrt(u+1). If p>=T1 and there is a later pre-offset y=x+p-1+E, E<=B, with both y+-1 having all odd prime factors >=T2/8, it fits section 1 whether or not its deficit is low. The latter roughness holds, for example, if the later event is upward in deficit with label >=T2. For each x,p,e there are O_(A,K)(1) crossing destination times, by the modular overshoot formula of the rank-line note. Therefore the set of distinct such crossing destination states is

    O_(A,K,C)(Y(B+1)/(log^2 T1 log^2 T2)).

For T1=T2=T and B fixed, a positive proportion of reset origins whose first crossing has this additional nearby-rough-offset property would have to merge into O(Y/log^4 T) crossing destinations. Cauchy-Schwarz then forces a basin of size Omega(log^4 T) and Omega(Y log^4 T) ordered distinct-origin collisions. The earlier single-crossing supply result required only Omega(log^2 T) merging. This strengthens that conditional merging burden without assuming any bound on source support or event count. It does not establish that a first crossing must have such a nearby rough offset.

## 6. Executed arithmetic audit

Source research/min_primorial_dense_pair_audit.py at eebb4852c90c575a689b5fc6a6031931ac17d821, remote blob a71f91a3f9b2072526e1e0df72da433dbdfdff71 equals the locally executed git hash-object. Requires SymPy and sibling min_primorial_record_supply_audit.py. Run:

    python research/min_primorial_dense_pair_audit.py 100000

All 6,048 local root comparisons passed (two and four forms, all degeneracies). Full local strip graphs at u<=100000, including arbitrary envelope-valid states, pre-record source cut, both endpoints inside strip/cap:

    D0    vertices   edges     Q
    6     199980     136298    6
    12    349965     264277    30
    24    649920     528540    2310

For each threshold, the counts (T, |S|, |S'|) of actual source states and preceding singular states as in section 3:
- D0=6: (17,1911,907), (31,537,243), (61,156,68).
- D0=12: (26,1438,486), (31,1070,328), (61,322,100).
- D0=24: (50,977,199), (61,755,151).

All 7,166 pair checks and 7,365 rough-form exclusions passed, as did the singular excursion bound and |S'|<=(Q+2)|S| for each threshold. Counts over overlapping thresholds are not independent populations. Small finite thresholds in this diagnostic need not meet T>=2Q; they test the exact pair and roughness conditions, not the asymptotic estimate (3). The sieve and transport deductions were not numerically fitted to these counts.

## 7. Remaining target

This replaces a sparse-support hypothesis by a four-form count of short-relay high pairs on the whole local graph, and covers near-square-root labels. But it does not bound physical gain in arbitrary long low-deficit paths or all high-rank crossings: pairs can be separated by low-label singular returns, and the number of singular returns can exceed the growing-depth range. No upper bound on total pre-record displacement G(r) or proof of unbounded twin records follows. The next specific issue is how to control the physical gain and ancestor mass of the intervening low-label singular returns, rather than merely count high-high pairs. No Lean kernel verification performed.