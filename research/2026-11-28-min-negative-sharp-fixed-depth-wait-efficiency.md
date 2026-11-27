# Negative MIN: sharp fixed-depth completed-wait efficiency and height-accumulating non-twin trajectories

2026-11-28 JST, Issue #10. Continuation of a95c55dad72905a79af2b201a247845f0cf15aa6. Checked core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a, 614 declarations unchanged. Intermediate goal 4.85 and ultimate unconditional twin infinitude. Previous sequential chains had age G/2 at the last reset, with the long horizon almost entirely supplied by terminal quiet time. Here derive the sharp limiting completed-wait/gain ratio for each fixed number of large-label actual firings, construct matching height-accumulating histories, and obtain low-gain trajectories with a substantial completed-time fraction and NO twin center visited. No new Lean compile or independent human review.

## 1. Exact finite-depth upper bound from height quantization

Write h=x/2+n for the signed-clock height (half of height2 in the checked core), h0=3 at an even canonical birth. Let p_1,...,p_k be the successive actual winning primes of a complete prefix ending at the k-th firing, all >=11. Let w_j be the positive full wait since birth or the preceding firing. Let G=sum(p_j-1), W=sum w_j. The checked height identity gives
    h_j=h_(j-1)+w_j-(p_j-1)/2,    W=G/2+h_k-3.
The calendar gives 1<=w_j<=2p_j. The verified tick_height_pin and nonnegative height imply
    h_j=m_j p_j+c_j,  m_j integer >=0,  c_j in {0,3}.
Indeed height2 is even and p_j is odd, so the coefficient in its pin is even; with p_j>=11, a negative m_j is incompatible with h_j>=0. The even-clock branch has c=0, the odd-clock branch c=3. Thus
    h_j <= h_(j-1)+(3p_j+1)/2.

Define a_1=1 and a_j=2a_(j-1)/(a_(j-1)+1/2) for j>=2, equivalently
    a_j=3/(2+4^(-(j-1))).
For all such actual prefixes, the following EXACT upper holds:
    h_k <= a_k sum_(j<=k)(p_j+3)=a_k(G+4k).              (1)
At j=1, h1<=3+(3p1+1)/2<2p1 for p1>=11, so m1<=1, h1<=p1+3. Suppose (1) through j-1 and write a=a_(j-1), b=a_j, S=sum_(i<j)(p_i+3), p=p_j, m=m_j, c=c_j. If m<=1, h_j<=p+3<=b(S+p+3). If m>=2, then
    (m-3/2)p+c <= a S+1/2.
Since 1<=a<3/2, b/a>1, b>=1, and
    m <= b[1+(m-3/2)/a]  (equality at m=2),
we have
    h_j=mp+c
       <= b(S+p)+b/(2a)+c(1-b/a)
       <= b(S+p+3).
This proves (1) by induction. Therefore, putting C_k=1/2+a_k,
    W <= C_k G + 4a_k k - 3.                            (2)
In particular for minimum label >=P>=11,
    W/G <= C_k + 6/(P-1).
The additive error is uniform in k; for very large k the direct bound W<=2G+2k is stronger than the displayed additive error. This theorem is for canonical prefixes with ALL completed labels >=11; it must not be applied unchanged to a noncanonical subblock or a history with smaller labels.

The limiting upper constants for fixed k are:
    k=1: 3/2
    k=2: 11/6
    k=3: 43/22
    k=4: 171/86
    k=5: 683/342
and C_k increases to 2 with deficit (3/2)4^(-(k-1))/(2+4^(-(k-1))). No potential computation is required for this new large-label fixed-depth upper. It supplements rather than supersedes the all-label mod2310 certificate W<=17G/8+395/12.

## 2. A sufficient exact CRT prescription for accumulating height

The upper proof suggests taking m_1=1 and m_j=2 for every j>=2, instead of resetting height to 0 or 3 after each firing. All desired firings use the even-clock branch. For a fixed k, put m_1=1, m_j=2 (j>=2). Choose distinct odd primes p_j with p_1,p_2=7 mod12 (only p_1 for k=1) and p_j=1 mod12 for j>=3. Let
    d_i=sum_(j=i+1)^k(p_j-1),  x_i=x+d_i,  A=x_0,
    h_0=3, h_j=m_j p_j,
    w_j=h_j-h_(j-1)+(p_j-1)/2.
Assume 1<=w_j<=2p_j. Require x_j=2m_j p_j mod 4p_j. Then n_j=h_j-x_j/2 is 0 mod2p_j, so is an even eligible clock for p_j at source x_(j-1), because x_(j-1)+1=x_j+p_j. The congruences modulo 4 are compatible: x_0=0 mod4, x_1=2 mod4, and x_i=0 mod4 for i>=2, as prescribed by the residues of the p_j. Modulo p_j the condition is just x=-d_j mod p_j; all pins are independent. Require x=0 mod3, and every p_j=1 mod3, so all x_i are canonical spatial centers (though their actual heights after firing are NOT the birth height).

Pin-exclusion condition for each j:
    d_i-d_j+s !=0 mod p_j, for 0<=i<=k, s in {-1,+1},
    EXCEPT (i,s)=(j-1,+1).
At the exception divisibility is intended. If every other odd prime <=Z=2T+8 is excluded from both neighbors at every x_i, then the entire planned chain is actual through any chosen T>=sum w_j. To see this inductively, the current phase's sole possible eligible label before age T is p_j: the general canonical height bound on a winner through age t is p<=2t+7, from nonnegative postheight and h_pre<=3+t-1. The pin gives the first positive eligible wait w_j, since the static even clock has period 2p_j and 1<=w_j<=2p_j. No other label <=Z divides its neighbors, and no larger label can actually fire within the age bound. Hence the actual winner is p_j, the arrival is exactly (x_j,n_j), and the induction continues. At x_k=x all p_j are excluded by the pin-exclusion condition; excluding all other odd primes <=Z gives a stationary tail through T. The total completed time is W=G/2+m_k p_k-3, NOT G/2 as in reset chains. This is a construction of actual least-prime events, not just a relaxed height path.

## 3. Match the fixed-depth upper with many polynomial-scale actual prefixes

Fix k>=1 and an arbitrarily small accuracy epsilon>0. Introduce small fixed eta>0. Choose target label ratios r_1=1, r_j=m_(j-1) r_(j-1)/(1/2+eta) for j>=2. Thus r_j strictly increase for small eta. As eta tends to 0 these approach 1,2,8,32,... (r_j=2*4^(j-2) for j>=2). Choose pairwise disjoint fixed narrow relative intervals [r_j(1-tau),r_j(1+tau)] around the ratios, with tau>0 sufficiently small depending on k,eta. Let P=R^delta, where delta>0 will be a sufficiently small FIXED constant. Choose p_j in these intervals scaled by P. For j>=2 choose tau so h_(j-1)/p_j is in (1/2+eta/2,1/2+3eta/2). Then
    w_j=(5/2-h_(j-1)/p_j)p_j-1/2
lies between (2-2eta)p_j and 2p_j for large R; w_1=(3p_1-7)/2 is positive and <=2p_1. In the limit eta,tau->0,
    h_k/sum p_j -> a_k,
since for k>=2 the ideal sum of scaled labels is (1+2*4^(k-1))/3 and ideal final height is 4^(k-1); for k=1 the limit is 1. Thus choose eta,tau sufficiently small that every tuple in these fixed bands has W/G>=C_k-epsilon for large R. In particular W,G are both comparable to P with constants depending on k,epsilon.

We now prove abundance of such tuples and actual roots, rather than relying on CRT moduli containing all primes through Z (which would be far larger than polynomial R). Let B0 be a fixed multiple of 12 containing all odd primes <=2k+3. At odd q>=5 dividing B0 impose p_j=1 mod q, x=0 mod q. For mod4 use the pattern of section 2, and mod3 use p_j=1,x=0. For p_j the resulting progression class mod B0 is reduced, hence fixed-AP PNT gives >>P/log P labels in each interval. The pin-exclusion condition removes only O_k(P^(k-1)) ordered tuples: for a fixed unwanted congruence, the cases i=j and i=j-1 are automatic nonzero, and any other difference of suffix sums contains another label linearly with coefficient +/-1. Fix all labels except that one, including p_j. It is then restricted to one residue modulo p_j, and its interval has length O_k(P), while p_j>=c_k P. There are only O_k(1) candidate integers for that remaining label. The labels are distinct by disjoint bands. Thus >>P^k/L^k tuples remain, L=log R. For k=1 there are no such unwanted congruences. Constants may depend on k,epsilon,delta.

Choose also a common horizon T=ceil(C P), for a fixed constant C sufficiently large that T>=W for all tuples; choose C and label bands more specifically in section 4. Force an extra prime r in a fixed interval [C'P,2C'P] where C'>2C+10 and exceeds every label band, by pinning x=-1 mod r. This gives a composite x+1 for x of order R, and ensures r>Z for large R. It does not interfere with any clock or small-prime pin. There are >>P/L choices of r. For each admissible tuple and r the full CRT modulus B=B0*r*prod_j p_j is comparable to P^(k+1). The CRT class exists by coprimality and the mod4 pattern.

Sift x in that class and in [R,2R-d_0] so A is in the slab. The class contains X asymptotic to R/B integers. For any free odd q<=Z, q not dividing B, forbid all the residues x=-d_i+/-1 (equivalently forbidden neighbor zero); on the parameter indexing this class the count nu(q) is at most Kappa=2(k+1). Every such q is >2k+3, hence nu(q)<q. For pinned primes in B0 all neighbors avoid them, and each p_j has precisely its intended incidence. The extra r is above Z. For free squarefree d the bad count is nu(d)=prod nu(q), exact CRT remainder <=nu(d), density nu(d)/d. The one-sided dimension-Kappa product bound holds uniformly in tuples, by Mertens and the convergent O_Kappa(1/q^2) correction, omitting primes only decreases the upper product; the local product V(Z)>>_k L^(-Kappa). The ordinary fixed-dimensional combinatorial lower fundamental lemma at level D=floor(X^(1/2)) gives a positive fixed fraction of X V(Z) when log D/log Z is sufficiently large depending on Kappa. Choose delta small enough that (1-(k+1)delta)/(2delta) exceeds that required constant with room, and (k+1)delta<1. This choice is uniform over the fixed label bands. Remainders sum at most sum_(d<=D)Kappa^omega(d)<<D log^(Kappa-1)(2D), via the elementary fixed divisor moments, and are o(X/L^Kappa). Thus each CRT class contains >>R/(B L^(2k+2)) roots satisfying the required roughness. This is the same elementary interval lower-sieve mechanism already used in the previous reset work; no new large-modulus prime distribution theorem or growing-dimensional uniformity is assumed.

Sum over the >>P^k/L^k tuples and >>P/L choices of r. With B comparable to P^(k+1), total tuples/x/r >>R/L^(3k+3). The actual first k labels uniquely determine the tuple from A by deterministic evolution, and x=A-G is then fixed. The auxiliary r is a prime divisor of x+1 in [C'P,2C'P], so at most log(2R+1)/log(C'P)=O_delta(1) choices per A. Dividing by this constant proves that for ALL sufficiently large R there are
    >>_(k,epsilon,delta,C) R/L^(3k+3)
distinct canonical A in [R,2R] having exactly k events by T, W/G>=C_k-epsilon, and W,G comparable to R^delta. Every prefinal source has composite neighbor divisible by its prescribed p_j of order P=o(R), and final x has composite neighbor divisible by r. Hence NO twin center is visited at any time through T. A future event at the final center is guaranteed within 2r ticks of any current clock, because of the static r calendar. In particular the terminal quiet phase exits at age O(P), even though it lasts through T. This additional pin eliminates the possibility that the construction is simply taking advantage of already existing twin centers. The exponent delta depends on k and accuracy and is small; there is no claim of delta=.249, .285 or near .5 for these completed-time families.

This proves sharpness of (2) in the following precise sense: for each fixed k, as the required minimum label P0 tends to infinity, the supremum of W/G over actual canonical k-event prefixes with all labels >=P0 tends to C_k. Upper follows from (2), and lower from the construction with any fixed epsilon, R arbitrarily large. In particular the height relaxation's extremal bound is realized asymptotically by actual arithmetic trajectories. With k increasing after the fixed-depth limit, the supremum approaches 2. An alternative simpler construction with m_j=j and p_j ratios near (j-1)/(j-3/2) gives W/G>=2-O(1/k)-epsilon; it motivated the sharper m=2 recurrence, but is not required for the theorem.

## 4. Low gain with substantial completed time, and the remaining square-root requirement

Fix a target gamma with 0<gamma<1/2 (e.g. gamma=1/3). Let A0=sum r_j. Choose T=ceil((1+tau)A0 P/gamma), hence G<=gamma T, G/T>=gamma(1-tau)/(1+tau)-o(1). Because W<=2G+2k and gamma<1/2, W<T for large R. The construction in section 3 applies with this fixed C, including the extra composite pin r. It gives
    W/T >= (C_k-epsilon)*gamma(1-tau)/(1+tau)-o(1).
For any prescribed accuracy choose k sufficiently large, then eta,tau small and finally delta sufficiently small, all fixed. This yields at least c R/L^(3k+3) actual canonical roots at a common polynomial horizon T comparable to R^delta, with G/T<=gamma and W/T>=2gamma-epsilon' for any fixed epsilon'>0. Every visited center is non-twin. For gamma=1/3, completed waits occupy arbitrarily close to 2/3 of total age; the final stationary tail contributes about 1/3, in contrast with previous reset constructions whose completed fraction tends to zero. For large-label histories with G/T<=gamma the elementary W<=2G+2k shows this completed fraction is asymptotically optimal as min label->infinity. The ratio bound by itself at a small polynomial horizon is therefore demonstrably NOT a twin certificate.

Apply (2) instead at T=ceil(8S), S=sqrt(2R+1), for an actual canonical root in [R,2R] with exactly k>=1 completed events, all >=11. If the endpoint is non-twin, its final incomplete wait is <2S, since one neighbor is composite and has least factor <=S; all centers remain large by the height gain bound. Thus
    C_k G_T +4a_k k-3 >= T-2S.                            (3)
A strict violation certifies a twin endpoint. For fixed k and T->infinity the limiting non-twin gain threshold at T=ceil(8S) becomes
    3/(4 C_k),
rather than the previous unconditional all-label 6/17 from the mod2310 certificate. For k=1,2,3,4 the new conditional-on-depth-and-label thresholds are respectively 1/2,9/22,33/86,129/342, tending to 3/8 with k. Use the exact additive inequality (3) or a fixed strict margin, not a vanishing-margin comparison to a limiting threshold. At k=0 an idle root through T>=2S is already twin. More generally the elementary complete-wait estimate forces I/T>=1-2gamma-o(1) for large-label low-gain histories (I=T-W final idle); this shows no collection of completed large-label phases alone can give a ratio below 1/2. The new sharp constructions attain the best possible fraction but cannot eliminate the final idle needed for square-root certification. We have not constructed prefixes satisfying (3)'s strict violation at square-root scale. The fixed-k upper theorem holds for all actual paths under its hypotheses, without a model of random factors; no claim that almost all actual paths satisfy the hypotheses. The earlier all-label 6/17 criterion remains available.

## 5. Independent finite verification and scope

Two runnable exact BigInt audits, both executed in ECMAScript and pinned remote contents read back:
- research/lean/negative_min_height_accumulation_audit.mjs @9c58680f16e4bb94b5aa33418631db148d59fe16, blob 12e5d223cc6394bb6ebcd99126f50464b664ca91. First m_j=j construction: 75 tuples tried, 6509 pin checks, 87 local admissibility checks, 10502 CRT steps, 28 actual firings, 46908 literal ticks, 29857 eligible-candidate checks, 46908 height ledger checks, 17051 final idle ticks. At k=7 labels 367,691,883,1051,1171,1291,1399, W=13213,G=6846,T=20538, W/G=1.930032..., W/T=.643344. No auxiliary composite pin in this first audit; no non-twin-only assertion for these examples.
- research/lean/negative_min_fixed_depth_efficiency_audit.mjs @1a07b8b369786b7aa2d1205b9b290bf77a5d5ca0, blob e2b711197ebf3e2959cfd91462a4844cc1f51221. Improved m_1=1,m_j=2 construction for k=1..5, with extra forced final composite factor. 123 tuples tried,5473 pins,86 local checks,9943 CRT steps,15 literal events,47286 literal ticks,30885 eligibility checks; independent relaxed height DP checks 189672 possible transitions (2966 retained minimal-cost height states over depths1..8, primes11..97), all satisfy (1). At k=3, labels 79,151,601, waits115,298,1200, W=1613,G=828,T=2484, W/G=1.9480676 (limiting ideal C3=1.954545...), W/T=.649356, final forced composite factor4987. At k=4, W=6113,G=3108,T=9324,W/G=1.9668597, final factor18661. k=5 W/G=1.962569, not monotonic empirical optimality; labels chosen for CRT compatibility and finite ranges, not optimized to the limiting ratio. Actual roots generated by full finite CRT with all primes through Z pinned, using BigInt; e.g. k=4 root has 8041 digits. Literal recurrence checks ALL possible eligible divisors up to 2T+8, using the already checked height bound to exclude larger primes. These finite examples are not at polynomial time relative to their enormous root magnitudes. The separate interval sieve proof of section 3, not the finite CRT samples, supplies the polynomial-scale abundance. Future r firing time is only an upper bound on next event, not a claim r wins it. All tests pass.

Analytic inputs: fixed-AP PNT, Mertens, and fixed-dimensional lower combinatorial fundamental lemma as already verified and cited in a95c55d section7 (Tao 254A Notes4 Lemma17/Cor19, Kurlberg-Lester-Rosenzweig Superscars II section2.1). No new external literature search, no novelty claim for these standard inputs. 4.85 remains open. Exact fixed-depth large-label extremal theorem is a new paper deduction, with no new kernel or independent human review. Main/sibling branches untouched. Next direct research: constrain actual high-depth mixed-label trajectories or develop near-square terminal-quiet witness, using (2)-(3) for fixed-depth cases; the sharp completed-time construction at small powers cannot by itself bridge the terminal roughness barrier.
