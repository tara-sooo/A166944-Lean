# Decreasing-prime staircases: constructive canonical lower bounds and high-section local supply

2026-11-28 JST. Issue #10. Base c6ab2f37a97dccc5739c5b17684c63464b3c0a20. The previous work established necessary polynomial-depth and local active-section conditions for M85 but did not construct the local connectors. This checkpoint changes direction to an explicit chronological construction. It prescribes arbitrarily many (fixed in the polynomial-scale theorem) decreasing prime labels with strict increasing postevent heights, proves their exact canonical first-height reachability by congruences and an elementary lower sieve, sums over prime tuples with bounded reverse ambiguity, and lifts the construction to high local sections at a growing subpower scale. These are genuine lower bounds, with stated scale/density limitations. They do not prove the density-scale lower at H=R^.4, M85, or twin infinitude. No new Lean compilation or independent specialist review.

Notation: L=log R. Even center x, signed clock n, height h=x/2+n. Canonical birth at A in [R,2R], 6|A, h=3. At a positive tick, sign s=+1 if n' even, -1 if n' odd; p divides x+s and n'=0 mod2p for plus, p+2 mod2p for minus. Least eligible odd prime wins. Moving transition x'=x-p+1, h'=h+1-(p-1)/2; idle increases h by1. At a preheight h the candidate p divides 2h+3 (plus) or 2h-3 (minus), hence p<=2h+3. A first-H path has age H-3+G/2, G=A-x. All our actual finite-slab constructions have H=o(R) and G=O(H), so the negative clock and physical position boundaries are not reached.

## 1. Design a strictly ascending postevent staircase

Fix an integer k>=1. All constants in sections 1-5 can depend on k, which is fixed before R tends to infinity. Put
    Q=4 product_(odd prime l<=max(5,2(k+1))) l.
Choose k primes p_1,...,p_k all =1 mod Q, with p_1 asymptotic up to fixed constants to a large scale X. Let g_i=p_i-1, G_i=sum_(j<=i)g_j, G_0=0. Choose odd positive multipliers a_i, intended postevent heights h_i=a_i p_i, as follows:
    a_1=1,
    a_2=3,    .54<p_2/p_1<.55,
    a_3=9,    .394<p_3/p_2<.396,
when those indices exist. For i>=4, if a=a_(i-1)>=9, choose an odd b=a_i and an open interval of ratios
    .39<r=p_i/p_(i-1)<.46,
    1.35 < b-a/r <1.45.                                  (1)
Such a nonempty interval exists: the range (a/.46,a/.39) has length >3.5 for a>=9 and therefore contains an interval (b-1.45,b-1.35) for some odd b. One may choose fixed subintervals strictly inside these inequalities. Then b>a, and the induction continues. This choice is made on real reference ratios and hence can be fixed for a given k, without dependence on X. All decimal constants here denote exact rationals.

For the first event use the preceding arrival height h_0=3. Define required full waits
    w_i=h_i-h_(i-1)+g_i/2.
All are positive even integers since each h_i is odd and g_i/2 even. For large X,
    0<w_i<=2p_i,
    h_i-h_(i-1)>g_(i-1)/2   (i>=2).                      (2)
For i=1, w_1=(3p_1-7)/2. For i=2, height gain=(3r-1)p_1>=.62p_1 and height gain/p_2=3-1/r<1.5. For i=3, height gain=(9r-3)p_2>.546p_2 and height gain/p_3=9-3/r<1.5. For i>=4, height gain/p_i=b-a/r in (1.35,1.45), and height gain>1.35*.39 p_(i-1)>.5p_(i-1). Thus w_i<=2p_i. Inequality (2) means the next postevent height surpasses the preceding prefire maximum, not just its postevent height. In particular later stages repair the entire previous downward height jump.

The total gain in all subsequent events after p_i is strictly less than p_i-1 for sufficiently large X:
    sum_(j>i) g_j < p_i-1.                               (3)
For i>=2, the ratio bound .46 gives sum_(j>i)p_j<=.46/(1-.46) p_i<.852p_i. For i=1, sum_(j>1)p_j<=.55(1+.396/(1-.46))p_1<.954p_1 (omit nonexistent stages); the strict margins absorb the additive1. In particular total G_k<2p_1. These strict geometric inequalities do not use prime distribution.

## 2. Choose prime intervals with no unintended reuse of a label

Set the canonical birth A=x_0+6, where the post-prefix center x_0 will satisfy x_0=30 mod60 (equivalently x_0=2 mod4, x_0=0 mod3 and5). The exact first three ticks are: idle, p=5 on the minus clock, p=3 on the plus clock. Indeed the first even clock at height3 has candidate factor only3, which cannot divide A+1. At the next tick the preheight is4, the minus candidate is5, A-1=x_0+5, and n'=2-x_0/2=7 mod10. It lands at x_0+2,h=3. The next plus clock is n'=3-x_0/2=0 mod6, with 3 dividing x_0+3, so p=3 wins and the state is x_0,h=3. No larger prime can preempt either moving tick, by the exact height candidate bound/least rule. This provides an actual canonical prefix, not an invented state.

The intended successive centers after the prefix are
    x_j=x_0-G_j,  j=0,...,k.
For p_i, prescribe x_0=G_(i-1)-1 mod p_i, so x_(i-1)+1 is divisible by p_i. For every earlier intended center x_j, j<i-1, forbid p_i dividing either
    S=G_(i-1)-G_j,  or S-2.
These are nonzero positive integers (for sufficiently large X). For fixed preceding primes, each has only O_k(1) prime divisors of size comparable to X, since their sizes are O_k(X). Thus only O_k(1) p_i candidates are lost in any fixed relative interval. For a later center x_j, j>=i, the residue modulo p_i is
    x_j = -sum_(i<l<=j)g_l mod p_i.
The sum is even and by (3) lies in [0,p_i-1), so cannot equal +/-1 mod p_i. Hence the pinned label is spatially eligible at exactly its intended source among these centers. This excludes both signs at the wrong sources, not only early plus-clock opportunities.

Choose one additional terminal prime q=1 mod Q in
    (1+1/(8a_k)) p_k < q < (1+1/(4a_k)) p_k.
Prescribe x_0=G_k-1 mod q. Exclude q dividing any G_k-G_j or G_k-G_j-2, j<k. Again only O_k(1) candidates lost, and q distinct from all p_i (for k>=2, q<p_(k-1); for k=1, q>p_1). Therefore q is eligible only at terminal center x_k among the main-word centers. All chosen prime labels are comparable to X for fixed k, with constants depending on k.

There are fixed open intervals I_1,...,I_k,I_q of positive length in the variable prime/X such that all their Cartesian-product choices satisfy the preceding strict ratio inequalities and the q interval inequalities. Construct a real reference tuple by choosing ratios in the interiors, then shrink a product neighborhood. This makes the prime intervals INDEPENDENT of the earlier prime choices; only the O_k(1) arithmetic exclusions depend on the prefix. The ordinary prime number theorem in a FIXED reduced residue class mod Q gives, successively,
    number of admissible prime tuples >>_k (X/log X)^(k+1). (4)
No uniform PNT for growing k or moduli Q is asserted. Only fixed k is used when summing polynomial-scale prime families. The diagonal argument later uses each fixed k after its own sufficiently large threshold.

## 3. A common terminal height and exact actual word

For all p_i and q, x_j/2 is odd, since x_0=2 mod4 and every g_i is divisible by4. All h_i odd. At the intended arrival x_i, p_i divides x_i and h_i, so n_i=h_i-x_i/2 is even and 0 mod p_i, hence 0 mod2p_i. The required wait w_i in (2) is positive and <=2p_i; therefore it is exactly the FIRST positive opportunity of p_i from the preceding arrival clock. The spatial uniqueness from section 2 rules out the other pinned labels at this source.

At the terminal center x_k, q is plus-eligible. Its stationary opportunity heights have the form ((4j+3)q-1)/2, j integer: these are congruent to -1/2 mod q and odd (as x_k/2 odd), the required even-clock parity. Because h_k=a_k p_k with a_k odd, and a_k(q-p_k)/q in (0,1/4), the first opportunity above h_k is
    J_q=((2a_k+1)q-1)/2.
Indeed J_q>h_k and J_q-2q<h_k. Its difference from h_k is greater than (p_k+1)/2 by a positive constant times p_k for large X. Choose a common H satisfying
    h_k+(p_k+1)/2 <= H < J_q.                            (5)
The real reference tuple has a nonempty open interval for H/X between these endpoints. Shrink the product boxes of section 2 if necessary and fix a common positive constant C_k in that interval, H=floor(C_k X), for ALL admissible tuples when X is large. Inequality (2) and (5) ensure every prefire height (including the final prefire h_k+g_k/2-1) is strictly below H. In particular the trajectory cannot already have hit H during a previous long wait. This distinguishes the construction from a HIGH arrival whose prefiring maximum exceeds its eventual target.

Set Z=2H+3 (integer). For each odd prime l<=Z not among the pinned primes p_i,q, impose
    x_0 != G_j +/-1 mod l   for all 0<=j<=k.             (6)
For l|Q choose x_0=0 mod l; every G_j=0 mod l, so all constraints hold. For other l, at most 2(k+1)<l residues are forbidden, so at least one allowed residue exists. All primes p_i,q are <=Z for large X. The constraints on selected labels are already consistent by section 2. For a center x_0 in the slab satisfying this finite CRT/sieve system, there are no other eligible labels <=Z at the main-word centers. Larger primes cannot fire while h<H by the exact height bound. Thus the actual chronological word is exactly
    5, 3, p_1,...,p_k
followed by idle to the COMMON first H in (5). At the terminal center
    qmin(x_k)=q,  G=A-x_k=6+G_k,  age=H-3+G/2.
In particular G=Theta(H) and G<=4H for large X, since H>=p_1, G_k<2p_1. Uniformly in k the reference construction has H=O(p_1): sum postevent increments <=1.5 sum p_i and final extra idle O(p_k), and sum p_i<2p_1. Hence total gain and age are comparable to H with absolute constants. Also
    qmin(x_k)/H <= C (0.46)^(k-2)    (k>=2),             (7)
with an absolute C (e.g. C=2), using p_2<.55p_1 and subsequent ratios <=.46. This ratio can be made arbitrarily small by choosing fixed k large. For fixed k it is a constant, not R^-delta.

## 4. Elementary lower sieve in each pinned progression

The modulus of fixed congruences is
    M=Q p_1 ... p_k q = Theta_k(X^(k+1)).
CRT gives one x_0 class modulo M satisfying x_0=2 mod4, x_0=0 mod each odd prime in Q, and all p_i,q pins. In [R,2R-6], the progression parameter interval has length N=R/M+O(1). For each free odd prime l<=Z not dividing M, the constraints (6) become nu(l)<=K=2(k+1) distinct forbidden residues of that parameter, with nu(l)<l since the small primes are included in Q. The sieve density
    V=product_(free l<=Z)(1-nu(l)/l)
is >=c_k/(log Z)^K. Indeed use nu(l)<=K, compare log(1-K/l) to K log(1-1/l) outside a fixed finite initial range, and sum O_k(l^-2); omitting pinned primes only increases the lower comparison product. Mertens gives the stated bound. This does NOT assume the forbidden shifts are pairwise distinct modulo every l; collisions are harmless to a lower bound on V.

For clarity, an elementary lower-bound sieve with explicit finite support is enough here. Partition the free primes into logarithmically geometric blocks
    Z^(2^(-j-1)) < l <= Z^(2^(-j)), j=0,1,...
stopping when the lower endpoint drops below the fixed small-prime threshold. The sums lambda_j=sum nu(l)/l are bounded by a constant depending only on k, by the ordinary prime reciprocal bound in these intervals. The survivor product V_j in each block is bounded below by a fixed positive c_k: for l>2K use log(1-nu/l)>=-2nu/l, and the finitely many smaller admissible primes contribute a fixed positive factor. Set even truncation n_j=2(A+j) for an integer A chosen large in terms of k. For block j let U_j be inclusion-exclusion through n_j factors and D_j the sum of positive violation indicators of subsets of size n_j+1. Pointwise
    U_j-D_j <= survivor_j <= U_j,  U_j>=0.
With independent uniform CRT residues, E D_j <=lambda_j^(n_j+1)/(n_j+1)!, so choose A so sum_j E D_j/V_j is as small as desired. The combined lower polynomial
    product U_j - sum_j D_j product_(i!=j) U_i
is pointwise <= true simultaneous survivor indicator: telescope the product difference using nonnegative upper polynomials. Its exact CRT expectation is >=V/2 for sufficiently large fixed A, since each E U_j is between V_j and V_j+E D_j, and the aggregate relative error is small. Expansion coefficients on squarefree divisors are 0,+1,-1, as the upper support and the one-overflow block supports are disjoint. All divisors in the polynomial obey
    d<= Z^B_k,   B_k=sum_(j>=0)(n_j+1)2^-j < infinity.
For a squarefree d, CRT gives at most nu(d)<=d residue classes, so its count differs from N nu(d)/d by at most d. Summed absolute remainder is O(Z^(2B_k)), uniformly in all prime tuples and shifts. Therefore the actual integer lower count in the progression is at least
    (N/2) V - O(Z^(2B_k)).                               (8)
This is the same elementary block-Bonferroni method as the earlier adaptive local-moment note, now for a fixed finite union of spatial forbidden offsets. No high-level prime distribution input is used in (8). For the prime tuples (4) only the classical fixed-modulus PNT in AP is used.

## 5. Sum over tuples at a common polynomial height: genuine distinct-state lower

For each fixed k choose a fixed beta>0 sufficiently small that
    beta (k+1+2 B_k) <1
with strict margin, and beta<1/2. Set X=R^beta. Then the error in (8) is o(R/(X^(k+1)(log X)^K)), uniformly. Each admissible tuple yields
    >>_(k,beta) R/(X^(k+1)(log X)^(2(k+1)))
actual canonical first-H witnesses. Within that tuple distinct x_0 give distinct terminal centers x_k=x_0-G_k. Summing with (4) yields at least
    >>_(k,beta) R/(log R)^(3(k+1))
tuple/witness incidences at the SAME H=floor(C_k R^beta).

We now remove all overcounting of terminal centers. Given a terminal x_k, the final p_k is a prime divisor of x_k (plus arrival pin), of size >=c_k R^beta. As x_k<=2R, there are at most O_beta(1) such distinct divisors, by taking the product of distinct large prime factors. For each candidate p_k, reconstruct x_(k-1)=x_k+p_k-1. It is still of size O(R), and its preceding p_(k-1) must divide x_(k-1), again at most O_beta(1) choices. Recurse for k labels. Finally x_0 and canonical A=x_0+6 are fixed; q is uniquely the actual qmin(x_k), or could conservatively be bounded by O_beta(1) large divisors of x_k+1. Thus each endpoint has at most O_(k,beta)(1) tuple incidences. This is an arithmetic inverse bound for the SPECIFIC decreasing-prime words, not a bound on all canonical ancestors of a generic sink.

Conclusion: for every fixed k>=1 there are fixed beta_k>0,C_k>0 such that for all sufficiently large R, at H=floor(C_k R^beta_k),
    # distinct actual first-H sites with G<=4H,
       exactly k+2 completed events of prescribed form,
       qmin/H <= C (.46)^(k-2) for k>=2
          >>_k R/(log R)^(3(k+1)).                       (9)
The k main events are all strict postevent height records, and actually each later one exceeds the preceding prefire maximum. This is a constructive polynomial-height lower for a family of moving canonical paths, unlike merely an upper/depth obstruction. It extends fixed-depth construction to arbitrary fixed depth and common H; it is MUCH smaller than R/L², and beta_k is sufficiently small and not .4. The terminal qmin itself has order H for each fixed k, not a polynomially smaller order. Hence (9) is consistent with the previous O(R/L³) upper for short-record dynamic endpoints. This is not an improvement of the best static rough-pair exponent and not M85.

## 6. Density-scale constructive paths at growing subpower height

Keep k fixed but instead choose X=L^(1/(k+1)), and choose just ONE admissible tuple in the fixed product boxes for each R. Then Z=O_k(X), and the complete CRT period
    P=4 product_(odd prime l<=Z) l
has log P=O(Z) by Chebyshev, hence P=R^o(1). The exact density of all allowed x_0 classes modulo P is
    rho= (1/M) product_(free l<=Z)(1-nu(l)/l)
          >>_k 1/[L (log L)^(2(k+1))].
The full-period count in the slab is >=rho(R-O(P)), so there are
    >>_k R/[L (log L)^(2(k+1))]
distinct actual canonical first-H sites with the same word, qmin/H bounded by (7), G=Theta(H). This is omega(R/L²) for each fixed k, at H=Theta_k(L^(1/(k+1))). One can make a diagonal choice k=k(R) tending to infinity sufficiently slowly: choose increasing thresholds R_k so for all R>=R_k the fixed-k construction works, H>=k, count>=R/L^(3/2), and the estimates in section7 hold with the indicated margins. Set k(R) to the largest applicable threshold index. No uniform PNT in growing Q is required. Then
    H->infinity, H=R^o(1), qmin/H->0,
    # distinct actual canonical active first-H sites >= R/L^(3/2),
    G=Theta(H), k+2 completed events ->infinity.          (10)
The scale is at most polylogarithmic and chosen by the construction, not an arbitrary prescribed height. This is a genuine density-scale lower for active canonical endpoints at a growing but small scale, not an extrapolation to polynomial H. It also confirms why the previous short-record obstruction needed a fixed polynomial lower for H; (10) has no contradiction with that theorem.

## 7. Lift the same constructive word to occupied local geometry at high height

We can use the same residue family to build actual local connectors at much larger absolute heights without making the whole high primorial part of the modulus. This is a lower bound for starting states of the local transition problem; it does not assert these starts already have canonical ancestors at the chosen high first section.

Take the subpower construction of section6, with k fixed for the moment. Begin at x_0+2, at the local starting height u (not a canonical birth), where
    u=3 mod M0,   M0=6 p_1...p_k q.
At u=3 the prescribed prefix p=3 immediately fires into x_0,h=3. With u shifted by a multiple of M0, that same p=3 fires immediately, because x_0+3 divisible3 and n'=u-x_0/2 even and divisible3. The subsequent main word has exactly the same relative heights, waits and signs: u-3 even and divisible by every selected p_i and q, so all their clock residues are unchanged. At each intended stationary center no other labels <=Z are eligible by (6). The starting x_0+2 has qmin=3; at its first tick 3 wins regardless of other primes. Let D=H-3 and local gain g=2+G_k. The trial word (labels <=Z) first hits u+D after T=D+g/2=O_k(X) ticks. Its endpoints have qmin=3 and q, with q/D bounded by (7) up to vanishing relative correction. The low alphabet trial has gain Theta(D) and duration Theta(D), uniform absolute comparability as above.

Let Hbig=floor(R^theta) for fixed 0<theta<=1/2 (in particular theta=.4), and allow u in the arithmetic progression above within [Hbig/2,3Hbig/4]. There are N_u>> Hbig/M0 such heights, since M0=Theta_k(L). For each such u, the prescribed trial height and spatial offset at every tick are deterministic; the sign parity is independent of u and x_0 in the selected congruence system. A prime l>Z can preempt a trial tick only if it divides the corresponding linear expression 2u+c_t (or its negative) in the preheight, where c_t is fixed by the template and the sign; it must also divide the corresponding spatial neighbor x_0-d_t+s. These height expressions are nonzero odd integers of magnitude O(Hbig) for large R. Let
    B(u)=sum_(ticks t) sum_(prime l>Z, l|2u+c_t) 1/l.
We may overcount moving ticks where a large label cannot win; this is an upper on interference. For l>Z, l is coprime to M0, so within the u-progression the proportion satisfying the divisibility is <=1/l+1/N_u. Average:
    E_u B(u) <= T sum_(l>Z) 1/l²
              + (T/N_u) sum_(l<=O(Hbig)) 1/l
            <<_k 1/log X + o(1).                         (11)
Here T=O(X), Z=Theta(X), the elementary reciprocal-square prime upper is O(1/(Z log Z)), and T M0 log L/Hbig=o(1). Markov gives B(u)<=1/4 for a proportion 1-O_k(1/log X)-o(1) of the allowed heights. This is not a uniform assertion for every high height, nor a claim of independence of successive prime queries.

For a fixed good u, let J=rho P be the number of allowed spatial residue classes modulo P. The number of x_0 in [R,2R-6] in this set is >=J(R/P-O(1)). At each candidate interfering pair (t,l), l>Z and gcd(l,P)=1, the additional spatial condition pins one residue modulo l in each class. It excludes at most J(R/(Pl)+O(1)) candidates. For fixed u each nonzero height expression has O(L) distinct prime factors, so there are O(T L) candidate pairs. The union bound excludes at most
    J(R/P) B(u) + O(J T L).
Since P=R^o(1) and T polylogarithmic, the error relative to J R/P is o(1). Consequently at least half of the spatial candidates have no interference at all. Their actual trajectory is the trial template through first local target u+D, by induction on the ticks. This argument is a count on actual finite integer slabs, not just the existence of huge CRT representatives.

Distinct x_0 give distinct terminal centers and hence physically disjoint local connectors before first u+D, by deterministic continuation. For every good u, the number of connectors is
    >>_k R/[L (log L)^(2(k+1))].
Their starts have qmin=3, ends qmin=q, both much smaller than D as k grows diagonally, gain Theta(D), elapsed Theta(D), and every moving prime <=Z=O(D) with k strict local postevent records. Taking the slow diagonal choice of section6, for each sufficiently large R one obtains a growing D=R^o(1), q/D->0, and >=R/L^(3/2) such disjoint actual local connectors at a proportion tending to1 of the heights in the specified progression of step M0=Theta_k(L) (constants may depend on the current fixed k). In the diagonal version thresholds can ensure M0<=L^2 and at least Hbig/(10L^2) good heights. All heights are within [Hbig/2,3Hbig/4]. This establishes the constructive local supply at subpower width, including near Hbig=R^.4, not the polynomial-width, canonically occupied local section supply demanded in c6ab2f37. The missing connection is actual ancestry from birth to these high starts. Also the widths and allowed heights do not form a consecutive tiling; we cannot concatenate these local families simply by counting their starts and ends.

## 8. Executed audit and limitations

research/lean/negative_min_decreasing_prime_staircase_audit.mjs @0a46636779f8ea1866c9e59369cb056fb6c3a496, blob 7faa176d55c22eb80ac5365541241eaa3970e0a8. Executed twice as ECMAScript, final source independently fetched from pinned commit and active branch and compared exactly. Fixed k=1,2,3,4 searches in finite AP intervals; spatial residues chosen for every prime<=2H+3, checked exact one eligible pinned label at each word center. Independent height-local tick replay includes actual p5,p3 canonical prefix, exact first-height stopping, clock pins and reverse arrival divisibility. For k=1,2 also materialized full BigInt CRT representatives (combined decimal lengths 11871 digits), replayed actual integer coordinates independently and checked all 3157 CRT residue conditions. For k=3,4 the coherent finite CRT residue model suffices to replay the word but no giant representative was materialized. All finite checks passed:
    prime controls 189547
    source residue checks 893174
    independent height-local tick computations 1762759
    main clock/height checks 10
    reverse pins 10.
Examples (finite templates, NOT scale-R density estimates):
    k   primes                         terminal q  H       q/H
    1   1021                           1201        1666    .720888
    2   6121,3361                      3541        12078   .293178
    3   139861,76441,30241             31081       291279  .106705
    4   435541,235621,93241,42841       43261       925596  .046739
The k=4 example has G=807246, age=1329216, strict main postheights 435541,706863,839169,899661. The actual CRT representatives are vastly larger than these height scales. No finite sample is claimed to validate the asymptotic lower sieve or high-section average. Section4's lower bound is a paper derivation, sections5-7 use that and classical fixed-modulus PNT/CRT only.

## 9. Remaining obstruction and source ledger

Reopened previous signed band/active slicing c6ab2f37 and progress-weighted record note a33ad0bd, plus prior height-local scan and min-plus section transport. The block-Bonferroni lower is the earlier elementary method of research/2026-11-27-min-local-negative-adaptive-local-moments-and-absorption-probability.md adapted to a fixed multi-offset sieve. No new external search or advanced distribution input. No literature priority claim. The prior active-first-record-and-deficit note supplied a two-event lower at small exponent; the new construction uses an arbitrary fixed number of decreasing labels with full repair of each prefire maximum, common target height and fixed-depth reverse packing, and actual high-section lift via averaging. The fixed-k polynomial-scale lower loses 3(k+1) logarithmic powers; the density-scale version remains subpower. To approach M85, the prescribed fixed tuple method would need a new collective transport estimate or a lower sieve at growing path depth, and high starts must be linked to canonical ancestry. Neither follows from the current construction. Core b0e26798535b2c997f1383c1dc37bbe560aac938 unchanged; main/siblings untouched. 4.80 latter, 4.85 remains unmet, no unconditional twin proof or independent specialist/Lean verification.
