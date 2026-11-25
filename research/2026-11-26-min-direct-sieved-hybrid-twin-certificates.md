# Primorial-offset twin certificates, sieved hybrid smoothing, and the super-logarithmic A1 population

Continuation of [319d42d](https://github.com/tara-sooo/A166944-Lean/blob/319d42d2ac9bf3dcdfc2cfd34ce8a4117f1cd611/research/2026-11-26-min-direct-last-exit-corridors-and-record-support.md). Two directions pursued together. First, arbitrary fixed numbers of full low-label A1 recovery corridors can occur consecutively on an actual canonical ray at controlled log-scale horizons, with many initial integers. Second, a new direct twin-prime witness is obtained from the offset of a high-label jump crossing a primorial multiple. A hybrid barrier family, additionally sieved beyond the original cutoff, removes the exact-anchor escape from that witness. Bonferroni truncation transfers the existing 4/11 Fourier certificate to the sieved family with no loss of smoothing exponent. This gives the same X^(9/11) necessary FAR A1 count at labels almost of size (log X)^2, under the existing sparse-window hypotheses and absence of the twin witness. Paper deductions with exact finite audits; not Lean kernel verification or external novelty claim. No finite-twins contradiction yet.

## 1. Fixed-length dense chains at controlled absolute scale

Let m>=1 be any FIXED integer, N0=8m, and Q0 the product of odd primes <=2N0+1. Take arbitrarily large primes p=3 mod4, p=1 mod Q0 (Dirichlet). We choose a word of N0 distinct odd primes a_0,...,a_(N0-1), a_0=p. At indices 8i choose mark primes p_i=a_(8i), p_0=p, and for i>0
    1.01p<p_i<1.08p.
Within each cycle choose seven descending recovery labels, each satisfying
    .67 a_(j-1)<a_j<.70 a_(j-1).
Every label after a_0 is 1 mod4 and 1 mod Q0. The last label of a cycle is <1.08*.70^7 p<.089p. All labels are >.06p for sufficiently large p, all are <1.08p (except the first equality at p), and the seven low labels in each cycle are <.756p.

We require that the forced congruences at selected primes have no cross-stage conflict. Here is a justification of the simultaneous choice, rather than assuming prime tuples in proportional intervals. Choose the normalized vector x_j=a_j/p first in the nonempty open domain given by x_0=1, the mark intervals and all descent intervals. Exclude equalities between label values, and for every pair of distinct stage indices i,j exclude all hyperplanes
    sum_{h=min(i,j)}^{max(i,j)-1} x_h = z*x_i
for integers z in the finite possible range of the ratio on this domain. Omit the case j=i+1: its sum is x_i identically. Every other equation is nontrivial (the sum includes a different variable, or the fixed x_0 while x_i varies); there are finitely many hyperplanes for fixed m, since every x_i is bounded away from zero. A small product of open intervals for x_1,...,x_(N0-1) remains inside the domain and away from these equalities. The prime number theorem in the single FIXED reduced progression 1 mod 4Q0 supplies a prime in each such proportional interval for every sufficiently large p. This gives distinct primes and ratios separated uniformly from all the forbidden equalities; no simultaneous-prime conjecture is used.

Let g_i=sum_{j<i}(a_j-1), and impose H0=0 mod4 and, at every pre-horizon H_i=H0+g_i,
    H_i=1 mod a_i,
    H_i != +/-1 mod f for every other odd prime f<=4p.          (1)
For an unselected prime f<=2N0+1 all gains vanish mod f and H0=0 works. For every larger unselected f there are at most 2N0 forbidden residues, hence at least one allowed residue. At a selected prime a_i the forced residue is H0=1-g_i mod a_i. At any other stage j the two forbidden coincidences are g_j-g_i=0 or -2 mod a_i. If j=i+1, the difference is a_i-1=-1 mod a_i, safe. All other cases are excluded by the normalized hyperplane separation just established: the exact difference is a signed sum of the prime values with a bounded integer correction of magnitude<=N0, so cannot approach an integer multiple of a_i within a bounded distance for sufficiently large p. Thus (1) is locally compatible at every prime.

For any H0 satisfying (1) with H0>=max a_i^2+8, start at canonical tick t0=H0/2+3, d0=6. The first mark is the even-side event p at wait (3p-7)/2; each subsequent event a_i is even-side with
    w_i=(3a_i-2a_(i-1)-1)/2 >0,    d'_i=2a_i.
The parity is correct since a_0=3 mod4 and all later primes are1 mod4 (the first subsequent formula is divisible by4 in the numerator because 2a_0=2 mod4). At even ticks the defect d+2w+1 is in the class 3a_i mod4; the preceding multiple of a_i in this class is -a_i, not a future even-tick defect. At odd ticks the selected prime cannot fire since H_i=1 mod a_i. All defects through the intended tick have absolute value <=4p, by the bounds on a_i. The other prime factors of those defects are excluded by (1); at the intended tick raw gcd is a_i (the possible extra factor 3 of 3a_i is excluded). Hence this is the actual adaptive MIN word, not just selected-clock realizability. Every mark p_i is A1 because its pre deficit is6 initially, or twice the preceding final recovery prime <.178p, and p_i>=p. Its recovery sequence has all subsequent d strictly decreasing through its seven low labels.

Put X=2^ceil(12p/5), log X=(12/5)log(2)*p+O(1), and let R be the balanced cutoff largest odd prime with P_R<=sqrt X. Then R~.8318p. For large p, every mark has p_i>R, and every recovery label is <=R. Each mark is in the same band [T,2T) with T=p. The preceding last-exit corridor definition applies: the state just after the mark has x=d+3>=2p; the first low event has post x<1.9p, and after four lows x>2*.67^4*p>.4p, whereas after five lows x<=2*1.08*.70^5*p+3<.4p. Thus each corridor begins immediately after its mark, consists of exactly five low events, is a complete good corridor, and is disjoint from the other such corridors. There are exactly m such marked A1 in the word. The total gain of the entire 8m-event word is <4mp, since the sum per cycle is at most 1.08p*(1+.70+...+.70^7)<3.6p. The elapsed ticks are also <4mp by the exact deficit balance. These are dense LOCAL chains on one actual ray, not disjoint single-root examples.

There are many realizations of the whole word in the PRESCRIBED absolute interval H0 in [X,2X). First impose (1) at odd primes f<=Y=floor(p/100) and at all selected primes, plus mod4. The modulus L0=4 P_Y prod a_i has log L0=(.01+o(1))*p. All selected primes exceed Y. Each allowed small-prime class has X/L0+O(1) consecutive representatives in this interval. At remaining primes Y<f<=4p (except selected primes), each excludes at most 2N0 residues; within any one progression, the number excluded by their union is at most
    2N0*(X/L0+O(1))*sum_{Y<f<=4p}1/f + 2N0*pi(4p) = o(X/L0),
uniformly over classes, since the reciprocal sum is O(1/log p) and X/L0 exponential in p. The small-prime allowed density is >>_m (log p)^(-2N0): finitely many f<=2N0+1 contribute positive constants, and for the others compare 1-2N0/f with (1-1/f)^(2N0), whose quotient product converges positively, then use the usual prime Mertens product. Consequently at least
    c_m X/[p^(8m) (log p)^(16m)] = X^(1-o(1))                     (2)
distinct canonical roots M=H0/2+1 realize these m full corridors, for arbitrarily large X and every fixed m.

In particular a fixed-length chain of full good log-scale corridors cannot have a uniform power-saving count over ALL canonical starts. By choosing p sufficiently large for each increasing m, the local chain length can grow without bound, with m>=G_chain/(4p) of order G_chain/log X; no uniform o(G_chain/log X) bound on every such short local block with growing m is possible. This does NOT establish such density on a macroscopic block of size X, or a single infinite ray. The finite-twins hypothesis is not used in this construction.

A simple complementary restriction on periodic spacings: if A1 marks with p>=T have pre-horizons H_i=H_*+iD for i=0,...,m-1, each odd prime f<T has both residues +/-1 omitted by the whole sequence (A1 least-factor theorem). If f does not divide D and m>=f-1, the progression visits at least f-1 residues, impossible. Hence prod of odd primes f<T, f<=m+1 divides D, which gives m=O(log T) for D<=T^C with fixed C and T->infinity, by PNT. The same applies to each phase of an exactly periodic intermark-gain word, with D the total gain per repeated period. This restriction does not require identical intervening prime words. The constructed dense chains have varying gaps and do not contradict it.

## 2. A direct primorial-offset twin certificate

Let 3<=S<=R<V<=S^2 be integers; write P_S for the odd primorial and use even horizons. Let J be a multiple of 2P_S. Consider an actual event p>S, with H<=J<H+p-1 (the half-open crossing convention), p<=V, and with neither H-1 nor H+1 divisible by an odd prime<=S (call this S-rough). Put u=J-H. Then u even, 0<=u<=p-3, and u+1<S^2. If u>0, u=2 is impossible since u+1=3; thus u>=4. For each odd prime f<=S the relation J=0 mod f and S-roughness imply f does not divide u-1 or u+1. Both are odd integers >1, smaller than S^2, and hence are PRIMES >S: a composite of this size has a prime factor <=S. We obtain the exact certificate
    S-rough pre-horizon,  H<J<H+p-1,  p<=S^2,
    2P_S | J  ==>  (J-H-1, J-H+1) are twin primes >S.            (3)
The earlier A1 least-factor theorem gives S-roughness for all A1 p>S. The theorem also applies to arbitrary S-rough events, regardless of adjusted deficit or A1. It is not a statement about primality of H+-1 themselves. If (3) can be forced for arbitrarily large S, twin infinitude follows. Under finite twins it is absent for all sufficiently large S. The exact anchor H=J is the escape in this unsieved version.

## 3. Sieving out the anchor and classifying moderate crossings

Put P=P_R. In integer horizon coordinate j=J/2 define the hybrid R barrier by local conditions
    J=0 mod f for odd primes f<=S,
    J mod f in {0,2,...,f-3} for S<f<=R.
This is a nonempty CRT family with base period P in j; it is a subset of the ordinary R horizon barriers, so no selected label <=R crosses it. Its density is
    alpha = 1/P_S * prod_{S<f<=R} (f-1)/(2f).
Additionally sieve this family by requiring J not congruent to +/-1 modulo EVERY prime R<f<=V. Call surviving cuts sieved hybrid cuts. Each is V-rough in the same sense and divisible by 2P_S. The additional local sets are exclusions, not the downward-deficit barrier sets.

For any moderate event R<p<=V crossing a surviving cut J, H=J is impossible: the selected prime divides H-e and the cut is V-rough. Therefore H<J. If the pre-horizon is S-rough, (3) yields a twin witness >S. Otherwise a prime f<=S divides H+-1 and is eligible (f<p, p^2<=H+1). Its next strict future clock is at most 2f ticks away, so actual earliest wait w<=2S. Consequently in the absence of a twin witness,
    R<p<=V and crossing a sieved cut ==> w<=2S,
    d-d' = p-1-2w >= p-1-4S.                                   (4)
When S=o(R) this is an ordinary decrease of almost the entire gain. Such an event is B for sufficiently large R: the low-pre-deficit criterion p>=5d+15 would imply w>= (p-1-d)/2 >=.4p+1 >2S by d'>=0. This includes the moderate reset case. A nonreset additionally has d'>=2p, hence d>=3p-1-4S. These are pointwise statements, and no clock assumption on an entire corridor is made.

The challenge is to retain enough normalized barrier coverage after this extra sieve, without multiplying the smoothing scale by the enormous full primorial P_V. Sections 4-5 address this using fixed-order inclusion-exclusion.

## 4. Transfer of the 4/11 smoothing certificate to finite intersections

Let R tend to infinity, S->infinity, S=o(R), R<V<=S^2. For a finite subset F of the additional primes R<f<=V, put
    P_F^*=P*prod_{f in F} f,
    w_F=prod_{f in F}(2/f),   alpha_F=alpha*w_F.
Let f_F(j) be the indicator of the base hybrid condition AND divisibility J=+/-1 mod f for each f in F, divided by alpha_F. This normalized indicator has mean1 over the period P_F^*. Include F=empty. These are intersections of BAD extra-prime residues, used to express the sieve by Bonferroni. Their local sets have cardinality2 at the extra primes, cardinality1 at primes<=S, and the original horizon cyclic interval at S<f<=R.

Write r=pi_o(R), ell=ceil(P^(4/11)). For every FIXED K and all F with |F|<=K, the forward moving average f_(F,ell) has the uniform complete-period variance bound
    sigma_(F,ell)^2 <= exp(-.001*r)                                (5)
for sufficiently large R. To justify this extension, reuse the exact three-class certificate of [f763c6b](https://github.com/tara-sooo/A166944-Lean/blob/319d42d2ac9bf3dcdfc2cfd34ce8a4117f1cd611/research/2026-11-26-min-direct-cluster-recovery.md) (435880 rationally certified cells, saving>.003, original delta=7/11). Use as ambient primes those <=R, >S, and >=R/log R. Their number n~r, min b has log b~log R. All their local sets are the original H-family intervals. Their normalized Fourier factors and class moment bounds are unchanged, with the full modulus P_F^* CRT inverse; every omitted local factor has absolute value <=1. The shortened projection/conditional-moment argument uses ONLY the ambient primes and bounds all other factors by1, so the same finite inequalities and entropy certificate apply.

Choose a COMMON frequency cutoff for these different periods
    M=ceil(P^(7/11) * exp(r) * P_S).
Since log P_S=o(R), log M=(7/11+o(1))*log P, M<P/2 eventually and the residue agreement parameter floor(log M/log b)/n -> 7/11. This is why pinning all primes up to S to zero does not change the low-frequency exponent, as long as S=o(R). The uniform positive certificate gaps still apply. Its summed low-frequency energy is exponentially small in r, uniformly in F. The high-frequency Parseval term is bounded by
    (P_F^*/(2 ell (M+1)))^2 / alpha_F
    <= [V^(2K)/(4 exp(2r) P_S^2)] *
          P_S exp((log 2+o(1))*r) V^K
    = exp(-log P_S + (log 2-2+o(1))*r).
Here log V=O(log R)=o(r), K is fixed, and the non-singleton base densities have the original log2 bound. The small-prime density penalty is offset by the factor P_S in M; M remains below P/2. This proves (5) with the same .001 margin by the preceding certificate and symmetric Fourier split. In particular the smoothing length is P^(4/11), NOT (P_V)^(4/11), and need not be enlarged even by a power of log X for any fixed K. No new entropy certificate or external Fourier theorem is asserted.

## 5. Uniform smoothing of the additional sieve on a macroscopic interval

Let
    f_sv(j)=f_empty(j)*prod_{R<f<=V}(1-1_{2j=+/-1 mod f}),
    Q=prod_{R<f<=V}(1-2/f).
The product is a finite indicator. Its full period may vastly exceed the horizon window; we never apply full-period Parseval to that large product. The reciprocal-prime estimate/Mertens gives
    mu=sum_{R<f<=V}2/f <= 2 log 2+o(1),
    Q>=1/4-o(1)
because V<=R^2. For each k put Q_k=sum_{|F|<=k}(-1)^|F| w_F over subsets of the extra primes. Pointwise Bonferroni bounds f_sv between the odd and even truncated sums of (-1)^|F| w_F f_F. Their expectations bound Q in the same way, with gap <=mu^(k+1)/(k+1)! for successive truncations. These inequalities also hold after taking any forward moving average. The sum of absolute coefficients in any truncation is <=exp(mu)=O(1).

On a crossed horizon window [X,lambda X] with fixed lambda>1, take R balanced P<=sqrt X (the argument also works at any fixed P<=X^rho, rho<1, with ell as above). Let J0=[a,b) be the integer-coordinate interval of the contiguous event block, n0=b-a=Theta(X). For ANY union U of m0 disjoint half-open integer subintervals of J0 that covers all surviving cuts there, form U^- expanded by ell-1 positions to the left and J0'=[a-ell+1,b), n'=n0+ell-1. Nonnegative smoothing, exactly as in [78b1212](https://github.com/tara-sooo/A166944-Lean/blob/319d42d2ac9bf3dcdfc2cfd34ce8a4117f1cd611/research/2026-11-26-min-direct-mean-square-barrier-smoothing.md), gives
    sum_{j in J0} f_sv(j) = sum_{j in U} f_sv(j)
       <= sum_{j in U^-} (f_sv)_ell(j),
    |U^-|<=|U|+(ell-1)m0,   |U^-|<=n'.                             (6)
Fix integer h>=0. Each f_F with |F|<=2h+1 is nonnegative normalized periodic; its sum on J0 differs from n0 by at most P_F^*. The odd truncation therefore gives
    sum_{J0} f_sv >= Q_(2h+1)*n0 - exp(mu)*P V^(2h+1).
The even smoothed truncation gives
    sum_{U^-} (f_sv)_ell <= Q_(2h)*|U^-|
             + sum_{|F|<=2h} w_F sum_{J0'}|f_(F,ell)-1|.
By (5), Cauchy-Schwarz and period counting, the last sum is at most
    exp(mu)*sqrt(n'*(n'+P V^(2h)))*exp(-.0005*r).
For every fixed h both errors are o(X): P<=sqrt X, V=O(log^2 X), ell=o(X). The same statement at fixed rho<1 follows identically. The errors are uniform in U, even if its intervals are selected using all the barrier positions. Now take h fixed but sufficiently large to make the Bonferroni expectation gaps arbitrarily small, using mu bounded and Q bounded away from zero. Since n',|U^-|=O(X), for every epsilon>0 these gaps cost <=epsilon X after normalization by Q, for all sufficiently large X. Combining with (6) proves the uniform asymptotic union bound
    n0 <= |U|+(ell-1)m0+o(X).                                     (7)
No growing-order sieve theorem is needed: the epsilon argument uses each fixed truncation order separately, with ell independent of that order. In particular the o(X) can be chosen uniformly over arbitrary U. This is an upper on normalized mass of intervals covering the sieved cuts, with NO constant loss of density after normalization. Merely removing anchor positions using a union bound without re-smoothing would have incurred a constant loss and a weaker threshold.

## 6. New necessary large-label A1 population, or direct twin witness

Retain the canonical crossed-window notation G=(lambda-1)X+O(sqrt X), C=floor sqrt(lambda X+1), G_f all far gain, n_near=O(sqrt X), G_f>=G/2-O(sqrt X), N actual canonical visits, with the fixed earlier near-square definition. Suppose there is no event of section2 that crosses a surviving cut and produces the witness (3) with twin lower member>S. In particular this is automatic for all sufficiently large S under finite twins. Define
    m_big = number of far A1 with p>V,
    F_big = their gain,
    B_star = number of far B with p>R and either p>V, or
             R<p<=V and w<=2S.
B_star can be restricted to actual surviving-cut crossers, but we use this simpler superset. It is <= the previous B_R, and its moderate part has drop >=p-1-4S. Let n_A0 count all far A0 with p>R. By section3 and the no-witness condition, the union of jumps from the following populations covers every sieved hybrid cut:
* all near events with p>R;
* all far A0 with p>R;
* all far B counted in B_star;
* all far A1 counted in m_big.
No far A1 in (R,V] is needed: its crossing would produce a twin witness since it is S-rough, and the anchor is excluded. Only these populations are needed, since p<=R cannot cross an ordinary R barrier. All selected jump intervals are disjoint. Their absolute gain is <=G-G_f+F_big+C(n_A0+B_star) and their count <=n_near+n_A0+B_star+m_big. Apply (7) and multiply by2:
    G_f <= F_big+C(n_A0+B_star)
             +2ell(n_near+n_A0+B_star+m_big)+o(X).                (8)
The established far-only ordinary recovery allocation applies to ANY subset of A1. With c=9/5-o(1) and D_nr total near decreasing-reset drop, it gives
    (1+c) F_big <= G_f+D_nr+2C.
As previously, near decreasing resets and far A0 resets are disjoint and associate to distinct canonical visits, apart from one possible endpoint visit, hence their combined count<=N+1. D_nr is bounded by C times its own reset count. Substituting into (8) and using ell n_near=o(X) at the balanced cutoff gives
    9G/28-o(X) <= 2ell*m_big+(C+2ell)*(N+1+B_star).                (9)
This is the same leading coefficient as the original 4/11 bound but m_big is a much smaller, higher-label population. It is a window alternative: either a direct twin witness (3) occurs, or (9) holds. No sparsity hypothesis is used in deriving (9) other than the no-witness condition. At the balanced cutoff, if N,B_R=o(sqrt X) along crossed windows with no witness, then B_star is also sparse, and
    m_big >= (9*(lambda-1)/56-o(1))*X/ell
          = Omega(X^(9/11)).                                     (10)
The same lower bound follows from sparsity of N,B_star alone. The original B_R sparsity is needed below for the full low-label corridor extraction, because noncrossing high B may interrupt a corridor.

Choose for instance S=floor(R/loglog R) (for sufficiently large R), V=S^2. More generally S=R/omega(R) with omega->infinity sufficiently slowly, R<V. Thus V=R^(2-o(1)); in particular for any fixed epsilon>0 the necessary population in (10) can be confined to p>R^(2-epsilon) without weakening the X^(9/11) exponent. At balanced R~.5 log X, this excludes the possibility that the entire necessary far A1 population of that order is supplied only at p=O(log X). There may still be many smaller A1 in addition; (10) is not a relative proportion bound for all A1. The log-scale dense-chain construction of section1 is therefore compatible with the new theorem but no longer supplies the whole necessary population.

## 7. Consequence for actual high-multiplier record recovery

Assume the original sparse hypotheses N,B_R=o(sqrt X) and absence of the twin witness, and use V=S^2 as above. Apply the previous last-exit corridor theorem of 319d42d to ALL m_big marks, in dyadic bands T_j=(V+1)2^j. The total number of pending/bad marks across bands is at most O((N+2)log X+B_R)=o(m_big), by that theorem's localized exception charges. Thus (1-o(1))m_big actual good corridors exist, with ALL labels<=R, each of net ordinary deficit drop Delta>=1.5T_j>=1.5V. The three-color bound ensures that any physical event belongs to at most three good corridors. Each corridor has at least Delta/(R-3) strict record-minimum decreasing events, and every record multiplier h satisfies
    2s h > (4/15)T_j-9,   s<=R.
Consequently the number of DISTINCT actual record-decreasing nonresets supplied over all these corridors is
    >= (1/3)*(1.5V/(R-3))*(1-o(1))*m_big
     = Omega(X^(9/11) * V/R),                                    (11)
all with h=Omega(V/R). No artificial division into disjoint dyadic mark populations loses a factor log X here; the factor-three overlap is used. For any fixed cutoff S0>=47, apply the previous arbitrary-support record barrier inequality D_out>=theta_F(Delta-2P_F) with F all odd primes<=S0. Since V->infinity, the same order lower bound (constant depending on S0) holds for distinct far nonreset B record-decreases with S0<s<=R. One may take S0~log R instead: P_S0=R^(1+o(1))=o(V) for S=R/loglog R, theta_S0=R^(-o(1)), giving Omega(X^(9/11) R^(1-o(1))) such occurrences in the lower band log R<s<=R (in the exponent lower-bound sense). Multipliers still grow at least as R/(loglog R)^2. All these events are real ordinary decreases, not arbitrary high precursors; label3 cannot be a record decrease, and all labels<=R are far at these horizons.

For S=R/loglog R, (11) is Omega(X^(9/11) R/(loglog R)^2). This is a stronger necessary recovery population than the previous dyadic existence with unconstrained log-size T, and is tied to the new twin certificate. It does not force the distinct-prime discovery count of the earlier rapid-recovery packing or a short elapsed time. The corridor support product P_rec>1.5T_j-5 still holds. Large record multiplicities remain a possible source of the supply. Neither N nor B_R (nor B_star) is known sparse on an unbounded sequence merely from finite twins. The next objective is an upper supply theorem for these many high-multiplier record decreases at super-logarithmic deficit scales, or to force the direct offset witness (3) by excluding the other alternatives. The existing large-tail upper at T~ell is far above the present V, so no contradiction follows by comparing the two thresholds.

## 8. Diagnostics and preservation

[Log-scale chain audit 7eb8e6f](https://github.com/tara-sooo/A166944-Lean/blob/7eb8e6f704a86526733d69affd0c524e93d15aad/research/min_direct_log_scale_a1_chain_audit.mjs), blob 3067103859d454669477d35de65881776382f552, exact remote readback. Run node research/min_direct_log_scale_a1_chain_audit.mjs. Actual ECMAScript executed in tool runtime, not a separate Node process. Four actual canonical roots with m=2,3,4,6, p=78031,91291,87931,86311; exact X=2^ceil(12p/5), balanced cutoffs65213,76253,73477,72089. Root decimal digits56376,65956,63528,62358 respectively. Finite search uses locally checked prime words (not requiring every small-prime gain vanish), exact CRT up to a modulus <=X^.97 and scans the remaining progression. All 4 starts within [X,2X); 1421 candidates,1417 rejected. 120 actual events,15 A1 marks,15 complete five-label good corridors,2054962 full relative raw-GCD ticks including prime-power checks,624 independent literal BigInt gcd ticks,3563064 stage residue checks,51674 CRT prime checks. The six-mark word has A1 labels86311/87481/88861/88741/92221/92581 and 48 total events, gain1622010, elapsed817783. These finite roots test scale, compatibility and actual first-hit, not the asymptotic density proof (2).

[Sieved-hybrid audit d853632](https://github.com/tara-sooo/A166944-Lean/blob/d8536323b9a835be58e19093e8a18b314fa39cdc/research/min_direct_sieved_hybrid_twin_certificate_audit.mjs), blob 3cf8a739bc5239b765c110615973ce7221a2fbdb, exact remote readback. Run node research/min_direct_sieved_hybrid_twin_certificate_audit.mjs 60000. Actual ECMAScript execution. 29998 canonical roots through60000,549085 actual events,5254 A1 least-factor checks,0 unresolved cap180. Across overlapping finite cutoff controls,48833 moderate hybrid-crossing incidences,30570 anchor incidences before extra sieve (all excluded),12280 strict S-rough twin-certificate incidences. 7994 surviving-cut crossings,4697 produced offset twin witnesses (99 at A1),3297 had an eligible small competitor and satisfied w<=2S and the exact drop bound. Counts are incidences, not distinct twin pairs. Example actual A1 from M4587: pre H9210,t4608,d6,p61,odd side,w91,post d128; S11,R13,V121,J9240,u30 yields twins29/31. Actual non-A1 example M503,H1038,p17,w9,S5,R7,V25,J1050,u12 yields11/13. Small-competitor example M347,H834,p17,w3,d44->34,J840,S5,small factor5. The finite V=S^2 tests do not impose S=o(R); the asymptotic B classification and high multipliers are not extrapolated from them.

Six complete small hybrid/sieve-period controls (max full period255255),28 intersection periods;1214130 exact CRT position and1214130 exact rolling variance checks,3363570 pointwise Bonferroni and3363570 smoothed Bonferroni comparisons,1080 arbitrary disjoint union controls including negative translates,1440 lower mass,1800 upper smoothed mass,5040 exact BigInt Cauchy-Schwarz comparisons. All passed. These are finite identities and bounds; they do not numerically test the asymptotic 4/11 threshold at large R. The proof of (5) explicitly reuses the earlier rational entropy certificate with its positive gaps, changes the ambient set and frequency limit, and bounds the high-frequency term. No new Lean executable/kernel verification. Main and sibling branches not modified by this work.
