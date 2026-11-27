# Negative MIN: full relaxed barriers, rough difference geometry and void-moment entropy

2026-11-27 JST. Continuation of [c7f471e](https://github.com/tara-sooo/A166944-Lean/commit/c7f471e17088db7a62013bdb7da62c9687b6dd08). Goal: unconditional twin infinitude, independent verification and Lean formalization. The uniform primorial partition imposes an expensive initial entropy. Use all relaxed downward barriers for the small alphabet, not only common multiples. The single-prime relaxed crossing classification is the reflected version of the positive MIN classification already in the direct arithmetic branch (2026-11-25-min-direct-arithmetic.md, head 14c6176); no claim of originality for that classification. The new deductions here are the exact barrier-difference and multi-point geometry, its finite-twin obstruction, variable-cell support/entropy, and a computable short-distance second moment controlling the size-biased gap entropy without enumerating the full period. Actual asymptotic estimates remain open.

## 1. Exact downward barriers

For even b a downward jump a -> a-p+1 crosses b iff a-p+1<b<=a. With a even, j=a-b is even in [0,p-3], and eligibility requires b+j=+1 or -1 modulo p. Thus the crossing residues of b modulo p are {1,2,4,...,p-1}; the complementary barrier residues are {0,3,5,...,p-2}. In half-coordinate t=b/2, these are
    Omega_p = {0,-1,...,-(p-3)/2} mod p,
an interval of length l_p=(p-1)/2 on the circle. For any real z>=3 define P_z=product of odd primes p<=z and
    B_z={even b : b/2 mod p in Omega_p for all odd p<=z}.
This is the FULL phase-free barrier set for that alphabet. A failure of a barrier condition only guarantees a possible relaxed crossing, not an actual first-hit MIN event. B_z is periodic mod 2P_z, consists of multiples of 6, and contains all multiples of 2P_z. Its exact cardinality per period is K_z=product l_p. Its density among canonical roots (multiples of 6) is
    delta_z=3 K_z/P_z=product_{5<=p<=z} l_p/p.
The elementary prime number theorem and Mertens product give log(1/delta_z)=(log 2) pi(z)+O(loglog z), while log P_z~z. Thus mean gap is exponentially smaller than the primorial width, but mean gap under uniform B_z sampling is NOT the root-size-biased mean needed for entropy.

## 2. Pair differences are exactly rough twin centers

Take even D=2d. Write r_p=d mod p in [0,p), e_p=min(r_p,p-r_p). Two shifted circular intervals of length l_p intersect in exactly
    I_p(d)=max(0,l_p-e_p)
residues (2l_p<p). CRT gives the complete-period count of b in B_z with b+D in B_z as product_{p<=z odd} I_p(d). It is positive iff e_p<l_p for every p, equivalently d mod p differs from +/- (p-1)/2, equivalently D mod p differs from +/-1. Therefore
    D belongs to B_z-B_z iff gcd((D-1)(D+1),P_z)=1
for even D, with actual integer differences realized by CRT, not merely modulo the period. In particular every positive distance is divisible by 6, and is z-rough on both sides.

If 6<=D<=z^2-1, then D-1,D+1>1 and <=z^2. A composite among them has a prime factor <=z; hence both must be prime. Under finite twins, once z exceeds every prime in a twin pair, no positive difference D<=z^2-1 is possible. Thus every adjacent gap of B_z has width >z^2-1. This is not a proof of twin infinitude: the mean barrier gap is ~exp((log 2)pi(z)+O(loglog z)), much larger than z^2. It is a concrete obstruction to using a static barrier partition with polynomial cutoff z=R^epsilon and polylog cell entropy. On the infinite complete lattice, every full cell has log(root count) >=2 log z-O(1) under finite twins. In a finite slab truncated cell sizes can be smaller, so this lower bound must not be asserted for truncated mass without controlling the edge cells. Even for cutoffs z=log^c R, c>1, the full-cell baseline alone is above 2 loglog R under finite twins.

There is a stronger multipoint formula. For even shifts 2d_0,...,2d_k, sort their DISTINCT residues mod p and take their circular gaps g_i (one distinct residue has the single gap p). The number of t with all t+d_i in Omega_p is
    I_p(d_0,...,d_k)=sum_i [g_i-(p+1)/2]_+.
Indeed the shifted residues must fit inside a circular arc of length l_p-1; the complementary gap must be at least p-(l_p-1), and the number of placements of the interval is g_i-(p-l_p). At most one gap can exceed p-l_p. CRT multiplies these counts. Pairwise roughness is not sufficient for multipoint realizability: e.g. p=11, half-coordinate shifts 0,4,7 have pair overlaps positive but no simultaneous interval placement. This identifies the local correlations to use for higher-order void bounds.

As a density optimality observation, any subset of residues modulo 2P_z consisting of even points with all distinct pair differences z-rough (including differences modulo 2P_z) projects at each odd p to a subset of Z/pZ with no two residues differing by 1. The maximum independent set of the odd p-cycle has size (p-1)/2, so the original subset has cardinality at most product l_p by CRT. B_z attains this bound. Every maximum independent set of the local odd cycle is a translate of the same alternating pattern (successive circular gaps at least 2 and their sum p=2l_p+1). Thus no arbitrary pairwise-rough CRT packing can improve this density at the same cutoff. This assertion concerns pairwise-rough sets, not all conceivable time-sensitive MIN barriers.

## 3. Variable-cell certificates and entropy

Let consecutive barriers b_j<b_{j+1} define cells [b_j,b_{j+1}), width D_j, canonical root capacity M_j=D_j/6. Labels <=z cannot exit any cell downward. For actual negative MIN from A in [R,2R] divisible by 6, observe elapsed T=ceil sqrt(2R+1) as in c7f471e. If choosing an observation before the first exit, it is confined to the initial cell, and the same gain/wait inequalities (1),(2) of c7f471e hold with actual internal gain G=A-x<=D_j-2. In particular every exit label p>z, but this alone does not give near-square-root roughness.

Use M_j^R=# canonical slab roots in cell j. For each root select any pre-exit position x(A). Since each belongs to the root cell, each selected position has total inverse weight at most 1 with weight 1/M_j^R per root. Thus
    sum_{distinct x(A)} w_R(x) >= sum_A w_R(x(A))/M_{j(A)}^R.
Taking one maximum-weight representative per cell strengthens this. For all-root selection, Jensen gives the sufficient entropy form
    N exp(-E log M_{j(A)}^R - E c_R(x(A))),
where c_R=-log w_R. For an arbitrary selected cohort one can use the corresponding cohort cell counts and loss -log selected fraction. Neither synchronizing root clocks nor analyzing late coalescence is needed for this pre-exit selection. For the general cell path inverse flow of c7f471e, use the actual initial cell capacity M_j^R in the root-offset probability (zero births if M_j^R=0). Its descending row-subprobability argument is unchanged even though cell widths vary. In the signed coarse ledger of e173792, the exact mixing-minus-splitting identity is unchanged; replace log M by the actual initial cell entropy E log M_j^R. The previous uniform-width signed Taylor moment simplification does not directly transfer, since the initial masses now differ across full cells.

On a full canonical period K=P_z/3, let m_j=D_j/6 be the cyclic gap lengths in canonical coordinate k=b/6, sum m_j=K. The size-biased mean initial entropy is exactly
    H_z = (1/K) sum_j m_j log m_j
        = log K - H({m_j/K}).
In particular H_z>=log(1/delta_z) by Jensen, and H_z<=log K. For a slab of N consecutive canonical roots, since the per-root log full-cell size is a nonnegative K-periodic function bounded by log K, its mean differs from H_z by O(K log K/N). Actual truncated initial entropy is no greater. Thus when z=O(loglog R logloglog R) the PNT gives K=R^{o(1)} and the exact periodic initial-entropy estimate transfers to actual integer slabs with o(1) error. This transfer concerns the STATIC partition only, not the distribution of MIN histories.

## 4. Void probability from exact pair correlations

For the canonical-coordinate barrier indicator B(k)=1_{6k in B_z}, its mean over period K is delta=delta_z. For integer h>=1 define the exact normalized correlation
    r_z(h)=E_k B(k)B(k+h)/delta^2
          = product_{5<=p<=z} [p I_p(3h)/l_p^2].
For a backward window of H canonical lattice sites define C_H(k)=sum_{i=0}^{H-1} B(k-i). Then E C_H=H delta and its relative variance is exactly
    V_z(H)=Var(C_H)/(H delta)^2
          = 1/(H delta) + (2/H^2) sum_{h=1}^{H-1}(H-h) r_z(h) - 1.       (1)
This is computable in O(H pi(z)) local modular operations, without enumerating K. Cauchy-Schwarz on C_H restricted to positive values implies
    Pr(C_H=0) <= V_z(H)/(1+V_z(H)).                                    (2)
The exact void probability is sum_j (m_j-H)_+/K. If m_j>2H, then m_j-H>m_j/2. Hence for a uniform canonical root, whose cell size M is size-biased,
    Pr(M>2H) <= min(1,2 V_z(H)/(1+V_z(H))).                             (3)
The same result follows from the backward inclusive and forward STRICT windows (strict is needed at a barrier root). In particular
    H_z <= min(log K, log(2H)+min(1,2V_z(H)/(1+V_z(H))) [log(K/(2H))]_+). (4)
One can integrate (3) over H or sum dyadic tails for a stronger estimate, using monotonicity of the void tail. Equation (4) is a convenient one-window certificate.

A concrete asymptotic subtarget: if for some fixed C, H<=delta_z^{-C} and V_z(H)=O(1/log z), then H_z=O(pi(z)) by (4) and the prime number theorem. In particular for z=O(loglog R logloglog R) the static initial entropy is O(loglog R), at a cutoff larger than the O(loglog R) scale allowed by a uniform primorial baseline. To obtain a prescribed coefficient rather than O(1), choose explicit constants in H and the relative-variance bound. This is only a conditional improvement of the initial entropy budget: neither this variance estimate nor the necessary dynamic coarse entropy/roughness estimate is proved. The short-gap obstruction in section 2 prevents extrapolating such control to arbitrary polynomial cutoff.

## 5. Literature check and application boundary

Andrew Granville and Par Kurlberg, *Poisson statistics via the Chinese remainder theorem*, arXiv:math/0412135v2 (21 Feb 2005), Theorem 1, p.3, equation (1), original PDF https://arxiv.org/pdf/math/0412135 (inspected 2026-11-27). Their sufficient condition requires local multipoint counts at distinct residues to be asymptotically the product-density expectation with a relative error decaying like a power of p. For our Omega_p, already at half-coordinate shift 1, I_p(1)=l_p-1=(p-3)/2, whereas the product-density expectation is l_p^2/p~p/4; the relative discrepancy tends to 1, not zero. At shifts (p-1)/2 the count even vanishes. Consequently their Theorem 1 cannot establish Poisson spacing or the short-window variance bound here. The paper provides a correlation framework, not a theorem applicable to this particular half-interval alphabet. A full literature survey or claim of absence of another applicable theorem is not made. The exact correlation in (1) is therefore retained rather than importing a Poisson model. A subsequent route is to bound the weighted sums of r_z(h) over H=exp(O(pi(z))) using their interval-overlap structure, or exploit the multipoint formula for void bounds without assuming independent local residues across h.

## 6. Audit and exact remote readback

A. [Full barrier audit ba0b707](https://github.com/tara-sooo/A166944-Lean/blob/ba0b707845671b81d46f28ff65993377c4d279f4/research/min_local_negative_relaxed_barrier_gap_audit.mjs), blob 872a4092e21933e97aa1bc1459cd658c31a2f152. Executed ECMAScript function and exact remote content re-executed. Enumerated complete half-period CRT barriers through z=23 (P_z=111546435, 142560 barriers), 174729 finite structural checks including local relaxed crossing and multipoint counts, exact small-period pair correlations and rough difference checks. Actual MIN elapsed-T paths R480000, N80001, seven cutoffs z=3..19, 560007 root/cutoff observations and 8480163 small-label barrier checks. Same clock implementation as earlier work; not an independent proof verifier.

Selected full-period statistics (entropy in natural units, width in even center coordinate):
    z      mean width      max width      size-biased H_z    log(P_z/3)
    7       35              108             2.119700          3.555348
    11      77              198             2.820819          5.953243
    13     166.833          438             3.538932          8.518193
    17     354.521         1428             4.385008         11.351406
    19     748.433         3570             5.163382         14.295845
    23    1564.905        10710             5.906099         17.431339
At actual R480000,z17 initial entropy 4.37935, final coarse entropy 4.63786; z19 initial 5.16505 and final 5.27605. Their net growth is small but baseline remains. At z17 pre-exit maximum-per-cell actual weight certificate 1107.0873, finite bad capacity 1105.3077; the weaker certificate based only on waits is 66.5381. The actual weight includes already-existing twins, so no asymptotic conclusion. Increasing z does not monotonically improve the certificate.

B. [Void moment audit 6ea8daa](https://github.com/tara-sooo/A166944-Lean/blob/6ea8daaca150225724063971a266853decc4e228/research/min_local_negative_barrier_void_moment_audit.mjs), blob 4bb4d36dddfe8e643b320ca85cf6e7446bbe30a0. Executed before commit and after exact remote fetch, 1641721 correlation terms, 78 structural checks (literal window variance on small periods, exact gap void/tail/entropy inequalities for z<=23). All assertions passed. Floating-point finite evaluations, not rigorous interval arithmetic. At z=53 the canonical period is 5431526412865007455, delta=.00002491828, log K=43.13875; H=1284224=32 ceil(1/delta) gives relative variance .02352326, tail bound .04596527, H_z upper estimate 16.06330 via (4). At z=43 the corresponding values are H=308320, V=.02354463, upper estimate 14.34354 versus log K=35.31831. No enumeration of those huge periods or proof of uniform V asymptotics; the evaluated bounds are rounded numerical diagnostics of exact analytic inequalities.

No Node process or Lean kernel invocation. No independent mathematical certification or twin infinitude proof. The original age-frontier, signed flux and reverse-flow certificates remain available. Next: derive an analytic bound for the relative variance at subprimorial H using the explicit triangular local correlations, then quantify variable-cell coarse mass amplification or use the pre-exit/flow occupation. The static gap entropy alone cannot prove twins, and its short-gap equivalence explains the obstruction to high cutoffs. Main and sibling branches unchanged.