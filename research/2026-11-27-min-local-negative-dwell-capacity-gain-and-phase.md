# Negative MIN: periodic dwell sieve, displacement packing, and departure-phase entropy

2026-11-27 JST. Continuation of [19c2f29](https://github.com/tara-sooo/A166944-Lean/commit/19c2f297816af0403d1f8b8e36b9c6e624388c91) and [5e932c4](https://github.com/tara-sooo/A166944-Lean/commit/5e932c408a237debff6fa3672088dc652ebde830). The requested work is continued proof research within the same turn, not just a new sufficient condition followed by a numerical check. Here derive a uniform residue-class non-twin dwell sieve; use it to obtain a root-time displacement lower bound under finite twins; apply the previous unconditional Fourier gap moments to dynamic pre-exit time and relative transport; then remove both terminal and repeated-label occupation hypotheses from a new information-theoretic criterion, and develop an arithmetic majority-phase inverse decoder. Test attempts to close the resulting inequalities. None establishes an unconditional twin infinitude proof.

## 1. Observation convention and dwell capacity

Canonical roots A in [R,2R], 6|A, N~R/6, birth b(A)=3-A/2. Negative MIN at even center x chooses the earliest future eligible prime-factor firing, least prime at ties. A p-event decreases x by p-1. For even firing n, p|x+1 and n=0 mod 2p; for odd n, p|x-1 and n=p+2 mod 2p. Postheight n+x/2 stays nonnegative. Define S=sqrt(2R+1), T=ceil S, and q(x)=min(lpf(x-1),lpf(x+1)). In the expanded slab all centers are positive and even for large R, and q(x)>S iff x-1,x+1 are both prime.

Two observation conventions will be used explicitly:
- Own elapsed H, R^.45<=H<=T (integer): T is not a common absolute clock, gain at observation <=2H+6. Use this for first passage from birth.
- Synchronized root windows of width W=6 floor(T/6), latest birth n0 and observation interval [n0,n0+T) of T post-ticks, retirement n0+T. Full gain <=3T+6; use this for endpoint phase and L_end. The root's earlier trajectory before n0 is real, but not included in the observed time.

In either convention the whole path is monotone, so each center is occupied in at most one interval by a given root. The periodic clock of q(x) bounds this interval's full length by 2q(x). For observation length H define
    t_H(x)=min(1,2q(x)/H).
The conditional probability omega(A,x) of observing x at a uniform observation tick on root A satisfies omega(A,x)<=t_H(x), sum_x omega(A,x)=1. Truncation by a root-dependent event or a selected root cohort only reduces these weights. In the synchronized convention H=T. All centers lie in I=[lo-3T-6,hi] after rounding to even endpoints, where lo,hi are the canonical slab endpoints. The new capacity is the dwell probability, not the previous soft weight w_R; it may be much smaller for short segments.

## 2. Uniform periodic non-twin dwell sieve

Fix s>0 and 3<=z<=C loglog R for fixed C. Let L=2 prod_(3<=p<=z) p=6K, with K the canonical barrier period in f32926b. By Chebyshev, L=R^{o(1)}. For each even residue b mod L, prove
    sum_(x in I, x=b mod L, q(x)<=S) t_H(x)^s
      <<_(s,C) (R/L) (log(z+2))^2
                   (1+log^+(S/H))/(log R)^3.                 (1)
Uniformly R^.45<=H<=T. The sum excludes twin centers; no finite-twins assumption is needed for (1).

Small q<R^.4: each weight <=(2R^.4/H)^s=O_s(R^(-s/20)), and the residue contains O(R/L) centers. This is negligible versus the asserted bound.

For larger q=p>=R^.4, at least one neighbor x+e=p r, e=+1 or -1, is composite with least factor p; r>=p is prime for sufficiently large R, since otherwise p*r has at least three prime factors >=R^.4, impossible below 2R+1. Both neighbors are p-rough. Fix p and e. The residue x=b mod L gives one residue r mod L, since p>L's prime factors. Enlarge r to [1,ceil((2R+1)/p)]. For every prime ell with z<ell<=D=R^(1/100), both
    r != 0 mod ell,  p r-2e != 0 mod ell.
Indeed the actual r is prime >=R^.4 and the other neighbor is p-rough. The two forbidden residues are distinct because ell>3 and ell!=p. On the single arithmetic progression mod L, each squarefree sieve modulus d coprime to L has exactly rho(d)=2^omega(d) forbidden residue combinations, giving X*g(d)+O(rho(d)) with X the progression length, g(d)=rho(d)/d. This count follows by enumerating the progression parameter modulo d. It is independent of p,b,e. Here X<=O(R/(p L)) and R/(p L)>=R^(1/2-o(1)).

For completeness use the same Selberg quadratic diagonalization as [14c6176, sec.4](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md), now g(ell)=2/ell. On squarefree d<=D supported on primes z<ell<=D there are weights lambda_1=1, |lambda_d|<=prod_(ell|d)(1-g(ell))^-1<=d, with main quadratic form 1/G(D), G(D)=sum_(d<=D) prod_(ell|d) g(ell)/(1-g(ell)). The error expanding the square is O(sum_(d,e<=D) d e rho(lcm(d,e)))=O(D^6) since rho(lcm)<=lcm<=de. To bound G below, take the finite Euler product over z<ell<=D^eta, for fixed sufficiently small eta>0. Its mass is prod(1-2/ell)^-1 >> (log D/log(z+2))^2 by Mertens and the convergent quadratic correction. Under the normalized product measure each ell occurs with probability 2/ell, hence the mean log d is O(eta log D) by Chebyshev and partial summation. Choose eta so this is <=(log D)/2; at least half the mass lies at d<=D. Thus G(D) has the stated lower bound, uniformly even for the growing omitted interval. The D^6 error is negligible compared to X's upper scale R/(p L log^2 R); no short progression assumption beyond L=R^{o(1)}.

It follows that for this p,e,b the number of possible x is
    << (R/(p L)) (log(z+2)/log R)^2.
Multiply by min(1,2p/H)^s, sum over p>=R^.4 and the two signs. Using dyadic bands and the elementary prime upper count pi(v)<<v/log v, each band above H contributes O(1/log R) to the weighted harmonic sum, and bands below H decay geometrically with ratio 2^-s. There are O(1+log^+(S/H)) bands above H. This proves (1). No lower sieve, prime-tuple asymptotic or independence of CRT trajectories is used.

In particular, taking z=3 and summing over even residues yields
    C_H^bad := sum_(x non-twin in I) t_H(x)
      << R (1+log^+(S/H))/(log R)^3.                          (2)
At H=T, the factor is 1. At H=S exp(-(log R)^alpha), 0<alpha<1, the logarithmic exponent of the capacity is 3-alpha. This is a different upper sieve from the soft frontier: it selects near-square-root roughness by the actual upper limit on one-root time spent at a center.

## 3. Use the sieve for full-path gain, without endpoint fibers

Let omega(A,x) be any of the selected dwell weights in section 1, eta=N^-1 sum_(A,x) omega(A,x), and G=A-x>=0. For a fixed x, the possible A are spaced by 6 and >=x. Thus, for any nonnegative decreasing function psi,
    sum_A omega(A,x) psi(A-x) <= t_H(x) sum_(k>=0) psi(6k).
Sum over x. If twin pairs are finite, all centers in I are non-twin for large R. Applying (2) to FULL observation (eta=1) and psi=1_[0,D] gives
    Pr_(A,U)(G<=D) <= (1+floor(D/6)) C_H^bad/N
       << (D+1) (1+log^+(S/H))/(log R)^3.                      (3)
For own elapsed H=T and D=log^(3-epsilon) R, this tends to zero under finite twins. No condition on repeated small labels, terminal waiting, or synchronization is required. For own elapsed observation let tau_D be the first tick at which G>D, or infinity if none. Because G never decreases,
    E_A min(tau_D,H)/H = Pr_(A,U)(G<=D).
Hence (3) is also a quantitative first-passage restriction on actual paths. Conversely, a sequence of unbounded R with a fixed positive fraction of root-time having G<=log^(3-epsilon) R implies twin infinitude.

More general weighted moments: write m_x=sum_A omega(A,x), gamma=1+G/6. Sorting roots by increasing G gives gamma_i>=i for i=1,2,...; each weight <=t=t_H(x). For any increasing function of gamma, the minimum given total m_x is achieved by filling the earliest indices up to weight t, then a partial last weight. For s>0, comparison with the integral of u^s from 0 to m_x/t gives
    sum_A omega(A,x) gamma^s >= m_x^(1+s)/((1+s)t^s).
Similarly integrating log u (integrable at zero) gives
    sum_A omega(A,x) log gamma >= m_x log(m_x/t)-m_x.
Apply Holder and log-sum across x:
    (N eta)^(1+s) <= (1+s)(sum t)^s sum_(A,x) omega(A,x) gamma^s,
    (1/N)sum omega log gamma >= eta log(N eta/sum t)-eta.    (4)
All sums may be restricted to actual occupied support; for a selected subpopulation eta=0 interpret the statements trivially. With full observation, finite twins and H=T, (4) implies E log(1+G/6)>=3loglog R-O(1), and E (1+G/6)^s >>_s (log R)^(3s). These are displacement constraints on actual root-time, not entropy of a final endpoint. They give a sufficient bound on the geometric mean of displacement, not the (possibly heavy-tailed) arithmetic mean. The same inequalities with eta=theta apply to the terminal part alone.

An attempted shortcut: the deterministic height bound gives G<=2H+6 (or 3T+6 for synchronized windows), hence only E log gamma=O(log R), not the needed loglog bound. The first-use small-label gain <=R^(2 epsilon) controls only distinct first uses, not repeat gains or all later displacement. These two bounds cannot contradict (3) or (4). Neither a small-gain occupation lower bound nor a displacement logarithmic upper bound with coefficient <3 is proved here.

## 4. Apply prior Fourier cell moments to (1)

Let B_z be the full relaxed barriers of f32926b. Its cells [b_j,b_(j+1)) have full root capacities M_j=(b_(j+1)-b_j)/6, periodic mod L. Write M(x)=M_j for even x in cell j. Across the L/2 even residues in one period the mean of M(x) is the size-biased canonical mean E_per M=(1/K)sum_j M_j^2: each cell contains 3M_j even positions. Multiplying (1) by the nonnegative residue weight M(x) and summing gives the unconditional weighted non-twin capacity
    sum_(x non-twin) M(x) t_H(x)^s
       << R E_per M (log(z+2))^2
               (1+log^+(S/H))/(log R)^3.                      (5)
This weighted count is justified by a uniform residue-class sieve, not by treating roughness and the barrier partition as independent.

First use (5) on the initial-cell residence time of own elapsed paths. Let tau_exit(A) be the first completed exit from A's initial full cell. Only roots initially in that cell contribute to its pre-exit time; their count is <=M_j. Each has at most t_H(x) time weight at x. Consequently under finite twins
    eta_z(H):=E min(tau_exit,H)/H
       <= (1/N)sum_x M(x)t_H(x)
       << E_per M (log(z+2))^2 (1+log^+(S/H))/(log R)^3.       (6)
Apply the previously proved unconditional Fourier moment (7) of 19c2f29:
    E_per M <= min(K,8D_z[1+log^+(K/(8D_z))]),
    D_z=prod_(5<=p<=z)(1+p beta_p), beta_p=[(p-1)sin(pi/(2p))]^-2.
For z=a loglog R, fixed a>0, log D_z=(a+o(1))loglog R, so at H=T,
    eta_z(T) <= (log R)^(a-3+o(1))  under finite twins.        (7)
For a<3, almost all roots exit their small-label-protected initial cell by a vanishing fraction of T. Every exit label p>z by the barrier theorem. Nonnegative height gives elapsed exit time >=(p-1)/2-3. Thus for 0<lambda<=1, lambda T>=14, under finite twins
    Pr(no exit by T or first exit p>=lambda T)
        << eta_z(T)/lambda.                                  (8)
This extends the previous first-exit certificate to an all-root upper bound from the new sieve and the prior Fourier moment.

Attempted closure with static geometry: the height bound also gives tau_exit>=3k-3 for a root at offset 6k in a full initial cell, and T is much larger than K for z=a loglog R. Averaging over complete periods inside the slab (at least 1-O(K/N) of roots), the lower bound is of order E_per M/T up to O(1/T), not E_per M/log^3 R. Comparing with (6) yields only a bound of the order T >= log^3 R/(log(z+2))^2 when E_per M grows, which already holds. Static barrier widths and height cannot supply the missing lower residence estimate by this comparison.

Next apply (5) to the variable-cell relative transport of 19c2f29, for either convention. Pad all full cells meeting the actual slab as before; N'=N+O(T+K), P_j=M_j/N', mu_j=(M_j+d_j)/N', d_j=real terminal minus initial cell mass, X=chi^2(mu||P). Write theta_A for the fraction of observation in the terminal segment at Y(A), theta=E theta_A. Put t_j=max_(x in cell j and actual I) t_T(x), zero if the intersection is empty. Under finite twins theta_A<=t(Y(A)), and Cauchy-Schwarz with likelihood ratio mu/P gives
    theta^2 <= (N'/N)^2 (1+X) E_P t_j^2.
Since sum_j M_j t_j^2<=sum_(x in I) M(x)t_T(x)^2, (5) and the Fourier moment yield
    theta^2 << (1+X) E_per M (log(z+2))^2/(log R)^3.           (9)
Thus with z=a loglog R, a>0, a sufficient route to twin infinitude on unbounded slabs is
    X+1 <= (log R)^(b+o(1)), theta >= (log R)^(-c+o(1)),
    a+b+2c<3.                                                (10)
The earlier transport entropy condition involved a+2b<2 AND a time-penalty estimate. This terminal-only route has a wider permissible concentration exponent if theta is bounded below, and no repeat-occupation condition. It still needs a concentration upper bound and a terminal lower bound. No asymptotic such bounds are claimed. Our finite chi-square audit uses own elapsed T, so its theta differs from the synchronized theta of 5e932c4; (9) itself is valid in both.

## 5. Dwell channel: a direct entropy identity without roughness penalty

Return to full observation, now synchronized. Let A uniform and U independent uniform offset in [0,T), X0=X_U(A) the observed center (write X0 to distinguish it from chi-square X above). Then P(X0=x|A)=omega(A,x)<=t_T(x). Let C=sum t_T over all occupied centers (or the entire slab), rho(x)=t_T(x)/C on that support. The entropy identity
    H(A|X0) = log(N/C) + KL(P_X0||rho)
                          + E_(A,X0) log(t_T(X0)/omega(A,X0))      (11)
follows from H(A|X0)=log N+H(X0|A)-H(X0). Both added terms are nonnegative. Under finite twins C<<R/log^3 R, hence H(A|X0)>=3loglog R-O(1). This proves a sufficient criterion with neither outgoing-label nor terminal penalty:
    liminf H(A|X0)/loglog R <3.                              (12)
Do not replace H(A|X0) by endpoint entropy without accounting for unknown clocks.

There is also a one-shot, list-decoding version. For any list L(x) of at most m roots depending only on x,
    Pr(A in L(X0)) <= m C/N.                                  (13)
Indeed each joint atom P(A=a,X0=x)<=t_T(x)/N. This recovers (3) by the list of roots in [x,x+D] and supports the actual phase decoder below. It is valid without an entropy or average-log estimate.

## 6. Synchronization via departure phase instead of encoding the whole tick

Let J be the root's window and V be the first outgoing completed firing time from the observed center within that window's retirement, or a terminal marker. For a root and observed position V is unique since a root never returns to a center. It is also determined by (X0,U,J) through the first eligible clock at the observed tick. A completed V determines the unique winning label by that clock and center; all roots with the same (X0,V,J) therefore have the same future and endpoint Y. The terminal marker implies Y=X0. At most B0=ceil((3T+6)/W)+2=O(1) windows can contain a root visiting any fixed x.

Consequently, using Y a function of (X0,V,J) and Y a function of A,
    H(A|X0) = H(A|X0,V,J)+H(V,J|X0)
       <= L_end+log B0+H(V|X0,J).                            (14)
The equality uses V,J deterministic given A,X0. Moreover, V is a function of X0,U,J so
    H(V|X0,J)=I(A;V|X0,J)<=I(A;U|X0,J)
       = H(X0|A,J)-I(X0;U|J) <= H(X0|A).                    (15)
The displayed chain uses A and U independent conditional on J and X0 deterministic given A,U. Thus phase ambiguity is no larger than per-root time-partition entropy, and may be much smaller. We do not encode absolute times across the T-tick window uniformly. The previous soft frontier penalty Q_R and this actual phase entropy are different quantities; neither universally dominates the other.

New arithmetic upper estimate on the phase ambiguity: for a nonterminal visit at x let p be its completed outgoing label and n_f its firing tick. Put x'=x-p+1, h'=n_f+x'/2>=0. For even n_f the height satisfies h'=0 mod p; for odd n_f it satisfies h'=3 mod p. Encode h'=(c mod p)+kp with c=0 or 3 and integer k>=0. The sign/parity is determined by p dividing x+1 or x-1, disjoint for odd p. Thus (p,k) determines n_f and hence V, even when p=3 and the residue 3 mod p is zero. For a root visiting x, the elapsed age when it reached x is <=3G, since every completed wait <=2q<=2p<=3(p-1), where G=A-x. The outgoing wait <=2p. Therefore h'<=3+2.5G+1.5p+.5 and k<=4+2.5G/p. This uses full gain from birth, including any pre-window jumps.

A valid inverse probability code conditional on x,J: assign half to terminal marker, half to nonterminal; choose p from the distinct factors of x±1 with probabilities proportional to log p; then choose k from a normalized law proportional to 1/[(k+1)(1+log(k+1))^2]. The total log of candidate factors is <=2log(2R+1); invalid words can be discarded. This gives code length for a nonterminal phase
    <= log(2log(2R+1)/log p)
       + log(1+G/p)+2log(1+log(1+G/p))+O(1).
The coefficient of the height quotient logarithm is one, up to a subleading loglog. For finite audit use the simpler normalized k law 1/[(k+1)(k+2)], coefficient two. Both are valid. The code depends only on x,J, not on the unknown A; G is used solely in its upper bound.

Do not charge even this code on all visits. At each (x,J) choose the phase of largest observed root-time mass; let lambda be the total root-time fraction in other (minority) phases. Encode a majority/minority flag and use the arithmetic code only on minority. Discarding the major phase preserves the subprobability property, so conditional entropy on minority is bounded by its expected code length. Jensen for binary entropy h gives
    H(V|X0,J) <= h(lambda)+E[1_minority ell_code(V)].
Fix epsilon<1/4 and let sigma_min be the fraction of visits both minority and nonterminal p<R^epsilon; B_min=E[1_minority,nonterminal log(1+G/p)]. The above heavy-tail code yields
    H(V|X0,J) <= sigma_min loglog R + B_min
                          +O_epsilon(1+log(1+B_min)).         (16)
The label rank costs O_epsilon(1) for p>=R^epsilon. As in 5e932c4, all first-use low-label time is o(1), so sigma_min<=sigma_rep+o(1) if using its same cutoff. No bound on B_min, or on the minority incidence, is assumed. The code pays only actual phase ambiguity, not every move; unlike the prior reverse code it does not reconstruct a long trajectory.

## 7. Use the one-shot capacity to eliminate phase rank costs

For each x,J choose the k phases of greatest observed root-time mass (or all if fewer). Let lambda_k be the mass fraction not in those phases. Each phase fixes a final Y. If its global endpoint fiber m(Y)=#roots with that Y is <=m, put those roots in a list; if the fiber is larger discard the phase. Since there are at most B0 windows at x, the resulting list at x has size <=B0 k m. Applying (13) under finite twins gives
    Pr(m(Y)<=m and visit in top k phases) << k m/(log R)^3.
Therefore
    Pr(m(Y)>m)+lambda_k >= 1-O(k m/(log R)^3),              (17)
    L_end >= log m [1-lambda_k-O(k m/(log R)^3)].
For k=1, m=floor(log^(3-delta) R), fixed delta>0,
    L_end/loglog R >= (3-delta)(1-lambda-o(1))               (18)
under finite twins. In particular an endpoint entropy coefficient <=2 and a fixed majority-phase capture >2/3 on the SAME unbounded slabs suffice for twin infinitude. More generally limsup lambda<=lambda0 and L_end coefficient strictly below 3(1-lambda0) suffice along those slabs. No entropy-of-rank bound or positive terminal fraction is required. This actually uses the new dwell sieve and actual phase decoder to give a weaker additional requirement than controlling all phase entropy; the proof does not claim any asymptotic estimate for lambda.

Tried closing (18) with the elementary phase bounds. Terminal phase is unique at each x,J, so lambda<=1-theta, which gives the older terminal-majority route if theta>2/3 and L_end coefficient<=2. Also lambda<=1-exp(-H(V|X0,J)) by entropy >= negative log maximum conditional phase probability and Jensen. Neither is an unconditional bound lambda<1/3: the known height and gain caps do not give theta>2/3 or uniformly small time-partition entropy in (15), and the observed small minority code cost in (16) has not been bounded as R grows. The phase criterion is a sharper actual target, not a closure. A proof of phase sparsity must use arithmetic constraints on repeated visits at distinct clocks, or use a different route. The previous static geometry, entropy moment and elementary phase estimates alone do not finish the proof.

## 8. Independent implementation, finite audits and persistence

All reusable source files are committed on research/min-local-crossing-support, fetched at their exact commit and verified. A and B use the existing ECMAScript factor-calendar clock; executed before commit and re-executed on remote readback. C is an independently implemented literal per-tick gcd replay executed as a real Python process in the working container. It checks small finite controls, not the asymptotic sieve or analytic proof.

A. [Dwell/gain audit 3d73eda](https://github.com/tara-sooo/A166944-Lean/blob/3d73eda3dee34588c614da8ad5fab42052da4985/research/min_local_negative_dwell_gain_capacity_audit.mjs), blob 6275667bf6d88c7a9586bb9d3a5785e0dc49de5d. Six slabs R12000..2000000, own elapsed T. 622004 roots, 15877617 completed root events, 16495323 nonzero dwell segments, 4716869 counted packing/structural checks, additional local clock and semiprime checks. For R480000 and 2e6 also variable-cell weighted capacities, pre-exit and terminal chi-square bounds. At R2e6 full time mean gain597.2863, E log(1+G/6)=3.63694793, theta=.61800026, terminal-weighted conditional mean gain572.1749. Bad dwell capacity17129.49775, full occupied capacity27755.24888. Among tested small-gain CDF cuts the best lower certificate was D=0, 19284.5982; log-gain lower certificate3229.0697 and first-moment1657.5860 were much weaker at this finite size. The D=0 certificate includes existing twin births; no asymptotic contradiction or extrapolation. The terminal chi-square bad bound did not contradict the measured theta^2 at any tested cutoff; no success claimed for (10).

B. [Dwell phase audit 88f110e](https://github.com/tara-sooo/A166944-Lean/blob/88f110ec3c3042ef989356ed1280888d4c7a96cf/research/min_local_negative_dwell_phase_entropy_audit.mjs), blob 618a805b4027837ea36f6f4be1ddaebe23f4e2dd. Six same slabs but SYNCHRONIZED observation. 622004 roots, 17010526 completed root events, 9730511 nonzero observed segments, 10367255 counted phase endpoint/disjointness checks, additional quotient/Kraft/capacity entropy assertions. Exact phase-key endpoint equality, phase intervals disjoint within position/window, height quotient bound, arithmetic code mass, (11),(14),(15), minority code entropy bound checked (floating-point diagnostics).
    R       L_end     H(A|X0)  H(X0|A)  H(V|X0,J)   lambda     minority code upper
    12000   2.492899  2.444259  1.056931 .08370115   .03874837  .38108072
    48000   2.992458  2.904122  .967063  .06131029   .02715306  .27413048
    192000  3.389066  3.319101  .912642  .05478217   .02472624  .24999275
    480000  3.658996  3.555330  .815285  .04702285   .02041034  .21562290
    1000000 3.807664  3.707535  .741356  .03931894   .01730686  .18580499
    2000000 3.989016  3.880228  .692784  .03436318   .01492752  .16253009
At R2e6 H(J|X0)=.35542851, H(A|X0,V,J)=3.49043673, B_min=.03140494, mean minority label-rank cost .02708913. The exact all-support entropy certificate N exp(-H(A|X0))=6882.0293 is smaller than bad capacity17143.9895, so that entropy certificate alone does not give a finite contradiction here despite existing twins. Formula (18) provides a more targeted asymptotic condition on majority phases; finite values do not establish its hypotheses.

C. [Literal gcd independent implementation 3bf19e8](https://github.com/tara-sooo/A166944-Lean/blob/3bf19e8007bf706e99741c36bfe2c3c27f0dadab/research/min_local_negative_dwell_literal_crosscheck.py), blob 44cbc7798b581fd68820cebe61ca7600ca03e5f9. Run python research/min_local_negative_dwell_literal_crosscheck.py 12000 48000. Executed actual Python in container: R12000 2001 roots,310155 literal ticks,20702 visits,3236 occupied positions; R48000 8001 roots,2480310 ticks,112871 visits,13091 occupied positions. Every endpoint and per-root dwell histogram matched independent factor-calendar replay. 133573 exact integer per-visit gain CDF checks and integer first-moment packing inequalities per position and globally. This does not certify the asymptotic sieve. No Lean executable/lake available in container, no Lean kernel run, no independent analytic referee. No main or sibling changes.

All new asymptotic necessary conditions under finite twins (3),(4),(7),(8),(9),(11),(17) follow from the proved upper sieve and exact dynamics, not from numerical extrapolation. The contradiction still requires one of the missing positive lower or concentration/entropy upper estimates. The prior Fourier-to-transport results were actually used in (6)-(10); attempts to close via static lower residence, total gain/first-use cap, and terminal/phase bounds did not succeed. The strongest next direction suggested by the calculations is the joint low endpoint mass and dominant phase condition (17)-(18), alongside the full-path gain CDF (3); proving either on unbounded slabs remains open.