# Negative MIN: reverse-depth occupation bounds and explicit canonical reset fans

2026-11-28 JST, Issue #10, parent #1. Continue from b6b7282544f72de714c53fac138c731b4220e915. Goal remains actual negative-MIN proof of unbounded twin primes. No growing-scale lower bound or unconditional twin proof is established.

## 1. Previous phase integrals verified

The previous four pending declarations arrivalMass_sum, arrivalMass_clip, stationaryPhase_clip_integral, stationaryPhase_pair_integral now compile. Run 46053710911 had one complement-length normalization error in arrivalMass_sum; fixed at 50bce1324daa4e949f7337f91930f759e0d21ad7, CI 46054551834 success. No change in statement. Included in final green core below.

## 2. Clock-free reverse ancestry (kernel checked)

If an actual nonidle tick with prime p arrives at x>2, its source is y=x+p-1; the even clock gives p|x, the odd clock p|(x-2). The corresponding height/clock pins from earlier research still apply. In particular p<=x (the exclusion x=0,2 is essential).

For fixed upper spatial limit U, reverseParents U x lists the positions x+p-1<=U for odd prime divisors p of x or x-2. The list forgets the clock and least-prime tie-break: its members are POSSIBLE spatial predecessors, not necessarily actual eligible ticks or reachable roots. reverseReach U x d recursively applies these parents or stays at the same position for d steps. Every actual trajectory from s with s.x<=U and endpoint x>2 has its original position in reverseReach U x (eventCount s k). Induct on ticks: a quiet tick changes neither x nor eventCount; a firing supplies one verified predecessor. Staying allows padding to any larger depth.

If the maximum parent count on (2,U] is B, reverseReach length <=(B+1)^d. The length counts paths with repetitions, so distinct reachable roots are bounded by it. In particular shallowObsFiber_bound applies to the actual synchronized observed fiber, counting roots with <=d firings since birth (INCLUDING pre-observation). Since distinct prime factors of m<=2R+1 have product at least omega(m)! (and divide m), omega(m)=O(L/log L), L=log R. Thus B=O(L/log L), and d=2 ancestry fits M~L^2.1 for all sufficiently large R. This statement is about a shallow subcohort, not about all roots at the bin. Deep arrivals can still saturate it.

## 3. A stronger growing-depth bound via maximum-degree vertices (paper)

Use the relaxed spatial graph on even sites in I=[R-3T-6,2R], with directed edges from y to y-p+1 for odd primes p|y+1 or p|y-1, retaining only endpoints in I. Add a self-loop at each vertex to pad paths. All actual observed trajectories up to retirement lie in I by the canonical gain bound; for sufficiently large R, I lies in (2,2R]. Define Delta(v) as the maximum of in-degree and out-degree, including the self-loop. Both are at most
    1+omega(v-2)+omega(v-1)+omega(v)+omega(v+1).
The graph contains all spatial firing edges of actual trajectories. It may contain many others.

For any S subset of vertices, let P_d(S) be the number of padded length-d spatial paths ending in S (all starting vertices allowed). Every path either has all vertices of degree <=K, or has a vertex v of maximum degree Delta(v)>K. The first class contributes at most |S| K^d by backwards enumeration. For the second, fix v and its index i in the path (0<=i<=d). In the subgraph induced by vertices of degree <=Delta(v), at most Delta(v)^i predecessor paths and Delta(v)^(d-i) successor paths extend from v. Their product is <=Delta(v)^d. Summing over v and i, possibly overcounting, gives the exact finite inequality

    P_d(S) <= |S| K^d + (d+1) sum_(v:Delta(v)>K) Delta(v)^d.       (1)

Crucial: the large-degree term uses the MAXIMUM-degree vertex of the path, not global worst-case degree after the first exceptional vertex. This avoids an exponential-in-d global maximum-degree factor. No independence of neighboring factor counts, no CRT along a full path, no assertion of actual reachability.

Let X=2R+1. Elementary reciprocal-prime bound: taking s=1+1/log X, for p<=X we have 1/p<=e p^-s. Euler product gives sum_p p^-s<=log zeta(s)<=log(1+log X), so sum_(p<=X)1/p=O(log L). Count integers with omega(n)>=j by selecting j distinct prime divisors and summing floor(X/product):
    # <= X (sum_(p<=X)1/p)^j / j! <= X (C log L/j)^j.
For Delta>=k one of the four factor counts is >=(k-1)/4. Thus for k>=K=A log L, choosing fixed A sufficiently large yields
    # {v:Delta(v)>=k} <= C R exp(-k)
(the exponent 1 is arbitrary fixed by increasing A). Uniform over k in the finite degree range. For d=floor(c log L/loglog L), fixed c>0, summing k^d exp(-k) for k>=K gives
    sum_(v:Delta(v)>K) Delta(v)^d <= O(R (K+1)^d exp(-K)).
Indeed the ratio of consecutive summands <=exp(d/(k+1)-1)<exp(-1/2) eventually. Including d+1, choose A sufficiently large for any fixed C0 to make the exceptional term O(R L^-C0). Meanwhile K^d=L^(c+o(1)). Consequently

    P_d(S) <= |S| L^(c+o(1)) + O(R L^-C0).                     (2)

All asymptotics for fixed c,C0, no uniform limit c->infinity. For fixed d, the same proof gives a bound O(|S| (log L)^d + R L^-C0).

A cap-safe actual subcohort: restrict to histories with <=d firings and every prior spatial site of degree <=K. The restriction is prefix-closed. For every observed or pre-observation bin, at most K^d such roots, via (1)'s good-path count with fixed endpoint. If c<2.1, K^d=o(M), so selecting exactly the roots while the restriction is satisfied gives a full-capped policy (possibly stop at violating arrival; only a prefix is retained). The roots lost because of a prior high-degree vertex, while still <=d firings, have total observed ticks <= T times (d+1)sum_bad Delta^d, by counting ordered pairs (A,x) admitting a padded exceptional path. Distinct A,x imply distinct paths, and a root stays at a given site for at most T observed ticks. Hence that lost mass/(NT) is O(L^-C0) for arbitrary C0, after increasing A. This is a deterministic arithmetic strengthening of the crude 2-jump cap-safe region, not evidence that a substantial fraction of roots stays shallow.

## 4. Near-square-root shallow occupation upper bound and a new depth obstruction (paper)

Use T~sqrt(R) exp(-L^.5), M~L^2.1 and d as in section 3. Let eta_d be the full, UNCLIPPED observed tick mass of roots whose completed event count since birth is <=d, normalized by NT. This includes any mask, since eta_d is raw. Take H=floor(T L^-a) for fixed a>.25. The shallow portion of a root occupies at most d+1 stationary phases. The contribution of phases with observed length <=H is <=N(d+1)H.

In a phase with observed length >H there are at least H consecutive quiet transitions, so each odd prime dividing x+1 or x-1 exceeds H/2 by the verified calendarWait <=2p. Call S_H all sites of I with both neighbors H/2-rough. A root present in such a shallow phase supplies an actual reverse path of length <=d ending in S_H; pad it to d. For every distinct (A,x) choose one path; different pairs give different paths. Thus long-phase mass <=T P_d(S_H). No additional factor for windows, phase clocks or repeated visits to x (actual x only decreases on firing).

The earlier near-square-root rough sieve (e.g. 2026-11-27-min-local-negative-square-root-horizon-and-rough-frontier.md, section 2) extends here: write Krough=H/2. Since Krough=R^(1/2-o(1)), each non-twin rough center has one neighbor q*r, Krough<q<=sqrt(2R+1), r prime and r>=q. For fixed q and sign, count the two forms r and qr±2 rough to a fixed sufficiently small power of R by a uniform two-dimensional upper sieve, giving O(R/(q L^2)). Summing q by dyadic Chebyshev prime counting over log-ratio O(L^.5+a log L) gives sum 1/q=O(L^-.5), and hence
    |S_H| <= twinCount(R,T) + O(R L^-2.5).
The sieve is the prior standard upper-sieve input, not a newly kernel-checked estimate. No lower-bound sieve at this cutoff is used. Combining (2) yields

    eta_d <= L^(c+o(1)) twinCount(R,T)/N
             + O(L^(c-2.5+o(1)) + L^(-a+o(1)) + L^-C0).       (3)

In particular if twins are finite, eta_d=o(L^-.25) for every fixed c<2.25 and a>.25. A lower bound eta_d>=c1 L^-.25 on unbounded slabs would instead force >>R L^(-c-.25-o(1)) twin centers. For c<2.1 the shallow cohort is cap-safe apart from an arbitrarily small exceptional mass as in section 3. However for c<1.75 the standard twin upper sieve O(R/L^2) together with (3) already makes such a lower bound impossible even if twins are infinite. Thus this particular sufficient lower target has a potentially useful exponent interval 1.75<c<2.1; actual abundance in that interval is entirely open.

An equivalent first-age consequence (without a short-phase term): if a canonical root has completed <=d events by age floor(T/2), one of its <=d+1 stationary phases has length >=floor(T/2)/(d+1). Its site is rough at cutoff of that order, which has the same L^-2.5 non-twin count. Each such root supplies a path to one such site. Consequently
    # {A: eventCount(birth A,floor(T/2))<=d}
       <= L^(c+o(1)) (twinCount+O(R L^-2.5)) + O(R L^-C0).
Under finitely many twins this implies that, for any c<2.5, almost every canonical root has more than c log L/loglog L firings by that age. For c<2.25 the exceptional fraction is o(L^-.25). The finite-support theorem implies in particular that any fixed finite number of distinct labels in that prefix is similarly rare. This lower bound on required event depth is NOT an upper bound on cost or a contradiction.

Related base-wall specialization: suppose all labels divide a positive even base modulus Q, or are >=Y1=exp(L^.85), with at most d0 of the latter. Every maximal base run stays in one Q-cell by evolve_wall. Reverse each nonbase jump from one of <=Q possible arrival sites in that cell; at most O(L/log Y1)=O(L^.15) possible prime labels per site, by product of distinct factors. Previous cell determined by the predecessor. At most Q(1+C Q L^.15)^d0 possible root positions per site (pad cell search with self-loop). If Q=L^o(1), d0<=13 is cap-safe eventually. A restricted prefix has O((d0+1)Q) stationary phases, because each completed base run has gain<Q and every event loses >=2. Use the same short/long argument, with d0<=14, to obtain normalized restricted raw mass <= L^(.15*d0+o(1)) twinCount/N + O(L^(.15*d0-2.5+o(1))+L^(-a+o(1))). Under finite twins this is o(L^-.25). This is a different restriction from unrestricted degree paths and excludes intermediate labels. None of these arguments assumes every history has bounded depth.

## 5. Constructive canonical direct reset fans (kernel checked local certificate, paper CRT)

Unlike a relaxed predecessor edge, the following gives actual reachability. Let x be even, p>=11 odd prime, x divisible by 4p, and A=x+p-1. Assume all odd prime factors of A±1 are >=p. For the canonical birth A at height3, put w=(p-7)/2. No event before w: until the first firing spatial state A is unchanged, any winner >=p would lose >=p-1, but nonnegative height bounds total gain by 6+2k<p-1 for every completed age k<w. At age w the absolute clock is -x/2, even and divisible by 2p. p divides A+1=x+p and no smaller label is possible. So the actual least-prime rule selects p, reaches (x,-x/2) at height0. If all factors of x±1 are >=11, three subsequent ticks are quiet and it reaches birth(x) exactly. This means it coalesces with the canonical root x at its birth, not merely at the same spatial position.

Choose a finite list of distinct primes p_i>=11 with p_i=1 mod6, all dividing x, and x=0 mod12. For each A_i=x+p_i-1 impose the same roughness certificate. If all these roots and x lie in the same synchronized observation window, they have already coalesced by observation. If x is P-rough with P>7+3T, x remains stationary throughout observation and all r+1 roots are in the same physical bin at every observed tick. Kernel stationary_birth_fan_bound: clipped fiber mass >=min(M,r+1). The local construction uses the actual clock and winner; there is no assertion about how many arbitrary relaxed parents are reachable.

For ANY FIXED r, a compatible congruence system exists. Choose primes p_1<...<p_r, each 1 modulo 6 times all primes <=2r+2 and all preceding p_j. Existence follows even from the standard elementary special case of primes 1 mod m: take a large integer n divisible by m and any finite excluded primes; a prime divisor q of cyclotomic Phi_m(n)>1 cannot divide n or m (constant term 1), and n has exact order m mod q by squarefreeness of X^m-1 in that field, so q=1 mod m. This is used only for fixed r, with no size-uniformity.

For each prime q>=5 up to Z>=max p_i, require x not congruent ±1 mod q (target rough). Additionally for every p_i>q forbid x=-p_i or 2-p_i mod q (source rough). If q=p_j, force x=0; compatibility follows from later p_i=1 mod p_j. For q<=2r+2 not selected, all p_i=1 mod q, so only ±1 are forbidden. For q>2r+2 not selected, at most 2(r+1)<q residues forbidden, except equality at q=2r+2 which is even and not an odd prime. Thus each local condition has a solution. Add x=0 mod12 and use CRT. The chosen primes are fixed constants in R.

This produces arbitrary finite simultaneous reset fan sizes for sufficiently large x. More quantitatively for Z=(log R)^theta, fixed 0<theta<1, modulus 12*product_(5<=q<=Z prime) q <=12 Z! = R^o(1). The proportion of allowed classes is c_r prod_(max p_i<q<=Z)(1-2/q), c_r>0 fixed. By the standard Mertens product estimate already used in the previous static-frontier note, this is asymptotic to a positive fixed constant/log^2 Z. Counting x in [R,2R] has additive error <=modulus, negligible. With T=floor((Z-8)/3) and W=6 floor(T/6), remove the O(R max p_i/T+max p_i) possible x too near right window or slab boundaries. This error is o(R/log^2 Z) for fixed p_i, so there are still >>_r R/log^2 Z valid target centers. Distinct x contribute to distinct stationary bins throughout their observation. The terminal mask is satisfied at every such bin. Therefore at this SHORT horizon,
    G_M/(NT) >>_r min(M,r+1)/log^2 Z.
This is an explicit actual-trajectory amplification of static rough occupancy. Constants depend strongly on r; no uniform result for growing r or near-square-root Z. The preceding analytic good-field upper requires T~sqrt(R)exp(-L^.5), not this logarithmic horizon. At that scale CRT full modulus is far too large, and the required rough-center lower is precisely the old parity barrier. Also direct roots number <=1+omega(x)+omega(x-2)=O(L/log L), too small to reach M~L^2.1 by one-step fans alone. Do not infer near-square-root twin lower or assume the fixed-r construction can saturate M.

## 6. Reproducible audit and status

research/lean/negative_min_reverse_arrival_audit.mjs @945de34836eb22d9c90707cdbfb84e319ec81544, blob 16f771049a50fa1027689a0fa29dda445673b7d5. Exact remote content comparison and ECMAScript replay identical. Run with node research/lean/negative_min_reverse_arrival_audit.mjs. 2,335,902 assertions; 7,200 actual roots, 160 sampled windows, 3,661,200 tick advances, 494,899 actual shallow ancestor checks, 3,837 long-phase checks, 126 degree-path bounds, 5,940 specified maximum-degree vertex checks in complete finite relaxed spatial graphs R=300,1200,6000. BigInt direct CRT fans: r=1,2,3,4,6,8; selected prime list prefixes of [13,19,31,43,61,73,103,109], Z=4 maxp+100, T=floor((Z-8)/3), R=x and W=6 floor(T/6), 3,913 ticks. Independent literal eligible-prime search up to height bound equals gcd selection on all BigInt ticks; all direct roots fire exactly once (their assigned p) at height0, then merge at birth(x). Largest example r=8 uses 218-digit center and T=176, 9 actual canonical roots share the entire observed stationary phase. This is not a twin-primality certificate.

Sample observed shallow raw mass/(NT), cumulative depths 0,1,2:
    R=12000,T=72,M=4:      .155179,.232292,.377749
    R=48000,T=144,M=8:     .110352,.158420,.255331
    R=192000,T=288,M=16:   .085715,.120558,.196647
    R=768000,T=576,M=24:   .066631,.094379,.152728
All these shallow subcohorts fit their respective proxy caps at every sampled observed bin (largest depth-2 multiplicity 4,6,6,6; full maximum 10,21,44,65). Counts use actual sample windows, not full slabs, not asymptotic parameters. Declining shallow fraction is consistent with the depth obstruction; not a proof of a decay rate or evidence of a near-square-root lower.

Final verified core research/lean/NegativeMINCore.lean @c9b2d47f7cf473e3f8768a7c9292d4b2205c536a, blob bd0fef2174a497a5c9988b169ea5441d66c5b649, 10,634 lines, 614 theorem declarations (+22 from last verified 592, including previous 4 phase formulas). Pinned standalone Lean v4.33.1 [CI 46055354706](https://github.com/tara-sooo/A166944-Lean/actions/runs/46055354706) success. Selected axioms for stationaryPhase_clip_integral, stationaryPhase_pair_integral, tick_incoming_spatial_pin, actual_reverseReach, shallowObsFiber_bound, rough_quiet, shortReset_merge_birth, stationary_birth_fan_bound are subsets of propext, Classical.choice, Quot.sound. No sorry/admit/axiom declarations. Failed intermediate elaboration runs 46054767644,46054995964,46055238025 fixed; 46054919286 canceled. Exact remote source inspected; no full Mathlib build. Maximum-degree path lemma, asymptotic tails, shallow upper and CRT density are paper deductions, not kernel formalized. No new external literature search or novelty claim, no human independent review. Main/sibling branches unchanged. Remaining: actual profitable good-phase lower at near-square-root horizon, especially deep histories with >c log L/loglog L firings; upper analytical sieve transfer review, Mathlib bridge. Next investigate high-degree-resistant compressed ancestry with a marked long stationary phase, and whether repeated low-label histories supply a growing lower-bound population without full CRT modulus. Issue remains open.
