# Height-localized positive flux and uncapped sparse-level supply

Continuation of [6433547](https://github.com/tara-sooo/A166944-Lean/blob/64335472d06ac37b03076a7f59c5cb17e854c131/research/2026-11-26-min-direct-uncapped-flat-run-and-variation-supply.md). Replace small total variation by a localized potential that records ordinary-deficit change only in a union of height intervals assigned to selected ending deficits. Even if a trajectory repeatedly leaves and returns to these levels, almost all fast high gain ending at a sparse collection of heights must be paid by actual positive flux through those height intervals from outside the selected population. This strengthens the earlier conditional flat/near-flat capacity in a different direction: no bound on total variation, multiplier size, relay lengths, or common deficit baseline. The scope is a sparse weighted prime support of selected ending heights and a small union of guard intervals, not arbitrary high-deficit populations.

## 1. Rough-clock gain capacity uniform down to any growing label threshold

Take a contiguous actual canonical block with even pre-horizons H in [X,Y], Y=lambda X, fixed lambda>1, and C=floor sqrt(Y+1). Ordinary plateau deficits d,d' satisfy d'=d+2w-g, g=p-1, w<=2p, d>=0 and d'<=6+5(H+g-H_root). Take integer T->infinity, T<=R<=C, k=floor sqrt(T)>=3. For a selected high nonreset p in [T,R] split events into short clock (k w<g) and extended clock (k w>=g). The extended class is considerably larger than the earlier long class 4w>=g; its minimum relative waiting time tends to zero. In particular every event with strictly increasing ordinary d belongs to the extended class.

For every fixed p>=T and either side e, the gain of ALL extended-clock occurrences with this p and side on the block is
    O_lambda(X/log^2 p).                               (1)
Indeed w>=g/k>=(p-1)/sqrt(p). Every odd prime f with 2f<w is excluded from both H+-1, since f is eligible and a strict future competitor clock is at most 2f ticks away. On the progression H=e+pq, q=(H-e)/p in a translated interval padded to N=ceil(Y/p)+2 integers, both q and pq+2e avoid zero modulo each odd f<=z=floor(p^(1/24)) for sufficiently large T. The two forbidden residues are distinct since f<p and 2e is nonzero mod f. The self-contained Selberg estimate in [global sieve](https://github.com/tara-sooo/A166944-Lean/blob/64335472d06ac37b03076a7f59c5cb17e854c131/research/2026-11-26-min-direct-global-sieve.md) gives S<=N/G(z)+z^6, G(z)>>log^2 z. Here N>=p because p^2<=Y+1, z^6<=p^(1/4), so the error is absorbed in O(N/log^2 p). The chosen padding is O_lambda(X/p); each q and side fixes one actual first horizon, which cannot recur on a monotone ray. Multiply by p-1 to prove (1), sum the two sides if desired. No prime cofactor assumption: both forms need only avoid the small sieve primes. No fixed power lower bound on T relative to X is required. Using this shorter cutoff rather than N^(1/12) is essential when p is subpolynomial in X.

## 2. Ending-height support, even for unbounded multipliers

Let A be any finite set of even ordinary deficit heights >6, and select ANY subset of actual nonresets p in [T,R] whose ordinary post-deficit belongs to A. The selection may omit arbitrary events and need not be contiguous. At height a=d', the exact post formula a=2hp+6I implies
    p | a/2   or   p | (a-6)/2.
For p>=T>=7 these positive integers cannot both be divisible by p because their difference is 3. Thus the side is fixed by the ending height and label. In fact each fixed height/label also has the earlier exact first-horizon progression H=e+p(2I-2h-1) mod4p. The theorem below does not need to count occurrences separately on this finer progression.

Define the union of eligible prime supports
    S(A) = {prime p in [T,R] : p divides a/2 or (a-6)/2 for some a in A},
    D(A) = sum_(p in S(A)) 1/log^2 p.
For each actual selected label p count its extended-clock gain only once, irrespective of the number of heights at which it occurs. Equation (1) gives
    F_ext <= O_lambda(X D(A)).                          (2)
This weighted support can also be replaced by the smaller actual selected prime support, if known. It is NOT the number of multipliers, or the sum of prime supports over separate visits. In particular on a canonical block every actual positive ending height is O_lambda(X); we may discard unused heights from A. With b=max(1,floor(log(K_lambda X)/log T)) for a suitable envelope constant K_lambda, each height contributes at most 2b high prime factors. Therefore
    D(A) <= 2b |A|/log^2 T.                             (3)
For T>=X^eta with fixed eta>0 this shows that an arbitrary o(log^2 X)-element collection of actual ending heights has o(X) extended-clock gain, regardless of distances between the heights or repeated excursions. The weighted-support form (2) is stronger when many levels share prime factors. No fixed multiplier cap, low ordinary variation, or absence of twins is imposed. This capacity applies to all positive ordinary deficit production within the selected population since every increasing event is extended.

## 3. Localized flux potential and exact payment of short-clock gain

For each USED ending height a of the selected list, let g_a be the maximum gain p-1 of its selected occurrences, including extended ones. We can instead use the maximum over the eligible divisor support at a, or use the maximum over short-clock occurrences alone, omitting levels with no such occurrence. Either modification preserves the proof. Define the finite union of height intervals
    E_A = union_a [a,a+g_a],
    M_A = length(E_A).
Use the nondecreasing 1-Lipschitz potential
    Phi(d)=length(E_A intersect [0,d]),  d>=0.
This is a potential on plateau ordinary deficits, not on the horizon; intervals are in deficit space. Its range is contained in [0,M_A]. In particular
    M_A <= sum_a g_a <= |A|(R-1),
    M_A <= max A-min A+R-1
when A contains at least one used height. The union may consist of separated intervals; count overlaps only once. For each physical event i, define its positive localized flux to be
    P_i=max(0,Phi(d'_i)-Phi(d_i)).
Equivalently for an increasing event it is the length of E_A intersect (d_i,d'_i], and for any other event it is zero. Define P_ext,out=sum P_i over ALL unselected physical events in the block. The subscript out refers to the selected list, not to the height intervals. Only their actual positive variation WITHIN E_A is charged. In particular P_ext,out<=5 U_out, where U_out is the full complementary gain.

Let F=F_short+F_ext be selected gain, where short means k w<g as in section 1. Set alpha=1-2/k>0. Every selected short-clock event has
    d-d'=g-2w>alpha*g.
Because its post a=d' and the interval [a,a+g] lies in E_A, its actual localized potential decrease is at least alpha*g. This holds even if the event starts very far above the ending height, and irrespective of other selected heights. All selected positive flux is from extended-clock events and each satisfies
    Phi(d')-Phi(d)<=d'-d<=3g+4.
Thus selected positive flux <=(3+4/(T-1))*F_ext. By exact telescoping of Phi on the entire block, all localized negative variation is at most positive variation plus Phi(d_a)-Phi(d_b). In particular
    alpha F_short <= (3+4/(T-1))*F_ext
                        + P_ext,out + Phi(d_a)-Phi(d_b).  (4)
This endpoint term can be negative. For a simpler upper bound replace it by M_A. Hence
    F <= [1+(3+4/(T-1))/alpha]*F_ext
                     + (P_ext,out+M_A)/alpha.           (5)
No repeated initial deficit charge is made. Unlike the previous ordinary deficit budget, the initial potential is at most M_A even if the inherited ordinary deficit is of order X. Nor can positive variation at distant heights pay for these short events unless its actual upward path crosses E_A. The coefficient of F_ext tends to 4, and that of the outside flux tends to 1. This tends to the full gain cost for short events, not the half-gain cost from the older split 4w<g.

Combining (2) and (5) yields the uncapped height-localized upper supply bound
    F <= O_lambda(X D(A)) + (P_ext,out+M_A)/alpha.       (6)
The constant is independent of the number, positions, or diameter of the selected height intervals, and of T and R. For T large alpha>=1/2 and the coefficient in (5) is bounded. For a macroscopic population F>=rho X, the necessary condition is
    D(A) + P_ext,out/X + M_A/X >>_(lambda,rho) 1.
In particular if D(A)=o(1) and M_A=o(X), then
    P_ext,out >= (1-o(1))*F - o(X).                      (7)
Since P_ext,out<=5 U_out, a macroscopic sparse-height selected population must have macroscopic complementary gain; more specifically the complement must actually supply positive variation at these heights. This holds even if total ordinary variation is macroscopic and the selected list has very long intervening relays. For example, if the entire selected support in a canonical window consists of o(log^2 T/b) ending heights, (3) gives D(A)=o(1) and M_A<=|A|R=o(X) because R<=sqrt(Y+1). Thus a macroscopic population with negligible complement must occupy at least Omega(log^2 T/b) distinct ending heights, without any low-variation assumption. For fixed eta>0 and T>=X^eta this is Omega(log^2 X). This is a distinct-height lower bound, not just the earlier label-diversity or small-variation lower bound.

If A is contained in a strip of width o(X) then M_A=o(X) automatically, even if the strip contains far more than log^2 T distinct heights; (6) then gives a weighted-prime-support alternative. More generally one can use several widely separated sparse sets in ONE selection, with a single union E_A and a single application of telescoping. If instead using pairwise disjoint physical blocks and changing E_A between blocks, one must keep their endpoint potential differences; no claim of cancellation of different potentials. On a single block, several disjoint guard unions have total positive flux bounded by actual ordinary positive variation, because their height indicators sum to at most one. Overlapping guard intervals should be merged or paid with their actual multiplicity.

## 4. Connection with the global crossing alternatives

For an actual crossed window [X,16X] on a fixed hypothetical infinite canonical ray use the earlier hybrid cut family and cube threshold T3 from the crossing-clock hierarchy (or the grouped-cut version with its updated kappa and o(X) error). Let U_c be the entire gain outside the actual surviving-cut crossers with p>=T3, and M_<T3 their complementary actual crossing mass below T3. The existing coverage estimate is U_c<=M_<T3+o(X). This follows from the prior smoothing with ell/T3=o(1); the argument here does not change its Fourier exponent.

Suppose the selected high nonreset population in section 3 has F>=rho X, D(A)=o(1), M_A=o(X). By (7), its complement must supply at least (rho-o(1))X positive localized flux. Count the positive-flux outside events either outside the cube-certified high crossing family (gain <=U_c), or in that family. In the latter case retain only actual unselected high crossers with positive Phi change, hence d'>d, and let F_up,local be their gain. The usual drift envelope gives
    P_ext,out <= 5 U_c+(3+4/(T3-1))*F_up,local
              <= 5 M_<T3+(3+o(1))*F_up,local+o(X).
Thus either M_<T3=Omega(X), which implies the prior small/middle crossing-count alternatives, or F_up,local=Omega(X). Each event in this latter supply population is an upward nonreset for sufficiently high starting/ending heights if E_A stays above 6; indeed any event with positive Phi change must have d' above some height in E_A, hence d'>6. It has 2w>g, so the cube certificate yields prime selected cofactor. Its actual positive-deficit segment intersects E_A in positive length. Since all physical label gains are <=C and ordinary increases <=3C+1, it begins no more than 3C+1 below some guard height and ends no more than 3C+1 above it. This is a level-localized version of the earlier positive-variation precursor alternative. It identifies where the external upward source is required, not merely that there was positive variation somewhere in the window.

The selected sparse-height/weighted-support condition has not been forced by the earlier crossing alternatives. In particular the actual high population may spread over a great many ending heights and primes, making (6) trivial. The original small/middle crossing counts, general large upward supply, and complete finite-twins contradiction remain open. The next useful target is to obtain an upper bound on this outside positive flux (or force a certified twin witness), or to exploit the alternative of many ending heights using an arithmetic restriction relating their successive level crossings. No global upper bound on total ordinary variation is claimed.

## 5. Diagnostics and preservation

[Audit c049711](https://github.com/tara-sooo/A166944-Lean/blob/c049711033d4250dbadcc7b8d5ae54bc9b1f626b/research/min_direct_height_localized_flux_audit.mjs), blob e8eaf7426dc662ee645f0479173ee3c3556be814. Exact remote readback. Run node research/min_direct_height_localized_flux_audit.mjs 40000. Executed actual ECMAScript in tool runtime. 19998 odd canonical roots through40000,352451 actual MIN events,0 unresolved cap180. 136915 finite selected-population controls with T9/17/31/61 and arbitrary height subsets (all, nearby heights, same residue mod6), plus late-start controls;345322 selected incidences,272052 extended clocks,73270 short clocks;345322 exact divisor/side/fixed-level phase checks,2043 repeated height/label/side spacing checks. 2143116 competitor roughness and corresponding cofactor residue tests each.3489207 Lipschitz/monotonicity controls,73270 localized short-drop tests,846917 outside positive localized flux incidences,136915 union and net flux/gain budget controls,7259 inherited-high-baseline controls,66065 multilevel and42415 disconnected union controls.3000 independent synthetic interval union controls, not claimed MIN trajectories. Example T9,k3,ending heights44,78,108,110,labels11,19,13,17, union length46, F66,F_ext48,F_short18,P_ext,out26,selected positive flux32, U_out38,d_start6,d_end120. Counts overlap across roots and selections; the finite audits test exact arithmetic and potential bounds, not asymptotic sieve constants or the old smoothing certificate. All assertions passed. No Lean executable/kernel verification, external novelty claim or final contradiction. Main and sibling branches unchanged.
