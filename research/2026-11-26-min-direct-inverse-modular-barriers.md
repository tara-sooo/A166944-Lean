# Exact reverse-tick basins, locally isolated targets, and dense modular barriers

Continuation of [9352942](https://github.com/tara-sooo/A166944-Lean/commit/9352942690619d3981ec3f7dac8ee49e5ba3dcfd) on the independent direct-arithmetic branch. The principal new global estimate improves the far-event theorem in [8b30078](https://github.com/tara-sooo/A166944-Lean/commit/8b30078811529f94c7ecafb1b66b4a646d266069) from a fixed power loss to a subpower loss at the same logarithmic prime cutoff. It uses modular cut geometry, not the historical cost decomposition, waits, cofactor primality, or a sieve upper bound for trajectories. No proof of twin infinitude or A166944; paper proof, not Lean kernel verification.

## 1. Exact reverse tick, including time and competition

State (t,H) has even H>=8, canonical root H0=2M-2, t0=M+2=H0/2+3 for odd M>=5. At next tick n=t+1 let e=+1 if n even and -1 otherwise, I=(1-e)/2. The label is the least eligible odd prime divisor of gcd(n-2I,H-e), eligibility p^2<=H+1. If none, the tick is quiet (formal quiet continuation at terminal plateaus is permitted here). A nonunit event gives Z=H+p-1.

For a prescribed post-state (n,Z), the complete predecessor test is:
* Quiet candidate (n-1,Z), if no eligible prime divides gcd(n-2I,Z-e).
* Event candidate (n-1,Z-p+1) for every odd prime p dividing gcd(n-2I,Z+1-e). Retain it iff H=Z-p+1>=8, p^2<=H+1, and no smaller prime divides gcd(n-2I,H-e).

Indeed p|H-e iff p|Z+1-e, and any smaller prime divisor is eligible when p is. Both tests are necessary and sufficient for the single tick; there is no omitted preemption condition, since previous ticks are examined in their own reverse steps. Restrict predecessors to H<=2(n-1) when seeking canonical ancestors, by the envelope.

For every target Z, this gives an exact finite algorithm for ALL canonical roots whose forward trajectory visits Z, not just roots of bounded event depth. Seed (n,Z) at each integer n with 7<=n<=3Z+3 and Z<=2n; traverse backwards in decreasing n using the two tests and deduplicate states. Record any encountered canonical state n=H/2+3, H=0 mod4. Why this time range suffices: if a canonical root H0<Z first hits Z, it hits at an event, and the total elapsed time up to that event is <=3(Z-H0) by w<=3(p-1). Its absolute arrival n<=3Z-(5/2)H0+3<=3Z+3; the case H0=Z is immediate. Conversely any reverse path ending at a canonical root is a genuine forward path by the exact tick tests. Formal quiet ticks at a terminal cannot create a later visit to a larger horizon, so this does not falsely add roots even when Z is terminal. The basin of a terminal twin center is therefore computed exactly with no event cap. The algorithm visits at most O(Z^2) time/horizon pairs (not a subquadratic runtime claim or a uniform sublinear basin size bound).

## 2. A three-state reverse island compatible with twin admissibility

Fix integer R>=7 and an even target Z sufficiently large, satisfying
    Z=0 mod3, Z=3 mod5,
    Z not in {-2,-1,0,1,2,4} mod l for every prime 7<=l<=R.
These are simultaneous nonempty congruence conditions by CRT. Write d=Z-h for reverse offsets. The relaxed predecessor test at h is p|h or p|h+2, giving new offset d+p-1. The set of offsets {0,2,4} is closed under all possible reverse steps with p<=R: p3 sends 0->2 and 2->4, p5 sends 0->4, and neither has another exit; all p>=7 through R are excluded since the candidate divisibility tests use Z,Z+2,Z-2,Z-4. Clock/eligibility restrictions can only delete edges.

Therefore ANY path reaching Z from h>=Z-R+1 must start in {Z,Z-2,Z-4}, independent of event depth and time: total gain <=R-1 entails p<=R for every step. In fact the exact local canonical ancestor set in that band is:
    Z=0 mod4: initial horizons Z-4 and Z;
    Z=2 mod4: initial horizon Z-2.
For Z=0 mod4 the root at Z-4 has first tick quiet (gcd divides9 and 3 does not divide H-1=Z-5), then odd tick with gcd exactly5 (gcd divides5 and H+1=Z-3 is divisible5); p5 eligible for Z>=24, and gain4 reaches Z. For Z=2 mod4 the root at Z-2 has first even tick gcd dividing9 and divisible3; least prime3 eligible, gain2 reaches Z. The root at Z itself is trivial. In particular if Z is an actual twin center, these are exactly its local terminal basin roots. Every other canonical ancestor must have initial H0<Z-R+1 and enter the three-state set by a jump p>R. This latter necessary condition also follows directly by following the path until its first entry in the set; no assertion about how many distant ancestors there are.

The target congruences avoid Z=+-1 mod every odd prime<=R, including 3,5, so are compatible with local twin admissibility. They do not imply either neighbor is prime. For fixed R, their exact density among even Z is
    gamma_R=(1/15)*product_{7<=l<=R prime}(1-6/l)>0.
The six excluded residues are distinct at l>=7. By the elementary reciprocal-prime product estimates in the first-return-map note, log(1-6/l)=6 log(1-1/l)+O(1/l^2) for l>=13 (smaller primes fixed), so gamma_R=Theta(log(R)^(-6)). Let P_R=product odd primes<=R. In any even-horizon interval of length L, the count differs from gamma_R*L/2 by O(gamma_R P_R+1), using complete periods of P_R even integers and one partial period. For R=floor(c log X) with 0<c<1/(8 log2), Chebyshev theta(R)<=4 log2 R gives P_R<=X^(4c log2)=o(sqrt X). Thus in [X,2X] there are Theta(X/(loglog X)^6) such targets with local exclusion radius of order log X. Almost all of them are nonterminal: the upper sieve bound on actual twin centers there is O(X/log^2 X)=o(X/(loglog X)^6). This is a large family of locally isolated horizons, not a construction of twins.

## 3. Generalized modular cut barriers

Here the target is a cut J, not necessarily the terminal candidate in section2. For an even J, say p can geometrically cross J if some even pre-horizon H<=J<H+p-1 has H=e modp for one sign e. (Eligibility and clocks may further prohibit it.) Put delta=J-H, so delta is one of 0,2,...,p-3. For e=+1 the possible residues J modp are 1,3,...,p-2; for e=-1 they are p-1,1,3,...,p-4. Their union is precisely the odd residues 1,3,...,p-2 and the residue p-1. Hence the exact complementary residues are
    B_p={0,2,4,...,p-3},   |B_p|=(p-1)/2.
For p=3 this is {0}. The condition includes J=H: no low p is active at J itself. The half-open crossing interval [H,H+p-1) is essential: landing exactly on J is permitted and the next step that leaves J is responsible for crossing it.

Define an R-barrier to be an even J with J modp in B_p for all odd primes p<=R. No event with p<=R can cross such a J. This generalizes the old primorial-multiple barrier (which used only residue0 at each prime). CRT gives the exact density among even integers
    alpha_R=product_{3<=p<=R prime}(p-1)/(2p).
It is much larger than 1/P_R. Let A_R=alpha_R P_R be the integer number of barriers in one complete period of P_R even integers. For any even endpoints a<=b, with B_R(a,b) the number of barriers in [a,b),
    |B_R(a,b)-alpha_R*(b-a)/2| <= A_R.                (1)
Indeed there are floor((b-a)/(2P_R)) complete periods and a remainder of fewer than P_R even positions, containing between zero and A_R barriers. This sharper discrepancy is valid for arbitrary translates, not only intervals beginning at zero. Chebyshev's elementary pi(R)<=7R/log R and each factor >=1/3 give
    alpha_R>=exp(-7 log3 * R/log R)                  (2)
for R>=3. No distribution of primes in short intervals is assumed.

In any actual contiguous block from H_a to H_b, the jump intervals partition [H_a,H_b). Each barrier is thus assigned to a unique actual event p>R. In particular the total gain on high labels is >=2 B_R(H_a,H_b), since a jump of gain g covers g/2 even positions. The next section strengthens this to high labels FAR from square, without timing assumptions.

## 4. Far-event gain with only a subpower loss

Fix eps in (0,1) and lambda>1. For each event write H=pq+e, x=(p+q)/2, k=(q-p)/2. Near means k^2<=eps*x and x>=ceil(16/(1-eps)^2), as in the square-band packing note; for large H all events meeting the inequality meet the center threshold. Far means the complement. Recall that each center x can have at most one near event on a monotone path, and on pre-horizons in [X,Y] the total near gain is <=(Y-X)/2+O_eps(sqrt Y), with number of near events O_eps(sqrt Y). These follow from each jump exceeding the width of its center's square band and summing x over the possible integer centers.

Consider a finite block and partition its high (p>R) events into near and far. Let N_g be high-near gain, N_c their count, and F high-far gain. With total gain G=H_b-H_a, (1) gives the exact finite inequality
    F >= alpha_R*(G-N_g) - 2 A_R*(N_c+1).           (3)
Proof: total barriers >=alpha_R G/2-A_R. High-near intervals cover at most alpha_R N_g/2+A_R N_c. Low intervals cover zero. All remaining barriers belong to high-far intervals, which contain at most F/2 even positions. No assumption about which event types lie between them is used.

For an infinite canonical ray, take the block from its first horizon >=X to its first >=Y=lambda X. All pre-horizons in [X,Y), initial overshoot <=sqrt(X+1), and G>=(lambda-1)X-O(sqrt X). By square packing N_g<=(lambda-1)X/2+O_eps,lambda(sqrt X) and N_c=O_eps,lambda(sqrt X). Choose any fixed c in (0,1/(8 log2)) and
    R=floor(c log X).
Then P_R<=exp(4 log2 R)<=X^(4c log2)=o(sqrt X) and A_R=alpha_R P_R. Consequently the error in (3) is o(alpha_R X), even after dividing by the small density alpha_R. For all sufficiently large crossed windows,
    F >= ((lambda-1)/2-o(1))*alpha_R X.
Combining with (2) gives the new theorem:
    F >= Omega_(eps,lambda,c)( X exp(-C_c log X/loglog X) ),
    #high far events >= Omega_(eps,lambda,c)( sqrt X exp(-C_c log X/loglog X) ).
Here C_c>0 is a finite constant; the event count uses individual gain<=sqrt(Y+1). In exponent notation these are lower bounds X^(1-o(1)) and X^(1/2-o(1)), respectively. More explicitly, for any fixed xi>0 both are Omega(X^(1-xi)) and Omega(X^(1/2-xi)) eventually at the SAME fixed cutoff c log X. All these counted events satisfy p>R and q-p>2 sqrt(eps*p). No q primality or long-wait condition.

This improves the previous primorial-run filtering estimate for a logarithmic cutoff R=floor(eta log X/(4 log2)), 0<eta<1/2, from F>=Omega(X^(1-eta) log X) to F>=X^(1-o(1)); counts improve correspondingly. The proof uses the density of barriers and their discrepancy on long near-event intervals, rather than a worst-case bound on lengths of low-label runs. It does not establish a positive constant fraction uniformly when R grows, nor force labels of polynomial magnitude, nor guarantee long waits. Under finite twins every sufficiently high canonical ray is infinite and must satisfy (3) and the asymptotic theorem in every sufficiently large crossed window. The necessary condition is not yet contradictory to finite twins.

## 5. Diagnostics and reproducibility

[Audit 6a53bb5](https://github.com/tara-sooo/A166944-Lean/blob/6a53bb5f734170639538dc055bcfebebd2e097b1/research/min_direct_inverse_modular_barrier_audit.mjs), blob c272f82435ed8636ace47612150736e7d19f28fa. Exact remote readback. Run node research/min_direct_inverse_modular_barrier_audit.mjs 100000 180.

Actual ECMAScript execution in tool runtime (not separate Node process): exact reverse-tick algorithm for every even Z=8..600, 297 targets, 1,311,544 reverse states (time/horizon incidences), 230,598 event candidate tests; compared full canonical ancestor sets to 22,201 direct forward root/target tests, 759 matching memberships. No depth cap for these basin comparisons. Local isolation R=7,11,13,17,19,23: 1,941 target/cutoff incidences through Z200000, 23,838 reverse closure checks, 2,916 local canonical ancestor memberships; exact predicted sets all matched. Example R13,Z1578 has unique local initial horizon1576, target nonterminal.

Complete barrier periods for R=3,5,7,11,13,17:
    P_R = 3,15,105,1155,15015,255255;
    A_R = 1,2,6,30,180,1440.
Actual canonical scan odd M5..100000 up to180 events: 1,020,339 actual events on 48,906 nonempty paths. 4,041,436 low-event barrier exclusion checks, 293,436 block/cutoff checks of exact far inequality (3), all passed. Example M75671,R3, block H151340->154620, 546 barriers, zero on high-near intervals, far gain3150. These are finite prefix diagnostics, not macroscopic asymptotic window examples. No Lean kernel verification; no external novelty claim. Main and sibling branches unchanged.

Next: combine dense cut barriers with time/phase constraints so that the forced far large-label events cannot all be short waits or nonreset events, or find a genuine terminal existence argument. The local reverse islands constrain nearby basins but do not bound distant ancestors or produce arbitrarily large twin centers.
