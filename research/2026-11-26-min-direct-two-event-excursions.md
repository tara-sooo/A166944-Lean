# Long high-deficit excursions in two-event canonical returns

Continuation of [cafea3c](https://github.com/tara-sooo/A166944-Lean/commit/cafea3c33ea989eb4134c90125d85f5f0e36efd5) on the independent direct-arithmetic branch. The previous note gave lower bounds for high-deficit duration on an infinite ray and proposed seeking an opposing upper bound. Here an unconditional exact construction shows a limitation of such upper bounds: even first-return segments with just two nonunit events and a fixed first nonreset label 7 have very long high-deficit excursions. A finite Bonferroni count transfers the construction to actual integers at a super-polylogarithmic scale. This is a family of canonical roots, not a statement of infinitely many such excursions along one fixed ray. No twin infinitude proof or Lean kernel verification.

## 1. Exact two-event return

Canonical odd root M has (t0,H0)=(M+2,2M-2). Use the same adaptive eligibility p^2<=H+1. At an absolute tick n=t+1, pre-deficit d=2t-H, the raw gcd on the even side divides d+3, on the odd side divides d-3. More generally at offset j after a fixed plateau (t,H) with unchanged H, the even-side raw gcd divides d+2j+1, and the odd-side gcd divides d+2j-5. These follow by subtracting twice the appropriate clock argument from H-e; the gcd is odd and the defects are nonzero odd integers. This bounds all potential labels in a quiet interval by its defects, not by the absolute horizon.

Choose an odd prime r>23 with r=3 mod220 (thus r=3 mod4, mod5 and mod11). There are arbitrarily large such primes by Dirichlet's theorem. Impose the following conditions on the odd M:
    2M=2 mod3, 4 mod5, 3 mod7, 4 mod11,
    2M=0 mod13,17,19,
    2M=-3 modr,
    2M not in {-5,-3} modl for every prime 23<=l<r.
These are simultaneous nonempty local residue conditions. Require M large enough that r^2<=2M+5 and the initial and terminal small labels are eligible. In particular M>=r^2 suffices.

The first event is exactly p=7 at relative tick j=7. At initial quiet offsets j=1..7, the even-side defect (j odd) is 2j+7<=21, and the odd-side defect (j even) is 2j+1<=13. The imposed residues exclude all divisibility of H0+-1 by primes<=21 except 7|H0-1. The first even-side 7 clock is j=7 (2j+7=21); no earlier relevant defect is divisible7 on that side. The raw gcd at that tick is exactly7 (3 excluded). Thus t1=M+9 even, H1=2M+4, ordinary deficit d1=14, adjusted D1=14=2*7. This is a genuine nonreset event.

At H1, both neighbors avoid every prime<r. Indeed H1-1=2M+3, H1+1=2M+5, and all the small fixed residues and the fresh exclusions ensure this. Also r|H1-1, r does not divide H1+1. The next winning wait is
    w=(r-15)/2 >0 even.
For offsets 1<=j<=w, even-side defects are 15+2j for even j, odd-side defects 9+2j for odd j. They are positive and <r for j<w, and at j=w the even-side defect is exactly r. Thus all earlier ticks quiet, then r fires at n2=t1+w=M+(r+3)/2. Its new horizon H2=2M+r+3=2*n2, so d2=D2=0. Both events were actual least-factor adaptive events; there is no hidden competing eligible prime.

Because H2 !=2 mod3 (2M=2 mod3 and r nonzero mod3) and H2=0 mod5, the seven-tick normalization theorem of 123bbd4 gives exactly three quiet ticks to the canonical state H2,t2+3. This can also be checked directly using defects 3,5,1 at those ticks. The target is nonterminal: H2+1=0 mod11, with 11 eligible at the large horizon. This condition was imposed so the formal/actual return distinction does not arise. There can be no earlier new canonical state: before the first event H unchanged, afterwards d>=14 until the reset, then the canonical tick is three ticks later. The first return is therefore
    F(M)=M+(r+5)/2
with exactly two nonunit events 7,r, relative winning ticks 7 and (r-1)/2.

Between these events, the ordinary deficit is exactly 14+2j at t1+j for j=0,...,w-1. Its peak is r-3 just before the second event; there are precisely (r-3)/4 ticks with d>=r/2 (for r>23 in this prime class). These ticks are consecutive, followed eventually by the reset. In particular arbitrarily long high-deficit excursions are possible even with fixed first label7, fixed ordinary post-deficit14 at their start, and exactly one further event before normalization. No assumption about twin finitude or an arbitrary abstract phase is used.

## 2. Exact density for each fixed r

Let Q0=2*3*5*7*11*13*17*19. The small and r conditions specify one residue class modulo Q0*r. Each fresh prime 23<=l<r excludes precisely two distinct residues in that class (the modulus is coprime to l). Among all odd roots the exact density of the construction for fixed r, ignoring finitely many eligibility exceptions, is
    delta_r = 2/(Q0*r) * product_{23<=l<r prime}(1-2/l)
            = Theta(1/(r log^2 r)).                 (1)
The order follows from the elementary two-root prime product proved in the first-return-map note 6bdbf35; omitted small primes change only constants. Distinct r give disjoint sets of roots because their actual second event differs. This is a lower-density family of two-event first returns, not a formula for all possible two-event returns.

For example, for a fixed sufficiently large S, the primes r in [S,S^2] of the prescribed class give a finite disjoint union. The prime number theorem in the fixed arithmetic progression 3 mod220 implies
    sum_{S<=r<=S^2, r=3 mod220 prime} 1/(r log^2 r)
       = Theta(1/log^2 S).                           (2)
One way to see the order is to divide into dyadic subintervals. Each full [A,2A] contributes Theta(1/log^3 A); there are Theta(log S) such intervals between S and S^2, and log A comparable to log S. Thus even among roots with fixed first event7 at wait7, a family of two-event first returns has a heavy waiting-time tail of this order in the limiting distribution of roots. This uses the classical PNT in AP, not an assumed prime-tuple conjecture.

## 3. Finite Bonferroni transfer beyond the full CRT period

A complete CRT period up to r may exceed X when r grows faster than log X. We instead count the construction uniformly for r in a much larger range using elementary inclusion-exclusion.

Let X be sufficiently large and set
    U=exp(log X/(1024 loglog X)),   S=sqrt(U).
For any prime r in [S,U] with r=3 mod220, the initial small/r conditions select an AP of modulus Q0*r. All M in [X,2X] there meet eligibility because U^2=X^o(1). For a subset J of the fresh primes 23<=l<r, imposing that EVERY l in J violates its exclusion condition yields exactly 2^|J| residue classes modulo Q0*r*product_{l in J}l. CRT and the count of integers in an interval give
    N_J = X/(Q0*r)*product_{l in J}(2/l) + O(2^|J|).
This is a count over ALL integer M, but parity is already in Q0. The empty subset formula includes the bounded endpoint error.

Write beta_r=product_{23<=l<r}(1-2/l) and S1=sum_{23<=l<r}2/l. The earlier elementary prime reciprocal estimate gives S1<=3 loglog r for sufficiently large r. Let m be the smallest odd integer >=100 loglog r. Bonferroni gives a lower count using intersections through order m, and an upper count using order m+1. The analogous truncated alternating sums of the main products straddle beta_r, with difference the elementary symmetric sum of order m+1, at most
    S1^(m+1)/(m+1)! <= (e*S1/(m+1))^(m+1) = O((log r)^(-3)).
The first inequality follows by expanding the power and counting all ordered distinct factors; the factorial bound follows from integrating log or the standard elementary Stirling lower bound. Thus for sufficiently large r both main truncated sums are beta_r*(1+o(1)), since beta_r=Theta(log^-2 r).

The total counting error for each truncation is
    O(sum_{j<=m+1} 2^j binom(pi(r),j))
      <= O((2r)^(m+2)).
Uniformly for r<=U and r>=S, for sufficiently large X, m+2<=101 loglog X and log(2r)<=2 log X/(1024 loglog X). Consequently the error is O(X^(1/4)), which is negligible relative to X/(r log^2 r)=X^(1-o(1)). These estimates prove uniformly
    #{M in [X,2X] satisfying the construction for r}
       = Theta(X/(r log^2 r)).                      (3)
No lower-bound sieve theorem for prime tuples is needed; the bound uses only a finite Bonferroni expansion, CRT and elementary reciprocal-prime estimates. This counts integers with avoided small factors, not primes in the two linear forms.

Using (2) with U=S^2, and disjointness across r, proves that for all sufficiently large X the interval [X,2X] contains
    Theta(X/log^2 S) = Theta(X*(loglog X/log X)^2)
odd canonical roots in the constructed family with r between S and U. Every one has a first-return segment of exactly two nonunit events, with maximum deficit >=S-3 and at least (S-3)/4 consecutive ticks of deficit >=S/2. Since
    S = exp(log X/(2048 loglog X)),
these durations and deficit levels exceed every fixed power of log X. The constants in the Theta statements are positive absolute constants (the fixed AP is unchanged). This is an unconditional theorem using the standard PNT in one fixed AP solely for aggregating the r values. The elementary uniform bound (3) is separate.

Also using only r in [U/2,U] gives Theta(X/log^3 U) roots with durations Omega(U), hence a family-average lower bound Omega(U/log^3 U) for the first-return gap even from this restricted two-event construction (assign gap zero outside the subfamily, or use any nonnegative gap convention for the full family). This average over different roots is not the time average on a single infinite trajectory.

## 4. Consequences and limitation of the previous route

Any proposed upper bound on excursion length that is uniform over canonical first-return segments and polynomial in log of their initial horizon is false. This remains false when the first nonreset is always p=7 with d=14, and the first return uses exactly two events. Even an upper bound solely in terms of number of events or initial deficit cannot hold. The result is stronger than choosing abstract clock phases or forcing a long first wait: the large deficit begins after a real nonreset event and is dissipated by a real large reset, followed by a nonterminal canonical return. The construction gives super-polylogarithmic scales without a full exponential-sized CRT modulus being needed to fit inside [X,2X].

It does not disprove a bound applying only to the tail of each fixed infinite ray, with constants or thresholds depending on its root. The constructed roots vary with X; they may later terminate. It does not exclude an upper bound on the total gain or frequency of such excursions along a single ray. In particular it does not contradict the macroscopic high-deficit lower bounds of cafea3c; these two-event excursions occupy only X^o(1) ticks, rather than a macroscopic interval. An argument using the aggregate frequency on one ray would need additional global coupling. Under finite twins these constructed segments at sufficiently large roots would all extend to infinite rays, but this is consistent with that hypothesis.

## 5. Diagnostics and reproducibility

[Audit 2dafd0c](https://github.com/tara-sooo/A166944-Lean/blob/2dafd0c8250725aba4b491eeb2c1e08be9cf8503/research/min_direct_two_event_excursion_audit.mjs), blob 3667f7811d0456dea36059522e23b40d2b29bf95, exact remote readback. Run node research/min_direct_two_event_excursion_audit.mjs. Actual ECMAScript function execution in tool runtime, not a separate Node process.

Six primes r=223,443,883,1103,1543,2203 in the chosen AP. Three exact BigInt CRT lifts for each (18 roots), 3111 residue checks. For each r also enumerated 20000 consecutive candidates in the small/r AP (120000 total), found 29342 satisfying all fresh-prime exclusions, and independently ran literal tickwise gcd on the first five survivors per r (30 additional roots). Across 48 full first-return segments, 25712 literal ticks, verifying both event labels/ticks, eligibility, exact peak deficit, exact high-tick count, no earlier canonical visit, nonterminal target. 48 finite Bonferroni inequalities tested using the first seven fresh primes on the same AP intervals. All assertions passed. For r223 the gap114, peak220, high ticks55; r2203 gap1104, peak2200, high ticks550. The CRT representatives have up to925 decimal digits; the smaller sampled AP roots also obey the exact rule. The asymptotic counting theorem is a mathematical deduction, not an empirical fit to these samples. No new macroscopic canonical ray scan, no Lean kernel verification, no external novelty claim. Main/sibling branches unchanged.

Next: seek restrictions on repeated long excursions along the SAME ray (rather than uniform excursion bounds contradicted here), or a different global stopping criterion. The joint barrier count/gain theorem remains valid; this note closes only the uniform short-duration upper-bound approach.
