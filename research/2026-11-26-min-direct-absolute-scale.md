# Absolute-scale restrictions on fresh-label renewal and multiplicity growth

Continuation of [0b21129](https://github.com/tara-sooo/A166944-Lean/commit/0b21129dea8dc71d1968bf4159b2f42645521a01) on the independent direct-arithmetic branch. We distinguish the uncut MIN from the adaptive square-root MIN, and actual canonical integer roots from abstract modular cylinders. The new results are a bounded-multiplicity termination theorem, an all-window multiplicity lower bound, an absolute-scale gap for fresh-label cylinder representatives, and a two-family characterization of the exceptional linear-size representatives as twin-prime witnesses. No merger, cumulative return-cost, energy, or source-ensemble argument. Elementary prime counting suffices for the multiplicity results (the prime number theorem is optional for asymptotic constants). Paper deductions and exact finite computation; not Lean kernel checked. Twin infinitude and the original A166944 conjecture remain open.

## 1. Setup

Canonical odd root M>=5 has (t,H)=(M+2,2M-2). On even tick n, a label p divides n and H-1; on odd tick n, it divides n-2 and H+1. Write e=+1 for the even/minus-neighbor side, e=-1 for the odd/plus-neighbor side, so p|H-e. The next event is the earliest strict future hit, then the least odd prime at a tie, and H'=H+p-1. Uncut MIN admits all odd primes, whereas adaptive MIN admits only p^2<=H+1. The previous relative formula, with E the pre-event accumulated gain and j=n-(M+2), is

    gcd(M+j+2,2j+7-E),  j odd;
    gcd(M+j,  2j+1-E),  j even.

The invariant H<=2t implies E<=2T+6 at relative T, so all raw gcds through T divide odd nonzero defects of magnitude <=2T+7. Thus a sufficient condition for uncut/adaptive agreement through T is 2M-1 >= (2T+7)^2. Do not replace this by a linear-in-T condition: section 4 gives a counterexample to such a proposed simplification.

Let L(k) be a uniform upper bound on contiguous actual adaptive nonunit event blocks on at most k distinct primes, with L(0)=0. We use the earlier exact bases L(1)=2,L(2)=5,L(3)=11, and the constructive recursion for larger k from 0b21129. They concern consecutive events, not arbitrary subsequences.

## 2. Bounded multiplicity forces termination

Define A(x)=sum_{3<=q<=x, q prime}(q-1), and pi_o(x) the number of these odd primes. Let a record label p (strictly larger than every preceding label) occur in an actual adaptive trajectory starting at H0. If every label was used at most R times before that event, then necessarily

    p^2 <= H0+1+R*A(p-1).                                 (1)

Proof: every earlier label is <p, the pre-horizon is H0 plus all earlier increments, and adaptive eligibility requires p^2<=H+1. This is a deterministic constraint on each actual first record.

Elementary prime counting gives pi_o(x)=O(x/log x) and hence A(x)=o(x^2). For completeness: for positive integer m, every prime in (m,2m] divides binom(2m,m)<=2^(2m). Summing log-primes over dyadic m gives theta(x)<=4x log 2 (choose the next power of two). Primes >sqrt(x) each contribute at least (log x)/2, so

    pi_o(x) <= sqrt(x) + 8(log 2)*x/log x, x>=2.

No prime-pair estimate or PNT is necessary.

If R is fixed and H0 is fixed, (1) bounds all record labels absolutely. Therefore no infinite adaptive trajectory can use every prime at most R times: an infinite trajectory needs unbounded labels by the fixed-support product barrier. This yields a termination criterion even if the available alphabet is not assumed finite at the start.

More quantitatively, every record under multiplicity bound R satisfies

    p <= max(sqrt(2*(H0+1)), 2^(32R))

for integral R>=1. Indeed p>=2^(32R) ensures sqrt(p)>=4R and log p>=32R log2, so the preceding elementary estimate gives R*A(p-1)<=p^2/2. This bound is deliberately crude. For fixed R and H0 tending to infinity, (1) implies every record p<=(1+o(1))*sqrt(H0); thus any such prefix gains at most R*A((1+o(1))*sqrt(H0))=o(H0) and has O_R(sqrt(H0)/log H0) events. This includes the entire prefix up to its first repeated label (R=1). For any fixed R, the asymptotic statement holds uniformly over such prefixes: split record p into p bounded below a fixed threshold, or large p with R*A(p)/p^2 arbitrarily small.

There is a fully elementary explicit stronger bound for R=1 without primality: all earlier odd labels <p each occur at most once, so their gains sum to at most (p-1)(p-3)/4. Therefore

    3p^2+4p-3 <= 4(H0+1).

All selected labels are <sqrt(4(H0+1)/3), and the sum of all distinct odd label gains is at most (P^2-1)/4 for largest selected odd P. The total horizon gain is consequently <(H0+1)/3. In particular an adaptive path of distinct labels cannot even increase its initial horizon by one third (up to the displayed +1). The prime counting version gives a stronger o(H0) asymptotically.

## 3. Many recurrent labels in every large horizon window

The previous result excludes bounded multiplicity globally. A stronger local necessity follows from the finite-support block bound L(k).

Consider an actual infinite adaptive path, initial H0<=X, and even X<Y, with Y-X>sqrt(X+1). Let H_a be the first event horizon >=X (initial horizon permitted), H_b the first >=Y. Since the overshoot at X is at most sqrt(X+1),

    H_b-H_a >= Y-X-sqrt(X+1).
    B = floor(sqrt(Y+1)).
    n = b-a >= (Y-X-sqrt(X+1))/(B-1).                     (2)

All n labels of this block are <=B, since pre-horizons are <Y. For any fixed set S of at most k labels, delete the events outside S; equivalently split the original block at those events. If r outside events occur, the r+1 contiguous S-runs each have length <=L(k), so

    n <= (L(k)+1)*r + L(k).                              (3)

Let m_(k+1) be the (k+1)-th largest multiplicity among the labels in the block (zero if absent). Choose S to be k most frequent labels. Then r<=m_(k+1)*pi_o(B), whence the exact lower bound

    m_(k+1) >= [ (Y-X-sqrt(X+1))/(B-1) - L(k) ]
                 / [(L(k)+1)*pi_o(B)].                    (4)

Use max with zero and round up for integer multiplicities if desired. This uses only the number of outside events, not a decomposition of costs, gain weights or source mergers. It also works for a finite path that actually crosses the given window; no infinite-path assumption is required beyond existence of the block.

Taking Y=2X, the elementary prime bound in section 2 gives m_(k+1)>=Omega_k(log X) for all sufficiently large X for each fixed k. Optional use of the classical prime number theorem pi_o(B)~B/log B yields the more precise coefficient

    m_(k+1) >= (1-o(1))*log(X)/(4*(L(k)+1)).               (5)

For k=1,2,3 the respective denominators are 12,24,48. For the largest multiplicity alone there is also the sharper weighted bound

    m_1 >= (Y-X-sqrt(X+1))/A(B),

since the total gain cannot exceed m_1*A(B). For Y=2X, PNT and partial summation give A(B)~B^2/(2 log B) and hence m_1 >= (1-o(1))*log X/2.

Equation (3) holds for ANY prescribed set S of k labels, not only the most frequent ones. Thus for each fixed finite S and every sufficiently large dyadic horizon window, some prime OUTSIDE S must occur Omega_k(log X) times there. In particular it is impossible for all primes outside some finite S to have globally bounded multiplicities, even if primes in S are allowed to occur arbitrarily often. More generally if outside S total multiplicities satisfy f(p)=o(log p) as p->infinity, and each outside prime has finite multiplicity, then sum_{p<=B,p outside S} f(p)=o(B) by the elementary prime bound (a finite set of small primes contributes O(1)); (2),(3) contradict this. These are stronger constraints than simply requiring new labels periodically. They do not imply that any one fixed prime recurs infinitely often.

Under finite twin primes, every adaptive trajectory starting beyond the last twin center is infinite (first direct-arithmetic note). Therefore (4),(5) apply to all such rays and every sufficiently large horizon window, regardless of starting phase. They require arbitrarily many recurrent labels, not merely infinitely many first appearances. This remains a necessary condition, not a contradiction.

## 4. Correct treatment of the cutoff, and the long-wait roughness lemma

At a common plateau of uncut and adaptive MIN, if the uncut winner p satisfies p^2<=H+1, their next events coincide. If not, the raw gcd can select a LARGE prime FACTOR of a composite neighbor: it is not necessary that H-e=p. A tempting linear-in-T agreement claim based on that incorrect identification is false.

Explicit actual canonical counterexample: M=47, H=92, t=49. Uncut MIN has p=13 on even tick n=52 (relative j=3), since 91=7*13 and gcd(52,91)=13. The adaptive cutoff is floor(sqrt(93))=9; adaptive MIN instead chooses 3 on odd tick n=53, since 93=3*31. Thus the models differ with j=3 << M, without a terminal twin. A larger initial-neighborhood example: M=45561, after a common prefix the state (t,H)=(45564,91122) is reached; uncut chooses p311 on odd side at w155, H+1=311*293, whereas adaptive next is p293 at w439. No linear agreement theorem is asserted.

There is nevertheless a useful true replacement. At a winning event (p,w,e) from horizon H, every prime factor r of H-1 or H+1 satisfies

    2r >= w, and if 2r=w with r<p it is impossible.       (6)

For uncut MIN, any such factor supplies a hit within 2r ticks. For adaptive MIN, w<=2p<=2*sqrt(H+1), so any r<w/2 (or r=w/2) is in the adaptive pool; the same competition proof works. Hence (6) holds for both models. It is a necessary roughness condition on BOTH neighbors at the selected plateau. If H+1<(w/2)^3, each neighbor is prime or a product of exactly two primes counting multiplicity. Indeed a product of three factors >=w/2 is too large.

If the uncut label p is ineligible adaptively and H-e=pq with q>1, then q<p and every factor r|q is <p. In particular its least prime factor r has w<2r by the tie rule; if w>=2sqrt(q), q cannot be composite. Thus a long wait before an ignored label forces a prime cofactor, not a prime neighbor. This is the relevant distinction from the incorrect argument.

## 5. Absolute-scale gap for a prescribed fresh label

Fix any feasible uncut canonical prefix through relative tick T, gain E, and set B0=2T+7, d=2T+6-E>=0. Fix p>B0 prime, and side e=+1 or -1. The previous note gives its prescribed next-event time, if realized without an earlier event:

    k in {1,3}, k*p=1-E mod4,
    j=(k*p+E-7)/2   (e=+1),
    j=(k*p+E-1)/2   (e=-1).
    w=j-T=(k*p-d-1)/2 or (k*p-d+5)/2 respectively.

This w satisfies 0<w<2p for p>B0 (d>=0). At any integer root realizing the word, write H=2M-2+E=pq+e, with q positive odd. If q>1, (6) and w<2p imply q>w/2: for q>=p this is immediate, for q<p its least factor would preempt p unless 2r>w. Thus

    M >= ceil((p*(floor(w/2)+1)+e+2-E)/2).                (7)

For fixed T,E as p->infinity, this is M>=k*p^2/8-O_T(p). It applies even to the UNcut transcript, not just to adaptive realizations. The sole possible exception is q=1, with unique linear-size candidate

    M_lin=(p+e+2-E)/2.                                    (8)

The candidate must be an odd integer >=5 and realize the given earlier prefix. Adaptive realizations of the scheduled event, whether or not the uncut word agrees, must also satisfy M>=ceil((p^2+1-E)/2). Thus there is a genuine gap between the linear-size exception and the quadratic regime.

### No linear exception on the even side

For e=+1, q=1 gives H=p+1 and M=(p+3-E)/2. Odd parity of M implies k=3. Since d+1<=B0<p, w=(3p-d-1)/2>p. If H+1=p+2 is composite, its least prime factor fires within 2sqrt(p+2)<p (p>=11). If H+1 is prime, its odd-side clock in the same fixed plateau occurs at relative tick (p+2+E-1)/2 because its class is k'=1, strictly before j=(3p+E-7)/2 for p>4. The prime p+2>B0, so that tick is after T. Both cases contradict p winning. Hence (7) holds on the even side with NO exception for any p>B0.

### Odd-side exception is a twin witness for large p

For e=-1, q=1 gives H=p-1 and M=(p+1-E)/2. Odd parity implies k=1. If w>2sqrt(p+2) (in particular for all sufficiently large p for fixed prefix), (6) forbids a composite H-1=p-2. Thus p-2,p are twin primes and adaptive MIN stops at this horizon, provided the earlier prefix was adaptive. For the canonical uncut prefix at the linear root, previous labels must be adaptive once p is sufficiently large relative to T, since M_lin grows linearly with p and the finite earlier word has fixed labels; the earlier quiet ticks are also quiet adaptively. Conversely, if p-2 and p are prime, the odd candidate root is admissible and realizes the earlier prefix, p>B0+2 and k=1, then p wins the uncut next event: the other prime p-2 has the even-side k'=3 clock at (3(p-2)+E-7)/2, later than (p+E-1)/2 by p-6. No other labels exist on the plateau. This proves an exact exceptional-root criterion for sufficiently large p.

Consequently, if twins are finite, for every fixed feasible prefix all sufficiently large prescribed fresh labels have ONLY quadratic-size uncut realizations (7); unrestricted CRT escape does not give small representatives. Even with infinitely many possible finite extensions, ordinary integer root size cannot be disregarded. Conversely, arbitrarily large linear exceptions for a fixed prefix certify unbounded twins. This is an arithmetic gap, not a guarantee of a small representative.

### Two fixed families capture both twin orientations

There is an exact reformulation with no unknown prefix reachability condition. Use all-odd canonical roots, not necessarily prime roots. For every sufficiently large prime p (p>=53 suffices), prescribe its next ODD-side event with k=1 as follows:

    p=1 mod4: empty prefix T=0,E=0, M_lin=(p+1)/2;
    p=3 mod4: prefix [3] at relative tick 1 (T=1,E=2),
               M_lin=(p-1)/2.

In both families H=p-1 at the endpoint. If p-2 is prime, the first family already starts there; for the second family p=1 mod3, M=(p-1)/2 is odd and divisible by3, so the first even tick M+3 is divisible by3, H0=p-3 is 1 mod3 and label3 wins immediately. The state becomes p-1 as required. Both prefixes are free in the all-odd-root variant (the second is NOT a prime-root family, since M must be 0 mod3). The two families therefore have arbitrarily large CRT realizations for every prescribed p, but their exceptional linear candidate realizes the full uncut extension iff p-2 is prime by the preceding proof. The quadratic lower bound (7) exceeds M_lin for p>=53, so the exceptional candidate, when present, is the SMALLEST positive admissible odd root M>=5 realizing that uncut extension.

We obtain the exact equivalent criterion:

    Infinitely many twin primes
      iff arbitrarily large prime p have a smallest uncut representative
          of size (p+1)/2 or (p-1)/2 in the indicated two families.

The adaptive version stops at the linear root rather than selecting p. This is a re-expression of the twin problem, not a solution; it is useful because the two families have explicit finite CRT descriptions and the exceptional representative is isolated below a proven quadratic gap. To prove infinitude one still has to show arbitrarily large linear exceptions, not merely prove that some huge CRT representative exists.

## 6. Same-side nested renewal strengthens the quadratic lower bound

Take a renewal tail of consecutive fresh labels p_1,...,p_i (after an arbitrary fixed prefix), all on the same side e and p_j=1 mod every earlier tail label. Put D=product_{j<i} p_j, p=p_i. Each earlier post-horizon had residue e-1 mod its label and all later increments preserve it. Hence the current pre-horizon satisfies H=e-1 mod D. Since p=1 mod D and H=pq+e,

    q=-1 mod D,    q-p+2=0 mod 2D.

If this event is adaptive, q>=p (for even side p^2<=pq+2 implies q>=p for odd q and p>=3; odd side p^2<=pq directly). It follows that

    q >= p+2D-2,
    H >= p*(p+2D-2)+e,
    M >= ceil((p*(p+2D-2)+e+2-E)/2).                      (9)

For D>1, this is strictly stronger than the ordinary square-root gate, and if H=O(p^2), w is proportional to p, then the roughness lemma also forces q prime for sufficiently large p. The other neighbor is prime or semiprime. This does not force q to be prime at arbitrary absolute scale; the roughness inequality is essential.

Mixed sides have the exact separate congruences q=e_j-1-e mod p_j, not necessarily the common -1. Formula (9) is for same-side renewal only. For renewal constructions in the previous note, p_i>2T_prev+7>E_prev, so adaptive eligibility gives p_i^2 < 2M-1+p_i; each such label is bounded by the positive root of z^2-z=2M-1. Also D_i=D_(i-1)*p_i>D_(i-1)^2 when p_i=1 mod D_(i-1). Thus the depth of this particularly separated renewal construction at a fixed integer root is at most O(log log M) (once the first tail label is fixed >=3). This gives an explicit absolute obstruction to extending the previous nested CRT construction at a single fixed root. An arbitrary adaptive path need not have this nested congruence structure; section 3 is the general constraint.

## 7. Reproducible finite diagnostics

[Audit at 19a3a36](https://github.com/tara-sooo/A166944-Lean/blob/19a3a36774e15b68c0dcb22f6feb02d65275bb13/research/min_direct_absolute_scale_audit.mjs), blob 95f0892306a0bb5636b8f5eaaa1653e1c789f60a. Exact remote readback. Run from repo root:

    node research/min_direct_absolute_scale_audit.mjs 50000 499 1000000

Executed the actual ECMAScript audit function in the tool runtime (not a separate Node process). Smallest-prime-factor sieve and exact clock jumps. Scan all odd M=5..50000 for at most 150 nonunit events (or earlier termination): 452868 adaptive event incidences; 228460 record tests for R=1..4; 41609 distinct-record tests; 79630 long-wait rough-neighbor factor-count tests; 24998 first uncut/adaptive mismatches including 4231 composite-neighbor cases, 20767 prime-neighbor cases. 498 literal tickwise GCD mismatch checks at M<=1000; all pass. The provisional linear transfer conjecture was abandoned after the actual M47 counterexample (not merely an abstract counterexample).

37433 complete finite horizon windows from those trajectories, 149732 multiplicity/run-count comparisons, 37433 weighted comparisons. No full dyadic [X,2X] crossing was found in that bounded canonical scan; the dyadic asymptotic theorem is a conditional paper deduction, not a numerically observed infinite ray. Example short complete window from M30467: X60932 to Y62928, 123 nonunit events, 21 distinct labels, leading counts 3:44,5:19,7:15,11:9,13:8. All finite-window checks pass.

For the empty prefix, [3] at relative1, and [quiet,quiet,quiet,3,3,quiet] through T6, exhaustive increasing search over the necessary root residue class for every p<=499 with p>2T+7, both sides. 538 specified schedules; 60673 root candidates; found exact minimum odd M>=5 separately for the uncut schedule, adaptive schedule, and common schedule in every case before M=10^6. The first adaptive root can be smaller than the first COMMON root: 129 such schedules. Thus searching only uncut realizations satisfying the cutoff does not compute the minimum adaptive realization. In total 269 uncut vs adaptive minima differ. 782 nonexceptional uncut quadratic checks, 727 fresh roughness checks, 30 exceptional linear realizations encountered (not necessarily distinct p); all odd-side, 28 have sufficiently long waits and certify twins. 137 direct candidate even-exception tests exclude all; 80 two-family equivalence checks at p>=53, 18 positive, all pass. The two short-wait exceptions are not asserted to certify twins merely from q=1.

Examples of exact minima:

| prefix | p | side | first uncut M | first adaptive M | first common M |
|---|---:|---|---:|---:|---:|
|empty|53|even|505|2095|2095|
|empty|257|even|20947|36367|36367|
|empty|421|odd|211|88621|88621|
|[3]|53|odd|4425|1881|4425|
|[3]|31|odd|15|945|945|

For empty-prefix p421 odd, linear M211 gives twin center420 (419,421). The first adaptive event at the *same specified tick with label421* needs M88621 instead. For [3] p31 odd, M15 gives twin center30 (29,31). For [3] p53 odd, the adaptive minimum1881 is below the uncut minimum4425, illustrating the importance of mode-specific minimum search. 516 same-side nested congruence arithmetic controls verify (9); not asserted to be canonical path witnesses.

## 8. Next independent target

The previous uniform support theorem forced increasing diversity in infinite trajectories; the present theorem forces many repeated labels of increasing multiplicity in each large absolute-scale window. The renewal construction survives every finite CRT step but has quadratic-scale representative bounds and rapidly bounded depth at a fixed root. The special linear exceptions give exact twin witnesses in just two fixed families. A natural next research target is to examine how actual MIN could sustain the required simultaneous recurrence of many labels while introducing new record labels, using (1),(4),(6) and the bounded recency constraints, or to exploit the isolated linear representatives of the two-family cylinders by a new arithmetic principle. The latter equivalence alone is simply a restatement of the twin obstacle, and finite modular feasibility alone cannot force a linear representative. No proof of finite-twins contradiction or original record conjecture; no Lean executable available, no Lean changes. Main and sibling branches untouched.
