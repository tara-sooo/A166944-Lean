# A166944 Issue #4: synchronous q-clock collision energy as a single positive sufficient condition for twins

2026-11-23 JST. Dedicated branch `research/issue-4-terminal-survivor-positive-budget`, Issue #4 / #1. This extends the paper/finite-exhaustive [sharp average horizon and weighted clock criteria](2026-11-23-average-horizon-and-weighted-clock-criteria.md). New mathematical identities and Cauchy implications are **paper arguments**; finite observations use the full original parity-specific squarefree-clipped GCD in a standalone compiled C++17 auditor. The collision-energy asymptotic remains OPEN; no Lean kernel/twin-prime/OEIS strict-record proof.

## 1. Exact synchronous incidence identity (paper)

For even dyadic X>=256, B=ceil sqrt(7X), odd canonical starts M in [X,2X), start s=M+2 and terminal K(M)=floor((7M−1)/4). Let C_M(n−1) be the ORIGINAL full-wheel GCD state at the step immediately before n. Let J_B be primes q in [13,B]. The parity-specific GCD implies an exact q-hit at time n iff

    n even: q|n AND q|C_M(n−1)−1;
    n odd:  q|(n−2) AND q|C_M(n−1)+1,

provided M+2<n<=K(M). For q define its **absolute clock set** C_q as all n within the global relevant interval [X+3, max_M K(M)] with either q clock congruence. The number of original starts hitting q at clock n is

    mu_(q,n)=#{M in I_X: M+2<n<=K(M) and q divides d_M(n)}.

Thus exactly H_q=sum_(n in C_q)mu_(q,n) actual q-hits; this counts all q factors of composite d, not only the smallest factor. If p_i is the smallest high factor of event i, previous weighted high budget Lambda_X satisfies

    Lambda_X <= A_X :=sum_(q in J_B)q H_q.

## 2. NEW POSITIVE two-source collision-energy criterion (paper)

Define

    J_X := sum_(q in J_B) q sum_(n in C_q) mu_(q,n)^2.

It is a nonnegative triple-incidence weighted count: for each q,n, mu² counts ORDERED PAIRS of canonical starts (M,M') both hitting q AT THE SAME ABSOLUTE CLOCK n. The global clock interval has length strictly below 5X/2, and there are exactly TWO allowed q-clock residues modulo 2q. Consequently

    |C_q| <= 5X/(2q)+2,
    Q_X := sum_(q in J_B) q |C_q| <= (5X/2+2B) |J_B| <= 3X |J_B|

for dyadic X>=256 (B<=X/4). Apply weighted Cauchy to all (q,n):

    BOXED:  A_X² <= Q_X * J_X <=3X |J_B| J_X.       (Q1)

Thus the SINGLE NEW analytic estimate

    BOXED: J_X = O(X B² |J_B|)                     (Q2, OPEN)

would imply

    A_X=O(X B |J_B|)=O(XB²/log B)=O(X²/log B)=o(X²).

Then Lambda_X<=A_X=o(X²), meeting the earlier sufficient bound Lambda_X/X²<39/848 along all sufficiently large dyadic X and giving infinitely many twin primes by the established terminal full-sink certificate. Equivalently, one can directly use the older stronger o(X²) weighted certificate. Q2 requires no signed cancellation in its statement, unlike prior mixed-prime reset-dispersion conjectures.

**Strongest simple subgoal:** uniformly for all q,n,

    BOXED: mu_(q,n) <= C B                          (Q3, OPEN)

for one absolute C. Then J_X<= C²B² Q_X<=3C² X B²|J_B|, so Q2 follows. The finite maximum mu/B is below 0.5 for all scanned sizes, but this is NOT a uniform theorem. A more flexible Q2 permits occasional heavily occupied clock fibres; this is why Q2, not Q3, is the preferred target.

## 3. Exact joined/nonjoined trajectory-pair structure

The square mu_(q,n)^2 counts ordered M,M'. If M=M', its contribution is the regular first moment A_X. For distinct sources, the pair can either have identical pre-event state C_M(n−1)=C_M'(n−1) (**coalesced at that clock**, which causes a large positive collision contribution) or distinct states (**not identical at that clock**). For the latter pair, the q-hit congruences imply

    BOXED: q | [C_M(n−1) − C_M'(n−1)],

AND q|n (n even) or q|(n−2) (n odd). Thus q must divide a concrete gcd involving BOTH the clock number and the state separation. This gives a divisor-correlation condition even when past histories differ and the state trajectories are adaptive. A large q contributes to only a limited set of pair differences unless states exactly coalesce.

The coalesced contribution can be grouped by the exact event-state graph node (n,C) and source multiplicities; the noncoalesced contribution can be grouped by difference DeltaC and the factorization of gcd(DeltaC,n) or gcd(DeltaC,n−2). This is a concrete proposed combinatorial/analytic split for Q2. A naive upper bound on each pair using only the number of divisors of DeltaC is too weak when summed over all source pairs; extra transport/dispersion information is necessary. Such a bound would supply precisely the arithmetic information not captured by ordinary independent CRT phase assumptions.

## 4. Finite original-GCD all-source audit

Standalone C++17 `research/q_clock_collision_audit.cpp` enumerates all odd M in five X windows, reconstructs exact original parity GCD and all q factors for each high event, packs (q,n) keys to compute mu_(q,n), sorts all observed q clocks, and computes J_X by integer squared multiplicities. It also checks independently the historical original total growth for X4096,16384,65536, all high event counts, each weighted high-to-high gap <=133+2p_i, and the exact dyadic horizon sum 9X²/16−5X/4. The complementary committed `research/weighted_high_clock_criterion_audit.cpp` independently checks the same weighted first moment and five prime-size bands.

| X | B | total q hits (including composite multiplicity) | max_(q,n)mu/B | max_q qH_q/(XB) | J_X/(X B² |J_B|) |
|--:|--:|--:|--:|--:|--:|
| 4096 |170| 7679 |0.48235|0.0289005|0.00174579|
| 16384|339|45499|0.47493|0.0194726|0.000798319|
| 65536|678|224924|0.47493|0.0109905|0.000352633|
| 262144|1355|1201692|0.48930|0.00727166|0.000142737|
| 1048576|2710|5533149|0.42325|0.00417369|0.0000394002|

X1048576: J_X=118,028,336,599, |J_B|=389, 253345 distinct occupied (q,n) keys, global maximum simultaneous hits mu=1147 at prime q17. For selected q13/17/31/61/127/257/509/1021/2053, a separate original-GCD `unordered_map` time histogram independently checked the exact per-q fibre sizes/moments (e.g. q13 max985, sum mu²118627473; q17 max1147, sum mu²75266989). All finite ratios are experiments, not proof of a uniform asymptotic cap.

## 5. A focused proposed proof strategy

A strong, immediately testable intermediate claim is a deterministic or averaged **synchronous q-clock fibre bound** of order B (Q3) or its square average Q2. The residual problem can be attacked with a paired-source transfer ledger:

1. At a common q-clock n, group source pairs by their exact C values. Coalesced values contribute the square of the mass at an event-state node; seek a usable global **nonterminal collision energy** bound on the full high-event graph (earlier work measured only reset-node coalescence).
2. For noncoalesced pairs, use q|gcd(DeltaC,n−0 or n−2) and the fact that low-prime blocks have <=22 events and <=133 elapsed time, creating a bounded local inverse history between high events. Sum large-q common factors *across q and clock times* before taking upper bounds; the two-root low-sink CRT from previous research may help in the subset following resets.
3. If Q2 fails globally due a small class of heavy clock fibres, partition by exact source multiplicity, or exclude a negligible exceptional set of clocks with an explicit remaining q-weight budget. One must verify the exceptional contribution, not assume that finite low ratios continue.

**What is still difficult:** the values C_M(n−1) are selected by the earlier GCD events and are NOT uniformly distributed modulo q for free. Merely applying the Chinese remainder theorem at one low-sink plateau, or assuming independence of distinct prime clocks, will not prove Q2. Any successful transport/discrepancy estimate must use genuine dynamical time-order information and break the usual parity barrier. Standard source context: Terence Tao, *254A Notes 4, Some sieve theory*, §parity, https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/ ; Friedlander and Iwaniec, *Asymptotic sieve for primes*, Annals of Mathematics 148 (1998), pp.1041–1065, https://annals.math.princeton.edu/articles/13036 , a precedent for the need for additional bilinear information beyond ordinary sieve local densities, NOT an existing proof of our Q2.

No Lean kernel theorem, no twin primes or A166944 strict-record conjecture proof, no main merge. Theorem Q1 and reduction Q2=>twins are paper-level, conditional on the previously scanned finite low-wheel bound 133.

### Reproduce

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q_clock_collision_audit.cpp -o /tmp/q_clock_collision_audit
/tmp/q_clock_collision_audit 4096 16384 65536 262144 1048576
```
