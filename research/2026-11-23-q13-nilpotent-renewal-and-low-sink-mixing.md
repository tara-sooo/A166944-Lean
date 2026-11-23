# A166944 Issue #4 — An exact nilpotent 13-renewal operator, quotient high-event accounting, and fixed-modulus CRT mixing model

2026-11-23 JST. Project `tara-sooo/A166944-Lean`, dedicated branch `research/issue-4-terminal-survivor-positive-budget`; child Issue #4, parent #1. This note extends the previous first-merger genealogy / sharp 39-to-one low-wheel certificate. **The algebraic statements are paper proofs using full finite certificates; the exhaustive computations are C++17 and independent literal-GCD Python, not Lean-kernel proofs. Twin-prime infinitude and the original A166944 strict-record conjecture remain open.**

## 1. Remove duplicate source histories by a quotient of exact state-time trajectories

For every canonical odd source M∈[X,2X) at time n within its lifetime, the original full clipped-GCD state C_M(n) is deterministic. Two sources that share the same (n,C) have identical future updates until the earlier source's cutoff K(M)=floor((7M−1)/4). Since K(M) strictly increases with M, for the EXISTENCE of a trajectory reaching a full prime-pair sink, one can keep only the largest M from every group of coalesced active sources. Its deadline is at least as late as that of all redundant group members. New sources must still be inserted at s(M)=M+2. This is an **exact quotient**, not a claim that source multiplicities are uniformly bounded or that mean-event inequalities for all starts can be replaced by unweighted counts automatically.

A compiled exact simultaneous-time cohort sweep (`research/quotient_high_state_audit.cpp`) reconstructs original parity-specific GCD events and tallies high events once per distinct (event time n, pre-event C), in addition to their usual source-weighted count:

| X | source-weighted high (prime≥13) events | distinct high (n,C) event nodes | distinct high q-factor weight |
|--:|--:|--:|--:|
| 4,096 | 7,675 | 973 | 30,758 |
| 16,384 | 45,343 | 3,984 | 156,210 |
| 65,536 | 224,221 | 16,240 | 816,038 |
| 262,144 | 1,198,498 | 69,914 | 4,604,331 |
| 1,048,576 | 5,516,751 | 290,651 | 25,512,892 |

The weighted q-hit mass at X1,048,576 is 775,958,451, versus unweighted q-hit mass 25,512,892. At this scale, integrating the number of distinct active states over time gives quotient spacetime area 14,736,021,430, versus original source-duration area 618,474,504,192, factor41.97. This diagnostic explains why a direct source-pair L² estimate is dominated by inherited coalescence. **However, the quotient alone does not provide a lower bound on the amount of spacetime area that must survive in a hypothetical no-twin process.** A single long-lived packet might absorb many new starts.

## 2. The low-only terminal map is a retraction, not a mixing operator (PAPER)

For S={3,5,7,11}, put P=1155, L=2310. For any fixed time t and even C, let L_t(C) be the C-value after all S-only GCD events, known from the earlier all-state DAG to terminate within133 time steps, with exact maximal inverse degree39. The terminal set is

    Omega={c even mod2310: gcd(c−1,P)=gcd(c+1,P)=1},   |Omega|=135.

Every terminal state is fixed by another low-only sweep, hence

    BOXED: L_t(L_t(C))=L_t(C).                    (RET)

The map is a **projection/retraction**. Iterating the 39-fold L² majorant without an intervening HIGH event is not meaningful: after one sweep the state is already terminal, and low-only dynamics can no longer mix it. Genuine changes in low-terminal residue classes are driven by new high-prime pulses.

## 3. A NEW rigorous Doeblin bound for an EXPLICIT uniform-unit pulse model (PAPER)

At a low sink c∈Omega, a true high-only clipped increment d is odd and coprime to P. Consider the ARTIFICIAL Markov kernel: choose d uniformly from the 480 odd unit residues modulo2310, set c'=c+d−1, then take the 11-low restricted terminal retraction L_t(c'). Let K_t(c,y) be the resulting law on Omega, with any fixed time residue t mod2310. This kernel is NOT automatically the transition law of the actual deterministic GCD process.

For two initial sink states c,c' and a target y∈Omega, if both integers y−c+1 and y−c'+1 are units modulo P, then there is at least one pulse residue from EACH source that reaches y directly, without any low reactivation. Hence K_t(c,y),K_t(c',y)≥1/480 for such a y, independently of t.

By CRT, the number of such **common direct targets** is at least

    p=3: 1 target, p=5: 2 targets, p=7: 3 targets, p=11: 7 targets;
    total >=1*2*3*7 = 42.

Indeed the admissible sink residues modulo p exclude ±1. A direct transition further forbids y≡c−1 and y≡c'−1 modp. For p=3 only y=0 survives; for p=5 among the three sink residues only y=2 can be newly forbidden; for p>=7 at most two sink residues are newly forbidden, yielding p−4. The bound 42 is attained for suitable CRT-compatible pairs c,c'. Therefore the common part of every two rows K_t(c,·),K_t(c',·) has mass at least 42/480=7/80, and their Dobrushin contraction is

    BOXED: ||mu K_t−nu K_t||_TV <= (73/80) ||mu−nu||_TV. (MODEL)

This holds with the same constant even if the time phase t is selected separately for different rows, since the direct-transition common mass does not depend on t.

The C++ checker `research/low_sink_uniform_unit_kernel_audit.cpp` verifies exactly 135 sink classes, 480 units, **13,024 direct sink-preserving (c,d) pairs of 64,800**, and EXACT minimum of 42 direct common outputs over every pair of sink classes. Thus under a uniformly chosen sink class the probability a uniform unit pulse leaves the low wheel inactive is

    BOXED: 13024/64800 = 407/2025 ≈20.0987654%,

so reactivation probability is about79.9012346%. For seven sampled time phases, the FULL kernel including low retraction had pairwise overlap minima of 395–405 out of480, even stronger than the rigorous universal 42 bound. These sample overlap maxima are NOT asserted for all time phases. It also independently verifies RET for every even low-wheel input residue at the sampled phases.

A generalization: for any fixed prime wheel S={3,5,7,...,y}, Q=product(S), the analogous uniform-unit direct-target overlap is at least

    [1*2*product_(p∈S,p>=7)(p−4)] / phi(Q).

In the expanded S up to13, this is 378/5760=21/320. The lower bound decreases only by multiplicative factors (p−4)/(p−1), roughly a power of log y, rather than as the reciprocal of the full wheel modulus. This is a statement about artificial uniform-unit pulses, not a theorem on actual selected prime factors.

## 4. ACTUAL prime pulses are FAR from uniform, despite one similar statistic

The independent original full-B-wheel C++17 scanner `research/actual_low_sink_residue_audit.cpp` enumerates all canonical starts and all high q>=13 events, collects every event for which the pre-state has no active 3/5/7/11 prime, and deduplicates by (n,C). The full increment d is guaranteed to be coprime to P, since no low p divides the pre-event neighbors. It measures how frequently the post-event state reactivates any low prime, and compares with the uniform-unit kernel's conditional mean using the **actual observed pre-event c residue**:

| X | distinct low-sink high events | actual low reactivation | uniform-unit model, same c frequencies |
|--:|--:|--:|--:|
| 4,096 | 626 | 77.64% | 79.54% |
| 16,384 | 2,592 | 77.66% | 79.63% |
| 65,536 | 10,633 | 78.46% | 79.68% |
| 262,144 | 46,361 | 78.39% | 79.61% |
| 1,048,576 | 194,328 | 78.46% | 79.61% |

At X=1,048,576, 194,020/194,328 distinct sink high pulses were single-prime increments; only308 composite. **Yet the full empirical distribution of d mod2310 has total variation distance about0.7927 from the uniform distribution on480 units**, due to frequent small prime q=13,17,... . The reactivation statistic agrees within~1.2 percentage points because it is only ONE coarse observable, not because the actual source-conditioned high-pulse law is uniform. Therefore MODEL must NOT be silently applied as a contraction theorem for the actual dynamics. The REAL arithmetic challenge is to control the selected high-prime residue sequence and/or its finite-state deterministic return structure.

## 5. MAJOR NEW exact FINITE certificate: append prime 13 to the low-only wheel

A better way to address the most frequent high factor is to stop treating q=13 as a random high pulse and instead incorporate it **exactly** into the low wheel. Let S_13={3,5,7,11,13}, P_13=15015, L_13=30030. Consider the original parity-specific squarefree clipped-GCD process using ONLY these five primes, WITHOUT any q>=17.

Immediately AFTER an event containing q=13, the state (t,C) must satisfy

    t even: 13|t,    C≡0 (mod13),
    t odd:  13|(t−2), C≡−2 (mod13),
    C even.

Modulo L_13 there are precisely 2310 possible event times t and 1155 possible even post-state C classes for each such t; therefore EXACTLY

    BOXED: 2310*1155 = 2,668,050 q13 POST-EVENT states.

The standalone compiled `research/q13_renewal_graph_audit.cpp` enumerates ALL such states, calculates the exact NEXT q13 event (if any) by the ORIGINAL five-prime even/odd GCD clocks with simultaneous low+q13 increments, and builds a functional directed graph with one successor per q13 post-event state. Intermediate events before the next q13 can only involve S_11={3,5,7,11}, so the previous <=22-event finite certificate guarantees the jump algorithm terminates for each node.

**Complete exact finite graph findings** (not stochastic):

- Number of states:2,668,050; no-next-q13 states:2,216,514; edges to next q13:451,536.
- Full Kahn topological sort consumes all 2,668,050 states: **NO directed cycles**.
- Maximum next-q13 return depth after an already completed q13 event: **5 further q13 events**.
- Depth histogram (# further q13 events =0,1,2,3,4,5): 2,216,514 / 413,658 / 36,266 / 1,517 / 89 / 6.
- From any post-q13 state, maximum subsequent nonunit events (3/5/7/11/13 only) is40, maximum elapsed clock time222, and maximum low-wheel cumulative growth1406. These maxima need not be achieved by the same state.
- Some q13 steps contain a simultaneous low factor (25,175 graph edges), and the exact scan includes their PRODUCT increments.

Before the FIRST q13 event in any five-prime-only trajectory, only the 11-low wheel acts, so this prefix lasts <=133 clock steps and has <=22 low events and growth<=1156. If a first q13 event occurs, it lies at most26 steps after the preceding plateau and has clipped increment at most 13*1155=15015. Consequently the entire restricted five-prime orbit always terminates with the following rigorous (finite-certificate-dependent) universal bounds:

    BOXED: number of q13-bearing events <=6;
           total nonunit events <=22+1+40 =63;
           total elapsed time <=133+26+222 =381;
           total low-wheel growth <=1156+15014+1406 =17576.       (LOW13)

An INDEPENDENT literal one-step parity-GCD Python oracle checks the two extremal graph witnesses and 1,500 randomly chosen q13 post-event states, plus 1,200 completely arbitrary original (t,C) states, verifying the bounds and agreement with the jump simulator. The exact full graph is not a Lean kernel certificate; its finite computation and source code are independently reproducible.

**New high17 renewal corollary (PAPER):** In the FULL B-wheel, any maximal string of events involving primes<=13 only is a PREFIX of a five-prime-only orbit, so it contains at most63 low-only events and lasts at most381 steps. Let T_{17}(M) count events with some clipped factor q>=17; then full nonunit events E_B(M) obey

    BOXED: E_B(M) <=63+64*T_{17}(M),

and if an original canonical orbit reaches NO full-wheel sink by its cutoff K(M), then

    BOXED: K(M)−s(M) <= (T_{17}(M)+1)*(381+2B).          (HI17CLOCK)

The previous exact aggregate dyadic horizon sum H_X=9X²/16−5X/4 therefore yields the NEW sufficient open analytical target

    BOXED: liminf_(dyadic X→∞) sum_(odd M∈[X,2X)) T_{17}(M)/(XB) <9/224

for infinitely many twin primes, with no need to bound q13-bearing events separately. This is an alternative sufficient condition, not a proved liminf upper bound. The all-original-GCD finite measured T17 counts are:

| X | B | events with factor>=13 | events with factor>=17 | >=17 weighted first count / (XB) |
|--:|--:|--:|--:|--:|
| 4,096 | 170 | 7,675 | 6,131 | 0.008805 |
| 16,384 | 339 | 45,343 | 37,272 | 0.006711 |
| 65,536 | 678 | 224,221 | 187,142 | 0.004212 |
| 262,144 | 1,355 | 1,198,498 | 1,001,099 | 0.002818 |
| 1,048,576 | 2,710 | 5,516,751 | 4,612,625 | 0.001623 |

## 6. A precise induction program: q-event renewal graph is always only 2P² nodes

If a proven finite low-wheel uses squarefree odd product P, adjoining any NEW odd prime q coprime to P gives a wheel modulo2Pq. Its q-bearing event-post states satisfy one of two parity-aware event-time congruences and one post-C congruence modq. Counting leaves exactly

    BOXED: (2Pq/q) * (Pq/q) = 2P² event-post residue states,

**independent of the size of the newly added q**. The q-return map can be computed by following the smaller P-wheel between q-bearing events, using its already-proved termination bound. If this functional graph has NO directed cycles, its longest path yields a NEW finite-wheel termination theorem by the same argument as LOW13.

For P=1155 and q=13 this graph has 2,668,050 states and nilpotent q-return adjacency (no path of six q-return edges). For the next extension P=15015 and q=17 the exact graph has **450,900,450 event-post states**, making a sparse/symbolic topological analysis or a compact successor representation the concrete next computational/theoretical problem. Earlier random probes for S<=17/19 found no cycles among 30,000 states per wheel, but those are samples, not a finite certificate for q=17 or19.

An eventual UNIFORM theorem bounding the q-renewal depth and restricted-wheel elapsed time as the low cutoff grows could make it possible to isolate only genuinely large primes in the arithmetic part of the twin-prime argument. Such a general induction is NOT established; the finite q13 graph only completes one new induction step. Enlarging the wheel also increases the CRT period and the worst-case time constants; direct benefits to the current q>=193 two-root estimate must be rechecked, not assumed.

## 7. Proof status and exact next bottleneck

1. **Established algebra + finite exhaustive certificates:** low-only retraction, finite-group uniform pulse Doeblin 73/80 model, exact q13 graph acyclicity/LOW13, and the reduction to T17; quantitative original-GCD finite data are tested.
2. **Important negative finding:** uniform high-pulse unit residues are NOT the actual source-weighted or unique-state increment distribution (empirical total variation~0.793 at X1m); a single matching low-reactivation statistic is no basis for applying Markov contraction.
3. **Still open:** a scale-uniform arithmetic bound on the actual adaptive q>=17 high-event return depth, or the q>=17 first moment sufficient threshold. The full signed/synchronous q-clock moment problems and twin-prime conjecture remain open.
4. **Recommended next route:** attempt a compact q17 first-return graph/symbolic ranking function; in parallel, treat fixed small high-prime deterministic renewal separately from the large q CRT/Type-II dispersion estimate. A uniform arithmetic Lyapunov invariant across prime extension steps would be far stronger than another finite scan.

### Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q13_renewal_graph_audit.cpp -o /tmp/q13_renewal
/tmp/q13_renewal
python3 research/q13_literal_oracle.py

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low_sink_uniform_unit_kernel_audit.cpp -o /tmp/low_kernel
/tmp/low_kernel

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/actual_low_sink_residue_audit.cpp -o /tmp/actual_sink
/tmp/actual_sink 4096 16384 65536 262144 1048576

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/quotient_high_state_audit.cpp -o /tmp/quotient
/tmp/quotient 4096 16384 65536 262144 1048576
```

All code is standalone (C++17 standard library or Python3 standard library); no dependency on existing research code. No branch merge, default-main change, or Lean-kernel proof.
