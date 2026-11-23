# A166944 Issue #4: sharp average-horizon constant, prime-weighted clock cost, and quantitative proof targets

Date: 2026-11-23 JST. Dedicated branch `research/issue-4-terminal-survivor-positive-budget`. This continues the actual original parity-dependent squarefree-clipped GCD recurrence research note `2026-11-23-high-clock-budget-and-constant-first-moment.md`. The mathematics below is paper-derived conditional on the **previous finite exhaustive low-wheel certificate** that any {3,5,7,11}-only continuation stops after at most 133 elapsed steps. All original-GCD finite tests below use compiled C++17, not Lean. Neither twin prime infinitude nor the strict-record A166944 conjecture is proved.

## Setup

Even dyadic X=2^k>=256, B=ceil(sqrt(7X)), odd M in I_X=[X,2X), s(M)=M+2, cutoff K(M)=floor((7M-1)/4). Each nonunit event at n>s has odd squarefree clipped increment d(n)>1 and C(n)=C(n-1)+d(n)-1. A HIGH event is any d with a prime factor >=13. Write T_B(M)=number of high events, p_i(M)=**smallest** prime >=13 dividing its high increment d_i, and G_B(M)=C(K(M))−C(s). Set T_X=sum_M T_B(M), Lambda_X=sum_{M,i}p_i(M), and W_X=sum_M G_B(M).

A FULL sink is a state with no prime <=B dividing either C−1 or C+1. In our bounded setup, such an actual sink encountered no later than K(M) yields two genuine twin primes C±1 (by the previous terminal certificate), and their size grows with X.

## 1. SHARP exact sum of original canonical horizons (paper)

Because K(M)−s = floor((3M−1)/4)−2, and X=4a is divisible by four, grouping M=4a+1+4j and M=4a+3+4j for j=0,...,a−1 gives

    H_X := sum_{M in I_X} (K(M)−s(M))
         = 9 X^2/16 − 5 X/4.                    (H1)

The previous sufficient no-sink lower bound used only min_M(K−s), missing a factor 3/2 in the dominant aggregate. N=|I_X|=X/2.

## 2. Three exact deterministic no-sink clock inequalities (paper)

The exhaustive 11-low-wheel result gives: between consecutive high events, or before the FIRST high event, the low-only run length is <=133 time steps. If it is followed by a high event with prime factor p_i>=13, the parity-correct p_i clock is at most 2p_i after the end of the low-only run. Thus the time from the preceding high event to the next high event is <=133+2p_i. For an orbit that has NO full sink by K(M), its final high-free tail has length <=133+2B (if no high-prime clock were active at the terminal low wheel, the orbit would already be a full sink). Therefore for each no-sink canonical M:

    K(M)−s(M) <= sum_{i=1}^{T_B(M)} (133+2p_i(M)) + 133+2B.

Summing over all canonical M, under the hypothetical assumption that NO M reaches a full sink in this dyadic window,

    2 Lambda_X +133 T_X >= 9 X^2/16 − X B − 271 X/4.   (H2)

Because p_i<=B, the weaker aggregate all-event count obstruction is

    T_X >= H_X/(133+2B)−X/2,

hence the strict **new sufficient condition**

    liminf_(dyadic X→∞) T_X/(X B) < 9/224 = 0.0401785714  (H3, OPEN INPUT)

implies infinitely many twins. This sharpens previous criterion 3/112 by factor 3/2.

The **single clock-cost criterion** is

    liminf_(dyadic X→∞) (2 Lambda_X+133 T_X)/X^2 <9/16     (H4, OPEN INPUT)

and it likewise suffices for infinitely many twins. Since p_i>=13, T_X <= Lambda_X/13, so still stronger-but-simple:

    liminf_(dyadic X→∞) Lambda_X/X^2 <39/848=0.045990566... (H5, OPEN INPUT)

suffices. The fixed coefficient is much less restrictive than the previous o(X²) weighted budget. For events with multiple distinct high factors the p_i is the minimum factor, never the full increment d_i; inequality is valid because its clock fires within 2p_i.

For a high event d_i>=13, the sharp elementary inequality

    133+2d_i <=(53/4)(d_i−1)

holds, with equality at d_i=13. Since p_i<=d_i, each no-sink trajectory obeys

    K(M)−s(M) <= (53/4) G_B(M)+133+2B.

Thus a **constant-growth criterion** using the ORIGINAL W statistic:

    liminf_(dyadic X→∞) W_X/X² <9/212=0.042452830...    (H6, OPEN INPUT)

also suffices for infinitely many twins. This is strictly weaker than the previous W_X=o(X²), and makes direct progress on the original mean-growth goal worthwhile even without a zero-limit theorem.

The exact finite threshold for any dyadic X, with NO full sinks, is

    T_X >= [9 X²/16−5X/4]/(2B+133)−X/2,
    2 Lambda_X+133 T_X >=9 X²/16−X B−271X/4,
    W_X >= (4/53) [9X²/16−X B−271X/4].          (H7)

These thresholds only guarantee at least ONE full sink in every sufficiently large scale meeting the opposite strict inequality. Since the sink C>=2X−3, infinitely many qualifying dyadic scales imply infinitely many distinct twin pairs. They do not assert positive density of twin primes.

## 3. Original parity-specific GCD exhaustive verification

Compiled `research/weighted_high_clock_criterion_audit.cpp` with `g++ -std=c++17 -O3 -Wall -Wextra -Werror`, ran all odd canonical M in X=4096,16384,65536,262144,1048576, and compared the exact high counts, known original-growth regressions, independent literal-step GCD M=7..119, and all high-to-high clock spans <=133+2p_i. Also checked (H1) as an exact integer equality for each X and (H2)-style no-sink weighted timing on all **event-prefix cutoffs n−1**, which are nonvacuous even though full canonical runs in these finite windows ultimately encounter twin-producing sinks. For each run the final original state was independently tested for full-sink status; every original M ended at a full sink in these five tested windows, a finite fact only.

| X | B | T_X | Lambda_X (min high prime sum) | 2 Lambda_X+133T_X over X² | Lambda_X/X² | W_X/X² |
|--:|--:|--:|--:|--:|--:|--:|
| 4096 |170| 7675 |286541 |0.0950013|0.0170792|0.0237907|
| 16384|339|45343|2129551|0.0383322|0.0079332|0.0108604|
| 65536|678|224221|16087001|0.0144344|0.00374555|0.00461633|
| 262144|1355|1198498|119219840|0.00578933|0.00173488|0.00202132|
|1048576|2710|5516751|775265653|0.00207752|0.00070510|0.00078571|

The thresholds for these normalized columns are 9/16≈0.5625 for the clock cost, 39/848≈0.04599 for Lambda, and 9/212≈0.04245 for W, respectively. These finite decreases are not asymptotic proofs.

A second finite classification sorts high events by their **smallest** high prime p_i relative to B. At X1048576, 4,583,782 of 5,516,751 high events (83.1%) have p_i<=B/16, but they account for only 177,774,206 of 775,265,653 units of prime-weight budget (22.9%). At the opposite end, only 99,276 events (1.80%) have p_i>B/2, but they account for 178,352,288 (23.0%) of prime weight. In X262144 the corresponding low-end and high-end masses are 26,418,285 and 26,989,619 of total119,219,840. Therefore a proof should distinguish the frequent low-q refiring contribution from rare expensive q~B hits; a raw event count can hide their arithmetic costs. The same auditor prints five disjoint p_i bands: (0,B/16], (B/16,B/8], (B/8,B/4], (B/4,B/2], (B/2,B].


## 4. Concrete proposed proof route: prime-hit incidence and arithmetic transport

Let H_q(X) count ALL ACTUAL high events across all canonical starts whose clipped increment d contains q>=13 (even if q is not their minimum high factor). The arithmetic identity/upper bound is

    Lambda_X <= sum_(13<=q<=B, prime) q H_q(X).

A **sufficient but unproved prime-incidence lemma** is a scale-uniform bound with some fixed absolute C:

    for every prime 13<=q<=B, H_q(X)<= C X B/q.         (INC, OPEN)

Then Lambda_X<= C X B * (pi(B)−pi(11)) = O_C(X B²/log B) = o(X²), which is even stronger than the new fixed-coefficient H5. Unlike merely verifying two affine CRT roots at a low sink, INC must control the occupancy of **ADAPTIVELY SELECTED** sink states and the charged-to-charged chains, including recurring q after intervening different high-prime events. Earlier proven all-state refractory lemma excludes a q>1157 at two immediately consecutive high events, but it can return later. The first/second high-wave CRT bounds already proved in earlier notes do not extend directly to unbounded depth because products of historical moduli exceed X.

An intermediate program that could prove INC or a less demanding directly aggregated fixed-coefficient H5:

1. For each q, split q-hit episodes into first q-hit and reactivations after other high primes. Use the exact q-specific clock and low-wheel bounded episode length; pin down an explicit charge to **intervening different-high-prime increments**, avoiding repeated counting when two q-hits are separated by many other high events.
2. Aggregate over q *before taking absolute values*. At low-sink visits q>=193 has exactly two candidate affine residues (previous sink-priority theorem), and q is inactive immediately after it fires. Test the joint source/time transport distribution on a **mesoscopic window of starts and q**, not each exponentially numerous adaptive CRT history cell.
3. Seek a signed Type-II / bilinear dispersion bound for the pushforward source-count measures at charged and low-sink states. A formula asserting independent uniform CRT phases at all adaptive visits is stronger than the known evidence and is not proved; the previous full-wheel data show nonzero individual prime biases and substantial cross-prime correlations.
4. A **fixed-coefficient** upper bound with a quantitative safety margin suffices: e.g., Lambda_X <= 0.04 X² along unbounded dyadic X is already below 39/848. The corresponding T_X <=0.03 XB is another sufficient target. Proving either remains OPEN.

Note a purely uniform density calculation of the two CRT roots cannot by itself guarantee twin-producing full sinks. This is a lower-bound parity issue. Terence Tao, *254A, Notes 4: Some sieve theory*, discusses the parity barrier, https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/ . Friedlander–Iwaniec, *Asymptotic sieve for primes*, Annals of Mathematics 148 (1998), pp. 1041–1065, https://annals.math.princeton.edu/articles/13036 , develops a bilinear axiom to overcome sieve parity in some sequences, but does NOT verify it for twin primes or for our dynamical pushforward measure. The extra arithmetic information would have to come from the **time-ordered GCD update and transported source multiplicities**.

## Status

**Paper-level proved, conditional on old finite 133-step certificate**: (H1)–(H7) and their twin-prime implications. **Computational, not Lean**: finite source scan/test table and 133-step certificate. **Unproved analytic inputs**: H3–H6 strict liminf bounds and incidence lemma INC. No twin-prime infinitude, OEIS A166944 strict-record theorem, Lean build or main merge.

### Reproduce

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/weighted_high_clock_criterion_audit.cpp -o /tmp/weighted_high_clock_criterion_audit
/tmp/weighted_high_clock_criterion_audit 4096 16384 65536 262144 1048576
```
