# A166944: low-clock deficit budget, exact 133-step low closure, and a constant-threshold first-moment twin-prime criterion

Date: 2026-11-23 JST. Issue #4 / parent Issue #1, dedicated branch `research/issue-4-terminal-survivor-positive-budget`. Continuation of `2026-11-23-low-sink-priority-and-two-root-renewal.md`. **Paper arguments below depend on an exhaustive finite 3/5/7/11 wheel certificate checked by committed C++17, not on a Lean kernel proof.** The **asymptotic mean-high-event bound remains open**, and neither infinite twin primes nor the stronger A166944 strict-record conjecture is proved.

## Definitions

For even dyadic X>=256, B=ceil(sqrt(7X)), canonical odd M in I_X=[X,2X), start s=M+2, C(s)=2M-2, K(M)=floor((7M-1)/4). At n>s, take the parity-dependent GCD g(n,C) (even n: gcd(n,C-1); odd n: gcd(n-2,C+1)), clip d=gcd(g,L_B) where L_B is product of odd primes <=B, and update C'=C+d-1. Events are times d>1. The high events are those d divisible by at least one prime >=13, counted as T_B(M). Low-only events have d with prime factors only in {3,5,7,11}.

At each event plateau origin (t,C), define nonnegative even deficit z=2t-C. At the next event with delay delta and increment d, the exact identity is

    z_after-z_before = 2 delta-d+1.                                 (1)

A *low-active* plateau means at least one of 3,5,7,11 divides (C-1)(C+1). A high event at such a plateau is called LOW-INTERRUPTING; a high event at a low-inactive plateau is called a LOW-SINK high event. This is an exact disjoint classification for ALL high events, including composite increments.

## New finite universal low-only bounds (exhaustive, NOT Lean)

The prior graph of all (t mod2310,C even mod2310) has 2310*1155=2,668,050 states, 311,850 terminal sinks, and **no directed cycle**. Extending its full topological dynamic programming to elapsed low-only clock time and to deficit-gain prefixes produces:

| quantity, over ALL low-only states | maximum |
|--|--:|
| nonunit low events until low sink | 22 |
| cumulative low-only growth sum(d-1) | 1156 |
| elapsed time from arbitrary origin until terminal low sink | **133** |
| maximum gain 2u-e over any low-only prefix, including the sink | **192** |
| maximum gain 2u-e over any low-only prefix whose endpoint STILL has active low clock | **172** |

Here u is elapsed time along low-only events and e=sum(d-1). These maxima are maxima of DIFFERENT quantities, not necessarily simultaneously attained. The source 
`research/universal_low_clock_time.cpp` computes the entire 2,668,050-state graph, checks acyclicity, and verifies all five bounds in <1s in a local C++17 -O3 run. A second independent original parity-specific full-wheel scan `research/charged_clock_budget_audit.cpp` checks all interpolated low-only blocks against these inequalities on X4096/16384/65536/262144/1048576 and confirms old high-event totals. **The universal 133 / 172 / 192 bounds are certified by a finite exhaustive computation, not yet Lean-checked.**

## 1. A NEW exact amortized interrupted-high-event inequality (PAPER with finite certificate)

Consider any two consecutive high events along a canonical orbit; for the first high, use the canonical origin s (z=6). In between, only low primes act, giving elapsed time u<=133 and total low growth e>=0. Let the next high event have delay delta, odd increment d, and pre-event frozen state C. By (1):

    z_new-z_prev = (2u-e)+(2delta-d+1).                      (2)

If the next HIGH event is LOW-INTERRUPTING, an active low prime a<=11 fires within 2a<=22, so delta<=22. The prefix endpoint is low-active and 2u-e<=172. Consequently

    BOXED: LOW-INTERRUPTING high event: z_new-z_prev <=217-d.    (3)

In particular d>=219 consumes at least 2 units of deficit across the COMPLETE low-only block and ensuing high event. This sharpens the simpler *single event* observation delta z<=45-d from an active-low plateau.

If the next high event instead occurs at the LOW-SINK, the low-prefix gain is <=192; some high prime q<=B divides C±1 and its clock is at distance delta<=2q<=2B. Hence

    BOXED: LOW-SINK high event: z_new-z_prev <=4B+193.          (4)

Choose any integer Q>217. Define `I_big(M,Q)`=#low-interrupting high events with **clipped increment d>=Q**, `I_small(M,Q)`=#low-interrupting high events with d<Q, and `S(M)`=#low-sink high events (ALL high events form their disjoint union). Starting deficit is z=6, and all subsequent event deficits are nonnegative. Sum (3),(4) over high events, bounding each small interruption's delta z by217:

    BOXED: (Q-217)*I_big(M,Q)
           <=6 + 217*I_small(M,Q) +(4B+193)*S(M).             (5)

No equidistribution, prime randomization, or conjecture is used here; the all-low-wheel finite certificate is the only computational prerequisite. In particular

    T_B(M)<= (1+(4B+193)/(Q-217))*S(M)
             +(1+217/(Q-217))*I_small(M,Q)+6/(Q-217).        (6)

For any fixed 0<theta<1 and Q≈B^theta, an upper bound S_total=o(XB^theta) and I_small,total=o(XB) (the latter still difficult) suffices for T_total=o(XB). Since the empirical low-sink category dominates, (5) is a STRUCTURAL separation, not a complete asymptotic argument.

## 2. Much weaker SUFFICIENT first-moment criterion for infinitely many twins (PAPER)

**New horizon lemma:** Suppose a canonical trajectory has not reached any full-wheel sink before its terminal clock cutoff K(M); a full-wheel sink means NEITHER C−1 NOR C+1 has any prime factor <=B. From any event plateau (or the initial origin), the next high event, or a full-wheel sink, is reached within at most

    D_B=133+2B                                                       (7)

time steps: first run the all-low-prime clock process, which has duration <=133, until it is interrupted by a high prime or no low primes remain. If no low prime remains and no full-wheel sink has appeared, some high q<=B is active and its clock rings within <=2q<=2B. The same argument bounds the last incomplete time block before cutoff, provided no full-wheel sink occurs before K. Hence for every NON-SINK trajectory,

    BOXED: K(M)-(M+2) <= (T_B(M)+1)*(133+2B).                 (8)

For odd M in [X,2X), `K(M)-(M+2)>=(3X-11)/4` and `B²/X->7`. Thus any non-sink M has

    T_B(M) >= (3X-11)/(4(2B+133))-1
           = (3/56-o(1))*B.                                  (9)

Because there are N=X/2 canonical odd starts, if NO start yields a full-wheel sink in a given dyadic window, the aggregate total T_X=sum_M T_B(M) must satisfy

    T_X/(XB) >= (1/(2B))*((3X-11)/(4(2B+133))-1)
             =3/112-o(1).                                    (10)

**CRUCIAL new weakening of the previous sufficient hypothesis:** Twin-prime infinitude follows if one can prove merely

    BOXED: liminf_(X=2^k -> infinity) T_X/(X B) < 3/112 ≈0.026785714.  (11, OPEN)

Indeed (11) means infinitely many scales have a canonical trajectory that reaches a full-wheel sink. Such a sink at n<=K(M) has C<=2n<=7X and C+1<(B+1)². With C±1 odd, having no prime divisor <=B forces **both** C−1 and C+1 to be actual primes. Their sizes grow >=2X−3 over unbounded scales, producing infinitely many distinct twin-prime pairs.

This is **strictly weaker** than proving T_X=o(XB). It requires only a SMALL ENOUGH fixed coefficient in an `O(XB)` bound, and only along an unbounded subsequence of dyadic scales. It is a meaningful change to the target theorem, not a proof of its open hypothesis.

A stronger positive-fraction statement follows if limsup T_X/(XB)<3/112, but the sources may coalesce to the same twin center and the count of DISTINCT twin centers would then require a multiplicity bound.

## 3. Finite original-GCD high-budget audit

The new independent full-wheel scanner verifies the exact jump-clock recurrence against literal one-step original parity GCD for M=7..119, verifies all prior high event totals, all time and gain bounds per low-only block, the amortized inequality (5) for Q=219 where Q<=B, and checks that full-wheel sinks have two primes by an independent smallest-prime-factor sieve.

| even X | B | threshold Q | all high T_X | low-sink high S_X | low-interrupt high d<Q | low-interrupt high d>=Q | T_X/(XB) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,096 |170|171|7,675|5,705|1,872|98|0.011022|
| 16,384 |339|219|45,343|33,806|11,279|258|0.008164|
| 65,536 |678|219|224,221|169,370|53,220|1,631|0.005046|
| 262,144 |1,355|219|1,198,498|924,164|264,278|10,056|0.003374|
| 1,048,576 |2,710|219|5,516,751|4,264,639|1,200,788|51,324|0.001941|

All 5 checked dyadic windows had a full-wheel sink for **every** canonical start before its original cutoff (finite fact only); the scanner independently verifies each resulting `C±1` pair is prime. This fits the constant-threshold argument but is not evidence that the property holds for all larger X. In X=1,048,576, sink events are 77.3% of high events; low-active high events with increment >=219 are only 0.93%, so focusing on rare large interruptions alone cannot finish the proof. The sink successor distribution and small low-interrupting events remain substantial.

The whole-orbit non-sink inequality (8) passed as a finite test (the non-sink branch was vacuous in these 5 windows, so its paper proof is essential). The per-high block bounds (3),(4) and global budget (5) were *nonvacuously* tested on all actual high events.

## 4. More realistic next arithmetic direction

Instead of the earlier demanding triple of separate signed reset-dispersion/4th moment/collision moment and charged-run estimates, investigate the **ONE constant-threshold mean count (11)**. A sharp enough first moment of high-event count suffices, without proving full o(XB), and can exploit the exact 2-root CRT of high events after low-sink states.

The budget (5) provides an accompanying decomposition: after summing over M, a strong control of LOW-SINK high-event visits and of low-interrupting increments smaller than a chosen Q automatically controls larger low-interrupting events. For Q≈B/2 the coefficients approach `(9)*S+(1)*I_small` at fixed scales as B→∞, though these categories still need analytic control. Empirically S dominates; the major OPEN estimate is occupation of recursively selected low-sink centers `C_inf±1`, with correlations generated by charged→charged dynamics.

**Parity barrier audit:** the full-wheel sink itself is the primality of an odd pair C±1; unconditional lower bounds on such sinks from only local residue densities run into the classical sieve parity obstacle. Ford, *On Bombieri's Asymptotic Sieve*, Trans. AMS (see https://www.ford126.web.illinois.edu/wwwpapers/asymsieve.pdf, especially introductory discussion), explains why residue-distribution axioms alone cannot detect primes; Friedlander–Iwaniec, *Asymptotic sieve for primes*, https://arxiv.org/abs/math/9811186, studies a bilinear extra condition needed to overcome a parity-type obstruction. Our finite-state time-order and exact clock competition are candidate extra information, but NO such parity-sensitive bilinear theorem has yet been established for our adaptive state measure.

### Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/universal_low_clock_time.cpp -o /tmp/lowclock
/tmp/lowclock

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/charged_clock_budget_audit.cpp -o /tmp/budget
/tmp/budget 4096 16384 65536 262144 1048576
```

The first source exhaustively certifies all low-wheel states; the second is independent full-event parity GCD, not an invocation of Lean. Existing branch research files provide the earlier derivation of `E<=22+23T` and `W<=3X+4B E`, which are not needed for the weaker criterion (11). No modification of main.
