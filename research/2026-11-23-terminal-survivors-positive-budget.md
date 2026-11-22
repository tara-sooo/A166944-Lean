# A166944 squarefree wheel: terminal survivor episodes, all-height one-shot transfer, and a positive insertion budget

Date: 2026-11-23 JST. Assigned child [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [#1](https://github.com/tara-sooo/A166944-Lean/issues/1). Independent work branch `research/issue-4-terminal-survivor-positive-budget`, based on main `bd180e3de0fe6e12cc3c3ea25d65a985445344eb`. Related but *mathematically distinct* from [Issue #3](https://github.com/tara-sooo/A166944-Lean/issues/3), which studies four-residue correlations.

**Evidence classification.** The finite-sum/episode-opening/one-shot shifted-state identities and conditional sufficient estimates below are elementary paper proofs, **not Lean kernel results**. The five-scale numbers are C++17 exact finite tests, verified by independent literal-step checks for small seeds and previously stored independent regressions on three scales. The universal positive stage budget, uniform shifted-state tail average, twin-prime infinitude, and original `OeisA166944.conjecture` remain **OPEN**.

## 1. Exact definitions, and the substantially weaker sufficient positive budget

For even `X>=256`, write `B=ceil(sqrt(7X))`, `I_X={odd M: X<=M<2X}`, `s=M+2`, `K(M)=floor((7M-1)/4)`. Start the original parity-specific clipped-GCD recurrence from `D(s)=2M-2`. The wheel `L_p` is the squarefree product of odd primes `<=p`, and `L_{p^-}` is the prefix before fresh odd prime `p`. Denote `G_p(M)=D_{L_p}(K)-(2M-2)` and `Delta_p(M)=G_p(M)-G_{p^-}(M)`, which can be signed.

Define the positive budget

    P_p(X) = sum_{M in I_X} max(Delta_p(M),0),
    P_X    = sum_{p<=B, p odd prime} P_p(X).

Since the prime stages telescope and each `G_B(M)>=0`, we have the exact comparison

    sum_{M in I_X} G_B(M) = sum_{p,M} Delta_p(M) <= P_X.

The previously established squarefree wheel twin certificate is

    K(M)-s-3*G_B(M) >= 2B  =>  C_B(M)-1 and C_B(M)+1 are prime,
    C_B(M)=2M-2+G_B(M).

Put `H_min=floor((3X-6)/4)` (the minimum `K(M)-s` on `I_X`). If the finite inequality

    BOXED: 6*P_X < X*(H_min-2B)

holds, there exists `M in I_X` satisfying the twin certificate: otherwise each of the `X/2` starts would have `3G_B(M)>H_min-2B`, forcing `6*sum_M G_B(M)>X*(H_min-2B)`, contradicting the budget. Thus, in particular, the following OPEN analytic hypotheses would suffice for infinitely many twin primes:

    liminf_{even X -> infinity} P_X / X^2 < 1/8,
    OR uniform P_p(X) <= C*X*p for all odd primes p<=B,
    OR (stronger) uniform P_p(X) <= C*X.

Indeed `sum_{p<=B}p = O(B^2/log B)` and `pi(B)=O(B/log B)`, so the latter two would give respectively `P_X=O(X^2/log X)` and `P_X=O(X^(3/2)/log X)`. A global `P_X=O(X*B)` would also suffice. **These are implications, not achieved universal estimates.** This is a route to twin-prime *infinitude*, not yet to the stronger OEIS A166944 strict-record statement.

## 2. Exact terminal survivor and episode-opening lemma

Compare **same start M, same index n** between old `L=L_{p^-}` and new `Lp` trajectories. Write

    H(n)=D_{Lp}(n)-D_L(n).

A nonzero *episode* begins at any step `n` where `H(n-1)=0` and `H(n) !=0`. If both horizons coincide immediately before that step, the raw parity-specific gcd `g` is identical in both wheels. As `gcd(p,L)=1`, exactly one of the following holds:

    p does not divide g: d_new=d_old and H(n)=0;
    p divides g:          d_new=p*d_old, H(n)=(p-1)*d_old>0.

**Lemma S1 (paper).** Every positive or eventually negative episode must **open with a p-containing event** in the new trajectory, and opens with strictly positive difference. Thus

    BOXED: number of nonzero episodes E_p(M) <= N_p(M),

where `N_p` counts new-wheel events with `p | d_new(n)`. A subsequent sign change without visiting H=0 is possible; positivity is asserted only at the episode *opening*. A return to H=0 **does not guarantee permanent equality**: a later fresh-p event can re-open a new episode.

Combining S1 with the earlier paper-level modular recharge lemma for odd `p>=5` gives, if any p-hit occurs,

    BOXED: (E_p(M)-1)*(p-1)
           <= (N_p(M)-1)*(p-1)
           <= sum_{n: p does not divide d_new(n)}(d_new(n)-1).

(The lower bound on the non-p excess between consecutive p hits is p-1 for a preceding even p hit, p+1 for preceding odd p hit.) This **charges the number of reopened episodes**, not their size, to non-p new-wheel growth; reusing a charge across different p is not yet addressed.

For terminal `H(K) !=0`, the final episode's exact opening time `tau_last` is the first index *after the last zero of H*, where H becomes nonzero. The identity

    BOXED: Delta_p(M)=sum_{tau_last<=n<=K} (d_new(n)-d_old(n))

follows by telescoping and includes **all cancellation** in completed earlier episodes. If `H(K)=0`, then the stage's terminal contribution is exactly zero even if many events occurred earlier. The last equality time is `tau_last-1` for a nonzero terminal episode. A stage with one p-containing event has at most one nonzero episode and can never reopen after exact equality is restored.

## 3. NEW: all-deficit-height post-freeze ONE-SHOT shifted-state identity

Fix prime p fresh to L, and a start M. Suppose:

1. The first divergence `tau` occurs strictly *after* the final nonunit event of the **old** L-wheel, so its terminal horizon `C=D_L(K)=D_L(tau-1)` is frozen and the old increment at tau is 1;
2. The new Lp-wheel has exactly **one** p-containing event on `(s,K]`, namely that first divergence at tau.

Then `d_new(tau)=p` and `D_new(tau)=C+p-1`. At every later step the new increment is q-free, so it is exactly the increment prescribed by the **old** L-wheel, but from the shifted state `(tau,C+p-1)` instead of the old canonical state.

Let `T_L(tau,H;K)` denote the cumulative `d_L(n)-1` over `tau<n<=K` when the L-clipped recurrence is restarted *at time tau* with horizon `H`, using the same original parity-specific gcd and no artificial canonical-reset requirement. We obtain

    BOXED: Delta_p(M) = (p-1) + T_L(tau,C+p-1;K).

This is a positive exact formula and makes **no assumption on post-hit deficit height `k`**. The earlier height-0 four-residue canonical-seed reconstruction was one way to bound the shifted-state term; for `k>=1`, the same term still exists and is well-defined, although it is *not* automatically equal to the growth of a natural canonical seed.

A clean missing input would be the *average arbitrary-state response bound*, for the set `S_p` of such post-freeze one-shot sources:

    CONJECTURAL TRANSFER INPUT:
    sum_{M in S_p} T_{L_{p^-}}(tau(M),C(M)+p-1;K(M)) <= A*X*p,

uniformly over `p<=B` and sufficiently large even `X`. Since `(p-1)*|S_p| <= X*p/2`, this would give an `O_A(X*p)` bound for **all post-freeze one-shot heights at once**. Proving it would not yet cover other post-freeze p-refires or pre-freeze positive insertion costs, but it is a precise, height-independent target.

**Important scale check:** A much stronger pointwise claim `T_L(...)<=C*p` for a small numerical C is false in the finite data: at `X=65536, M=122897, p=383`, the post-hit old-wheel tail is 6260, i.e. `6260/383 >16`. This is one reason to study averages rather than pointwise bounds.

## 4. Full-stage survivor audit, five dyadic scales

File: [`squarefree_survivor_audit.cpp`](squarefree_survivor_audit.cpp), compiled as C++17 `-O3 -Wall -Wextra -Werror`. It computes **all odd starts** `M∈[X,2X)` and **all odd primes** `p<=B`, comparing old/new exact event-jump parity-GCD trajectories up to the same natural K. All events are merged chronologically, and new-minus-old horizons are tracked after each event. Direct literal step-by-step gcd checks for odd `7<=M<=119`, caps `1,3,5,7,11,13,17`, all pass. Every first episode-opening satisfies `(p-1)*d_old(n)`, every episode count is <= number of p-containing hits, every post-freeze one-shot tail is independently rerun with the old wheel from the shifted state and matches the exact formula, and full signed prime-stage costs telescope to a separate B-wheel run.

| even X | B | # prime stages | touched stage/source pairs | terminal positive pairs | terminal negative pairs | touched but terminal zero | P_X | negative mass | terminal total growth |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1024 | 85 | 22 | 1,588 | 1,362 | 24 | 202 | 40,426 | 486 | 39,940 |
| 4096 | 170 | 38 | 7,953 | 7,014 | 257 | 682 | 445,678 | 46,536 | 399,142 |
| 16384 | 339 | 67 | 32,838 | 28,405 | 1,367 | 3,066 | 3,439,438 | 524,112 | 2,915,326 |
| 32768 | 479 | 91 | 66,733 | 59,095 | 2,321 | 5,317 | 7,171,394 | 602,226 | 6,569,168 |
| 65536 | 678 | 122 | 140,554 | 124,892 | 4,589 | 11,073 | 21,585,484 | 1,758,486 | 19,826,998 |

The first three `P_X`/negative/net values reproduce the independently stored `squarefree_first_split_timing_audit.cpp` regression. New scales 32768/65536 are fully calculated in this audit, not independently Lean-certified. At `X=65536`, 238 terminal-nonzero pairs had one or more completed returns followed by a **second episode**, e.g. `M=66819, p=11`; any such restart entails multiple p-containing events. The mean age of a nonzero final episode until K was **73,884 relative steps**, median 74,045. The final nonzero difference typically survives for a long frozen unit-increment tail; a late-time survival probability estimate based only on event frequency is therefore misleading.

| X | P_X/(X*B) | P_X/(X²/8) | max_p (P_p/X) | p attaining max | positive mass with exactly one p-hit / P_X |
|---:|---:|---:|---:|---:|---:|
| 1024 | 0.46445 | 0.30843 | 4.376 | 61 | 88.8% |
| 4096 | 0.64005 | 0.21252 | 14.267 | 79 | 90.4% |
| 16384 | 0.61925 | 0.10250 | 16.149 | 173 | 93.5% |
| 32768 | 0.45690 | 0.05343 | 7.320 | 257 | 95.6% |
| 65536 | 0.48579 | 0.04021 | 9.483 | 331 | 96.0% |

The measured `max_p P_p/X` values invite testing a uniform **`P_p<=C*X`** assertion, but those observations are not a proof and need not persist at larger scales. Even `P_p<=C*X*p` would suffice for the twin-prime mean criterion. The total raw time-activity L1 at X65536 was 31,068,254, versus 29,309,510 when including only each nonzero terminal episode's activity; deleting completed episodes reduces that particular L1 by ~5.7%, **not by an order of magnitude**. Rejoining alone therefore does not explain the much smaller final positive mass.

### Which post-freeze ONE-SHOT heights cost the most?

| X | total positive mass P_X | all post-freeze one-shot positive mass | tail contribution after first p-hit | (p>=11) height-0 cost | height-1 cost | height >=2 cost |
|---:|---:|---:|---:|---:|---:|---:|
| 1024 | 40,426 | 29,620 | 14,524 | 11,022 | 12,480 | 3,762 |
| 4096 | 445,678 | 352,256 | 202,720 | 94,572 | 143,694 | 104,556 |
| 16384 | 3,439,438 | 2,874,744 | 1,914,278 | 712,656 | 1,426,524 | 697,812 |
| 32768 | 7,171,394 | 5,748,088 | 3,219,950 | 2,109,072 | 2,586,126 | 977,370 |
| 65536 | 21,585,484 | 18,260,116 | 10,414,136 | 5,885,982 | 9,007,290 | 3,215,790 |

The height columns exclude p=3,5,7 and classify p>=11 using the proved post-freeze deficit lattice: height0 corresponds to `Z∈{0,6}`, height1 to `Z∈{2p,2p+6}`, height>=2 otherwise. At X65536, **height1 exceeds height0**, and **57%** of the all-height one-shot positive mass is from the *post-first-p tail*, not the initial p injection. Consequently a first-hit counting estimate or the prior height0-only canonical transfer cannot by itself settle the cost budget.

All five dyadic intervals additionally pass the sufficient finite `6P_X<X*(H_min-2B)` check. The scanner prints the first M meeting the original terminal prime certificate and independently checks both terminal neighbors are prime via the SPF sieve: `(X,M,twins)=(1024,1025,(2081,2083)), (4096,4097,(8291,8293)), (16384,16385,(32801,32803)), (32768,32769,(65537,65539)), (65536,65537,(131477,131479))`. These are elementary **finite** primality checks, not evidence for the unbounded X statement.

## 5. Next mathematical problem

The highest-value subproblem from this checkpoint is now sharply framed:

    Prove a uniform mean bound for the old L-wheel response
    to a single fresh-p shift of its frozen horizon, even when
    the first p-hit lands at deficit 2p+6 or higher.

A possible strategy is to count `(tau,C)` *shifted states* rather than canonical regeneration targets. For fixed `p`, collision of source starts into the same old frozen horizon `C=2M-2+G_L(M)` is controlled by the existing deterministic quadratic fibre-energy inequality `sum_C binom(k_C,2) <=(1/4)*sum_M G_L(M)` from `2026-11-22-squarefree-sqrt-wheel-mean-reduction.md`. This supplies a genuine combinatorial constraint on state multiplicity without relying on a complete primorial CRT period. What remains is a bound on the **old-wheel tail response** `T_L(tau,C+p-1;K)` for these correlated states; quadratic fibre energy controls multiplicity, **not** the dynamical tail values. It is conceivable to combine a shifted-state tail first moment with this fibre budget through dyadic truncation, but no universal bound has been established.

Also needed: fund p-refire **amplitudes**, rather than just episode counts, and bound pre-freeze positive costs, or find a different direct total-positive budget. Completed episodes should be removed only when they actually cancel; `H=0` at one time does not imply permanent coupling between different wheels. The main research target remains open, and there was no new Lean compilation in this checkpoint.

## 6. Reproduction

```bash
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/squarefree_survivor_audit.cpp -o /tmp/squarefree_survivor_audit
for X in 1024 4096 16384 32768 65536; do /tmp/squarefree_survivor_audit "$X"; done
```

The implementation's SPF sieve is fixed to the required finite X range (`256<=X<=262144`, even); only the five scales above are reported as completed. An attempted higher-scale X131072 run did not complete within the bounded execution budget and is **not** part of the verified table. No numerical result for that scale is asserted. C++ outputs `PASS` only if the embedded checks and historical regressions pass.
