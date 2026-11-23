# A166944 Issue #4: sharp RESET-slice LOW23 certificate, and a first-vs-repeat prime-hit route to twins

Date: 2026-11-23 JST. Branch `research/issue-4-terminal-survivor-positive-budget`, issue #4, parent #1. This is a new continuation of `research/2026-11-23-q17-exhaustive-nilpotence-and-symbolic-q19.md`. All formulas below are paper-level mathematical arguments, with explicitly separated finite computational certificates and open asymptotic hypotheses. **Infinite twin primes and the A166944 strict-record conjecture are not proved. No new Lean kernel proof.**

## 1. State-space compression specific to ACTUAL reset episodes

For odd squarefree low wheel with primes up to `y` (here y in {17,19,23}), put `P_y=product_(odd prime p<=y)p`, `L_y=2P_y`. The exact restricted GCD at plateau time t and even state C is computed using the original parity-specific gcd at future n: even n uses gcd(n,C−1), odd n gcd(n−2,C+1); clipped increment d is the product of distinct allowed p dividing this gcd, and C increases by d−1.

After an actual HIGH RESET (or at a canonical starting seed), the initial deficit `z=2t−C` is **0 if t is even, 6 if t is odd**. Thus the RESET initial state has the shape `C=2t−z(t%2)`. Since all restrictions depend only on `(t mod L_y,C mod L_y)` and `L_y` is even, the restricted orbit from the reset manifold is determined by `r=t mod L_y`, i.e. there are **only L_y possible reset initial states**, rather than `2(P_old)^2` arbitrary q-post-event states.

This is a very substantial compression: for q19, arbitrary post19 graph has 130,310,230,050 states, but the RESET initial manifold has `L_19=9,699,690`; for q23 the arbitrary post23 graph would have `2*(P_19)^2=47,041,993,048,050` post-q states, whereas the RESET initial manifold has `L_23=223,092,870`. **Important scope:** this finite result covers only true parity-compatible RESET origins. It does **not** establish that the complete {3,...,23}-wheel terminates from all arbitrary CHARGED post-event states; it cannot directly replace previous global LOW17 theorem in arbitrary high-event gaps.

## 2. Exhaustive finite low-wheel RESET certificates (C++17, NOT Lean)

`research/low23_reset_slice_audit.cpp` enumerates all `r=0,...,L_y−1` by the exact full parity-specific GCD event-clock formula, with all simultaneous low factors multiplied. It stops ONLY when no allowed p divides either C−1 or C+1; it throws if any restricted orbit lasts >=3000 nonunit events. The results are all-state complete finite certificates, validated against independent `research/low23_reset_literal_oracle.py` that computes literal one-step parity-specific gcd without event jumping at extremal and sampled states.

| y | complete #RESET initial classes L_y | max restricted nonunit events | max elapsed clock steps | max cumulative clipped growth | max y-bearing events |
|--:|--:|--:|--:|--:|--:|
| 17 | 510,510 | 40 | 239 | 316 | 4 |
| 19 | 9,699,690 | 56 | 388 | 568 | 5 |
| 23 | 223,092,870 | 88 | 599 | 946 | 6 |

All maxima are over actual parity-compatible RESET initial states; maxima in different columns may occur at different state residues. For q23, the 223,092,870 states were exhaustively partitioned into **three disjoint integer ranges** [0,75m), [75m,150m), [150m,223092870). All states terminated; maxima by partition: (#events,time,#23hits,growth) = (75,599,6,820), (68,514,5,796), (88,533,6,946). Global extrema #events88 and growth946 both occur at t mod223092870=175438762; time599 at t mod=7491793; max23hits6 at t mod=7491793 or163925126. Independent one-step GCD checks all these exact witnesses and 1000 randomized reset phases for each cutoff 17,19,23. q19 extrema at phase8264689 gave56 events,388 steps,568 growth; q17 phase164569 gave40 events,316 growth. The scan is streaming with negligible memory (no 223m-entry graph).

Also from the exact RESET restricted low-only event-plateau trace, the maximum pre-event *active low-clock plateau origin* deficit z=2t−C is 270/424/558 for y=17/19/23, respectively. This is measured at the origins of nonunit event-to-event jumps, NOT at every intermediate literal no-event integer step (where z can be larger). Full restricted prefix growth from reset is <=946 for y23.

## 3. Two useful actual-full-wheel corollaries of the RESET23 certificate

Let B=ceil(sqrt(7X)) >=29. Start from an actual full-wheel RESET state (t,z) with z0=0 even or6 odd. Before the first event whose increment includes any prime>=29, the actual full wheel is exactly a prefix of the S23 restricted wheel. Thus:

**RESET-to-high or sink clock bound:** From such a reset, within at most `599+2B` elapsed integer steps, either a >=29 prime has acted OR a full-wheel inactive state C (no prime <=B divides C±1) was reached. Proof: an >=29 high event may interrupt the 23-low process earlier; otherwise S23 becomes fully low-inactive within599 steps, and any remaining active high q<=B has next clock within2q<=2B.

**Terminal two-root simplification for sufficiently large FIRST high factor:** Suppose the first event involving a prime>=29 after RESET contains q>=653. Before that event, every low-active event-origin has deficit z<=558. If any p<=23 were still active, the event delay delta would be <=46, so `z_e=2n−C=z+2delta<=650`. At even event n, `gcd(n,C−1)=gcd(n,z_e+1)` has every prime factor<=651; at odd n, `gcd(n−2,C+1)=gcd(n−2,5−z_e)` has every factor<=645 (using z_e>=2). Contradiction to q>=653. Thus the first high q>=653 must occur after S23 low clocks stop. At its S23 virtual terminal `C_inf=2t−z+e_inf(t mod 2P23)`, q must divide C_inf−1 or C_inf+1: **TWO CRT roots mod q per fixed low residue**, now with all primes<=23 absorbed. This is a necessary condition for the first >=29 event only, not a theorem for later charged-state hits. It also does not improve the older >=193 bound with the smaller 11-wheel for the differently defined first >=13 high event.

**Reset-specific large-q refractory lemma:** If a q-bearing event q>947 leaves an actual parity RESET state, and no other high event with factor>=29 occurs before the next attempted q hit, then there can be no next q hit. The intervening 23-low-only cumulative growth E is <=946, but q post-state residues require E>=q−1 to reactivate q. This lemma is restricted to a RESET qpost state and absence of other >=29 factors; interactions between different large primes remain possible.

## 4. A NEW especially simple scalar sufficient theorem: first vs repeated q hits

We can use the earlier **arbitrary-state LOW17** finite theorem (all primes<=17-only trajectories stop within769 time steps) to count only primes q>=19 in the ORIGINAL full B-wheel. For each original canonical source M, let `N_q(M)=#{original events n<=K(M) with q|d_M(n)}`. Define

    H_q(X)=sum_(M in I_X) N_q(M),
    F_q(X)=#{M in I_X:N_q(M)>=1},
    R_q(X)=H_q(X)-F_q(X),
    H_X=Σ_(q>=19 prime<=B)H_q,
    F_X=Σ_q F_q,
    R_X=H_X−F_X,
    theta_X=F_X/H_X (when H_X>0).

`F_q` is one FIRST occurrence per original source if that q ever acts; `R_q` counts every second and later occurrence of the same q for that source. Since there are exactly |I_X|=X/2 canonical starts,

    F_X <= (X/2) * #{primes q in [19,B]}.                  (F1)

Every event bearing a prime>=19 contributes at least one prime incidence (events with multiple high factors contribute more). Thus

    T19_total(X) <= H_X = F_X/theta_X
                  <= (X/2)*pi_[19,B]/theta_X.            (F2)

**NEW PAPER SUFFICIENT THEOREM:** If there is a fixed rho<1 and infinitely many dyadic X along which

    R_X<=rho*H_X, equivalently theta_X>=1−rho>0,       (F3, OPEN)

then `T19_total=O(X*pi(B))=O(XB/log B)=o(XB)` on that subsequence. By previous no-sink high19 clock theorem and exact aggregate horizons, infinitely many twin prime pairs follow. No independent CRT phase assumptions are needed for the implication; the **OPEN** arithmetic task is F3 itself.

**WEAKER sufficient first-hit fraction:** A fixed positive lower bound on theta_X is far stronger than required. For example, on an unbounded dyadic subsequence, if

    theta_X >= c/sqrt(log B)   with any fixed c>0,      (F4, OPEN)

then T19/(XB)=O(1/sqrt(log B))→0 on that subsequence, also proving infinitely many twins. More generally `theta_X*log B→∞` along an unbounded dyadic subsequence is sufficient. This targets a positive density of first occurrences *relative to the repeated prime-hit population*, not a uniform distribution of all high-prime residues.

**Exact reactivation prerequisite (PAPER):** Immediately after any q hit, for q>=19, C≡0 (even event) or C≡−2 (odd event) modq; to hit q AGAIN, intervening events not carrying q must cumulatively grow C by an even nonnegative E satisfying E≡±1 (even qpost) or E≡1,3 (odd qpost) modq. Therefore E>=q−1 on any interval between consecutive q hits (and E>=q+1 after an odd qpost). This is a deterministic recharge constraint and suggests a multi-prime "recharge/dependency graph" proof of F3 or the weaker F4. **Double-counting obstacle:** many dormant q may use the same intervening non-q growth; simply summing E>=q−1 over q does not establish a contraction. The genuine task is a bound on overlapping recharge intervals or a source-weighted arithmetic transfer bound ensuring a fresh fraction of prime labels.

## 5. Exact original-full-GCD incidence audits

`research/high_prime_repeat_incidence_audit.cpp` performs full source-by-source event jumps implementing the original parity GCD and clipped squarefree product with original deadlines, and explicitly marks first q occurrence for each M. It matches earlier historical high13/high17/full-sink tests, and its small-M literal-step GCD control. Independently, `research/high_prime_repeat_literal_oracle.py` computes every ORIGINAL single integer step for X256,512,1024,4096, matching exact (H_X,F_X) (163,128),(265,265),(640,577),(5391,4823).

| X | B | H_X = total prime>=19 incidences | F_X = first incidences | R_X/H_X |
|--:|--:|--:|--:|--:|
| 4096 |170|5391|4823|10.5361%|
| 16384 |339|31042|25450|18.0143%|
| 65536 |678|160698|136058|15.3331%|
| 262144 |1355|868502|703647|18.9815%|
| 1048576 |2710|4031949|3248703|19.4260%|
| 1999996 |3742|8564171|6757307|21.0979%|

The last X is not dyadic and is only a finite diagnostic. At X1048576 q19 recurrence fraction is47.83%, q23 40.83%, q29 31.23%, q97 6.96%, q509 2.45%; the aggregate is much smaller than the small-q worst case. At X1999996 the q19 recurrence fraction reached50.9973%, aggregate21.0979%; thus **DO NOT** conjecture an untested per-q rho<=1/2 from earlier scales. Neither the aggregate <0.22 nor theta→constant is proved asymptotically. The finite tables provide no uniform estimate by themselves.

## 6. Actual next proof experiment / bottleneck

A realistic proof plan is **not** to enumerate arbitrarily many ever-larger q-return graphs; their state count grows primorial-squared, and even a termination result for the fixed wheel S<=B does not give the `o(X)` time bound needed by original K(M)~X. Instead:

1. Use the COMPLETE reset manifold to treat many low-clock episodes exactly; the S23 reset budget is<=599 elapsed steps and <=946 growth even though the arbitrary q23 post graph has astronomically more states. This collapses the predictable part of every reset-to-high transition.
2. Track q-bearing post-event states (q>=19), split first vs repeat q hits by ORIGINAL source ID, and analyze the EXPLICIT activation congruence E modq. For q>947 on RESET return episodes, any repeat needs some DIFFERENT >=29 high prime intervening. Study the resulting **overlap of prime-recharge intervals** in the event/source graph; a bound `theta_X >> 1/log B` even only on some dyadic subsequence would already finish the twin argument.
3. The hard case is arbitrary high-CHARGED post-event state and subsequent multi-prime recharge. Low<=23 RESET-slice certificates must NOT be claimed to control those states. Ordinary independent uniform unit pulse mixing was previously falsified by the actual high increment residue TV~0.793, so a valid contraction must use arithmetic/cross-prime correlations or source-weighted transport.

No proof of the asymptotic first-hit fraction, original A166944 record conjecture, or twin infinitude has been obtained. This is a scoped research checkpoint, with all finite computation independently reproducible and no Lean formalization.

## Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low23_reset_slice_audit.cpp -o /tmp/low23_reset
/tmp/low23_reset 17 510510
/tmp/low23_reset 19 9699690
/tmp/low23_reset 23 75000000 0
/tmp/low23_reset 23 150000000 75000000
/tmp/low23_reset 23 223092870 150000000
python3 research/low23_reset_literal_oracle.py

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/high_prime_repeat_incidence_audit.cpp -o /tmp/high_repeat
/tmp/high_repeat 4096 16384 65536 262144 1048576 1999996
python3 research/high_prime_repeat_literal_oracle.py
```
