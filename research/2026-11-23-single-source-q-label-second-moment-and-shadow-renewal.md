# A166944 Issue #4 — single-source prime-label second moment, quadratic-return tail, and leave-one-prime-out renewal

2026-11-23 JST. Dedicated branch `research/issue-4-terminal-survivor-positive-budget`, follow-up to `2026-11-23-q-reactivation-active-episode-two-step-survival.md`. All conclusions below are **mathematical implications**, conditional on the previously exhaustive finite LOW17=769-clock certificate; all numerical data are finite exact original clipped parity-GCD scans with independent integer-step Python verification. None of the requested asymptotic inputs has been proved, and the twin-prime / A166944 record conjectures remain OPEN. No new Lean kernel theorem.

## 1. An improved, FIXED-CONSTANT first-hit fraction criterion (paper)

Take X=2^k divisible by four, B=ceil(sqrt(7X)), odd canonical M∈I_X=[X,2X), original s=M+2 and cutoff K(M)=floor((7M−1)/4). Let q range over primes 19<=q<=B. Put N_q(M)=# original events with q dividing the odd squarefree clipped increment d_M(n). H_X=Σ_{M,q}N_q(M), F_X=Σ_{M,q}1_{N_q(M)>0}, theta_X=F_X/H_X if H_X>0, and T19_X=#events with a factor >=19. Let P_B=π(B)−π(18).

Earlier LOW17 arbitrary-state time bound769 and exact horizon Σ_{M in I_X}(K−s)=9X²/16−5X/4 imply that **in any dyadic X with NO full-wheel/twin-producing sink**, necessarily

    T19_X >= L_X := (9X²/16−5X/4)/(769+2B)−X/2
           = (9/224−o(1))*XB.

Always T19_X<=H_X, F_X<=(X/2)P_B, and H_X=F_X/theta_X. Therefore no-sink forces

    theta_X <= (X P_B /2)/L_X
             = (112/9+o(1))*(P_B/B)
             = (112/9+o(1))/log B.                         (FRACTION-OBSTRUCTION)

Consequently the **NEW, strictly WEAKER sufficient condition**

    BOXED: limsup_(dyadic X→∞) theta_X*log B >112/9≈12.44444  (OPEN INPUT)

implies infinitely many twin primes; previous proposed condition was theta_X*log B→∞. In particular theta_X>=13/log B on an unbounded dyadic subsequence suffices, once sufficiently large. This is an asymptotic hypothesis, not a verified empirical claim. The exact finite X certificate is `F_X/H_X > (XP_B/2)/L_X` (when L_X>0), where the RHS may exceed1 for small X and is then vacuous.

## 2. A different and potentially easier *same-source* positive second moment (paper)

Define

    BOXED: Z_X = Σ_(M∈I_X) Σ_(q prime 19..B) N_q(M)^2.

It involves ONE canonical source ID at a time. Unlike the previous positive synchronized q-clock energy `J_X=Σ_q qΣ_n mu_{q,n}²` over source PAIRS, this statistic is not inflated when many different sources have identical (n,C) trajectories after coalescence. Also

    Z_X=H_X+2D_X,
    D_X=Σ_(M,q) binom(N_q(M),2),

so D_X counts pairs of **two q-hit times within one original source**, whether consecutive or not. Weighted Cauchy over at most `K0=(X/2)P_B` source-prime labels gives

    BOXED: H_X² <= (X/2)*P_B*Z_X.                    (C-S)

The strong but transparent, **OPEN** estimate

    BOXED: Z_X=O(XB) on an unbounded dyadic subsequence   (MOMENT-STRONG)

implies H_X=O(XB/sqrt(log B))=o(XB), hence twin infinitude by the previous LOW17 horizon criterion.

The *strictly weaker fixed-coefficient* version is also sufficient:

    BOXED: liminf_(dyadic X→∞) Z_X/(X B log B)
                 < 81/25088 ≈ 0.0032286352.           (MOMENT-FIXED, OPEN)

Indeed P_B~B/logB and if no twin-producing sink exists, H_X>=(9/224−o(1)) XB, hence (C-S) entails

    Z_X >= H_X²/((X/2)P_B)
        >=(81/25088−o(1)) X B log B.

For each fixed X with `L_X>0`, the explicit arithmetic test `Z_X < 2 L_X²/(X P_B)` guarantees at least one full-wheel sink within the original canonical window. No distribution hypothesis is involved in the reduction, only in establishing its OPEN strict bound.

## 3. A clean *quadratic tail* sufficient condition (paper)

Let

    D_k(X)=#{(M,q): M∈I_X, q prime19..B, N_q(M)>=k}, k>=1.

The exact summation-by-parts identity is

    BOXED: Z_X=Σ_(k>=1) (2k−1) D_k(X),    D_1=F_X.

For odd prime q, successive q clock times have gaps at least `q−2>=17`: even q clock n≡0 mod2q, odd clock n≡q+2 mod2q. Since K(M)−s(M)<3X/2, the maximum possible N_q(M) is `O(X)`, and the number of nonzero terms of this sum has logarithm O(log X).

It would therefore suffice to prove the following **aggregate** (not per-prime!) tail:

    BOXED: D_k(X) <= C X P_B/k²  uniformly for k>=1.    (TAIL-2, OPEN)

Then `Z_X<=2CX P_B(1+log O(X))=O(X P_B log X)=O(XB)` by the prime number theorem; twins follow. The critical exponent 2 is enough here because `π(B)≈B/logB` supplies the necessary saving.

A particularly concise alternate **dyadic doubling contraction**, also OPEN, is

    BOXED: D_(2k)(X) <= (1/4) D_k(X)   for every k>=1.   (TAIL-DOUBLE, OPEN)

In fact, it is enough to impose the contraction ONLY at `k=2^j` for integer `j>=0`, not at every k. Iterating at powers of two gives `D_(2^j)<=4^{-j} F_X`; monotonicity yields `D_k<=4F_X/k²`; and therefore `Z_X=O(F_X log X)=O(XB)`. This hypothesis permits arbitrarily many q-hits in exceptional sources, as long as the **aggregate** return-label population drops by 1/4 under doubling the hit threshold. Pointwise contraction for each q is stronger and not claimed.

## 4. A *leave-one-prime-out shadow* identity for the next return (paper)

Fix one original source M, prime q>=19, and a q-hit post-event state `(t,C)` with original cutoff K(M). To predict the *FIRST* subsequent q hit, run a SHADOW copy of the original recurrence from this same state, but with q deleted from the clipped prime set, leaving all other p<=B unchanged. At each shadow plateau (u,C_u), let δ_other be the minimum clock delay of all active primes p≠q, and δ_q the next q clock delay if q divides C_u−1 or C_u+1 (otherwise infinity). The first q hit in the FULL recurrence is **exactly** the first shadow plateau for which

    δ_q <= δ_other AND u+δ_q <=K(M).

If δ_q=δ_other, the true event has a *composite* clipped increment with q among its factors; the next q-hit time is still u+δ_q. Before this first q hit, the full and q-deleted trajectories agree, by simple induction on their intervening non-q events. This comparison removes the feedback of q from its own first-return search, although the shadow starting state itself was generated by a history containing q.

For a SOURCE-WEIGHTED ensemble of FIRST q post-hit states `ν_q`, define the partial nonnegative first-return operator `R_q` mapping each tagged state (M,t,C,K(M)) to its next q post-hit state, or deleting the tag if no return before cutoff. Then exactly

    D_k(X) = ||R_q^{k−1}ν_q||_1 summed over primes q.

A non-stationary, source-averaged transfer/large-sieve estimate proving quadratic decay of these iterates would establish TAIL-2/TAIL-DOUBLE. A uniform operator-norm contraction over every possible state is NOT expected: source selection and charged post-event starts matter. The only open ingredient is an arithmetic estimate of how the ACTUAL transported source mass occupies the q-clock CRT residues of its q-deleted shadows.

This perspective isolates the key dependency: the q-shadow evolution has no q in its increments until the first return. Its state C_u may still depend on q through the original first-hit state, so naive independent CRT phases are not justified. The earlier exact two-event-active survival theorem can be used to split the final shadow q-clock competition into direct, one d=3 flip, and rare large-increment bridge cases.

## 5. Finite original-GCD numerical audit, including independent literal reference

`research/q_label_autocorrelation_audit.cpp` uses exact original even/odd full B clipped-GCD jump events and increments, carrying per-source per-prime hit multiplicities. It asserts old H,F regressions, exact original literal-vs-jump GCD for small odd M7..119, Cauchy inequality and the moment/tail identities, and reports hit-frequency tails and dyadic doubling ratios. Independent `research/independent_q_label_moment_literal.py` advances literally EVERY integer n for all original odd M at X256/512/1024/4096, without the jump clock, and matches H,F,Z including the q-hit pair count. A third independent literal-step `research/independent_prime_deleted_shadow.py` validates every **post-q first-return shadow** at X256/512/1024, including q labels that never return (original post hit count: 163/265/640 tests).

| X | H_X | F_X | Z_X | Z_X/(XB) | Z_X/(XB logB) | maximum N_q(M) | maximum over k of D_2k/D_k |
|--:|--:|--:|--:|--:|--:|--:|--:|
| 4096 |5391|4823|6751|.009695|.001888|5|.09973|
|16384|31042|25450|47482|.008549|.001467|6|.15234|
|65536|160698|136058|226332|.005094|.000781|8|.13846|
|262144|868502|703647|1371894|.003862|.000536|9|.15726|
|1048576|4031949|3248703|6476427|.002279|.000288|13|.16061|
|1999996|8564171|6757307|14661659|.001959|.000238|18|.16878|

X1999996 is NON-dyadic, for finite diagnostics only. All finite sampled doubling ratios were below1/4, but no asymptotic uniform contraction was proved; the moment normalized levels were below the sufficient `81/25088` threshold in these finite samples, consistent with every original canonical source reaching a twin-producing full sink there. At X1048576 q>=19 labels with >=1 hit=3248703; >=2 hits=521759 (16.06% of used labels), >=4 hits=57636 (1.774%), >=8 hits=2367 (.07286%), >=12 hits=40, maximum13. Global max of q-specific `k² * #{M:N_q>=k}/X` across q,k was .543634 (q19,k3) at X1m, increasing to .627747 at X1999996; DO NOT assert a uniform q-specific tail.

**Status:** The conditional algebraic lemmas and explicit constants above are derived from existing proven finite LOW17 information; the brand-new asymptotic target TAIL-2 / TAIL-DOUBLE, the scalar second-moment bound, and the shadow-source transport dispersion are UNPROVED. No Lean compilation, no twin-prime proof, no A166944 strict-record theorem.

### Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q_label_autocorrelation_audit.cpp -o /tmp/q_label_moment
/tmp/q_label_moment 4096 16384 65536 262144 1048576 1999996
python3 research/independent_q_label_moment_literal.py 256 512 1024 4096
python3 research/independent_prime_deleted_shadow.py 256 512 1024
```
