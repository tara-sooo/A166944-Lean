# A166944 — growth-adaptive wheel insertion: safe split, redundant prime powers, and the one-shot tail kernel

2026-11-22 JST. **PAPER proofs plus independently executed exact integer checks. No proof of the dyadic mean bound, Cap B, or twin-prime infinitude. No new Lean compilation.**

Builds on [wheel-insertion signed growth review](2026-11-22-wheel-insertion-signed-growth-review.md), [first-hit / BAD growth bound](2026-11-22-first-hit-growth-BAD-linear-lower-and-dyadic-average.md) and the original attached \`mission_scan/twin_proof/cap_bound/wheel_insertion_idea.md\` and \`refire_independent_audit.md\`. The complete relative-time arithmetic of the original parity gcd is essential; the wheel can contain any odd prime powers.

## 1. NEW growth-adaptive safe-split theorem

Fix odd canonical-shaped M≥7 and natural cutoff K=floor((7M−1)/4); use the same cutoff for two wheel paths. Let L odd≥1. The L-restricted increment at index n is the gcd of L with the original parity-specific two gcd operands computed from its own current horizon. Put s=M+2, T=K−s, and denote the old L growth by

    h=G_L(M)=sum_{1≤t≤T}(e_L(t)−1)≥0.

Insert an odd prime p (possibly already dividing L), obtaining the Lp wheel. Let v=v_p(L), q=p^(v+1), so the extra p-adic valuation is first visible at the prime power q. Write Δ=G_(Lp)(M)−G_L(M).

**Theorem A, exact (PAPER):** for ANY cutoff T, if

    BOXED: q>6h+7,                                       (1)

then

    (i) if v=0, Δ≥0, and either Δ=0 or Δ≥p−1;
    (ii) if v≥1, Δ=0: the two entire trajectories up to T are identical.

Consequently, a negative insertion contribution requires

    BOXED: Δ<0  ==>  q≤6G_L(M)+7.                       (2)

And an existing-prime higher-power insertion has ANY nonzero effect only when q≤6G_L+7. This is a *growth-based* rather than *wheel-size-based* criterion. It applies abundantly even when q≤2L and p≤12L+7, the dense region to which the earlier L-barrier and far-prime theory did not apply.

**Proof:** let g_(t−1) be old cumulative growth before relative time t. With κ=2,β=7 for odd t and κ=0,β=1 for even t, both original gcd operands are equivalent to

    b_t=M+t+κ;       f_t=2t+β−g_(t−1).

At a shared state, the wheel increment changes on inserting p iff q divides BOTH b_t and f_t, in which case e_new=p e_old. Every completed interevent gap g_i of the old wheel obeys g_i≤2e_i≤3(e_i−1) by the exact parity first-hit clock. Hence the last OLD nonunit event t_last, or 0 if no such event, satisfies

    t_last ≤ 3h.                                         (3)

For each t≤t_last, the odd nonzero integer f_t obeys

    −h < f_t ≤ 2t+7 ≤6h+7.

So when q>6h+7 it cannot divide f_t during any old event-active prefix, indeed during ANY t≤t_last. Thus the two wheels cannot split before the last old event. After t_last the old wheel increments are all 1 through T. If p|L, any q-divisible gcd has old increment divisible by p, so cannot split AFTER the old events; the entire paths coincide (ii). If p∤L, a split after t_last has old e=1 and new e=p. From this point forward old growth stays at h whereas every new growth increment is nonnegative, so Δ≥p−1 (i). If no split Δ=0. QED.

For truly attained canonical twin-prime M≡1 mod3 the previous sharper t_last≤(8/3)h yields a lower numerical threshold q>(16/3)h+7, but (1) works for EVERY artificial odd start.

**Important:** the threshold (1) is a sufficient *safe/zero* test, NOT a useful uniform upper bound on POSITIVE contributions. Once a fresh p fires, it can re-activate many old-prime clocks; the new path's growth may exceed p−1.

## 2. NEW conditional full-lift splitting theorem with threshold h, not L

Suppose p∤L and fix an odd residue class a mod2L. Because the L-wheel trajectory is identical for all M≡a mod2L in relative coordinates, let h_a be its FULL STABILIZED growth and t_a its last nonunit event. The old wheel always eventually freezes, with t_a≤3h_a<6L. Assume

    p>6h_a+7.                                          (4)

For every one of the p lifts M≡a (mod2L) modulo2Lp, first divergence cannot occur before the old wheel freezes. After freeze the old horizon is

    C_*(M)=2M−2+h_a.

The new prime p can first act iff p|(C_*(M)−1)(C_*(M)+1), since any p-factor clock fires in its parity-specific residue class within 2p indices. As 2 is invertible modulo p and p∤L, the two values C_*≡±1 modp define EXACTLY TWO distinct lifts among p. If a common cutoff is sufficiently far after all old events and at least 2p further indices (e.g. T≥t_a+2p), exactly TWO lifts diverge; for shorter common cutoffs AT MOST TWO. This holds even for p<<L. A M-dependent natural cutoff cannot simply inherit complete-lift frequencies because the interval may not contain full periods.

For inserted prime powers p^k,k≥2 satisfying q>6h_a+7, there are NO divergent lifts.

**Explicit genuinely dense example:** L=315, p=101, a=1 mod630. Here h_a=0 and 101<12·315+7. Among all 101 lifts M=6301+630k (k=0..100) using their actual natural cutoffs, exactly two split:

    M=25201,  old G315=0, new G31815=108,
      new events (25250,101),(25254,9).

    M=38431,  old G315=0, new G31815=108,
      new events (38483,101),(38484,9).

The 99 other lifts show Δ=0. The p-first-hit costs100 and the subsequent OLD-prime tail costs8. These starts are not asserted original-orbit attained or twin-prime inputs.

The exact two-lift law is derived from the OLD path and CRT; no stochastic independence is assumed.

## 3. NEW self-normalized one-shot renewal criterion

In the situation of §2 (p fresh, old wheel frozen), let τ_E,τ_O be the two first p-hit times. After the p-hit the new horizon moves by p−1. For each hit orientation, define B_E,B_O as the TOTAL additional growth in the hypothetical trajectory using ONLY OLD wheel L, starting just AFTER that p-hit at the increased horizon.

The exact first-hit return table for a prime p≥5 says two p-events require at least p−1 intervening even horizon growth. Therefore if

    BOXED: B_E<p−1 and B_O<p−1,                    (5)

neither lift can have a second p-event. The actual Lp trajectory after the first p-hit is then identical to that L-only tail, so with a sufficiently late common cutoff (the two L tails completed) the mean of the signed insertion difference across ALL p lifts is EXACTLY

    BOXED: (1/p)*Σ_(lifts) Δ
         = 2 +(B_E+B_O−2)/p.                          (6)

This extends the former "far p>12L+7" mean formula to **p much smaller than L**, provided the *observed old growth* h_a and the two *one-shot renewal tails* B± are small compared with p. Neither full-lift averaging nor the tail criterion automatically holds at a natural variable cutoff, so boundary-error and incomplete-period control remain indispensable.

**Exact zero-tail residue class, even when p<<L:** let R=rad(L), the product of the distinct old primes. If p≥5 is fresh and satisfies p≡1 (mod R), then after the p-event the new horizon C'=C+p−1 satisfies C'≡C (mod every old prime), so the L-wheel remains frozen. Moreover modulo p the active neighbor becomes inert (C'≡0 or −2, neither ±1 for p≥5). There can be NO later nonunit event at all. Thus each divergent lift has EXACT signed gain Δ=p−1, without any conditional tail estimate. Concrete dense case L315, R105, p211<2L: for a=1 mod630, the two divergent lifts are M22051 and110881, each with Δ=210, while the other 209 lifts have Δ=0. This proves a genuine one-step p-insertion formula despite p being far below L. Its rarity when rad(L)>>X limits direct dyadic application.

This suggests a precise two-stage bootstrap:
- control the distribution/mean of old terminal growth h_a to classify most prime insertions as safe, with higher prime powers inert;
- prove a signed/positive MEAN bound for the two one-shot L-tail renewal costs B±, and separately control exceptional q≤6h+7 and q refirings when B≥p−1.

A potentially useful CRT formulation of the first-stage event is

    p | 2M−3+h_L(M)   OR   p | 2M−1+h_L(M).        (7)

The phase h_L(M) depends adaptively on M. Even though fixing M mod2L gives exactly two lifts, in real dyadic windows the immense L generally exceeds the M interval, so the complete p-lift sample DOES NOT appear. A rigorous moving-residue sieve/discrepancy estimate for (7), *together with* a tail-cost estimate, is still the core missing global theorem.

## 4. Reproducible exact tests

An independent Python direct residue-clock audit checked (4) across 7,340 (L,a,p) triples for L=15,21,35,45,63,105,135,315 and p=43,53,67,79,101,127,149,181,211,257. Of those, 5,988 satisfied (4) and **all** had exactly 2 distinct first-split residues; 5,958 satisfied the new threshold while violating the old p>12L+7. Zero contradictions.

The independent SPF event-jump complete prime-power insertion ladder [adaptive_wheel_insertion_audit.cpp](adaptive_wheel_insertion_audit.cpp) directly checked (1) across ALL pairs (M,added q) in each dyadic test interval:

    X          #M    #prime-power q     SAFE q>6G_L+7   safe fresh Δ>0   safe higher powers Δ=0   unsafe negative Δ<0
    256        128         188                  11,735              16                     838                    15
    512        256         329                  60,918              28                   2,912                    53
    1024       512         592                 248,304              67                   9,519                    40
    2048      1024        1065                 935,126             184                  25,891                   113
    4096      2048        1947               3,510,359             455                  66,110                   352

No safe-pair violations. At X4096 there are 3,987,456 pairs total, so about 88% of individual insertion comparisons are in the *safe* regime, notwithstanding L being extremely large. The full signed positive/negative sums for X=256,512,1024,2048,4096 are respectively:

    X          sum positive    sum negative abs    actual net G      ΣM/4 target
    256            12658              372             12286             12288
    512            25622             6342             19280             49152
    1024           50044             2340             47704            196608
    2048          159740            13134            146606            786432
    4096          549928            52092            497836           3145728

These are finite checks, NOT a bound on all X. At X≥512 positive-only sums already fall below the target in these particular ranges, but no asymptotic positivity-only cost bound has been shown.

## 5. Assessment and open bottleneck

The earlier big-q>2L sign barrier is mathematically correct but nearly vacuous along the *ascending* prime-power ladder (q=3 is the first and exceptional large-q step; L then grows exponentially). The growth-adaptive criterion q>6h+7 provides genuinely many safe comparisons in the actual ascending ladder, even when q<<L.

To finish the dyadic-average route, an actual theorem must upper-bound cumulative POSITIVE costs, e.g. a coupled one-shot tail bound or multi-q signed amortization, AND handle incomplete CRT lifts for M∈[X,2X). The facts that most comparisons are safe and that there are two possible split residues per full lift do not, on their own, bound the aggregate cost; the two exceptional residues can concentrate on the sampled interval or have expensive tails.

The proposed two-stage bootstrap based on old growth h and perturbed tail B is concrete and falsifiable; its uniform large-X bound is unproved. This does not prove original A166944 Cap B or twin-prime infinitude.
