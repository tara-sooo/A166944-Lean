# A166944 squarefree wheel: two-prime cascade curvature, order stability, and initial-catalyst compression

Date: 2026-11-23 JST. Assigned research [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [Issue #1](https://github.com/tara-sooo/A166944-Lean/issues/1), branch `research/issue-4-terminal-survivor-positive-budget`. Continues [dyadic-band randomization and shared-factor response](2026-11-23-random-prime-order-and-shared-factor-response.md). Results in §§1–3 and §5 are finite algebraic proofs **on paper only**, not Lean-kernel-checks. Tables are exact finite C++17 audits, with independent literal-step GCD checks of the two strongest cascade witnesses. Uniform control of the twin-prime certificate, positive stage budget, and response second moment is **still OPEN**.

## 1. Exact adjacent-prime swap formula, with sharp local Lipschitz bound (PAPER)

For even `X>=256`, `B=ceil(sqrt(7X))`, and odd canonical start `M` in `[X,2X)`, let `G_S(M)` denote the terminal growth of the **original parity-specific squarefree clipped GCD** at cutoff `K=floor((7M-1)/4)`, with the set `S` of allowed odd primes. Arbitrary subsets `S` are permitted; no primorial ordering is assumed. For distinct uninserted primes `p,q<=B`, abbreviate:

    a = G_(S+p)(M) - G_S(M),
    b = G_(S+q)(M) - G_S(M),
    h = G_(S+p+q)(M) - G_(S+p)(M) - G_(S+q)(M) + G_S(M).

Here `h` is a **mixed second difference** (interaction curvature). In the order `p then q`, the two stage increments are exactly `(a,b+h)`. In the order `q then p`, they are `(b,a+h)`. The positive-variation totals are

    V_pq = [a]_+ + [b+h]_+,
    V_qp = [b]_+ + [a+h]_+.

Let `f_h(t)=[t+h]_+-[t]_+`; this is 1-Lipschitz in t and has its entire range in an interval of length `|h|` (regardless of sign of h). Therefore

    V_pq - V_qp = f_h(b) - f_h(a),

    BOXED (S1):  |V_pq - V_qp| <= min(|h|, |a-b|).

In particular, if `a,b,a+h,b+h` are all nonnegative, `V_pq=V_qp` even when `h` is huge. A negative marginal at one of the four edges is necessary for the ordering to affect the positive budget. Summing over M yields the same bound on the difference of whole dyadic stage-pair costs by the triangle inequality. By successively swapping adjacent primes, any two insertion orders can be compared via a sum of these **prefix-dependent** swap bounds; the prefix S necessarily changes after each exchange.

The bound is local order *sensitivity*, not a bound on the absolute terminal growth, direct p-injection, or old-prime response energy. By itself it cannot close the twin-prime problem because the common full-wheel growth is invariant under all orders.

## 2. Old-clock activation and a one-active exchange rule (PAPER)

Write `A_p(S,M)=1` if the trajectory driven by S, starting at `D(M+2)=2M-2`, ever has a fresh p-clock opportunity before K, i.e. at some n its parity raw gcd is divisible by p. The old-only first-clock argument already proved in the predecessor note works for arbitrary S: `A_p=0` iff adding p to S never changes the entire original recurrence trajectory, not merely its terminal growth.

**Zero-interaction support.** If `A_p=A_q=0`, the trajectory of `S+p+q` must equal that of S at every step: at their first hypothetical divergence a p- or q-containing increment would have been available along the unchanged S trajectory, contradiction. Hence

    BOXED (S2): h!=0  ==>  A_p(S,M)=1 or A_q(S,M)=1.

This gives the deterministic (generally loose) support count

    sum_(p<q in T) 1_{h_(S;p,q)(M)!=0}
       <= (|T|-1) * sum_(p in T) A_p(S,M)

for any set T of uninserted primes, with no independence assertion.

**One-active orientation.** If `A_q=0`, then b=0; S1 becomes the exact formula

    V_pq - V_qp = [a]_+ + [h]_+ - [a+h]_+ >= 0.

    BOXED (S3): a currently inactive prime q placed BEFORE p can never
    increase the *two-stage* positive variation for this particular M and S.

If a,h have the same sign (including zero) the difference vanishes; when their signs oppose, the difference is `min(|a|,|h|)`. Conversely if `A_p=0` and `A_q=1` the preferred orientation is p first. This is a per-start conditional exchange: different M can prefer different orders, and q may become active *after* insertion of p. It does not imply the existence of one globally optimal ordering.

The second condition in S2 cannot be strengthened to "both p and q were already active": adding one prime may induce the other prime's activation and a large second difference.

## 3. Explicit triggered-prime avalanche and failure of first-kick Lipschitz (FINITE COUNTEREXAMPLES)

At `X=4096`, choose the old squarefree set `S={odd primes <32}`, start `M=4727`, and p=37, q=41. Independent **literal one-step parity GCD** yields

    G_S=58, G_(S+p)=100, G_(S+q)=58, G_(S+p+q)=166.
    a=42, b=0, h=66.

The first p-hit is `(n,d)=(4810,37)`, so its first kick is 36. The old path has NO q-hit, but after adding p the enlarged p+q path has a q-hit `(4881,41)`. Thus `|h|=66 > (first-p kick)+(first-q kick)=36`. Both two-step additions nevertheless have positive variation 108: `V_pq=42+66=108`, `V_qp=0+108=108`. Large curvature need not cause any order sensitivity.

At `X=16384`, take `S={odd primes <128}`, start `M=19583`, p=157, q=173. Independent literal-step values are

    G_S=244, G_(S+p)=454, G_(S+q)=244, G_(S+p+q)=2446.
    a=210, b=0, h=1992.

The initial p-hit `(19782,157)` gives kick 156. q does not hit in S or S+q, but in S+p+q there is a q-hit `(20068,173)` followed by a SECOND p-hit `(20724,157)`. Thus `|h|/(first kick sum) = 1992/156 = 12.76923...`, yet `V_pq=V_qp=2202`, again zero order sensitivity. The nonlinearity includes a q-triggered p-refire; a first-kick-only response estimate is false.

These two direct-step witnesses are embedded as C++ regressions independent of the event-jump scan. They falsify `|h| <= F_(S,p)+F_(S,q)` for the canonical original parity-specific recurrence, not merely for an artificial state model.

## 4. Exhaustive pair curvature audit (COMPUTED, finite)

File: [`band_swap_curvature_audit.cpp`](band_swap_curvature_audit.cpp). For an even X and a dyadic band `[Q,2Q)`, set `S` to ALL primes `<Q` (rows marked `band-start`). For each unordered pair p,q of primes in the band and **each** odd M in `[X,2X)`, compute all four squarefree-wheel terminal growth values. Check S1–S3, both old-only first clocks, and the positive pair-variation identity; additionally run the literal GCD checks of the two witnesses above. A `half-preloaded` row starts instead with all primes `<Q` AND every other band prime in S; only the remaining band primes are compared.

| X | S | band Q | candidate prime pairs | total (p,q,M) | h!=0 | exactly 1 old-active | both old-active | swap-sensitive | sum |h| | sum |Vpq-Vqp| |
|---:|:--|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | band-start | 32 | 21 | 43,008 | 459 | 346 | 113 | 64 | 40,506 | 2,574 |
| 8,192 | band-start | 64 | 78 | 319,488 | 864 | 699 | 165 | 130 | 189,150 | 35,148 |
| 16,384 | band-start | 128 | 253 | 2,072,576 | 3,073 | 1,542 | 1,531 | 908 | 1,310,442 | 203,982 |
| 16,384 | half-preloaded | 128 | 55 | 450,560 | 774 | 329 | 445 | 368 | 676,722 | 251,238 |

Here "old-active" is a genuine OLD clock opportunity, **not** simply nonzero terminal Δ. The support theorem S2 held with **zero violations**. For X16384 at band-start, the one-active interactions account for `sum h² = 578,330,028`, which is 62.4% of the total curvature energy `927,134,892`, but their contribution to order-swap absolute variation is only `15,498`, or 7.6% of `203,982`. The BOTH-active interactions have the other `188,484` swap variation. Hence controlling a raw second-difference square moment is a much stronger and different task than controlling the order effect; a variance argument must retain the positive-part/sign structure.

When half the band has already been preloaded, the swap sensitivity is materially larger (`251,238/676,722 = 37.1%` of the curvature L1 versus `15.6%` at band-start) and the old-active classification changes. Bounds proved only at the *beginning* of each dyadic band need not persist throughout a random permutation.

An additional falsification check compares `|h|` with the **sum of the initial first kicks** on the S trajectory. It fails in `297` / `685` / `1,743` pair/start comparisons for the first three band-start rows, respectively (and `491` with half-preloaded band at X16384). The largest observed `|h|/(first kick sum)` was 11.667 / 8.854 / 12.769 / 16.538, respectively. There is no proved uniform upper bound of that type.

## 5. An independent exact compression: preload all initially inactive primes (PAPER)

For each individual odd M, write `C0=2M-2`, and let

    T(M) = {odd prime p<=B : p divides (C0-1)(C0+1)}
         = {odd prime p<=B : p | (2M-3)(2M-1)}.

Put `S0(M)={odd primes <=B}\T(M)`. Because the initial state has `gcd(L_(S0),C0-1)=gcd(L_(S0),C0+1)=1`, the `S0`-wheel stays at C0 forever: no nonunit event is possible at any index. In particular,

    BOXED (S4): G_(S0(M))(M)=0.

Consequently one may preload **all** those inactive primes at zero canonical growth cost, then insert only the primes `T(M)` in any order. For a chosen ordering `r_1,...,r_k` of T(M), telescoping gives exactly

    G_full(M) = sum_(i=1)^k [G_(S0 + {r_1,...,r_i})(M)
                               - G_(S0 + {r_1,...,r_(i-1)})(M)].

The number of required insertions is not pi(B): it is

    k=|T(M)| <= log((C0-1)(C0+1))/log 3 = O(log X),

and the same prime-factor arithmetic as in the prior first-hit portfolio note gives

    BOXED (S5): sum_(p in T(M)) p <= 7B.

For X>=256, the cutoff horizon is longer than 2B, so every p in T(M) really has an initial clock opportunity with the empty wheel. If T(M) is empty, C0±1 are already primes (both < B²), which is exactly a *finite twin-prime pair* at the unmodified seed, not a proof of an unbounded family. The **choice of S0 and ordering depends on M**; this is not a single common global permutation and cannot be conflated with the ascending prime-stage P_X.

### Finite complete audit of seed-specific preloading

[`seed_catalyst_preload_audit.cpp`](seed_catalyst_preload_audit.cpp) checks S4, S5, per-source seed-only signed telescoping, original full-wheel recomputation, independent small literal GCD, and historical W_full regressions, for every M in the following four dyadic windows. Seed primes are then added in ascending order.

| X | # starts | pi(B) (total possible primes) | average seed count k | maximum k | final sum G_full | seed-only positive variation | seed-only negative variation |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 512 | 22 | 2.566 | 6 | 39,940 | 44,044 | 4,104 |
| 4,096 | 2,048 | 38 | 2.823 | 7 | 399,142 | 452,722 | 53,580 |
| 8,192 | 4,096 | 51 | 2.952 | 8 | 1,084,898 | 1,291,454 | 206,556 |
| 16,384 | 8,192 | 67 | 3.063 | 8 | 2,915,326 | 3,422,986 | 507,660 |

Example M19583, X16384: initial seed set `{3,5,7}`, every other p<=339 is preloaded at zero cost; growth at seed insertions is `0 -> 310 -> 208 -> 1684`, matching the full 67-prime wheel. The nonmonotone middle step is retained (the seed-only positive variation is 1786, while full growth is 1684). M4727, X4096: seed `{3,13,23,137}` gives growth `0 -> 10 -> 178 -> 178 -> 178`, full growth178.

**Interpretation:** for each source M, only a few *initial catalyst primes* need to be explicitly inserted; all others can be preloaded. Their later actions may still cause huge, nonlinear avalanches. This compression is exact, but proving a uniform mean bound on the resulting few nonzero catalyst-stage changes is a new OPEN dynamical problem. It does not bypass the original twin-prime difficulty.

## 6. What this does and does not advance

- **Proved on paper:** exact sharp swap Lipschitz S1; old-activation support S2; inactive-before-active orientation S3; zero-cost per-source catalyst preloading and arithmetic seed bounds S4/S5. These identities hold at the original parity-specific clipped recurrence and arbitrary squarefree sets; all finite regressions pass.
- **Disproved finite candidates:** `|mixed two-prime response| <= first-p kick + first-q kick`, and the idea that large mixed curvature must cause large order sensitivity. An active p can induce a previously inactive q, then a p-refire.
- **Still OPEN:** bounding the total *direct prime injection* `J_X=o(XB²)` and old-prime terminal response energy `Q_X=O(XB³)` in the ascending or randomized-stage model; bounding the seed-only terminal positive budget `o(X²)`; proving twin-prime infinitude and the original stronger OEIS A166944 conjecture. The swap bound is only a comparison between orders, not an absolute growth estimate.

The most diagnostic next test is a **conditional** band experiment: for partial sets S already containing some band primes, measure the signed margins `a,b,a+h,b+h`, induced q-after-p first clocks, and a curvature statistic **conditioned on signs**. For a proof, a bound on final signed old-wheel response, not raw timewise or pairwise absolute curvature, is still needed. Another possible approach is to estimate catalyst-stage growth with M-dependent preloading, where the number of stages per source is logarithmic instead of pi(B); this is a distinct open reduction and would require careful correlated-state analysis.

## 7. Reproduction

```bash
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/band_swap_curvature_audit.cpp -o /tmp/band_swap_curvature_audit
/tmp/band_swap_curvature_audit 4096 32 0
/tmp/band_swap_curvature_audit 8192 64 0
/tmp/band_swap_curvature_audit 16384 128 0
/tmp/band_swap_curvature_audit 16384 128 1

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/seed_catalyst_preload_audit.cpp -o /tmp/seed_catalyst_preload_audit
for X in 1024 4096 8192 16384; do /tmp/seed_catalyst_preload_audit "$X"; done
```

A literal stepwise Python cross-check of the two strong witnesses was also performed separately, with `G_S,G_S+p,G_S+q,G_S+p+q` matching the embedded C++ stepwise regressions. The code paths contain no probabilistic sampler: the listed experiments enumerate all indicated prime pairs and all canonical starts. No Lean-kernel compilation occurred; the main branch remains unchanged. No public novelty claim is made.
