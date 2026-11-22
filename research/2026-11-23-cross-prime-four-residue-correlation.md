# A166944: cross-prime four-residue correlation and a global L1 transfer

Date: 2026-11-23 JST. Research child issue: [#3](https://github.com/tara-sooo/A166944-Lean/issues/3), parent [#1](https://github.com/tara-sooo/A166944-Lean/issues/1).

**Status.** The aggregate transfer is a paper-level consequence of the previously documented height-zero regeneration/fibre lemma; the polynomial incidence and CRT moment bounds below have elementary proofs. A dedicated exact parity-GCD C++ audit has been compiled and run at four finite dyadic scales. **No new Lean kernel proof has been compiled, no uniform dynamic correlation bound has been established, and neither twin-prime infinitude nor the original A166944 conjecture is proved.**

Starting source at pinned upstream SHA `bd180e3de0fe6e12cc3c3ea25d65a985445344eb`:

* [`2026-11-23-first-split-timing-height-and-signed-cost.md`](https://github.com/tara-sooo/A166944-Lean/blob/bd180e3de0fe6e12cc3c3ea25d65a985445344eb/research/2026-11-23-first-split-timing-height-and-signed-cost.md), §3b, exact paper-level `T1`–`T3` for post-freeze height-zero one-shot insertions;
* [`2026-11-23-squarefree-early-prime-cost-L1-residue-packing.md`](https://github.com/tara-sooo/A166944-Lean/blob/bd180e3de0fe6e12cc3c3ea25d65a985445344eb/research/2026-11-23-squarefree-early-prime-cost-L1-residue-packing.md), §1, first moment transfer and unique four-residue regeneration;
* [`2026-11-22-squarefree-sqrt-wheel-mean-reduction.md`](https://github.com/tara-sooo/A166944-Lean/blob/bd180e3de0fe6e12cc3c3ea25d65a985445344eb/research/2026-11-22-squarefree-sqrt-wheel-mean-reduction.md), §3, squarefree wheel average-growth-to-twin reduction.

## 1. A weaker, cross-prime sufficient hypothesis for one *subset* of stage costs

Let `X>=256` be even, `B=ceil(sqrt(7X))`, and `I_X={M odd: X<=M<2X}`. For each odd prime `11<=p<=B`, let `L_p` be the product of *all* odd primes strictly below `p`, and `G_{L_p}(v)` the natural-cutoff growth of its canonical-shaped squarefree wheel from odd `v`.

For `c>0` fixed, put

    U_c = 2X + floor(((c+1)B+7)/2) + 5,
    P(v) = v(v-1)(v-3)(v-5),
    T_{p,c} = sum_{v odd, X<=v<U_c, p|P(v)} G_{L_p}(v),
    E_{X,c} = sum_{11<=p<=B prime} p*T_{p,c}.

Consider *only* the set `S_p` of source starts `M in I_X` whose insertion of the fresh prime `p`:

1. first diverges **strictly after** the old `L_p` last nonunit event;
2. leaves the new trajectory at deficit `0` or `6` (height `k=0`);
3. has `G_{L_p}(M)<=c*p`;
4. completes the <=7-step bridge before the cutoff, if needed, and has **no second p-containing event** before the original cutoff.

The previously documented paper-level transfer `T3` is

    sum_{M in S_p} Delta_p(M)
       <= (p+7)*|S_p| + (1+c*p/4)*T_{p,c},

where `Delta_p(M)=G_{L_p*p}(M)-G_{L_p}(M)`. The four distinct residues `0,1,3,5 (mod p)` are equivalent to `p|P(v)` because `p>=11`.

Summing over `p`, using `|S_p|<=|I_X|=X/2` and `sum_p T_{p,c} <= E_{X,c}/11` (since `p>=11`), gives the **aggregate L1 transfer**:

    BOXED:
    sum_{11<=p<=B prime} sum_{M in S_p} Delta_p(M)
       <= (X/2)*sum_{11<=p<=B prime}(p+7)
           + (1/11+c/4)*E_{X,c}.

In particular, for `c=2` the coefficient on `E_{X,2}` is `13/22`.

Therefore the *single* aggregate hypothesis

    E_{X,c} = O_c(X*B^2/log B)

is sufficient to make the entire **post-freeze, height-zero, bounded-old-growth, one-shot** subset cost `O_c(X*B^2/log B)=O_c(X^2/log X)=o(X^2)`. The per-prime uniform AP-L1 hypothesis from the cited paper implies this aggregate estimate, but not conversely: exceptional primes may have much larger individual AP cost.

This is **not** a full prime-stage proof. The post-freeze `k>=1` branches (especially `k=1`), second and later p-events, and the pre-freeze signed cost require separate work. The new aggregate hypothesis remains OPEN.

## 2. Unconditional arithmetic sparsity of the four-residue incidence

For odd `v`, define the arithmetic weight

    w_B(v) = sum_{11<=p<=B prime, p|P(v)} p.

**Lemma A (pointwise).** If `X<=v<3X` and `B^2>=7X`, then `w_B(v)<=13B`.

Proof. Each positive factor `v`, `v-1`, `v-3`, `v-5` is strictly below `3X<B^2`. One such factor can have at most **three distinct** prime divisors `p>sqrt B`, because four such divisors have product `>B^2`. Across four factors, at most 12 of these large prime divisors contribute, each at most `B`, hence at most `12B` weight. Every remaining divisor satisfies `p<=sqrt B`; its total weight is at most `sum_{1<=j<=floor sqrt B} j <=B`. Add the two bounds. For the chosen `U_2` and `X>=256`, `U_2<3X`.

**Lemma B (mass and CRT second moment).** Let `V` be an interval of `N` consecutive odd integers, `Q={p prime:11<=p<=B}`, `J=#Q`, `S1=sum_{p in Q}p`, and `S2=sum_{p in Q}p^2`. Then

    sum_{v in V} w_B(v) <= 4*N*J + 4*S1,

and

    BOXED:
    sum_{v in V} w_B(v)^2
       <= 4*N*S1 + 4*S2 + 16*N*J*(J-1) + 16*(S1^2-S2).

Proof. For each p, the `N` consecutive odd integers run through residues modulo p, so the number in the four designated residue classes is at most `4*(N/p+1)`. For distinct p,q the Chinese remainder theorem gives exactly 16 compatible residue classes modulo pq, each appearing at most `N/(pq)+1` times. Expand `w^2` into diagonal and off-diagonal prime pairs and insert these exact counting bounds. Standard prime-counting estimates then give `sum_V w_B(v)^2 = O(X*B^2/log B)` when `N=Theta(X)` and `B=Theta(sqrt X)`.

Both statements are pure arithmetic and do not rely on a randomness assumption about the recurrence. Neither one alone controls `E_{X,c}`: the weights `G_{L_p}(v)` depend on `p` and could correlate strongly with the allowed residues.

## 3. Exact finite GCD audit of the dynamic correlation

Reproducible scanner: [`cross_prime_four_residue_audit.cpp`](cross_prime_four_residue_audit.cpp). It uses the **original parity-specific gcd event clock** capped by distinct primes `<=previous_prime`, and the natural cutoff `K(v)=floor((7v-1)/4)`. It contains a separate literal step-by-step gcd implementation checked against the event-jump implementation for all odd `7<=M<=119` and prime caps `1,3,5,7,11,13`, plus exact regression assertions at four X. An additional direct step-by-step parity-GCD check of the p-refire recharge inequality verifies 2,036 consecutive-p event gaps in the finite range `7<=M<=999`, across prime caps `5,7,11,17,31,41`; its smallest inequality slack is zero.

The following results were obtained by compiling and running the listed source locally under C++17 (not by formal Lean reduction). `E=E_{X,2}` uses `U=2X+floor((3B+7)/2)+5`. The comparison `E_ref=4*sum_{11<=p<=B} sum_{v in V} G_{L_p}(v)` is the natural **unconditioned** four-residue reference: it is not a statement of independence.

| X | B | #p | exact E | E/(X B^2/log B) | E/E_ref |
|---:|---:|---:|---:|---:|---:|
| 4,096 | 170 | 35 | 36,344,568 | 1.576847490 | 0.960924631 |
| 16,384 | 339 | 64 | 485,635,362 | 1.502662524 | 1.007836851 |
| 65,536 | 678 | 119 | 5,672,417,264 | 1.227494755 | 0.983213295 |
| 262,144 | 1,355 | 213 | 69,630,701,976 | 1.043304992 | not computed in full-reference mode |

For 4,096 and 16,384 the exact weighted-incidence second moments were 63,145,432 and 847,926,453 respectively, strictly below the explicit CRT bounds 197,202,872 and 2,518,641,264. At X=65,536 the measured second moment was 11,949,041,322 versus bound 35,733,764,476; X=262,144 was 158,456,197,474 versus bound 449,099,528,100. The regression tool also checks the large individual-incidence weights and the deterministic envelope inequality `E<=sum_v w_B(v) max_{p|P(v)}G_{L_p}(v)`.

Commands:

    g++ -std=c++17 -O3 research/cross_prime_four_residue_audit.cpp -o cross_prime_audit
    ./cross_prime_audit 4096
    ./cross_prime_audit 16384
    ./cross_prime_audit 65536
    ./cross_prime_audit 262144 fast

**Empirical interpretation:** E is near its unconditioned reference in the first three scales, and its normalized size falls across the four tested scales. This suggests an aggregate dispersion approach but is not an infinite-scale upper bound, and does not demonstrate cancellation for every dyadic interval.

## 4. Exact p-refire recharge constraint (paper level, separate from E)

For a genuine parity-GCD or squarefree-clipped trajectory with even `D` and odd increments `d(n)`, fix `p>=5` dividing at least two increments. At a p-containing event, just before the update,

    n even: D_before = 1 (mod p), D_after = 0 (mod p);
    n odd:  D_before = -1 (mod p), D_after = -2 (mod p).

The next p-containing event must again have `D_before = +/-1 (mod p)`. All intervening excess increments `d-1` are *even* and none contain p. Thus the sum `T` of intervening excess satisfies

    BOXED: T >= p-1 after an even previous p-event;
           T >= p+1 after an odd previous p-event.

If `N_p` p-containing events occur, the inter-event intervals are disjoint **for this fixed p**, and therefore

    (N_p-1)*(p-1) <= sum_{n: p does not divide d(n)}(d(n)-1).

The sum is over the specified finite trajectory. This is arithmetic, not a Lean theorem. It may help fund later p-refires via non-p growth, but different p reuse intervals can overlap and the right-hand side is from the **new** trajectory, not directly the old-wheel `G_{L_p}`. Those are separate remaining charging problems; this bound must not be treated as having closed them.

## 5. Concrete remaining proof tasks

1. Establish a **dynamic dispersion/weighted-correlation estimate** for `E_{X,c}`, or find a counterexample scale. The time-varying prefix weight `G_{L_p}(v)` is `p`-dependent; ordinary large-sieve estimates for a *single fixed coefficient sequence* do not immediately apply.
2. Formulate a p-refire charge in old-wheel (or already funded new-wheel) units, without double-counting growth across different primes.
3. Handle post-freeze heights `k>=1`, where there is no universal <=7-step canonical regeneration; use the existing high-height frequency bound only as a frequency estimate, not as a tail-cost bound.
4. Control pre-freeze signed insertion cost globally and combine the entire prime-stage ladder. Only then would the squarefree-mean-to-twin reduction apply.
5. Formalize the elementary Lemmas A/B, aggregate transfer, and refire parity-recharge in the pinned Lean environment as appropriate. **No Lean kernel results were generated in this checkpoint.**
