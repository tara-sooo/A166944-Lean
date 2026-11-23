# A166944: twin-prime-first weighted first/return ledger and exact signed prime-insertion transfer

Date: 2026-11-23 JST. Scope: cross-reference Issue #3 (squarefree signed prime insertion) and Issue #4 (same-source prime-label recurrence). These are elementary paper deductions plus finite exact tests, **not Lean-kernel-certified**. The original conjecture and twin-prime infinitude remain **OPEN**.

Sources checked: `research/2026-11-22-squarefree-sqrt-wheel-mean-reduction.md` and `research/2026-11-23-first-split-timing-height-and-signed-cost.md` on Issue #3, `research/2026-11-23-single-source-q-label-second-moment-and-shadow-renewal.md` on Issue #4. All use the **same** parity-specific squarefree clipped-GCD wheel when the final prime cutoff is identical; the per-prime *intermediate* paths are different from the final all-prime path.

## 1. Exact common definitions

Take dyadic X divisible by four, `I_X={odd M:X<=M<2X}`, `B=ceil(sqrt(7X))`, `s=M+2`, `K=floor((7M-1)/4)`, and initial even horizon `C(s)=2M-2`. Given a fixed set of odd primes S, the parity-GCD raw increment at n is `gcd(n,C(n-1)-1)` for even n, `gcd(n-2,C(n-1)+1)` for odd n. Its clipped squarefree increment is `d_S(n)=product of distinct p in S dividing the raw increment`; the horizon update is `C(n)=C(n-1)+d_S(n)-1`. Write `G_S(M)=C(K)-(2M-2)`.

At the FINAL wheel S=all odd primes <=B, for each p define `N_p(M)=# {n in (s,K]:p|d_S(n)}`, `F_p(M)=1_{N_p(M)>=1}`, `R_p(M)=N_p(M)-F_p(M)`. Let

- `W_X = sum_M G_S(M)`;
- `First_X = sum_(M,p<=B) (p-1) F_p(M)`;
- `Repeat_X = sum_(M,p<=B) (p-1) R_p(M)`;
- `Extra_X = sum_(M,n:s<n<=K) e(d_S(n))`, where `e(d)=d-1-sum_(p|d)(p-1)`.

Each `d` is odd and squarefree. Expanding `prod_(p|d)(1+(p-1))` gives the exact nonnegative simultaneous-prime surplus

`e(d)=sum_(T subset of prime factors of d, |T|>=2) product_(p in T)(p-1) >=0`.

Consequently there is an **EXACT PAPER IDENTITY**:

`W_X = First_X + Repeat_X + Extra_X`.   (L1)

This is distinct from Issue #4's unweighted high-prime label moment `Z_X=sum_(M,p>=19) N_p(M)^2`.

## 2. First-hit growth is automatically negligible at the twin-prime scale

There are X/2 starting M. A label (M,p) can be used for the first time at most once, irrespective of source mergers, adaptive clock dependence, and repeated hits. Hence

`0 <= First_X <= (X/2) sum_(odd primes p<=B)(p-1) = O(X*B^2/log B) = O(X^2/log X) = o(X^2)`.

The prime-count estimate is the ordinary prime number theorem / Chebyshev upper bound; it does not invoke a twin-prime estimate. As `Repeat_X` and `Extra_X` are both nonnegative, (L1) yields:

`W_X=o(X^2) iff Repeat_X+Extra_X=o(X^2)`.  (L2)

Combining (L1) with Issue #3's terminal squarefree-wheel twin certificate and the exact horizon sum `sum_M(K-s)=9X^2/16-5X/4` yields the **NEW WEAKER FIXED-CONSTANT SUFFICIENT CONDITION**:

`liminf_(dyadic X -> infinity) (Repeat_X+Extra_X)/X^2 < 3/16`  ==> infinitely many twin primes.   (L3)

For every sufficiently large dyadic interval attaining the strict inequality, one squarefree-wheel endpoint has `C(K)-1` and `C(K)+1` both prime. Their sizes grow with X. (L3) is an OPEN arithmetic input, not a proof of twin-prime infinitude.

Two genuinely different obstructions therefore remain in this route: **weighted same-prime returns**, and **simultaneous multi-prime surplus**. The second cannot be dropped as a deterministic consequence of the first: the exact source `M=49`, cutoff `B=31` has nonunit events `(n,d)=(60,5),(66,33),(79,7)`. Every prime factor is first-used, so `Repeat(M)=0`, yet the `3*11` event contributes `e(33)=20`.

### 2a. New pairwise simultaneous-clock upper bound

For each squarefree d with prime-factor set S, define the weighted pair charge

`pair(d)=sum_(p<q both divide d) (p-1)(q-1) * d/(pq)`.

**Exact elementary inequality:** `0<=e(d)<=pair(d)` for every squarefree d, with equality when d has at most two distinct prime factors. To prove it, expand `d=prod_(p in S)(1+(p-1))`. Each monomial involving r>=2 distinct `(p-1)` factors occurs **once** in e(d), and exactly `binom(r,2)` times in pair(d), because the chosen pair may be any two factors in that monomial. This is a deterministic factor-expansion inequality with no independence assumption.

Set `Pair_X=sum_(M,n)pair(d_S(n))`, so `Extra_X<=Pair_X`. Consequently the following stronger but potentially more accessible **OPEN sufficient estimate** also implies infinitely many twins:

`liminf_(dyadic X) (Repeat_X+Pair_X)/X^2 < 3/16`. (L4)

Unlike the exact higher-order surplus, Pair_X is an arithmetic weighted **two-prime same-event coincidence** statistic, so it gives a concrete target for cross-prime collision methods. It is *not* the within-one-prime across-time second moment Z from Issue #4. Numerical ratio Pair_X/Extra_X is exactly 1 for X<=4096 (no event with >=3 factors), 342248/331016=1.034 at X16384, and 9898872/9434664=1.049 at X262144. These are finite observations only.

### 2b. Alternative first-use-fraction threshold

Assume W_X>0 (automatic for all sufficiently large X if the twin-prime conclusion fails). By the prime number theorem,

`First_X <= (7/4+o(1)) * X^2/log B`.

If there were no twin-producing endpoints for any sufficiently large dyadic X, the terminal certificate would force `W_X >= (3/16-o(1))X^2`, and hence

`(First_X/W_X)*log B <= 28/3+o(1)`.

Therefore the following **OPEN** condition is independently sufficient for infinitely many twins:

`limsup_(dyadic X) (First_X/W_X)*log B > 28/3`. (L5)

A positive liminf First_X/W_X would imply (L5), but that stronger first-use share has not been established. This criterion needs no LOW17 finite graph, and the measured fractions are not an asymptotic theorem.

## 3. A matching exact SIGNED prime-stage decomposition

For any fresh p and older squarefree prefix L (all odd primes <p), write `Lp=L union {p}`. Let `N_q^L(M)` be q incidence on the **L path**, not on the final S path, and `E_L(M)=sum_n e(d_L(n))` on the same K. Then the change after inserting p is exactly

`Delta_p(M) = G_Lp(M)-G_L(M)`

`= (p-1) N_p^Lp(M) + sum_(q<p)(q-1)[N_q^Lp(M)-N_q^L(M)] + [E_Lp(M)-E_L(M)]`. (S1)

Call the last two signed terms `Interaction_p(M)`. Splitting the fresh p incidence into `F_p^Lp+R_p^Lp`, and using `(a+b)_+ <= a+b_+` for `a>=0`, obtains the paper inequality

`P_X = sum_(p<=B,M) (Delta_p(M))_+`

`<= FirstStage_X + RepeatStage_X + InteractionPositive_X`,   (S2)

with `FirstStage_X=sum_(p,M)(p-1)1_{N_p^Lp>=1} <= (X/2)sum_p(p-1)=o(X^2)`, `RepeatStage_X=sum_(p,M)(p-1)(N_p^Lp-1)_+`, and `InteractionPositive_X=sum_(p,M)(Interaction_p(M))_+`.

Since the signed stage differences telescope, `W_X=sum_(p,M)Delta_p(M)<=P_X`. Thus a **second sufficient condition** is

`liminf_(dyadic X -> infinity) [RepeatStage_X+InteractionPositive_X]/X^2 < 3/16`.  (S3)

This is an exact reduction, not a proven asymptotic estimate. It allows full negative pre-freeze cancellations; bounding positive fresh-p first hits *alone* never bounds the signed displaced-old-prime term. In particular, the label moment in Issue #4 refers to `N_p^S`, whereas (S1)-(S3) refer to `N_p^Lp`, and there is NO universal monotone comparison: for `M=159`, `N_23` on the p=23 prefix is 1 (event at n=255), but after insertion of 29 it is 0 (new 29 event at n=232). Both computations use the same cutoff K=278. The simpler source `M=19` loses its 5-hit when 7 is inserted.

## 4. Relation to Issue #4 second-moment approach

The existing high-q statistic `Z_X=sum_(M,q>=19)N_q(M)^2` controls high-label incidences via Cauchy:

`H_X^2 <= (X/2) pi_[19,B] Z_X`.

If the OPEN estimate `Z_X=O(XB)` held, then `H_X=O(XB/sqrt(log B))`. Hence high-prime weighted repeat growth satisfies

`sum_(M,q>=19)(q-1)R_q(M) <= B H_X = O(X^2/sqrt(log B)) = o(X^2)`.

The unconditional LOW17 finite-computation certificate bounds low-prime events in terms of high19 events, so the low-prime weighted repeat growth is also o(X^2) under that same hypothesis. However this DOES NOT bound `Extra_X`; composite `d` can be much larger than any single prime q<=B. The **direct Issue #4 proof already gives twin infinitude from Z=O(XB) without needing Extra_X**, through the event-clock route. The new ledger clarifies how much more would be needed to transfer that result to the stronger terminal-growth route; it is not a second independent proof.

The nonlinear surplus is precisely a sum of higher-order *same-event* prime correlations, while `Z_X` is a *same-source, same-prime across-time* second moment. Their difference is mathematically essential. A future direct mean-growth proof needs a bound for this nonlinear surplus (or signed cancellation in stage interactions), not just a q return estimate.

## 5. Reproducible computational cross-check

`research/twin_prime_signed_and_composite_ledger.cpp` is the event-clock C++17 auditor. It evaluates every original parity-specific clipped GCD trajectory for X<=262144, every ascending prime-insertion prefix for X<=16384, checks both exact decompositions, the pairwise simultaneous-prime upper bound, all aggregate consistency identities, and known H/F/Z reference values. Independent `research/twin_prime_ledger_literal_oracle.py` advances every integer n rather than jumping between prime clocks, and reproduces both ledgers for X=256,512.

Build and run:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_signed_and_composite_ledger.cpp -o /tmp/twin_ledger
/tmp/twin_ledger 256 512 1024 4096 16384 65536 262144
python3 research/twin_prime_ledger_literal_oracle.py 256 512
```

| X | final W | final first weighted | final repeat weighted | final nonlinear surplus | positive prime-stage sum | stage repeat weighted | stage interaction-positive |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 10222 | 6172 | 3550 | 500 | 10270 | 686 | 5406 |
| 512 | 20048 | 14140 | 4960 | 948 | 26042 | 750 | 14984 |
| 1024 | 39940 | 30162 | 8614 | 1164 | 40426 | 1260 | 20484 |
| 4096 | 399142 | 283224 | 79314 | 36604 | 445678 | 9764 | 248882 |
| 16384 | 2915326 | 1976336 | 607974 | 331016 | 3439438 | 48502 | 2264478 |

At X=16384, adding p=271 changes total G by **-203718** despite a positive fresh-p linear charge of **45900**; old-factor displacement is **-194886** and nonlinear-surplus change is **-54732**. This is an aggregate exact signed cancellation, not a reason to treat the insertion cost as nonnegative.

The standalone final-wheel auditor also checked X=65536 and 262144 (both with the pair upper bound): respectively `(W,First,Repeat,Extra)=(19826998,15228034,2920940,1678024)` and `(138903880,112025370,17443846,9434664)`; pair upper bounds were 2049576 and 9898872 respectively, and final high-q H/F/Z reproduced Issue #4. Only X<=16384 has the separate full stage-scan results above.

## 6. Next mathematical tests and proof work

1. **Target the signed interaction directly**: derive an averaged upper bound on `sum_(p,M)(old-factor drift+nonlinear drift)_+`, rather than bounding each post-freeze case by `G_L(v)` with no cancellation. The stage ledger identifies the exact signed object and makes negative-control tests reproducible.
2. **For high-q returns, use the q-deleted shadow map** from Issue #4 to control `Repeat_X` or `RepeatStage_X`. These are different ensembles: changing prime insertion order is not innocuous; either prove a transfer inequality or analyze the *final* wheel directly.
3. **For nonlinear surplus, develop two-prime simultaneous-clock correlation bounds using Pair_X from (L4)** on the actual transported source states. The factorial expansion above is an exact target. Rare composite events in finite scans do not imply small asymptotic surplus.
4. Try a **combined fixed-coefficient result** (`Repeat_X+Extra_X <(3/16-o(1))X^2` on arbitrarily large dyadic X) before attempting the stronger `o(X^2)` estimates individually. The 3/16 terminal threshold leaves substantial room.

**Status: PARTIAL.** Exact paper algebra, two explicit obstruction witnesses, strict-compiled C++ finite verification plus independent literal Python confirmation; no Lean kernel theorem or universal asymptotic bound, and no claim of an unconditional proof of twin-prime infinitude.
