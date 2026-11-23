# A166944 twin-prime-first: elementary LOW3 clock compression, marked q-deleted shadow, and high-owner return moment

2026-11-23 JST. A research **paper reduction** with exact C++17 and independently written literal Python audits, for the squarefree sqrt-wheel in Issue #3 with the leave-one-prime-out shadow from Issue #4. **NOT Lean kernel checked; NOT a proof of the remaining asymptotic moment bound; NOT a proof of twin-prime infinitude or the full A166944 record conjecture.**

Primary project antecedents:

- `research/2026-11-22-squarefree-sqrt-wheel-mean-reduction.md` (Issue #3): terminal sqrt-wheel certificate and exact dyadic horizon sum.
- `research/2026-11-23-minimum-prime-clock-return-reduction.md` (Issue #3): minimum-owned event-clock travel; the older all-odd-prime return criterion.
- `research/2026-11-23-twin-prime-signed-and-composite-ledger.md` (Issue #3): exact nonlinear composite surplus.
- `research/2026-11-23-single-source-q-label-second-moment-and-shadow-renewal.md` (Issue #4): q-deleted first-q-return shadow and high-q source-label moment.
- `research/2026-11-23-q17-exhaustive-nilpotence-and-symbolic-q19.md` (Issue #4): independently established LOW17 computer-audited boundedness, **not needed** for the main new theorem below.

## 1. Full final-wheel setting

Let `X=2^k>=256`, `I_X={odd M: X<=M<2X}`, `N=X/2`, `B=ceil(sqrt(7X))`, `s=M+2`, `K=floor((7M-1)/4)`. The parity-specific squarefree clipped-GCD wheel starts `C(s)=2M-2`, and at n>s makes the change `C(n)=C(n-1)+d(n)-1`, with `d(n)=product of distinct odd p<=B dividing gcd(n,C-1)` when n is even, or dividing `gcd(n-2,C+1)` when n is odd. An event means d>1. Write its event times `s=n_0<n_1<...<n_J=S`, with terminal C=C(K). Every event's frozen preceding gap `g_i=n_i-n_(i-1)` is <=2p for ANY prime factor p|d(n_i), because the corresponding active p-clock period is 2p. It need not be the **smallest factor of d** for this inequality.

The prior exact terminal certificate: `K-S>=2B` implies `C(K)-1,C(K)+1` are twin primes. Exact sum `sum_M(K-s)=9X^2/16-5X/4`. Therefore a dyadic interval with no twin-producing endpoints has

`Travel_X=sum_M(S-s) > 9X^2/16-5X/4-XB`.  (B0)

## 2. NEW unconditional elementary pure-3 termination bound: 7 time steps

Starting at ANY plateau `(t,C)` with C even, consider only the clipped prime {3} (omit all p>=5). There are three cases:

1. C≡0 (mod3): no 3 clock is active; no further event.
2. C≡1 (mod3): the only active 3 clock is at EVEN `n≡0 (mod6)`, reached in <=6 steps. After that d=3 raises C by2, making C≡0 (mod3), hence stops.
3. C≡2 (mod3): the only active 3 clock is at ODD `n≡5 (mod6)`, reached in <=6 steps. After d=3, C≡1 (mod3); the next even `n≡0 (mod6)` is exactly ONE step later, then C≡0 and stops.

**Exactly:** arbitrary pure-3 wheel has <=2 events and final elapsed time <=7. It is sharp, for example t≡5 (mod6), even C≡2 (mod3). No large finite graph, unproved CRT distribution, or LOW17 certificate is used. Independent 18-residue exhaustive Python audit also reproduces sharp7.

## 3. Replace all-prime minimum ownership by **smallest high factor p>=5**

Call an event **high** if at least one p>=5 divides d. Give it the **unique high owner** `h(e)=min{p prime: 5<=p<=B, p|d}`. A mixed `d=3*q` has high owner q even though its globally smallest prime factor is 3. Other events are pure-3 events d=3.

Within each M, let `U_q(M)` be the count of events whose high owner is q (q>=5). Define first high-owner count `Fcount=sum_(M,q)1_{U_q>0}` and weighted first high-owner charge `Fweight=sum_(M,q)q 1_{U_q>0}`; define number of repeated high-owned events `Rcount=sum_(M,q)(U_q-1)_+` and their ACTUAL preceding clock-gap total `Rtime=sum_(M,e high owner q previously owned)g(e)`. Let `Ftime` be actual high-first event gap total, and `LowTime` pure-3 event gap total. Then

`Travel_X = LowTime + Ftime + Rtime`. (H1)

Between high events, the original path follows the pure-3 wheel, up to but **excluding** the next high event. There are at most H+N such blocks where H=Fcount+Rcount high events, each consuming <=7 time to its last pure-3 event. Thus `LowTime<=7(N+Fcount+Rcount)`. Every high event with owner q has gap<=2q, so `Ftime<=2 Fweight`. Therefore

`Travel_X <= 7(N+Fcount)+2Fweight+[Rtime+7Rcount]`. (H2)

Unconditionally `Fcount<=N*pi(B)=o(X^2)`, `Fweight<=N*sum_(5<=p<=B) p=O(X B^2/log B)=o(X^2)` (standard prime-count upper bound, B²~7X). By (B0)-(H2):

**NEW sufficient condition (OPEN):**

`liminf_(dyadic X->infinity) [Rtime_X+7*Rcount_X]/X^2 < 9/16`   ==> infinitely many twin primes. (H3)

No composite-event surplus E is required, and the proof uses only an **elementary** finite low-wheel bound for q=3. A second sufficient condition follows from `Rtime+7Rcount<=sum_(M,q>=5)(2q+7)(U_q-1)_+`, and a fixed weighted high-owner return average below 9/16.

## 4. New q>=5 only high-owner second-moment criterion

Define `V_q(M)=(U_q(M)-1)_+` and

`Z5_X = sum_(M in I_X) sum_(5<=q<=B prime) V_q(M)^2`.

By weighted Cauchy,

`[Rtime+7Rcount]^2 <= [sum_(M,q)(2q+7)V_q]^2 <= N [sum_(5<=q<=B prime)(2q+7)^2] Z5_X`. (H4)

By prime-number-theorem partial summation, `sum_(q<=B)(2q+7)^2=(4/3+o(1))B^3/log B`. Since B²~7X, if **no** twin-producing terminal endpoint occurred on an unbounded sequence of dyadic X, (B0),(H2),(H4) would force

`Z5_X/(X B log B) >= 243/25088 - o(1)`, with `243/25088≈0.0096859056`.

Consequently the following is also sufficient, and still **OPEN**:

`liminf_(dyadic X->infinity) Z5_X/(X B log B) <243/25088` ==> infinitely many twin primes. (H5)

Crucial: this Z5_X measures **minimum among factors >=5**, not all q hits and not the all-prime minimum owner. The repeated factor 3 does not enter. It needs neither LOW17 graph nor its 769-step constant. The fixed coefficient happens to match the earlier all-prime min-return moment because the highest-degree 2q contribution dominates, but the statistic itself is materially different and removes the problematic q=3 component.

### Finite exact second-moment-to-twin certificate

For a *single* dyadic X let `Horizon=9X²/16-5X/4` (integer), `D=Horizon-XB-7(N+Fcount)-2Fweight`, `P2=sum_(prime 5<=q<=B)(2q+7)^2`. If `D>0` and

`N*P2*Z5_X <= D*D`, (H6)

then at least one source in I_X produces a twin prime pair, by (B0) and (H2)-(H4), **without evaluating the terminal pair's primality in the argument**. For X65536: `P2=69348969`, `Z5=1678123`, `D=2338846133`, LHS=`3813412041693167616`, RHS=`5470201233849053689`, hence true. For X262144: `P2=470734799`, `Z5=11447377`, `D=38065260743`, LHS=`706304896030765613056`, RHS=`1448964075432576912049`, hence true. This is finite mathematical/computer evidence, NOT an infinite theorem or Lean-certified result.

## 5. One-step marked q-deleted shadows, now with high-only masking

Fix any original **high-owner** event q>=5 and its post-event state `(M,t,C,K)`; q can be multiplied by 3 during this event, and still counts as high-owned. Start the **q-deleted shadow** from exactly this state: at each plateau, compare the next q clock with the next non-q clock, stopping when q clock wins or TIES. Until the first q hit, full and shadow states coincide. When q next fires at n, its clipped d may also contain some p<q; call this return **DIRECT/CLEAN** when NO other HIGH factor `5<=r<q` divides d. A low factor 3 is ALLOWED. If some high r<q divides d, q is **MASKED**: the q event still happens and changes the full state, so the shadow MUST be restarted after this q hit before predicting any later owned q return.

The one-step observed predicate on a tagged post high-owned state v is:

`b_q(v)=1{ first q hit in q-deleted shadow exists and has NO high factor <q }`.

The actual next-q-hit preceding gap `g_q(v)` equals the gap from the final non-q shadow plateau to the first q clock (a tie with 3 or any p>q is allowed). For the source-weighted COUNTING measure nu_q on **ALL actual post high-owned q states**, not a stationary/uniform CRT distribution,

`RcleanCount_X=sum_q sum_(v in nu_q) b_q(v)`;
`RcleanTime_X=sum_q sum_(v in nu_q) b_q(v)*g_q(v)`. (S1)

This is a single-shadow-step exact return observable. It is not the full unmarked q-hit return operator, because high-masked q hits can interpose.

Define high masking charge

`MaskCost_X=sum_(M,e high) sum_(q>=5|d(e),q>h(e)) (2q+7)`.

Each high-owned **repeated** q event with at least one high-masked q event since the previous high-owned q event can be injected into the LAST such intermediate masked q hit, with distinct tagged q hit for disjoint owner-return intervals. Its clock gap is <=2q; its one-event return count charges 7 more. Thus

`Rtime+7Rcount <= RcleanTime+7RcleanCount+MaskCost`. (S2)

For every high event, let h be its minimum high factor. For all masked q>h, h>=5,q>=7; the nonlinear composite surplus `e(d)=d-1-sum_(p|d)(p-1)` includes every pair term `(h-1)(q-1)`. Therefore `e(d)>=4*sum_(q masked)(q-1)`, and since `2q+7 <=(7/2)(q-1)` for q>=7,

`0<=MaskCost_X<= (7/8)*Extra_X`. (S3)

The constant7/8 is sharp at the single-event algebraic level for d=5*7=35 (masked q7 charge21, e(35)=24).

**NEW one-step sufficient input (OPEN):**

`liminf_(dyadic X->infinity)[RcleanTime+7RcleanCount+MaskCost]/X² <9/16` ==> infinitely many twins. (S4)

Also `(7/8)*Extra` may replace MaskCost to obtain a stronger sufficient hypothesis. This is a precise source-selected **first-return** correlation problem without full q-return-history iteration, but the counting measures nu_q remain adaptively determined by the original path. An unproved near-uniformity of source CRT residues has NOT been used.

### Explicit actual counterexample to a naive single-unmarked-shadow assumption

At X16384, M26111, q23, the actual q-bearing events include `(n,d,high owner)=(26496,23,23),(26843,23,23),(27211,299,13),(27395,23,23),(27487,23,23)`. From owned q23 at 26843, the *next* q23 hit is MASKED at 27211 (`299=13*23`); the subsequent q23 owner event at27395 is not the **first** q hit after26843. One uninterrupted q-deleted shadow from26843 cannot legitimately skip the event at27211. The all-prime-minimum analogue occurs already at M449,q7 with q-masked event d21 at n546 before owned q7 at n695.

## 6. Numerical audit and exact verification classes

Independent original parity-specific clipped GCD event-jump C++17 sources:

- `research/twin_prime_shadow_minowner_audit.cpp`: full all-prime minimum q labels; verifies q-deleted first-q-hit time, clipped d, post C, preceding gap and owner for **every** original post-q event (including q-hit with lower cofactor), as well as terminal no-q returns; X256,512,1024,4096,16384,65536,262144 PASS.
- `research/twin_prime_lowblock_highowner_audit.cpp`: HIGH-owner low-block ledger at fixed cutoffs3,5,7,17, per-source block clock bounds, exact first/return/masked decomposition and high moment Z5. X256,512,1024,4096,16384,65536,262144 PASS. Bounds for low5, low7, low17 are supporting finite diagnostics; the **new theorem only uses low3**.

Independent literal integer-by-integer Python:

- `research/twin_prime_shadow_minowner_literal.py`: checks q-deleted shadow from actual post-q states for all q, sourcewise time and masked budget; X256/512/1024 PASS.
- `research/twin_prime_low3_shadow_literal.py`: proves a finite 18-residue sharp LOW3 clock check and crosschecks high owner/clean shadow and fixed prior X-regressions using the original parity gcd advanced at every n; X256/512/1024 PASS. The arithmetic argument in §2 is independent of the finite enumeration.
- `research/low_wheel_finite_graph.py`: separate exhaustive pair-residue graph for S={3}, {3,5}, {3,5,7}, sizes18/450/22050, zero cycles; max low-only travel7/19/56. This auxiliary enumeration is **not** relied upon as a proof of the LOW3 lemma.

Build/run:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_shadow_minowner_audit.cpp -o /tmp/marked_shadow
/tmp/marked_shadow 256 512 1024 4096 16384 65536 262144
python3 research/twin_prime_shadow_minowner_literal.py 256 512 1024

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_lowblock_highowner_audit.cpp -o /tmp/low_high
/tmp/low_high 256 512 1024 4096 16384 65536 262144
python3 research/twin_prime_low3_shadow_literal.py 256 512 1024
python3 research/low_wheel_finite_graph.py
```

| X | high>=5 repeat time | high>=5 return count | time+7count | clean time | high mask weighted (sum q) | high masking charge | Z5/(XB logB) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4096 | 58720 | 7774 | 113138 | 58696 | 5205 | 11761 | 0.00868530 |
| 16384 | 419801 | 55974 | 811619 | 415348 | 26261 | 63351 | 0.0105257 |
| 65536 | 2071487 | 261241 | 3900174 | 2056383 | 155618 | 357268 | 0.00579326 |
| 262144 | 12439174 | 1442797 | 22538753 | 12338840 | 962761 | 2174407 | 0.00446887 |

At X262144, direct high-owner returned weighted clock time+count `22538753/X²≈0.00032798` vs sufficient threshold 9/16=0.5625. The one-step clean+mask upper `24526684/X²≈0.00035691`; these are FINITE ratios, not uniform estimates. X16384 moment ratio exceeds fixed threshold; X65536 and 262144 fall below it, and the exact finite scalar inequality H6 succeeds there. Neither finite fact implies an asymptotic theorem.

## 7. Actual remaining analytic lemma

Prove on arbitrarily large dyadic X one of:

- unconditional source-selected **high-owner time budget** (H3): `Rtime+7Rcount<(9/16-epsilon)X²` for fixed epsilon>0;
- q-deleted ONE-STEP selected-source bound plus high-high masked-event charge (S4);
- the unweighted **high-owner return second moment** (H5): `liminf Z5/(XB logB)<243/25088`.

The source-selected ensemble nu_q is generated by previous q and other prime events, not a uniform residue model; the first-shadow hit may be masked, and then the full process differs from the q-free continuation. This adaptive source-state dispersion / renewal bound is the remaining open mathematical obstacle. **No twin-prime infinitude theorem or new Lean-verified asymptotic lemma.**