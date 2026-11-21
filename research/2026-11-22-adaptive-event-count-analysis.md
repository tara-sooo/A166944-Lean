# Adaptive slow blocks: a stronger square-root event-count criterion

2026-11-22 JST. **Status:** paper deduction and independently executed finite checks. The main liminf hypothesis is **unproved**; neither Cap B nor twin-prime infinitude has been established here. The new statements below have **not** been compiled in Lean.

## Exact input and scope

The source for the relevant Lean-proved lemmas is the supplied `A166944-Lean.zip` workspace, especially `mission_scan/twin_proof/cap_bound/{AllIndices,CapSampleExact,SlowIntervalMission}.lean` and `mission_scan/twin_proof/index_window/ConditionalIndexCheck.lean` (`a_le_three_mul`). `AllIndices.twins_of_slow_interval` and `SlowIntervalMission.mission_of_slow_intervals` connect a slow interval to twin primality and an unbounded family of slow intervals to twin-prime infinitude. The supplied source uses the actual sequence `a` with `D(n)=a(n)-n`, and establishes `D(n)<=2n` for the relevant indices.

For a *genuinely attained canonical record* `M`, let `s0=M+2`, `K=floor((7M-1)/4)` and let `N_M` count actual nonunit increments `d(r)>1` at `s0<r<=K`. Throughout assume `s0<=K` and `s0>=24` (automatic at the platform threshold). A slow interval `[i,j]` obeys

`9*(D(j)-D(i))+32+8*floor(sqrt(D(j)+1)) <= 4*(j-i)`.

## Lemma: an adaptive unit block is slow

Fix `u>=24` and set `t=floor(sqrt(2u+1))>=7`, `L(u)=14+2t`. Since `2u+1 <= (t+1)^2-1`,

`2*(u+L(u))+1 <= t^2+6t+28 < (t+4)^2`.

Thus `floor(sqrt(2*(u+L(u))+1))<=t+3`. If every increment in `(u,u+L(u)]` is 1, then `D(u+L(u))=D(u)<=2*(u+L(u))`, and

`32+8*floor(sqrt(D(u+L(u))+1)) <= 32+8*(t+3) =4*L(u)`.

Therefore `[u,u+L(u)]` is slow. In particular, if *no* slow interval ends in `[s0,K]`, every nonunit event following an event/index `u` occurs within `L(u)` steps, and the final event-free suffix before `K` is shorter than `L(u)`.

## Theorem (paper): a stronger event-count threshold

Put `x(u)=sqrt(2u+1)` (real square root), `x0=x(s0)` and `xK=x(K)`. For any segment `[u,v]` of length at most `L(u)`,

`x(v)-x(u)=2*(v-u)/(x(v)+x(u)) <= L(u)/x(u) <= 2+14/x0`.

Split the index interval at its `N_M` nonunit events, yielding `N_M+1` segments, including its final suffix. If no slow interval occurs, the preceding lemma applies to every segment. Telescoping gives the **rigorous necessary condition**

`N_M+1 >= (sqrt(2*K+1)-sqrt(2*M+5))/(2+14/sqrt(2*M+5)).`   (A)

Consequently, the strict opposite inequality guarantees a slow interval and hence (by the inspected `cap_of_one_slow_interval`) Cap B for that `M`. Note (A) is only *necessary for the absence of slow intervals*, not a proved bound on the actual `N_M`.

Let genuine canonical record values tend to infinity. Dividing (A) by `sqrt(M)` shows that absence of slow intervals along this record subsequence would force

`liminf N_M/sqrt(M) >= c_adaptive = (sqrt(7/2)-sqrt(2))/2 = 0.2283075655069...`.

Thus **the weaker-than-before hypothesis**

`liminf_{M genuine canonical record -> infinity} N_M/sqrt(M) < c_adaptive`

implies slow intervals with unbounded final `D`, hence infinitely many twin primes by the existing Lean-checked `mission_of_slow_intervals` implication. An `o(sqrt(M))` unbounded record subsequence is a special case. The conditional implication is a paper deduction; the liminf premise is the open number-theoretic input.

The previously recorded uniform-length argument only reached `3/(4*sqrt(14))=0.2004459...`; this increases the admissible coefficient by about 13.9%.

## Exact finite threshold (integer-only block algorithm)

A slightly sharper finite criterion uses `L_exact(u)` defined to be the least integer `ell` satisfying

`4*ell >= 32+8*isqrt(2*(u+ell)+1)`.

If a block of length `L_exact(u)` contains only unit increments, the block is slow. Greedily partition `[s0,K]` into these consecutive variable-length blocks; if `q` complete blocks fit, `N_M<q` guarantees one empty block and hence Cap B.

At `M=45,895,573`, `K=80,317,252`:

- Simple `L(u)=14+2*isqrt(2*u+1)` yields `q=1545`, so `N_M<=1544` suffices.
- The exact integer rule yields `q=1546`, so **`N_M<=1545` suffices**.
- The previous uniform-block method gave only `N_M<=1356`.

These are numerical *sufficient tests* for this `M`, not verified event-count bounds for all records. Both counts are independently reproducible by [`adaptive_event_count_audit.py`](adaptive_event_count_audit.py).

## Why the available coarse inequalities do not prove the liminf premise

There is an explicit family of **abstract increments** satisfying the elementary height bound and coarse event/travel inequalities, but not the actual gcd first-hit equation. For large `M`, choose an odd `g` with `g~sqrt(M)` and set `D*(s0)=2M-2`. For indices strictly after `s0`, take increments `d*(s0+kg)=g` for `k>=1`, and `d*=1` elsewhere. Then

`D*(n)=2M-2+(g-1)*floor((n-s0)/g)`.

The increments are positive odd numbers, the nonunit size is `<M`, `D*(n)<=2n`, and each event interval has `gap=g<=2*d*` and for `g>=9`, `4g+32<=9*(d*-1)`; these imitate the coarse first-hit growth/travel constraints. The number of events in `[s0,K]` is `floor((K-s0)/g)~(3/4)*sqrt(M)`, far above the desired threshold.

Moreover this artificial path has **no slow interval** in `[s0,K]`: any interval of length `l` containing `m` events satisfies `l<=g*(m+1)` and `D*(j)-D*(i)=m*(g-1)`. For `g>=2`,

`4*l-9*(D*(j)-D*(i)) <= 4g+(9-5g)*m <=4g < 32+8*isqrt(2M-1) <=32+8*isqrt(D*(j)+1)`.

Therefore the elementary height, parity, event gap, and coarse growth bounds alone cannot establish the desired asymptotic event-count bound, or even force a slow interval. The omitted **exact divisibility and no-earlier-gcd-hit conditions** (and potentially authentic record attainment from `a(1)=2`) must be exploited. This is a countermodel to the *coarse abstraction*, not to A166944 or to Cap B.

There is also a finite exact-gcd diagnostic: the twin-shaped artificial start `M=28,549` has both `M` and `M-2` prime and produces **177 nonunit events** up to `K=49,960`, or `N/sqrt(M)≈1.0476`. A direct index-by-index gcd replay finds a slow interval nonetheless. This is not an attained record from the original A166944 sequence and is not an asymptotic counterexample. It illustrates that the event-count condition is sufficient, not necessary.

## Exact alternative: drawups rather than total event count

Define the integer potential `F(n)=4*n-9*D(n)`. For any `2<=i<=j`, the slow condition is **exactly equivalent** to

`F(j)-F(i) >= 32+8*isqrt(D(j)+1)`.

Therefore proving cofinally many upward excursions of this potential exceeding the square-root barrier is another sufficient route, weaker than proving the event count itself is small. At a unit increment, `F` rises by 4; at a nonunit increment `e>=3`, it changes by `4-9*(e-1)<=-14`. Local divisibility and first-hit rules govern whether these downward jumps can prevent long upward excursions indefinitely. This reformulation is algebraic; the unbounded-excursion assertion remains unproved.

## Current missing step

Prove an *unconditional* upper bound or infinitely-often upper bound on `N_M/sqrt(M)` for actual attained canonical records, or prove the unbounded existence of slow intervals by another method. The exact first-hit arithmetic and interactions among changing prime factors remain essential. Existing formalized event-count inequalities alone do not furnish that upper bound ([`CountBoundLimits.lean`](../A166944/CountBoundLimits.lean)). The improved conditional theorem above should be ported to Lean if this route is pursued.

**Validation:** Python 3 standard-library audit passed for the integer block counts and the direct synthetic-gcd replay. No new Lean build, Prove2Me submission, or proof of the open liminf hypothesis is claimed.
