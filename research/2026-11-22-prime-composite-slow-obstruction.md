# Prime/composite split for slow-interval avoidance

2026-11-22 JST. **Research result (paper deductions; no new Lean build).** The A166944 liminf event-count conjecture and the twin-prime conjecture remain open. This note isolates a sharper conditional criterion and a structural necessity for hypothetical sparse paths without slow intervals.

## 1. Exact context

Use the **original** A166944 recurrence, with increment `d(n)` and horizon `D(n)=a(n)-n`. For a genuinely attained canonical record `M>=23`, set `s0=M+2`, `K=floor((7M-1)/4)`, and `C0=D(s0)=2M-2`. Index events `s0<r1<...<rN<=K`, with `r0=s0`, `gi=ri-r(i-1)` and `ei=d(ri)>1`.

Partition the events into prime increments (`P` events) and composite increments (`Q` events), so `N=P+Q`. Let `Gcomp=sum_composite(ei-1)`. Denote `x(u)=sqrt(2u+1)` using the real square root, `x0=x(s0)`, and `xK=x(K)`.

The source Lean results are:

- Uploaded Prove2Me workspace `mission_scan/twin_proof/cap_bound/AllIndices.lean`, `CapSampleExact.lean`, `SlowIntervalMission.lean`; and `mission_scan/twin_proof/index_window/ConditionalIndexCheck.lean` with `D(n)<=2n`.
- [`FirstHitArithmetic.lean`](../A166944/FirstHitArithmetic.lean): `moving_horizon_composite_event_gap_sq`, stating `g*g<=4*e` for a composite first-hit increment.
- [`TravelFactors.lean`](../A166944/TravelFactors.lean): `moving_horizon_factor_reuse_growth` (`p-1` intervening horizon growth for reused factors `p>=5`); this is existing work, not a new reuse theorem.
- [Previous adaptive-block note](2026-11-22-adaptive-event-count-analysis.md).

Since `K<=C0` for `M>=7`, all nonunit events through `K` are genuine first hits inside the moving horizon; thus the composite gap lemma applies. The global `D(n)<=2n` bound implies

`0<=Gcomp<=D(K)-D(s0)<=Gmax:=2K-(2M-2)=(3/2)M+O(1)`.

## 2. New aggregate composite-gap lemma

For each composite event, `gi^2<=4ei`. Hence

`sum_comp gi <= 2*sum_comp sqrt(ei) <= 2*sqrt(Q*sum_comp ei) = 2*sqrt(Q*(Gcomp+Q))`.      (1)

The second inequality is Cauchy-Schwarz. This holds for all such canonical index windows, **without any assumption about whether a slow interval exists**.

In particular, if `N=O(sqrt M)`, then `Q=O(sqrt M)` and `Gcomp=O(M)`, so the total time spent in gaps ending at composite events is `O(M^(3/4))=o(M)`.

## 3. New finite sufficient condition for a slow interval

The previously derived adaptive quiet-block lemma says: for `u>=24` and `L(u)=14+2*isqrt(2u+1)`, if every increment in `(u,u+L(u)]` is 1 then that block is slow. In the absence of a slow interval wholly contained in `[s0,K]`, every event gap is `gi<=L(r(i-1))`, and the terminal unit suffix `K-rN` is `<L(rN)`.

For any `u<=v` let `Delta x=x(v)-x(u)=2*(v-u)/(x(v)+x(u)) <= (v-u)/x(u)`.

Thus the `P` prime-event gaps and terminal unit suffix together contribute at most

`(2+14/x0)*(P+1)`

to `xK-x0`. The composite gaps contribute at most

`(sum_comp gi)/x0 <= 2*sqrt(Q*(Gcomp+Q))/x0`

by (1). Therefore **absence of a slow interval implies**

`xK-x0 <= (2+14/x0)*(P+1) + 2*sqrt(Q*(Gcomp+Q))/x0`.      (2)

By contraposition:

> **Finite prime/composite criterion.** If the right-hand side of (2) is **strictly less** than `xK-x0`, a slow interval exists in `[s0,K]`, and the inspected `CapSampleExact.cap_of_one_slow_interval` proves Cap B for this genuinely attained record `M`.

This is a new paper consequence of existing Lean lemmas. It counts prime and composite events separately and can succeed even when the total event count exceeds the earlier uniform/adaptive block threshold.

For `M=45,895,573`, `K=80,317,252`, `xK-x0≈3093.397` and `Gmax=68,843,360`. As an **illustrative sufficient-test input, not an observed path**, `P=1500, Q=500, Gcomp<=Gmax` gives RHS at most `3042.924`, hence would force Cap B despite `N=2000` being above the previous event-count cutoff of 1545.

## 4. Asymptotic alternative, still conditional

Since every composite increment in this recurrence is odd and at least 9, `Gcomp>=8Q`. Thus

`Gcomp+Q <= (9/8)*Gcomp <= (9/8)*Gmax = (27/16)M+O(1)`.

Let `c=(sqrt(7/2)-sqrt2)/2=0.2283075655...`. From (2), along any record subsequence with `P=O(sqrt M)`,

`P/sqrt M + sqrt(27/32)*sqrt(Q/M) >= c-o(1)`      (3)

whenever there is **no** slow interval. The `o(1)` here is uniform when the displayed left side remains bounded, which is the only case relevant to its contrapositive.

Therefore an unbounded sequence of actual canonical records on which

`liminf [P/sqrt M + sqrt(27/32)*sqrt(Q/M)] < c`

is **sufficient for infinitely many twin primes**, using the already-checked mission theorem on unbounded slow intervals.

A useful special case is: on an unbounded genuine-record subsequence, `Q=o(M)` and `liminf P/sqrt M<c`. This requires only *sublinear composite event count*, not `Q=O(sqrt M)`. Also, if `N=O(sqrt M)` but slow intervals do not occur, (2) forces `P/sqrt M>=c-o(1)`: almost all the required leading-order count is necessarily from **prime** events.

These are reductions, **not proofs** that the displayed conditions occur.

## 5. Reuse rigidity if a no-slow sparse path existed

Here is a further structural conditional conclusion using the genuine *first-hit divisor rule*, not merely the coarse travel bounds.

At an event of size `e` and gap `g`, its pre-event horizon is `C`. The hit-side cofactor `v=(C-1)/e` or `v=(C+1)/e` is odd and at least 3. Since the earlier `g-1` indices are unit increments, `AllIndices.units_lt_twice_factor` applied to `v` implies `g<=2v`, whence

`g*e<=2*(C+1)<=2*(2K+1)`.      (4)

Also the same first-hit lemma with divisor `e` gives `g<=2e`.

Suppose a hypothetical sequence of genuine records `M->infinity` had **no slow interval** and `N<=A*sqrt M` for some fixed `A>0`. Set `delta=3/(8A)`. Gaps `g<delta*sqrt M` occupy at most `(3/8)M` index steps in total. Because the terminal quiet suffix is `O(sqrt M)` and `T=K-s0=(3/4)M+O(1)`, event gaps `g>=delta*sqrt M` must cover at least `(3/8)M-O(sqrt M)` steps.

No-slow implies every event gap is at most `L(K)=(sqrt(14)+o(1))*sqrt M`. Therefore there are at least `(3/(8*sqrt(14))+o(1))*sqrt M` long-gap events.

Only `O_A(1)` of these can be composite: (1) composite gap `g>=delta*sqrt M` entails `e>=delta^2*M/4`, while total horizon growth is `<=Gmax=(3/2)M+O(1)`.

All remaining long-gap events have prime increment `p`. From (4) and `g<=2p`,

`(delta/2)*sqrt M <= p <= (7/delta+o(1))*sqrt M`.

The number of **distinct** primes in this band is `O_A(sqrt M/log M)` by the elementary Chebyshev upper bound for prime counting. Since there are `Omega_A(sqrt M)` prime events in the band, **at least one such prime must be reused `Omega_A(log M)` times**.

The known Lean theorem `moving_horizon_factor_reuse_growth` already charges at least `p-1` *other-event growth* between consecutive reuses of a factor `p>=5`. However, the corresponding growth windows for distinct primes can overlap. The available reuse lemma does not yield a global sum exceeding `Gmax`. This overlapping-reuse budget is still the obstacle to a contradiction.

## 6. Finite diagnostic

[`prime_composite_slow_audit.py`](prime_composite_slow_audit.py) directly computes the original recurrence through index 2,500,000, then audits every genuinely attained record with `K<=2,500,000`. It checks:

- the canonical identity `D(M+2)=2M-2`;
- `e<=M` and the first-hit cofactor inequality `g*e<=2*(C+1)` on each relevant hit;
- `g^2<=4e` for every composite event;
- the aggregate squared inequality `(sum_comp g)^2<=4*Q*(Gcomp+Q)`;
- the first endpoint of an actual slow interval (if any).

The original local Python implementation was run successfully, including genuine-record examples `M=13` (`P=2,Q=1`, no slow), `M=43` (`P=4,Q=1`, no slow), `M=355723` (`P=54,Q=3`, slow at `j=358738`), and `M=1427749` (`P=65,Q=7`, slow at `j=1434396`). These finite checks do not establish the asymptotic claim.

## 7. Remaining gap

Neither `Q_M=o(M)` nor `P_M=o(sqrt M)` (nor the combined bound (3)) is currently established for an unbounded family of **actual** records. The new theorem proves that near-threshold hypothetical no-slow paths must consist predominantly of prime events and reuse primes of order `sqrt M`; it does not exclude those paths. The known `p-1` reuse-growth charge cannot simply be added across multiple prime keys because the charging intervals overlap. A simultaneous cross-prime reuse estimate or an authentic-attainment invariant is still required.

**Verification level:** paper mathematics plus a finite direct-gcd audit; no new Lean kernel proof, no Prove2Me final proof, and no claim of solving the twin-prime conjecture.
