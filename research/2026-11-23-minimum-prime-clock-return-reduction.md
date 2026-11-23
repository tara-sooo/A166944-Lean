# Twin-prime-first: minimum-prime clock ownership eliminates simultaneous-prime surplus from the sufficient condition

Date: 2026-11-23 JST. A166944 Issue #3 cross-prime correlation handoff to Issue #4. **Paper-level elementary theorem reduction plus verified finite programs; NOT a proof of the open analytic input, NOT Lean-kernel-checked, NOT an unconditional proof of infinitely many twin primes.** Built on `research/2026-11-22-squarefree-sqrt-wheel-mean-reduction.md` (terminal sqrt-wheel certificate) and `research/2026-11-23-twin-prime-signed-and-composite-ledger.md` (weighted prime-return and nonlinear pair budgets). Unlike the earlier growth-budget route, the result below needs NO cross-prime simultaneous-event surplus bound and NO finite LOW17 certificate.

## 1. Definitions

Let X=2^k>=256, I_X={odd M: X<=M<2X}, B=ceil(sqrt(7X)), s(M)=M+2, K(M)=floor((7M-1)/4). At s the squarefree parity-specific GCD wheel has even horizon C=2M-2. At even n>s use raw gcd(n,C-1); odd n>s use gcd(n-2,C+1); clipped d(n) is the product of all distinct odd primes <=B dividing the gcd, and C advances by d(n)-1. Let the nonunit event times for M be n_1<...<n_J, with n_0=s and S=n_J if J>0, else S=s. The canonical invariant is 2M-2<=C(n)<=2n. The existing certified **paper** terminal implication is: if `K-S >=2B`, then `C(K)-1` and `C(K)+1` are twin primes, because B>=sqrt(2K+1).

For each event e at time n_i, let `a(e)=min{odd prime p:p|d(n_i)}`. This is one prime label PER EVENT, even when its clipped increment is composite; no other factor receives event-time ownership. Define

`U_p(M)=# {event e of M: a(e)=p}`, `V_p(M)=max(U_p(M)-1,0)`;

`Fmin_X=sum_(M,p<=B) p*1_{U_p(M)>0}`;

`Rmin_X=sum_(M,p<=B) p*V_p(M)`;

`Tfirst_X=sum_(M,e: e is FIRST minimal-p event of source M) (n_i-n_(i-1))`;

`Treturn_X=sum_(M,e: minimal p of e was previously minimal for same M) (n_i-n_(i-1))`.

By definition, the exact total **last-event travel** is `Travel_X=sum_M(S(M)-s(M))=Tfirst_X+Treturn_X`.

## 2. Exact minimum-prime gap lemma (PAPER)

At the plateau just after n_(i-1), the horizon C is fixed until the next nonunit event at n_i. Its smallest prime factor p=a(e) divides the relevant frozen C−1 or C+1, and the corresponding parity-restricted p-clock has period 2p. As the next event occurs at n_i, the clock cannot have waited more than one period since n_(i-1):

`BOXED: n_i-n_(i-1) <=2*a(e).` (C1)

This is a clock identity, not an assumption that events are independent in arithmetic progressions. Consequently

`Travel_X <=2*(Fmin_X+Rmin_X)`;
`Tfirst_X<=2*Fmin_X`;
`Treturn_X<=2*Rmin_X`. (C2)

The first-minimal-event total is unconditionally negligible at the quadratic scale:

`Fmin_X <=(X/2) sum_(odd primes p<=B) p = (7/4+o(1))*X^2/log B =o(X^2)` (PNT; B²=7X+o(X)). (C3)

Also, for the *same FINAL* wheel, defining `N_p(M)=# events with p|d` and `RfullP_X=sum_(M,p) p*max(N_p(M)-1,0)`, we have `Rmin_X<=RfullP_X` because U_p<=N_p sourcewise. This does NOT equate final q-label multiplicities with those of ascending prime-insertion prefix wheels.

## 3. Sharper twin-prime sufficient conditions, with NO pair-surplus bound (PAPER)

The exact dyadic horizon identity is

`Horizon_X=sum_M(K-s)=9*X²/16-5*X/4`.

If a particular dyadic window yields no twin-prime terminal pair, its every source must have `K-S<2B` by the established sqrt-wheel certificate. Summing over all M then forces

`Travel_X > Horizon_X-X*B`, hence by (C2) and (C3)

`Treturn_X > 9*X²/16-5*X/4-X*B-2*Fmin_X`;

`Rmin_X > 9*X²/32-5*X/8-X*B/2-Fmin_X`.

This supplies TWO NEW PAPER SUFFICIENT CONDITIONS, each individually implying infinitely many twin primes:

`BOXED (CLOCK-TIME): liminf_(dyadic X->infinity) Treturn_X/X² < 9/16.` (C4)

`BOXED (WEIGHTED MINIMAL RETURNS): liminf_(dyadic X->infinity) Rmin_X/X² <9/32.` (C5)

A stronger but sometimes more directly accessible input is `liminf RfullP_X/X²<9/32`. Neither C4 nor C5 is proved asymptotically.

**Why this is strictly better as a sufficient route than the former pair-budget:** Previously one needed an OPEN estimate for `RepeatWeightedPrime_X+Extra_X`, or its stronger `RepeatWeightedPrime_X+Pair_X`, below `(3/16)X²`. The new bound uses ONLY the smallest prime assigned to each event, so the nonlinear simultaneous-prime surplus e(d) never appears. Indeed `Rmin_X<=sum_p p*(N_p-1)_+ <=(3/2)*RepeatWeightedPrime_X`, where RepeatWeightedPrime_X uses weights p-1. Thus every sequence of windows satisfying the earlier `RepeatWeightedPrime_X+Extra_X <(3/16-o(1))X²` condition also satisfies the new `Rmin_X <(9/32-o(1))X²`; the reverse implication is not required. The full pair-renewal/reset research remains useful for stronger growth bounds, but it is NOT a required input to C4 or C5.

C4 is the more natural renewal target: it bounds the **actual elapsed clock time** following recurrent minimal labels, without paying the worst-case delay 2p for each. Proving C4 along unbounded dyadic windows would finish the twin-prime-first objective through the existing terminal certificate.

## 4. New weighted-Cauchy minimal-return second-moment variant (PAPER)

Let `ZminRet_X=sum_(M,p<=B) V_p(M)^2` with V=(U-1)_+. By Cauchy-Schwarz,

`Rmin_X² <= [(X/2)*sum_(odd primes p<=B) p²] * ZminRet_X`.

By prime-number-theorem partial summation `sum_(p<=B) p²=(1/3+o(1))*B³/log B`; since `B²~7X`, any no-twin dyadic window would require

`ZminRet_X/(X*B*log B) >= 243/25088 - o(1) = 0.0096859056...`.

Therefore a THIRD sufficient condition, still OPEN, is

`BOXED: liminf_(dyadic X->infinity) ZminRet_X/(X*B*log B)<243/25088`. (C6)

This is an all-primes, one-minimal-owner-per-event moment and needs no LOW17 finite state estimate. It differs from Issue #4's *high q>=19*, all-label source moment `Z_X=sum N_q²`, whose earlier no-sink fixed constant is `81/25088`. Neither statistic dominates the other as needed for these thresholds; the distinct numbers must not be compared as if their source distributions were identical. At tested X<=262144, ZminRet/(XB logB) remains above 243/25088, principally owing to frequent minimal label 3; hence the raw C4/C5 clock-return budgets are a better immediate focus than this alternate C6 moment.

## 5. Reproducible finite audits and independent original-GCD oracle

`research/twin_prime_minimum_clock_audit.cpp` generates EXACT event-jump parity-specific clipped GCD histories for all odd M in each window and checks C1 on every event; sourcewise cutoff/horizon, actual prime endpoints and terminal sqrt certificate, and aggregate first/return time identities. The independent `research/twin_prime_minimum_clock_literal.py` instead evaluates the raw parity-specific gcd at EVERY integer n (including d=1 steps) and reproduces all counts and moments for X256/512/1024/4096.

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_minimum_clock_audit.cpp -o /tmp/min_clock
/tmp/min_clock 256 512 1024 4096 16384 65536 262144
python3 research/twin_prime_minimum_clock_literal.py 256 512 1024 4096
```

| X | total minimum-owned first weight Fmin | repeat weight Rmin | first time | repeat time Treturn | ZminRet | terminal twin starts |
|--:|--:|--:|--:|--:|--:|--:|
| 256 | 6,626 | 4,207 | 4,965 | 3,960 | 3,509 | 127/128 |
| 512 | 14,987 | 6,176 | 8,040 | 4,364 | 6,942 | 256/256 |
| 1024 | 32,225 | 10,640 | 20,964 | 9,325 | 10,648 | 512/512 |
| 4096 | 290,960 | 92,301 | 189,369 | 83,597 | 123,521 | 2048/2048 |
| 16384 | 2,014,723 | 678,809 | 1,393,520 | 582,420 | 1,302,871 | 8192/8192 |
| 65536 | 15,334,280 | 3,257,705 | 11,397,049 | 2,793,148 | 6,419,747 | 32768/32768 |
| 262144 | 112,443,814 | 19,294,492 | 81,775,536 | 16,242,087 | 44,204,878 | 131072/131072 |

At X262144, the observed ratio `Rmin/X²=0.000280772`, versus the sufficient target `9/32=0.28125`; `Treturn/X²=0.000236353`, versus `9/16=0.5625`. These exceptionally wide finite margins are diagnostics ONLY, not a proof that any uniform asymptotic inequality holds. The min-label second-moment ratio is instead `ZminRet/(XB logB)=0.017256867`, above its threshold `0.009685906` at this X.

## 6. Next specific analytic obstruction

The main remaining input is now **source-averaged recurrent minimal-clock travel** `Treturn_X`, not weighted multi-prime collisions. A useful exact first-return object is the leave-q-out shadow from Issue #4, but it must be coupled to the selection event that q is the *smallest* factor at its return. Track this selection with a tagged return operator on actual source states; bound `sum_(source,minimum-q RETURN) elapsed gap` rather than unweighted counts or unrestricted p/q pair collisions. For q<=17, the finite LOW17 low-only certificate can provide separate charging bounds, but C4/C5 themselves do not depend on that certificate.

Research result **PARTIAL**: elementary new conditional reductions C4-C6, reproducible finite checks and independent literal oracle, no Lean compilation, no asymptotic estimate, and no unconditional twin-prime proof.