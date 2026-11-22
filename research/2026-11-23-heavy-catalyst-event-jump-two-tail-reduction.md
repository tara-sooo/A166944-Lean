# A166944: stress-testing the heavy-catalyst bound and reducing growth to event count plus oversized jumps

Date: 2026-11-23 JST. Assigned research Issue #4 (parent Issue #1), branch `research/issue-4-terminal-survivor-positive-budget`. This continues `research/2026-11-23-sieve-away-light-catalysts-and-high-weight-tail.md`. The inequalities here are elementary *paper-level proofs*, not Lean kernel declarations. The reported scans are finite C++17 original-parity squarefree-clipped GCD tests, not asymptotic bounds. Neither twin-prime infinitude nor `OeisA166944.conjecture` has been established.

## 1. Definitions

For even X>=256, set `B=ceil(sqrt(7X))`, `I_X={odd M: X<=M<2X}`, `s=M+2`, `K=floor((7M-1)/4)`. Start the wheel with `C(s)=2M-2` and increments `d_B(n)=gcd(L_B,g(n,C(n-1)))`, where the raw original parity GCD is `gcd(n,C-1)` for even n and `gcd(n-2,C+1)` for odd n, and L_B contains each odd prime <= B just once. Let `E_B(M)` be the count of nonunit increment events `d_B(n)>1` before K; let `D_B(M)` be the maximum event increment (1 when no event); and let `G_B(M)=sum_{events}(d_B(n)-1)`.

Define the *initial catalyst weight* `w0(M)=sum_{p<=B odd prime, p | (2M-3)(2M-1)}(p-1)` and light/heavy boundary `y=(log X)^2`, with natural logarithm. The previous paper note proves `# {M: w0<=y}=o(X)` and its terminal growth total o(X²), using a smooth-number argument. It also gives the still-open sufficient heavy-source condition `#{M: w0>y and G_B>B*w0}=o(X)`.

## 2. New paper-level event budget and two obstruction sets

For every event with increment d>=3, write `u(d)=(d-1-B)_+`. The scalar inequality `d-1 <= B+u(d)` yields the **exact global upper budget**

    G_B(M) <= B*E_B(M) + U_B(M),
    U_B(M)=sum_events (d-1-B)_+.

Thus, if `E_B(M)<=w0(M)` and `D_B(M)-1<=B`, then `G_B(M)<=B*w0(M)`. In particular, for any X,

    {M: w0(M)>y, G_B(M)>B*w0(M)}
       subset {M: w0>y, E_B(M)>w0(M)}
              union {M: w0>y, D_B(M)-1>B}.

Consequently, proving both exceptional counts on the right `o(X)` would establish the previously OPEN heavy-root tail H1, hence twin-prime infinitude via the squarefree terminal certificate. This does **not** assert either rarity bound and does not bound individual oversized-jump amplitudes.

Summing over all starts, define

    E_total(X)=sum_M E_B(M),
    U_total(X)=sum_M sum_events (d-1-B)_+,
    W_X=sum_M G_B(M).

Then

    BOXED: W_X <= B*E_total(X) + U_total(X).

A **different OPEN sufficient pair**, requiring no initial weights or stagewise signed responses, is

    E_total(X)=O(X (log X)^A) for some fixed A,
    U_total(X)=o(X²).

Because B=Theta(sqrt X), these imply W_X=o(X²), hence infinitely many twin primes by the already documented squarefree terminal prime certificate. One can replace the polylog event-count bound by any `E_total=o(XB)`. The oversized surplus bound is essential: the clipped increment can be a squarefree composite product greater than B, despite every prime factor being at most B.

## 3. New paper-level two-tail criterion with free exponent trade-off

Let `alpha,beta>0` be fixed and `alpha+beta<2`. Define

    A_X(alpha) = {M: E_B(M)>B^alpha},
    C_X(beta)  = {M: D_B(M)-1>B^beta}.

For M outside their union, all nonunit increments satisfy d-1<=B^beta, so `G_B(M)<= B^(alpha+beta)`. The canonical horizon bound gives `G_B(M)<=3X` for all starts. Therefore

    BOXED: W_X <= (X/2)*B^(alpha+beta)
                    +3X*(#A_X(alpha)+#C_X(beta)).

Hence, **for any fixed alpha+beta<2**, the two OPEN rare-tail statements `#A_X(alpha)=o(X)` and `#C_X(beta)=o(X)` imply twin-prime infinitude. The choice alpha=3/4, beta=6/5 has sum 39/20=1.95. A stronger fully uniform statement about these two counts would imply a terminal certificate for every large start, but is not asserted.

In a finite C++ probe, counts use the slightly stronger event test `D_B>B^beta`, rather than `D_B-1>B^beta`. This only makes the reported exclusion set larger. We do not infer any asymptotic tail from zero counts at a finite scale.

## 4. Critical audit finding: apparent high-root pointwise success was non-discriminating

The earlier dyadic scans through X262144 found *no heavy-weight counterexample* to `G_B<=B*w0`. We extended the exact original-GCD scan through eight-million scale and many off-dyadic X. The reason the test always passed in this range is **simpler**: for every tested X, the global maximum over *all* starts already satisfies `max_M G_B(M) < B*(log X)^2`. Thus `w0>(log X)^2` automatically implies `G_B<B*w0` in these finite ranges, without exploiting any root-weight/GCD correlation. The finite success is genuine, but is not direct evidence of a special weight-amplification mechanism.

| even X | B | number of starts | global maximum G | max G/[B(log X)^2] | all G>B*w0 exceptions | heavy exceptions |
|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | 170 | 2,048 | 1,180 | 0.1003 | 29 | 0 |
| 16,384 | 339 | 8,192 | 4,736 | 0.1484 | 79 | 0 |
| 262,144 | 1,355 | 131,072 | 13,946 | 0.0661 | 446 | 0 |
| 1,048,576 | 2,710 | 524,288 | 19,142 | 0.0368 | 790 | 0 |
| 8,388,608 | 7,663 | 4,194,304 | 79,106 | 0.0406 | 3,521 | 0 |

Off-dyadic exact scans include X=500000,750000,1000000,1500000,1999998,3000000,6000000, all with zero heavy violations. Those additional finite tests do not strengthen the open universal claim.

## 5. Finite event and oversized-increment audit

Source `research/heavy_tail_event_budget_audit.cpp` computes the full canonical original-parity clipped wheel by independently constructed exact *next-prime-clock* event jumps; independently validates small starts against literal stepwise GCD; rechecks stored full-growth/initial-weight/exception regressions; and reports global event counts and oversized increments. Every start in every X row is enumerated, not sampled.

`highD` means at least one event with `d-1>B`; `overB` is the total **excess** `sum(d-1-B)_+`, not total growth of those events. `EgtLog2` counts trajectories with E>(log X)^2, and `EgtB^.75`, `DgtB^1.2` use the numerical thresholds. The latter pair is only a finite test of the sufficient alpha,beta criterion.

| X | mean event count | total events | overB | overB/W | # E>log² X | # highD | # E>B^.75 | # D>B^1.2 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | 14.3306 | 29,349 | 13,980 | 3.50% | 4 | 98 | 46 | 4 |
| 16,384 | 20.9263 | 171,428 | 102,054 | 3.50% | 119 | 162 | 203 | 96 |
| 262,144 | 31.1501 | 4,082,904 | 1,555,957 | 1.12% | 1,566 | 1,231 | 72 | 0 |
| 1,048,576 | 35.4486 | 18,585,269 | 1,756,272 | 0.203% | 1,912 | 1,022 | 1 | 0 |
| 8,388,608 | 48.2522 | 202,384,319 | 34,633,241 | 0.211% | 22,798 | 5,849 | 0 | 0 |

For the heavy set at X8388608, 383 sources have E>w0, 3,684 have an increment d-1>B, and their union contains 4,040 sources out of 4,194,304 (0.0963%). Actual heavy `G>B*w0` exceptions are zero. The union is a **sufficient exceptional superset**, not an equality. The average event count rose slowly with scale, and oversized surplus was very small relative to W, but no uniform polylogarithmic or rare-jump theorem has been proved.

## 6. What remains genuinely missing

This checkpoint creates a new, clear alternative to the initial-root heavy conjecture: control `E_total` (mean count of nonunit events) and `U_total` (cost of unusually large *squarefree composite* GCD increments). The second part should exploit the requirement that several odd primes divide the same raw parity GCD at an event; the first should exploit the p-refire recharge/disarming structure without double-charging across primes. Existing collision geometry by itself cannot control the adaptive residue dependencies, as the previous artificial sawtooth counterexample shows.

The finite scans show a scaling opportunity, but the event-count/oversized-jump estimates remain OPEN. None of the proposed uniform high-root pointwise condition, H1, global second moment, twin-prime infinitude or original OEIS A166944 conjecture has been proved here. No Lean kernel check or change to main branch occurred.

### Reproduce

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/heavy_tail_event_budget_audit.cpp -o /tmp/heavy_tail_event_budget_audit
    /tmp/heavy_tail_event_budget_audit 4096 16384 262144 1048576 8388608
    /tmp/heavy_tail_event_budget_audit 500000 524288 750000 1000000 1048576 1500000 1999998

Memory use increases with the maximum X in a command because the SPF sieve spans up to 8*maxX; for max X8388608 it required about 264 MB and approximately 25 seconds on this run for a five-X command. The full scanner accepts any even 256<=X<=10000000 and retains exact preexisting regression constants at four scales. Compiler tested with `g++ -std=c++17 -O3 -Wall -Wextra -Werror`. The output is a finite diagnostic, not a proof of a uniform growth estimate.
