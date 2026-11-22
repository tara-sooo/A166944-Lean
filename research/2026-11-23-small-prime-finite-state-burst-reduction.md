# A166944: finite-state low-prime bursts and a high-prime interruption reduction

Date: 2026-11-23 JST. Assigned [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [Issue #1](https://github.com/tara-sooo/A166944-Lean/issues/1); branch `research/issue-4-terminal-survivor-positive-budget`. Continues `2026-11-23-adaptive-screened-clock-moment-and-survival-audit.md`. **The symbolic decomposition and interruption inequality are paper mathematics; the four finite-state acyclicity/burst lengths are computational certificates from a compiled C++17 exhaustive verifier, not Lean-kernel theorems. The needed asymptotic high-prime event estimate and the twin-prime/A166944 conjectures remain OPEN.**

## 1. Arbitrary-state finite-state restricted wheel

Let `S` be a finite set of odd primes, `P=product(S)`, `T=2P`. At any integer clock origin `t` and even state `C`, define the next nonunit event of the original parity-specific squarefree wheel using only `S` by the earliest individual active q clock:

- if q divides C-1, its clock is the least even n>t satisfying n=0 (mod 2q);
- if q divides C+1, its clock is the least odd n>t satisfying n=q+2 (mod 2q).

If no q in S divides (C-1)(C+1), there is no further nonunit event. If n is the minimum clock across active primes, the squarefree increment is `d=product({q in S: next_clock(q)=n})` and the new event origin/state are `(n,C+d-1)`. Both time and state update depend only on `(t mod 2P, C mod 2P)`, with C even. There are exactly `(2P)*P=2P^2` such states; each has either one successor or no successor. The modulus contains the time parity, and because d is odd the even-state parity is preserved. The event clock congruences are **the original parity-specific GCD**, not an altered recurrence.

For an arbitrary initial state/time, if this functional directed graph has no directed cycles, the restricted wheel always stops; its maximal event count is the maximum directed path length to a sink, denoted `F(S)`. A cycle would be a nonterminating modular orbit and would invalidate this particular finite-burst claim for arbitrary inputs.

## 2. COMPLETE finite graph computations, with a bounded certificate

The standalone C++17 `small_prime_burst_audit.cpp` computes every successor for every state, performs independent direct parity-GCD first-event checks at deterministic spaced samples, removes vertices in topological indegree order, **rejects if any cycle remains**, and computes longest-event paths backwards. It requires no random simulation or chosen canonical seed to certify the finite graph. All four groups passed:

| S | P | total states 2P^2 | sink states | cycles | maximum nonunit events F(S) |
|:--|--:|--:|--:|--:|--:|
| {3} | 3 | 18 | 6 | 0 | 2 |
| {3,5} | 15 | 450 | 90 | 0 | 5 |
| {3,5,7} | 105 | 22,050 | 3,150 | 0 | 9 |
| {3,5,7,11} | 1,155 | 2,668,050 | 311,850 | 0 | 22 |

For S={3,5,7,11}, a state attaining the 22-event maximum has `t=813 (mod 2310)`, `C=1552 (mod 2310)`. It is an *arbitrary modular state* witness, not a claimed canonical M path. These finite checks supply a self-contained exact-enumeration research checkpoint; no proof of a general all-S acyclicity theorem is asserted.

## 3. NEW deterministic high-prime interruption lemma (paper)

Fix `Q=11` and the full canonical B-wheel, `B>=11`, on an odd start M. Let `E_B(M)` be all nonunit events up to the usual cutoff, and let `T_{>11}(M)` be the number of those events with at least one factor `q>11` in their squarefree increment. For each such large-containing event, cut the event sequence immediately before and after it. All events in each intervening block use **only** primes in `{3,5,7,11}`. Starting from the exact state and clock immediately after the previous large-containing event (or the initial canonical state), this block is an initial segment of the *restricted* wheel trajectory. If a future >11 clock cuts that segment short, the preceding restricted-wheel events still agree by the first-divergence/clock argument. Therefore, the verified `F({3,5,7,11})=22` caps every such block at 22 events. There are T_{>11}(M)+1 blocks, so

    BOXED: E_B(M) <= 22*(T_{>11}(M)+1) + T_{>11}(M)
                  = 22+23*T_{>11}(M).                        (A1)

The same reasoning applies to any finite subset S whose finite graph has an independently established maximal depth F(S), with all non-S-prime-containing events treated as interruptions:

    E_B(M) <= F(S) + [F(S)+1]*T_outside_S(M).                (A2)

This is the point of the new route: many small-prime events are deterministic bounded bursts, so one needs only control interruptions due to larger prime factors. The A1 inequality is a conditional mathematical consequence of a **completely enumerated** finite graph property, independent of assumptions on the adaptive distribution of clock phases.

## 4. Exact canonical original-GCD finite audit

The same verifier recomputes the full original parity-specific squarefree B-wheel on EVERY odd M in `[X,2X)`, classifies each event by whether its increment contains a prime >11, checks A1 per start, checks the maximum small-only burst ≤22, and matches exact historical event/growth regression values.

| X | B | starts | total nonunit events | containing a prime >11 | fraction with q>11 | max small-only consecutive burst |
|--:|--:|--:|--:|--:|--:|--:|
| 4096 | 170 | 2,048 | 29,349 | 7,675 | 26.15% | 18 |
| 16384 | 339 | 8,192 | 171,428 | 45,343 | 26.45% | 18 |
| 65536 | 678 | 32,768 | 795,689 | 224,221 | 28.18% | 21 |

Finite proportions are not asymptotic upper bounds. In particular, the fraction 26–28% could vary with X. The crude A1 numerical bound is not tight but removes the need to analyze the independent long-run survival of the smallest four primes directly.

### A bounded transient before a rough frozen plateau

For the fixed small set `{3,5,7,11}`, every restricted-wheel nonunit increment is at most `P=1155`. During a restricted low-prime run, the next event is within `2a<=22` time steps when the active set is nonempty, and the run contains at most 22 events. Consequently, starting from **any** even state/time, if no high-prime event interrupts it, the low-prime transient ends in **at most 484 clock steps** and changes the state by **at most `22*(1155-1)=25,388`**. At its endpoint the frozen even state `C` satisfies `gcd(1155,(C-1)(C+1))=1`. These very coarse constant bounds do not depend on X.

This yields a further exact qualitative decomposition between consecutive events that carry prime q>=13: either the next large event interrupts a bounded (<=484-step) small-wheel transient, or the small wheel has already relaxed to an **11-rough frozen state** and the next event is won by a prime >=13 from that plateau. It suggests attacking the adaptive large-prime count through a *finite-state relaxation map plus a rough-state sieve* rather than through all high/low prime clocks simultaneously. No quantitative distribution theorem for the resulting adaptively selected relaxed states is proved.

### NEW CRT counting lemma for the FIRST large-prime event (paper, relying on the finite F=22 certificate)

Let `N=X/2` be the number of canonical odd M, and write `C_j^(11)(M)` for the j-th plateau state (including the initial and final plateau) of the unrestricted-in-time `{3,5,7,11}`-only wheel from the canonical seed. By F=22, at most 23 plateau states occur. Given an odd residue `r=M mod 2310`, the event clock choices and all successive small-prime increments depend only on `(t=M+2 mod 2310,C=2M−2 mod2310)`. Therefore for every j along that residue-class path,

    C_j^(11)(M)=2M−2+h_j(r)

for an even integer `h_j(r)` independent of M in this residue class. For any odd prime `q>=13`, `gcd(q,2310)=1`, so each condition `q|C_j^(11)(M)−1` or `q|C_j^(11)(M)+1` selects exactly one residue class of M modulo q inside that fixed r class. There are at most 1155 odd r classes, 23 plateaus per class and two signs. Let `A_q(X)` be the number of M for which q divides either neighbor at SOME plateau of the small-only wheel. CRT yields the explicit universal bound

    BOXED: A_q(X) <= 46*N/q + 46*1155
                    = 23*X/q + 53,130.                       (CRT1)

This is a UNION upper bound; overlapping plateaus/residue classes only reduce the left side. Sum with weights q and use `pi(B)=O(B/log B)`, `sum_{q<=B}q<=B*pi(B)` and `B²=Theta(X)`:

    BOXED: sum_{13<=q<=B prime} q*A_q(X)
           <= 23*X*pi(B)+53,130*B*pi(B)
           = O(X*B/log B).                                   (CRT2)

If a full-wheel trajectory has a FIRST event whose increment contains at least one q>=13, all earlier events were small-only, hence follow an initial segment of the restricted wheel. Each q>=13 in that first large event is therefore included in the corresponding `A_q` set. Thus its total **large-prime-factor weight**, summed across all M at the first large event only, is bounded by (CRT2). This is an exact first-wave arithmetic estimate and requires NO equidistribution of adaptively generated full-wheel plateaus. The analogous estimate for the SECOND and later large events remains OPEN: their restart states depend on earlier high-prime hits and are not periodic functions of M modulo 2310 alone.

## 5. Explicit new sufficient OPEN target

Let `N_X=X/2` starts and `T_X=sum_(M in I_X) T_{>11}(M)`. Sum A1 over M:

    E_total(X) <= 22*N_X +23*T_X = 11X+23T_X.              (A3)

Earlier **unconditional paper** squarefree travel/horizon estimate is

    W_X <= 3X+4B E_total(X), with B=ceil(sqrt(7X)).        (A4)

Therefore either `T_X=o(XB)` or the more convenient stronger **OPEN** bound

    BOXED: T_X = O(X*pi(B)) = O(X*B/log B)                (A5, OPEN)

would imply `E_total=o(XB)` and `W_X=o(X^2)`, whence infinitely many twin primes by the existing squarefree sqrt-wheel certificate. No proof of (A5) is supplied. It remains an adaptive-prime-clock sieve question, but no long chains of small primes need to be handled in the high-prime counting stage.

A different useful **conditional** route is to establish for a slowly growing cutoff Q a general all-state acyclicity theorem with a quantitative `F(Q)=X^{o(1)}`, and then estimate the total >Q interruption count by `o(XB/F(Q))`. The small finite-state values 2,5,9,22 suggest a tractable growth rate but do not prove acyclicity or a quantitative F(Q) bound for any larger Q. The graph size 2*(product_{p<=Q}p)^2 grows exponentially with Q, so straightforward exhaustive checks cannot scale indefinitely.

## 6. Reproduction and evidence classification

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/small_prime_burst_audit.cpp -o /tmp/small_prime_burst_audit
/tmp/small_prime_burst_audit 4096 16384 65536
```

- **Paper algebra:** prime-clock state sufficiency modulo 2P, high-prime interruption inequality A1/A2, and implications A3–A5.
- **Computationally exhaustive finite verification:** every restricted state for sets through {3,5,7,11}, full canonical window regression scans of specified finite X.
- **OPEN:** uniform acyclicity/quantitative F(Q) for unbounded Q; `T_X=o(XB)` or A5; twin-prime infinitude; original stronger OEIS A166944 conjecture.

No new Lean kernel theorem was compiled and the main branch is untouched. These results should remain on assigned research Issue #4.
