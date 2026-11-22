# A166944: exact p-perturbation response, old-clock activation, and a global second-moment reduction

Date: 2026-11-23 JST. Assigned [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4) (parent #1). Research branch `research/issue-4-terminal-survivor-positive-budget`. This builds directly on `2026-11-23-terminal-survivors-positive-budget.md` and is mathematically separate from the four-residue correlation work in Issue #3.

**Evidence:** All identities and the sufficient conditions in Sections 1–4 are elementary proofs **on paper, not Lean-kernel theorems**. Numerical observations and the explicit small witness are from compiled original-parity clipped-GCD C++17, with a separate literal stepwise-GCD cross-check, full source-level telescoping and exact stored regressions. Neither the stage bootstrap, the global direct-injection bound, nor the global response second-moment bound is proved uniformly in X. The twin prime and OEIS A166944 problems remain open.

## 1. Exact signed perturbation formula (all heights, refires and early splits)

Fix any even `X>=256`, common cutoff `B=ceil(sqrt(7X))`, and an odd prime `p<=B`. Let `L` be the product of all odd primes strictly below p, so `L*p` is the newly enlarged squarefree wheel. Let `I_X={M odd: X<=M<2X}`, `s=M+2`, `K(M)=floor((7M-1)/4)`; both trajectories begin with `D(s)=2M-2` and use the SAME cutoff.

For an even state `C` just before step `n`, define

    g(n,C) = gcd(n,C-1)          if n even,
           = gcd(n-2,C+1)      if n odd,
    e_L(n,C)=gcd(L,g(n,C)).

Write the old/new pre-step states as `C_o(n)=D_L(n-1)`, `C_n(n)=D_{Lp}(n-1)` and define

    I_p(n,M) = 1 if p | g(n,C_n(n)), else 0.

Since `gcd(p,L)=1` and the wheel is squarefree, the exact new increment is

    d_Lp(n) = e_L(n,C_n(n)) * [1+(p-1)*I_p(n,M)]

and the exact old increment is `d_L(n)=e_L(n,C_o(n))`. Therefore, with summation over `s<n<=K(M)`, set

    J_p(M) = (p-1)*sum_n I_p(n,M)*e_L(n,C_n(n))  >= 0,
    R_p(M) = sum_n [e_L(n,C_n(n))-e_L(n,C_o(n))]  (SIGNED).

**Lemma 1 (unconditional finite identity):**

    BOXED: Delta_p(M) = G_Lp(M)-G_L(M) = J_p(M)+R_p(M).

This exact decomposition contains all post-freeze deficit heights, positive and negative pre-freeze costs, and all repeated p-hits. It preserves cancellations in `R_p(M)` until the *terminal* cutoff; do not replace it by timewise absolute differences.

**Lemma 2 (activation is determined by the OLD trajectory):** Let `A_p(M)=1` iff the new Lp trajectory ever has a p-divisible increment before K. Starting from equal horizons, the trajectories cannot first diverge unless `p | g(n,C_o(n))`. At that first p-clock, they agree immediately before n and the new increment is exactly p times the old one; hence

    BOXED: A_p(M)=1  <=>  exists s<n<=K(M) with p | g(n,D_L(n-1)).

The FIRST p-hit clock is readable solely from the old L trajectory, plateau by plateau. No assumption on the p-stage's future dynamics is made. When A_p(M)=0, the paths are identical and J_p(M)=R_p(M)=Delta_p(M)=0.

**Explicit positive-response witness:** M=127, p=11, L=3*5*7. The literal old-wheel trajectory has `G_L(127)=0`. The enlarged wheel's only p-divisible hit is `(n,d)=(145,11)`, followed by `(150,3),(157,5),(162,3)`; `K(127)=222`. Thus `G_Lp(127)=18`, `J_11(127)=10` and `R_11(127)=8>0` although the entire old growth is zero. Therefore a pointwise bound `R_p(M)_+ <= C*G_L(M)/p` fails for **every** C, even at p>=11. A bootstrap statement requires an additional additive term or a genuine average-dispersion property.

## 2. A new unconditional activation–response second-moment inequality

For fixed p define

    P_p(X) = sum_(M in I_X) [Delta_p(M)]_+,
    J_p(X) = sum_(M in I_X) J_p(M),
    N_p(X) = #{M in I_X : A_p(M)=1},
    Q_p(X) = sum_(M in I_X) [R_p(M)]_+^2.

Since `[J+R]_+ <= J+[R]_+` for J>=0, and the response vanishes when the p-hit never happens, Cauchy--Schwarz on the activated sources gives

    BOXED: P_p(X) <= J_p(X) + sqrt(N_p(X)*Q_p(X)).             (A)

This is NOT conjectural. It includes even p-stages with no terminal positive sources, negative old-response, multiple p-hits, completed/reopened episodes, and post-freeze heights k>=1.

A **sufficient but OPEN** three-part uniform stage hypothesis is

    J_p(X) <= C*X*sqrt(p),
    N_p(X) <= C*X/p,
    Q_p(X) <= C*X*p^2,

with a fixed C independent of X,p. It implies `P_p(X)=O_C(X*sqrt(p))`, hence `P_X=O_C(X*B^(3/2)/log B)=o(X^2)`, and the existing squarefree terminal certificate yields infinitely many twin primes. The exact density `1/p` is not mandatory: more generally `N_p=O(X*p^{-a})` and `Q_p=O(X*p^b)` suffice provided `(b-a)/2<1` and the direct term has some fixed power saving below p.

A bootstrap-compatible alternative is the OPEN hypothesis

    N_p(X) <= C*X/p,
    Q_p(X) <= C*(X*p^2 + W_(p^-)(X)^2/(X*p)),
    J_p(X) <= C*X*sqrt(p),

where `W_(p^-)=sum_M G_L(M)`. Indeed (A) and `sqrt(a+b)<=sqrt(a)+sqrt(b)` imply

    P_p(X) <= C'*X*sqrt(p) + (C'/p)*W_(p^-)(X).

The ensuing prime-stage bootstrap has a rigorously proved sufficient consequence, but its dynamical input is OPEN. The tradeoff is that `Q_p` is a terminal **signed response** second moment, not a raw sum over times.

## 3. Stronger result: aggregate over ALL primes before applying Cauchy

Write `J_X=sum_{p<=B}J_p(X)`, `N_X=sum_{p<=B}N_p(X)` and `Q_X=sum_{p<=B}Q_p(X)`. Apply Cauchy again, across prime stages, to (A):

    BOXED: P_X <= J_X + sqrt(N_X*Q_X).                       (B)

There are X/2 starts and at most pi(B) odd-prime stages, so **unconditionally**

    N_X <= (X/2)*pi(B) = O(X*B/log B).

Therefore the following single pair of **global** mean/energy estimates would already prove twin-prime infinitude:

    TARGET G1: J_X = o(X*B^2),
    TARGET G2: Q_X = O(X*B^3).                              [BOTH OPEN]

Proof: By (B), `sqrt(N_X*Q_X)=O(X*B^2/sqrt(log B))=o(X*B^2)`. Since `B^2=Theta(X)`, `P_X=o(X^2)`. One can replace G1 by the more concrete `J_X=O(X*B^(2-delta))` for any fixed `delta>0`; if the raw response energy is `Q_X=O(X*B^2)` as observed, there is an extra factor of B of slack relative to G2.

**This global route does not require** individually proving `N_p=O(X/p)`, any uniform short-interval CRT equidistribution, or a per-prime recursive W_(p^-) bootstrap. The two unknown estimates concern (i) total direct p-injection, and (ii) the squared **terminal** perturbation response.

## 4. Critical bootstrap coefficient and admissible logarithmic losses

If one nevertheless pursues a stagewise recursion, let `W_p=sum_M G_Lp(M)` (nonnegative), `W_1=0`, and suppose for constants `delta>0`, `0<=theta<1`, and `C` that

    P_p(X) <= C*X*p^(1-delta) + C*(log(2p))^theta/p * W_(p^-)(X).

Since `W_p<=W_(p^-)+P_p`, iteration gives

    W_B <= C*X*sum_(p<=B) p^(1-delta)
               *exp(C*sum_(p<=B) (log(2p))^theta/p).

For `0<theta<1`, the last prime sum is `O((log B)^theta)`; for `theta=0` it is `O(log log B)` (elementary prime counting plus partial summation). Consequently the exponential is `B^{o(1)}` and for `0<delta<=1` the resulting mean growth is `W_B=O(X*B^(2-delta+o(1)))=o(X^2)`. Thus even a factor `(log p)^theta/p` with **theta<1** is permissible for arbitrary fixed C.

**Critical distinction:** `(log p)/p` produces `sum_(p<=B)log p/p=Theta(log B)`, so for an unrestricted constant C the multiplicative bootstrap can grow as a positive power of B; this loss cannot be accepted without an additional quantitative restriction. This corrects the tempting but false claim that *any* fixed power of log p in the amplification coefficient costs only `B^{o(1)}`.

## 5. Why the existing horizon-collision energy cannot prove activation dispersion by itself

The old terminal-horizon geometry has `C_i=2M_i-2+h_i`, h_i>=0 even, C_i even and C_i<=2K(M_i), with collision bound `sum_C binom(k_C,2) <= (1/4)*sum_i h_i` derived from that structure. There is an explicit adversarial **artificial** height profile satisfying all these coarse constraints:

For any p>=11 odd and even X sufficiently large with `p<=B`, define for each odd `M_i in [X,2X)` the unique even

    0 <= h_i < 2p,     h_i = (p+1-(2*M_i-2)) mod (2p).

Then `C_i=2M_i-2+h_i` is even and `C_i == 1 (mod p)` for EVERY start, while `sum_i h_i < X*p` and the quadratic collision bound holds automatically. Thus an energy budget of order Xp, plus the collision bound and the horizon envelope, does **not** force even `O(X/sqrt(p))` incidence of `p | C_i-1` in the worst case. This is a counterexample to an inference using only the broad horizon geometry; it is NOT an actual trajectory of the original GCD recurrence.

For X4096,p79 the exact artificial profile has all 2048 starts in the candidate class, W=159,504 and `sum_C binom(k_C,2)=39,138 <= W/4=39,876`. By contrast the actual old p79 wheel has 217 terminal-horizon candidate starts, 231 p-activated starts and positive cost 58,440. The new moment approach must exploit the **actual recurrence**, not solely the universal fibre inequality.

## 6. Reproducible finite audit and limitations

Source: [`perturbation_bootstrap_audit.cpp`](perturbation_bootstrap_audit.cpp), which uses the original parity-specific *squarefree clipped* GCD, with exact event-jumps and independent literal-step verification for odd M7..119/caps1,3,5,7,11,13,17. It checks old-path-only p-clock equivalence against all new p-hit traces; verifies `Delta=J+R` per M,p; verifies the prime-stage telescope; verifies full P and signed-growth regressions; checks the explicit M127,p11 positive response with zero old growth; and checks the artificial sawtooth collision inequality.

| X | B | P_X | signed negative mass | J_X | N_X | Q_X | Q_X/(X B²) | `J_X+sqrt(N_X Q_X)` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 85 | 40,426 | 486 | 27,622 | 1,588 | 1,577,084 | 0.213 | 77,666 |
| 4,096 | 170 | 445,678 | 46,536 | 252,670 | 7,953 | 57,873,748 | 0.489 | 931,102 |
| 16,384 | 339 | 3,439,438 | 524,112 | 1,555,068 | 32,838 | 1,835,546,388 | 0.975 | 9,318,809 |
| 32,768 | 479 | 7,171,394 | 602,226 | 4,038,216 | 66,733 | 2,184,212,120 | 0.291 | 16,111,286 |
| 65,536 | 678 | 21,585,484 | 1,758,486 | 11,295,926 | 140,554 | 12,680,715,456 | 0.421 | 53,513,520 |
| 131,072 | 958 | 49,868,078 | 4,033,062 | 27,961,802 | 285,003 | 25,337,594,692 | 0.211 | 112,939,979 |

Across these six X, the maximum observed `max_p P_p/(X*sqrt(p)+W_(p^-)/p)` is 1.464 (at X4096,p79), with X16384 attaining 1.162 (p173). A broader finite falsification scan of all even X in [256,800], and 161 further non-dyadic/dyadic even X sampled through 8192, found a maximal ratio ~1.916086 at X556,p43, still below the **hypothetical** constant 2. These are finite checks; no uniform mathematical theorem (star-star) follows.

At X4096,p79 the actual p-activated source count was 231 (vs X/p about 51.85), and at X16384,p173 it was 248 (vs X/p about 94.71). The old terminal-horizon candidate counts were 217 and 242, respectively. This explicitly shows activation is adaptive and need not follow an exact 1/p frequency at individual stages; the global bound N_X <= X*pi(B)/2 avoids this question entirely.

A source-level stage diagnostic at X16384,p173 gives `P_p=264,600`, `J_p=42,656`, signed old response `sum_M R_p=221,584`, `N_p=248`, `Q_p=355,936,760`. Here the old response dominates the stage cost. The full X16384 sums have `J_X=1,555,068` and `sum_(p,M)R_p=1,360,258`, yielding exact total final growth 2,915,326. Negative stage costs explain why this final growth is smaller than P_X.

The aggregate upper (B) is about 2–3 times measured P_X across these six sizes, but is already strictly below the finite sufficient bound X²/8 at every listed scale; at X131072 the ratio to X²/8 is about 0.05259. These are numeric *diagnostics*, not an asymptotic theorem.

Build and run:

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/perturbation_bootstrap_audit.cpp -o /tmp/perturbation_bootstrap_audit
    for X in 1024 4096 16384 32768 65536 131072; do /tmp/perturbation_bootstrap_audit "$X"; done

A proposed X262144 run did **not** finish within the bounded audit runtime and is excluded from validated results. No Lean-kernel compilation was made. No source files on main were changed.

## 7. Next concrete proof tasks

1. Prove a global bound on direct p-injection `J_X=o(XB²)`, which is numerically about `(0.22..0.36)*XB` for the six verified scales; a first-stage target `J_p(X)<=C X sqrt(p)` is strong but would suffice.
2. Prove a global terminal-response energy bound `Q_X=O(XB³)`, with an entire factor B of slack above the observed `O(XB²)` scale. Explore arithmetic XOR of old-prime divisibility of the two horizon states, rather than the sum of absolute per-time differences which overcounts completed excursions.
3. The sharper conditional stage moment route is `N_p=O(X/p)`, `Q_p=O(X p²)`. The old-only p-clock characterization permits induction on the old wheel; the explicit artificial sawtooth warns that old growth/collision geometry alone does not force equidistribution.
4. In Lean, first target the finite algebraic identity `Delta=J+R`, old-only first p-clock equivalence, and the global activation-response Cauchy inequality under the pinned Mathlib policy. The open analytic bounds must not be passed as axioms or assumed in a claimed proof.

The existing Issue #4 remains OPEN for an unbounded-X estimate. Issue #1 remains the parent A166944 conjecture tracker. Novelty of the full open problem is not claimed.
