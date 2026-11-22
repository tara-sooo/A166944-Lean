# A166944: seed-catalyst amplification, rare-avalanche density, and weighted terminal energy

2026-11-23 JST. Assigned research Issue #4 (parent #1); branch `research/issue-4-terminal-survivor-positive-budget`. All unconditional reductions below are **paper proofs, not Lean-checked**. All numerical claims are finite original parity-specific squarefree-clipped GCD audits, with independent modular root counting and literal-step spot checks. The uniform tail/energy conditions, twin-prime infinitude, and original A166944 conjecture remain OPEN.

## 1. Initial seed weight has an arithmetic first moment

Let even `X>=256`, `B=ceil(sqrt(7X))`, `I_X={M odd: X<=M<2X}`. For the canonical squarefree wheel let `G_B(M)` be its nonnegative terminal growth at `K(M)=floor((7M-1)/4)` from `D(M+2)=2M-2`. Define initial catalyst set and weight:

    T(M) = {odd prime p<=B : p | (2M-3)(2M-1)},
    w0(M) = sum_{p in T(M)} (p-1),
    R_X = sum_{M in I_X} w0(M),
    W_X = sum_{M in I_X} G_B(M).

The previously proved per-source preloading lemma shows that the wheel using **only primes not in T(M)** never moves. More directly, if `w0(M)=0`, neither initial neighbor `C0-1,C0+1` has an allowed factor; hence no event can happen at any time and `G_B(M)=0`. Since `K(M)-(M+2)>=2B` for these X, the converse holds too: every initially active prime has a parity clock at most 2p<=2B steps after M+2, so `w0(M)>0` entails positive full-wheel growth. Thus

    G_B(M)=0  iff  w0(M)=0.                         (S1)

Write `M=X+1+2j`, `0<=j<N=X/2`. For every odd prime p, the conditions `p|(2M-3)` and `p|(2M-1)` determine two DISTINCT residues `j mod p`. Thus their combined number is `2N/p+O(2)=X/p+O(2)`, and exactly

    R_X=sum_{3<=p<=B prime}(p-1)*(X/p+O(2))
       =O(X*pi(B)+sum_{p<=B}p)
       =O(X*B/log B),                                (S2)

since B^2=Theta(X). No dynamics, independence, or full-primorial CRT period enters S2. The reproducible C++ checks R_X by **both** direct per-source trial division and separate modular residue counts.

## 2. First new sufficient theorem: rare amplification, not pointwise domination

The same horizon envelope gives `0<=G_B(M)<=3X` for M in I_X. Define

    E_X=#{M in I_X : G_B(M)>B*w0(M)}.

The good sources cost at most B*R_X; the bad sources are at most 3X each. Consequently,

    BOXED: W_X <= B*R_X + 3X*E_X.                  (S3)

Using S2 and B^2=Theta(X), the following unproved weak tail hypothesis suffices for twin-prime infinitude by the existing squarefree terminal certificate:

    E_X=o(X) along arbitrarily large even X.      (OPEN TAIL)

The stronger quantitative `E_X=O(X/log B)` would give `W_X=O(X^2/log B)`. A **uniform pointwise** estimate `G_B(M)<=B*w0(M)` is FALSE already at X1024,M1091: w0=2, B=85, G_B=370>170. At X16384,M30845, w0=2, B339, G_B=3892>678. Thus the exceptional set is essential. The ratio W_X/R_X is a ratio of total sums, **not** the mean of individual G_B(M)/w0(M).

## 3. Second new sufficient theorem: one weighted terminal second moment

Define, with zero terms at w0=0,

    Z_X=sum_{M in I_X, w0(M)>0} G_B(M)^2/w0(M).

Cauchy-Schwarz and S1 imply

    BOXED: W_X^2<=R_X*Z_X.                         (S4)

Consequently a single **OPEN** unbounded-scale estimate

    Z_X=O(X*B^3)                                  (OPEN ENERGY)

would yield `W_X=O(X*B^2/sqrt(log B))=o(X^2)`, hence infinitely many twin primes via the existing certificate. The observed energy appears smaller, of order `X*B^2`, but this is finite data only. Compared to the earlier old-wheel-response energy `Q_X` this uses just the **terminal full-wheel growth**, with no insertion ordering or signed stage bookkeeping. The tradeoff is a potentially severe small-denominator weight for sources whose initial catalyst is only p=3.

## 4. Exact finite original-GCD audit

`seed_catalyst_amplification_audit.cpp` compiles with g++ C++17 `-O3 -Wall -Wextra -Werror`; it scans all odd M in each interval, independently checks the direct root sum against an exact modular-residue count, spot checks event jumps against step-by-step gcd for M=7..119, checks S3, and asserts the stored full-wheel growth and exceptional-count regressions.

| X | B | R_X | W_X | W_X/R_X | E_X (G>B w0) | E_X/(X/2) | Z_X/(X B^2) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 512 | 60 | 7,544 | 20,048 | 2.6575 | 6 | 2.34% | 0.2420 |
| 1,024 | 85 | 21,450 | 39,940 | 1.8620 | 5 | 0.98% | 0.0871 |
| 4,096 | 170 | 149,886 | 399,142 | 2.6630 | 29 | 1.42% | 0.1071 |
| 8,192 | 240 | 406,116 | 1,084,898 | 2.6714 | 57 | 1.39% | 0.0988 |
| 16,384 | 339 | 1,072,888 | 2,915,326 | 2.7173 | 79 | 0.96% | 0.1039 |
| 32,768 | 479 | 2,929,084 | 6,569,168 | 2.2427 | 91 | 0.56% | 0.0442 |
| 65,536 | 678 | 7,889,844 | 19,826,998 | 2.5130 | 219 | 0.67% | 0.0524 |
| 131,072 | 958 | 20,881,044 | 45,835,016 | 2.1951 | 212 | 0.32% | 0.0266 |

The exceptional fractions fluctuate, and their finite small size does **not** prove a density-zero theorem. Pointwise G/w0 can be huge (e.g. 1946 at X16384,M30845); total-mass amplification remains around 2–3 at these finite scales.

## 5. Proof strategy and limitation

S3 suggests proving a rare-avalanche statement by analyzing the **first crossing** of growth over B*w0, perhaps via an encoding of the catalyst-triggered sequence of GCD events. A single small initial catalyst p=3 can lead to multiple induced prime hits, as previous exact cascades show, so neither number of initial catalysts nor first-hit total cost controls growth pointwise. The earlier artificial phase-concentration counterexample also prevents inferring the needed tail from collision geometry alone. A bound on the density of trajectories with long induced cascades, or on the weighted terminal moment Z_X, must exploit actual parity-specific clock dynamics and the dependencies among prime events.

This route targets twin-prime **infinitude** via the conditional squarefree terminal certificate only. Proving original `OeisA166944.conjecture` would need a separate bridge from twin-prime existence to the specified record values. No new Lean build; main unchanged.

### Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/seed_catalyst_amplification_audit.cpp -o /tmp/seed_catalyst_amplification_audit
for X in 512 1024 4096 8192 16384 32768 65536 131072; do /tmp/seed_catalyst_amplification_audit "$X"; done
```
