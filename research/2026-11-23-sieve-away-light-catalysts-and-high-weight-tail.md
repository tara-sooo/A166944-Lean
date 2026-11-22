# A166944: sieve away light initial catalysts; reduce twin-prime growth to heavy-root avalanches

2026-11-23 JST, Issue #4, branch `research/issue-4-terminal-survivor-positive-budget`. Continues `2026-11-23-seed-amplification-tail-and-weighted-energy.md`. This note contains a new **paper-level elementary/standard-sieve argument, not a Lean kernel check**, and a finite original parity-GCD audit. The dynamical high-root tail or energy estimate and both twin-prime and A166944 conclusions remain OPEN.

## 1. A genuinely unconditional small-root reduction

For even X>=256 put B=ceil(sqrt(7X)), let I_X contain odd M in [X,2X), and define the initial root weight

    w0(M)=sum_{odd primes p<=B, p|(2M-3)(2M-1)}(p-1),
    G(M)=G_B(M), and y=(log X)^2.

**Lemma (on paper):** the set `L_X={M in I_X: w0(M)<=y}` satisfies

    #L_X = O(X*log log X/log X + X^(3/4+o(1))) = o(X).       (L)

Proof. Put n=2M-1<4X<B^2. If w0(M)<=y, then n has no prime factor p with `p>y+1` and `p<=B`; otherwise p−1>y. Write z=y+1. Because n<B^2, n can have **at most one** prime factor P>B, with exponent one. Therefore either n is z-smooth, or n=d*P with d z-smooth and P>B prime.

The number of z-smooth n<=4X is at most

    Psi(4X,z) <= (4X)^(3/4) * product_(p<=z)(1-p^(-3/4))^(-1)
              <= X^(3/4) * exp(O(z^(1/4)))
              = X^(3/4+o(1)),

by Rankin's elementary weighted counting method (`z=(log X)^2+1`). For n=d*P, the usual Chebyshev upper bound `pi(t)=O(t/log t)` at t>=B gives

    # {dP} <= O(X/log B)*sum_(d z-smooth)(1/d)
            <= O(X/log B)*product_(p<=z)(1-1/p)^(-1)
            = O(X*log z/log B)
            = O(X*log log X/log X),

using the classical Mertens product upper bound. Restriction n=2M−1 for odd M only reduces the count. This proves (L). There is NO assumption about GCD dynamics in this counting lemma.

The original wheel has universal `0<=G(M)<=3X` via C<=2K. Thus

    BOXED: sum_(M in L_X) G(M) <=3X*#L_X = o(X^2).          (L1)

This unconditionally handles **every** trajectory with w0<=log²X, even if its catalytic avalanche is arbitrarily severe up to the known horizon envelope.

## 2. Two narrower sufficient (OPEN) statements

Write H_X=I_X\L_X, and `R_X=sum_M w0(M)=O(XB/log B)` as proved in the predecessor note. The following two alternative UNPROVED dynamic estimates would each suffice for infinitely many twin primes:

**Heavy-root tail criterion**

    #{M in H_X: G(M)>B*w0(M)}=o(X).                        (OPEN H1)

Indeed the nonexceptional high-root growth is at most `B*R_X=O(X^2/log B)`, the high-root exceptional growth is at most `3X*o(X)`, and the low-root portion is already o(X²) by (L1). Hence `sum_M G(M)=o(X²)`.

**Heavy-root terminal second moment criterion**

    Z_hi(X)=sum_(M in H_X) G(M)^2/w0(M)=O(X*B^3).          (OPEN H2)

Cauchy gives `sum_(H_X) G <= sqrt(R_X Z_hi)=O(XB²/sqrt(log B))=o(X²)`; combine with L1. This is a *single full-wheel* weighted energy problem, with no prime-stage signed perturbation bookkeeping. It allows the huge amplification at small initial primes to be discarded from the analytic moment estimate.

The stronger pointwise candidate `G(M)<=B*w0(M)` for all M is already FALSE (X1024,M1091: weight2,G370>B*2=170); H1 is strictly weaker and specifically exempts low-root sources.

## 3. Reproducible finite heavy/light diagnostics

Updated `research/seed_catalyst_amplification_audit.cpp` computes full growth, R_X, heavy/light split, E_X=number with G>B*w0, maximal w0 among all E_X, and Z_hi/(X B²); it checks the direct per-source initial weights against independent modular counts, historical signed-wheel total-growth regressions, the horizon inequality, and literal-step small-start gcd. C++17 `g++ -O3 -Wall -Wextra -Werror` PASS on all 9 indicated dyadic scales. This is finite evidence, not the H1/H2 proof.

| X | B | all exceptional E_X | largest w0 among E_X | light-source count w0<=log²X | heavy energy Z_hi/(X B²) |
|---:|---:|---:|---:|---:|---:|
| 512 | 60 | 6 | 4 | 177 | 0.007538 |
| 1,024 | 85 | 5 | 2 | 330 | 0.003643 |
| 4,096 | 170 | 29 | 4 | 1,241 | 0.004428 |
| 8,192 | 240 | 57 | 6 | 2,339 | 0.003993 |
| 16,384 | 339 | 79 | 12 | 4,505 | 0.004075 |
| 32,768 | 479 | 91 | 6 | 8,629 | 0.001708 |
| 65,536 | 678 | 219 | 8 | 16,334 | 0.001711 |
| 131,072 | 958 | 212 | 6 | 31,513 | 0.000905 |
| 262,144 | 1,355 | 446 | 8 | 60,310 | 0.001058 |

In all 9 finite tests, every source violating pointwise `G<=B*w0` lies **entirely** in the arithmetically sieve-disposable light class `w0<=log²X`. At X262144, all 446 such sources have w0<=8 (many have w0=2), while the heavy group had zero recorded violations. This does NOT establish universal H1; a counterexample at larger X remains possible. Note that the finite light group is still large as a fraction of all starts, although lemma (L) proves this density tends to zero in the infinite limit.

At X131072, the weighted terminal energy over **all** starts was `Z/(X B²)=0.026606`; after removing light starts, `Z_hi/(X B²)=0.000905`. The low-root class contributed about 96.6% of this finite weighted energy. The high-root analytic problem is therefore much more focused than the unfiltered global response-moment problem, although it remains open.

## 4. Next diagnostic or formal target

A focused proof attempt can target `w0(M)>log²X ==> G_B(M)<=B*w0(M)` (stronger than required H1). Stress-test this statement at larger scales and off-dyadic X before committing to it. If it fails, measure the density of heavy-root violations and target H1 instead. Another rigorous route is to bound `Z_hi` by stratifying `w0(M)` into dyadic ranges and using the original parity-specific p-refire recharge and phase differences to control high growth tails within each range. Collisions of terminal horizons alone are insufficient (known adversarial sawtooth counterexample); genuine clock dynamics must enter the bound.

Paper lemmas L/L1 and implications H1/H2 are not Lean-kernel-checked. No asymptotic H1/H2 result, no twin-prime infinitude, no original A166944 theorem, and no main branch modifications.
