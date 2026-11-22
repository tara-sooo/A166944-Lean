# A166944: squarefree square-root wheel reduction and a much weaker prime-insertion mean criterion

2026-11-22 JST. **Status:** two exact elementary paper lemmas, exhaustive finite computation of 4,999,997 odd starts M<=10,000,000, and finite squarefree prime-stage means. **No proof of the uniform mean insertion bound, no twin-prime infinitude theorem, no original A166944 Cap B theorem, and no new Lean kernel compilation.**

Context: [full prime-power wheel review](2026-11-22-wheel-insertion-signed-growth-review.md), [growth-adaptive split condition](2026-11-22-growth-adaptive-wheel-splitting-and-tail-bootstrap.md), [first-hit travel / BAD linear growth](2026-11-22-first-hit-growth-BAD-linear-lower-and-dyadic-average.md).

Reproduce the exhaustive all-odd scan from [squarefree_sqrt_wheel_scan.cpp](squarefree_sqrt_wheel_scan.cpp) and the fixed-dyadic signed prime-stage checks from [squarefree_prime_stage_audit.cpp](squarefree_prime_stage_audit.cpp), both using C++17 with -O3.

## 1. A different recurrence: retain ONLY the distinct small primes

For ANY odd artificial canonical start M>=7 set

    s=M+2,  K=floor((7M-1)/4),  D_B(s)=2M-2.

Choose B>=3 and the SQUAREFREE primorial

    W_B=product of odd primes p<=B, each ONCE.

Run the same parity-specific gcd recursion, truncating the increment:

    h(n)=gcd(n,D_B(n-1)-1)        for even n;
         gcd(n-2,D_B(n-1)+1)     for odd n.
    d_B(n)=gcd(W_B,h(n));
    D_B(n)=D_B(n-1)+d_B(n)-1.

The wheel W_B can be exponentially large but need not be materialized: factor the two frozen neighbor integers and retain only distinct prime factors <=B. The first-hit prime clocks are exact. Their parity locations remain (even n multiple 2p for p|D_B-1; odd n≡p+2 mod2p for p|D_B+1).

The original invariant D_B(n) is even and 2M-2<=D_B(n)<=2n continues to hold: the capped increment is a divisor of the original parity gcd at the SAME D_B state. With X(n)=2n-D_B(n)>=0, the original gcd is bounded by X(n-1)+3 at even n, while at odd n it divides |X(n-1)-3|; therefore the update X(n)=X(n-1)+3-d_B(n)>=0. Consequently the terminal C_B=D_B(K) obeys 2M-2<=C_B<=2K, and C_B±1 are O(M).

Let G_B(M)=C_B-(2M-2), let S_B(M) be the last event d_B(n)>1 in (s,K], or s if none.

## 2. Exact terminal twin certificate for a SQRT wheel (PAPER)

Every complete interevent gap (n_i-n_(i-1)) in the squarefree wheel is bounded by 2p<=2e_i<=3(e_i-1): after a frozen state, the prime p that triggers the next nonunit increment e_i has its clock period 2p, and e_i is odd>=3. Thus, for every odd M and B,

    BOXED: S_B(M)-s <= 3G_B(M).                         (1)

Fix B>=sqrt(2K+1). If at cutoff C_B-1 OR C_B+1 were composite, its least prime factor q would satisfy q<=sqrt(C_B+1)<=sqrt(2K+1)<=B and so q|W_B. The corresponding parity-specific q clock has a hit within 2q<=2B steps after S_B; hence if K-S_B>=2B, a forbidden later event would have occurred. Contradiction.

**Theorem (exact):**

    BOXED: B>=sqrt(2K+1) and
           K-s-3G_B(M)>=2B
             ==> C_B-1 and C_B+1 are BOTH PRIMES.       (2)

No original full gcd trajectory equivalence is required. The squarefree wheel may diverge significantly from the original sequence and even turn a full-gcd BAD start into a GOOD prime pair.

For reference, the older 8/3 mod-3 event-block improvement may further sharpen the constant, but (2) alone is enough for a clean average-growth route.

## 3. REDUCED mean-growth sufficient theorem: only O(sqrt X/log X) prime stages

Let X grow (e.g. powers of 2), and define I_X={odd M:X<=M<2X}. Choose ONE common prime cutoff for the whole dyadic interval,

    B_X=ceil(sqrt(7X)),

so B_X>=sqrt(2K(M)+1) for all M∈I_X. Define h_X(M)=G_(B_X)(M) for the SQUAREFREE wheel.

**Conditional sufficient theorem A (proved reduction, open premise):**

    If for arbitrarily large X,
      (1/|I_X|)*sum_(M∈I_X) h_X(M) = o(X),
    then infinitely many twin prime pairs exist.

Indeed choose M with h_X(M)=o(X). Since K-s>=3X/4-O(1), and B_X=O(sqrt X), the terminal certificate (2) holds for large X. The resulting twin primes C_B±1 have size>=2X-3 and are unbounded.

Enumerate odd primes 3=p_1<...<p_J<=B_X, let L_j=product_(i<=j) p_i be SQUAREFREE, and let Δ_j(M)=G_(L_j)(M)-G_(L_(j-1))(M). Then h_X(M)=sum_j Δ_j(M) exactly, with signed differences allowed.

**Conditional sufficient theorem B (NEW vastly weaker per-prime target):**
For some absolute constant C and arbitrarily large X, suppose every single prime stage p_j<=B_X satisfies

    BOXED: (1/|I_X|)*sum_(M∈I_X) Δ_j(M) <= C*B_X.    (3)

An even more natural (stronger) target is <=C*p_j. By telescoping and the elementary prime-count bound pi(B)=O(B/log B),

    mean h_X <= C B_X*pi(B_X)
             = O(X/log X)=o(X).

Hence (3) would imply twin-prime infinitude.

This is far weaker than the previously proposed mean cost H(X)=o(log X) for EACH of O(X/log X) full-prime-power insertions. Here there are only O(sqrt X/log X) squarefree prime stages, and an upper cost O(sqrt X) per stage suffices. The central unproved issue remains UNIFORM signed mean growth control for each stage over the SHORT M interval, where the enormous full CRT wheel period does not fit.

## 4. Exact terminal-horizon fibre/collision energy inequality (PAPER)

This addresses an observable obstruction to interpreting the old complete-lift 2/p frequency as short-interval independence.

Fix ANY wheel L (squarefree or not) and a finite set of DISTINCT ODD starts M. Put

    h(M)=G_L(M)>=0, C_L(M)=2M-2+h(M).

For each even c let k_c=#distinct starts M having C_L(M)=c. If M_1<...<M_k share c, then M_(i+1)-M_i>=2 implies h(M_i)-h(M_(i+1))>=4, while h(M_k)>=0. So

    sum_(i=1)^k h(M_i) >= 4*sum_(j=0)^(k-1) j
                        =2k(k-1)=4*binom(k,2).

SUM over all fibres c:

    BOXED: sum_c binom(k_c,2) <= (1/4)*sum_M h(M).   (4)

This is a deterministic QUADRATIC collision/plateau budget, requiring neither random residues nor a full wheel period. Consecutive odd M in the same c-fibre necessarily have growth decreasing by exactly 4 per step.

For odd M∈I_X, all even terminal horizons c lie in [2X-2,7X]. For prime p>=3 let N_p=#starts with p|C_L(M)-1 or p|C_L(M)+1. At most D_p=ceil(5X/p)+4 DISTINCT even horizon values in the range satisfy these two residue classes. If W=sum_M h(M), by Cauchy-Schwarz and (4),

    N_p^2 <= D_p*(N_p+W/2),

so

    BOXED: N_p <= (D_p+sqrt(D_p^2+2D_p W))/2.       (5)

When the adaptive first-split criterion for a fresh p applies after old-wheel stabilization, split starts form a SUBSET of these N_p. Thus (5) is a rigorous *incomplete-lift* upper bound, paid by old growth energy W rather than an unjustified Bernoulli 2/p. It currently has an excessively large sqrt(W) loss, and DOES NOT prove (3). A sharper "distinct-horizon residue dispersion" estimate using the real dynamics is still needed.

Illustration: with L=315 and odd M∈[1024,2048), p=211 divides C_L(M)+1 when C_L=2742 for FIVE starts M=1363,1365,1367,1369,1371. Their h values are 18,14,10,6,2: sum50, while (4) requires at least 40. This is why terminal prime residues can cluster inside intervals much shorter than 2Lp.

## 5. Finite exhaustive numerical evidence (not a proof)

A C++ SPF-based exact first-hit implementation was run on EVERY odd M in [7,10,000,000], 4,999,997 starts, with its OWN minimal B(M)=floor(sqrt(2K(M)+1)). The wheel is squarefree, not the full gcd.

    BAD C_B±1: only SEVEN starts:
       M=11,23,25,39,41,43,45.
    ALL ODD M>=47 through 10M: terminal GOOD.
    Last-event locality violations S_B-s>M/2: exactly15, last M=171.
    G_B>=M/4: exactly94, last M=1131.
    Maximum absolute G_B=52316 at M=8760663.

Examples where the squarefree wheel differs from full original:
    M=13: squarefree sqrt-wheel C_B=30, twin (29,31), full original BAD.
    M=305: squarefree sqrt-wheel C_B=660, twin (659,661), full original BAD.
    M=27: squarefree C_B=60, twin (59,61), full original C=72, twin (71,73).

Independent Python direct factor/jump checks reproduced the early and representative cases. The exhaustive C++ source is committed separately; its finite result does NOT imply the same statement for all M.

For the COMMON dyadic cutoff B_X=ceil(sqrt(7X)), all odd M in each sample interval, and successive SQUAREFREE primes p<=B_X, exact signed stages gave:

    X       #prime stages       average final h_X     max positive-ONLY mean Δ_j  (at p)
    1024             22                78.0078125            8.75390625    (61)
    4096             38               ~194.894             28.53515625    (79)
    16384            67               355.875              32.2998046875  (173)

For these finite tests every observed signed/positive per-stage mean was <p (in fact max positive mean/p<=2/3 for X>=1024), compatible with (3) and the stronger bound Cp. But even Cp is NOT established, and the much weaker CB_X estimate (3) is also NOT proved.

## 6. Proposed actionable next theorem

Use the exact short-interval fibre collision bound (4)-(5) to separate high-multiplicity terminal horizon plateaus from distinct horizon values. Prove a **growth-weighted sieve dispersion + one-shot renewal-cost** upper bound for squarefree prime insertion stages p<=sqrt(7X) of size <=C sqrt X averaged over odd M∈[X,2X).

This limits necessary correlation analysis to at most ~sqrt X/log X prime stages, no large primes and NO higher powers. One could first aim for a bound on POSITIVE parts: mean_(M)(Δ_j(M))_+<=C sqrt X, which is stronger but may be more tractable via excursion/tail accounting than direct signed cancellation. If the signed estimate (3) is established for arbitrarily large dyadic intervals, the elementary reduction in §3 yields twin-prime infinitude, **not** necessarily the original A166944 full-gcd Cap B.

No proof of the required per-prime mean estimate has been achieved. No Lean verification of new paper lemmas yet.
