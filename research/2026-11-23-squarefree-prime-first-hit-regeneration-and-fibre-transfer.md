# A166944 squarefree prime insertion: exact first-hit phase, canonical regeneration, and a fibre-weighted transfer inequality

**2026-11-23 JST. Status:** exact elementary paper proofs and original-gcd finite audits. **No theorem bounding dyadic prime-insertion means, no Cap B, no twin-prime infinitude, and no new Lean kernel check.**

Prior work: [squarefree sqrt-wheel sufficiency](2026-11-22-squarefree-sqrt-wheel-mean-reduction.md), [growth-adaptive insertion](2026-11-22-growth-adaptive-wheel-splitting-and-tail-bootstrap.md), and [Shevelev comparison / commuting diamond](2026-11-22-shevelev-dual-reset-commuting-diamond.md). Full finite exact C++ reproducibility: [squarefree_prime_regeneration_audit.cpp](squarefree_prime_regeneration_audit.cpp).

## 1. Exact FIRST p-clock time, not merely "two of p lifts"

Let M be odd >=7, s=M+2, K=floor((7M−1)/4). Use the ORIGINAL parity gcd but cap each increment at a fixed odd squarefree wheel L, run through K. Define h=G_L(M) and old frozen terminal horizon

    C=2M−2+h.

Let p be a prime NOT dividing L, and impose the proven safe condition

    p>6h+7.                                           (A)

The old last nonunit event occurs at relative time t_old≤3h. As proved previously, a new p cannot produce an earlier first split. After t_old, old horizon C is fixed. Thus, if neither p|C−1 nor p|C+1, insertion L->Lp makes NO change. Otherwise let

    a=(p+h−1)/2,
    eps=0 if a is EVEN, eps=1 if a is ODD.

Here h is even, p>=11, and p|C−1,C+1 cannot both hold. The exact FIRST eligible p-clock relative time t=n−s is

    p|C+1 (ODD n):   t_+ = a + eps*p,
    p|C−1 (EVEN n):  t_- = a−3 + eps*p.                (B)

At that index the old increment is 1 and the enlarged wheel increment is EXACTLY p (provided t_±<=K−s). Formula (B) is obtained directly from p|2M−1+h or p|2M−3+h, the parity and the modulo 2p clock; (A) ensures both candidate times occur AFTER t_old.

Write the original deficit coordinate X(n)=2n−D(n). Immediately AFTER the first p-hit (and BEFORE any subsequent events), formula (B) gives EXACTLY

    p|C+1:   X(n) = 6+2*eps*p,
    p|C−1:   X(n) = 2*eps*p.                         (C)

Therefore the POST-hit deficit belongs to {0,6,2p,2p+6}. This is an exact **four-state reset normal form**. It is *not* an assertion that every Lp trajectory eventually becomes canonical; it classifies only the first p-hit when (A) holds.

The "early" phase eps=0 is equivalent to p+h==1 (mod 4); "late" eps=1 otherwise. With eps=1, X=2p or2p+6 and no immediate canonical reset is claimed.

### Universal p-hit residue invariant (no safe assumption)

There is a more general rule for ANY odd prime p dividing an actual odd nonunit increment e(n), with no truncation/safe/frozen condition. For the original parity gcd evaluated at any EVEN previous horizon D(n−1) and updated by e−1:

    BOXED: n even AND p|e(n) ==> X(n)=2n−D(n) == 0 mod 2p;
           n odd  AND p|e(n) ==> X(n)=2n−D(n) == 6 mod 2p. (U)

Proof: at even n, p|n and p|D(n−1)−1, so n==0, D(n−1)==p+1 and e==p mod2p (n even, D previous even, e odd). Hence D(n)==0 and X(n)==0 mod2p. At odd n, p|n−2 and p|D(n−1)+1, so n==p+2, D previous==p−1 and e==p mod2p. Hence D(n)==−2, 2n==4 and X(n)==6 mod2p.

Thus **any** p-hit with 0<=X(n)<2p must land at X=0 (even index), or X=6 (odd index), with the latter giving an immediate canonical renewal at artificial odd start M'=n−2. More general hits land on the lattice X=2kp or X=6+2kp. The safe insertion condition (A) ensures k∈{0,1}, producing the four-state special case (C). This invariant is valid for unsafe insertions too; it does not upper-bound how often the higher k values occur.

## 2. Early-phase canonical regeneration, including an exact bridge of length THREE

Define the **regeneration map**

    BOXED: u=Phi_p,L(M)=M+a=(C+p+1)/2.               (D)

Because eps=0, a is even, so u is odd. The map is determined SOLELY by the old frozen terminal horizon C. Moreover

    p|C+1  ==>  u==0 (mod p),
    p|C−1  ==>  u==1 (mod p).                         (E)

Case PLUS: p|C+1. By (B), the p-event occurs at n=u+2 (odd). By (C), X(n)=6, i.e.

    D_(Lp)(u+2)=2u−2,

EXACTLY the canonical starting state of the OLD L-restricted process with artificial odd start u. After that hit, as long as no further p-hit intervenes, the two processes follow IDENTICAL L-restricted gcd increments at all later absolute indices.

Case MINUS: p|C−1. By (B) the p-event occurs at n=u−1 (even), and X(n)=0. The subsequent three increments at indices u, u+1, u+2 are 1 IF AND ONLY IF

    (3 does not divide L OR u−2 is not divisible by3)
    AND
    (5 does not divide L OR u+1 is not divisible by5).  (F)

The exact gcd operands are respectively 3,5,1 (gcd with the respective index), and p>=11 stays inert during this three-step quiet bridge. If (F) holds, at n=u+2 we obtain X=6 and the same canonical old-wheel start u.

Thus a fresh p insertion, surprisingly, can RESTART the process at an explicit later artificial canonical start, with no assumption that u is a prime or an attained A166944 record. The PLUS case is immediate; the MINUS case is a three-step "diamond" with explicit 3/5 obstructions.

## 3. Exact one-shot growth transfer and its sharp elementary thresholds

Suppose an EARLY-phase PLUS reset as above and write H_L(u;K) for the additional L-only cumulative growth from seed (u+2,2u−2) through the OLD cutoff K(M), not the possibly later cutoff K(u).

The p-hit changes C by p−1, so the insertion difference is

    Delta_p(M)=G_(Lp)(M)−G_L(M)
              =p−1+H_L(u;K)                          (G)

PROVIDED there is no later p-event before K. At the PLUS p-hit the new horizon is −2 mod p; to reenable a p-clock requires at least p+1 additional EVEN growth. Therefore the verifiable sufficient condition

    H_L(u;K)<p+1                                     (H+)

guarantees NO refire and (G).

For the early-phase MINUS case satisfying bridge (F), the new post-hit horizon is 0 mod p. The minimum extra even growth needed to restore p activity is p−1. Thus the stronger threshold

    H_L(u;K)<p−1                                     (H−)

also yields the EXACT identity (G).

For either case, H_L(u;K)≤G_L(u) provided K(M)≤K(u), which holds because u>M and K is monotonic.

These two sufficient thresholds are useful but not necessary: a hypothetical L-only tail may accumulate more than p±1 without a p-clock actually firing, because foreign L-events can preempt the p clock. The exact no-refire criterion is a FIRST-HIT comparison on every frozen interval of the hypothetical L-only continuation: a p-clock must never occur at or before the next L event/cutoff. This can be audited without running the full enlarged wheel, but an unproved bound on the number of such preemptions is still required for an all-X estimate.

## 4. NEW deterministic fibre-weighted renewal transfer (PAPER)

Let I be a finite set of distinct odd M, let S⊆I be a set of early-phase PLUS splits satisfying the no-refire condition (for example (H+)). For each M∈S put u=Phi_p,L(M), h(M)=G_L(M), and k_u=#elements of S mapping to the same u. Let N=|S| and W=sum_(M∈S) h(M).

Two starts M_i<M_j in the SAME u fibre have equal old horizon C and satisfy

    h(M_i)−h(M_j)=2(M_j−M_i)≥4.

Since h≥0, a fibre of size k costs at least 2k(k−1) total old growth. Consequently

    BOXED: sum_u binom(k_u,2) ≤ W/4,
           sum_u k_u^2 ≤ N+W/2.                       (I)

The regeneration gain, (G), and Cauchy-Schwarz yield the EXACT deterministic upper

    sum_(M∈S) Delta_p(M)
      ≤(p−1)N
       +sqrt(N+W/2)
        *sqrt( sum_(u∈Phi(S)) G_L(u)^2 ).            (J)

No probabilistic independence, period averaging, or disjoint event charges are assumed. The target starts u are automatically in the residue class u≡0 mod p.

For the MINUS/no-refire/quiet-bridge subset there is an analogous bound with u≡1 mod p.

**Why this is not a proof of the dyadic mean bound:** the second-moment term over the restricted shifted starts u≡0,1 mod p, as well as all late-phase/bridge-defect/re-fire/unsafe contributions, is uncontrolled at arbitrarily large X. The fibre factor is exact, but its sqrt(W) cost can still be enormous.

## 5. Finite original-gcd squarefree-stage audits

Prime stages are successive distinct odd primes 3≤p≤ceil(sqrt(7X)); the old wheel contains ALL preceding primes ONCE, never prime powers. All odd starts M∈[X,2X) are tested by the exact parity-specific first-hit recurrence at their individual K(M).

    X                         4096         16384
    #old-safe comparisons      12030        105280
    actual first-p splits      501          2463
    early-phase splits         254          1183
      early PLUS               128           597
      early MINUS              126           586
    late-phase splits          247          1280
    early PLUS H_L<p+1         77            356
    actual p-refires in PLUS   3             18
    early MINUS quiet bridge   111           498
    bridge and H_L<p−1         62            266
    actual p-refires (bridge)  3             22

The first-p event indices and (C) reset values were verified for EACH of these safe splits. For every case satisfying (H+) or (H−), the exact signed growth identity (G) held. In ALL early PLUS samples, the L-only tail had already stabilized before the old cutoff; this is a finite observation, not a general bound.

The discrepancy between the PLUS sufficient test and ACTUAL repeated p-hits is notable: at X4096, 51/128 had hypothetical L-tail growth >=p+1, yet only 3/128 actually refired. At X16384, 241/597 exceeded that threshold, yet only 18/597 refired. Therefore the exact clock-preemption criterion, rather than a crude B<p bound alone, matters.

## 6. New precise research target

The original proposed dyadic prime-insertion mean bound E[Delta_p]≤C sqrt X remains open, but the EARLY regenerative contributions are reduced to:

- counting starts for which the adaptive old horizon C_L(M) hits ±1 mod p and whose phase is early, over a short M interval;
- controlling the RESTRICTED SECOND MOMENT of old-wheel growth G_L(u) for u≡0 or1 (mod p), weighted by the explicit fibre energy (I);
- showing the actual q-clock refiring/bridge-defect contribution is small; separately handling late-phase resets X=2p,2p+6 and unsafe p≤6h+7.

A possible proof would build a *renormalization inequality* for terminal-fibre collision energy and the restricted growth second moment, then bootstrap across p≤sqrt X. Such an inequality is NOT established. The new four-state first-hit normal form and the canonical regeneration/fibre map are rigorous structural tools, not themselves a mean-growth upper bound.

**No proof of twin-prime infinitude or original A166944 Cap B.**
