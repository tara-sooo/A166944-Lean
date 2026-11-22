# A166944: first-hit travel–growth bridge, mod-3 blocking, and a dyadic mean-growth sufficient criterion

Date: 2026-11-22 JST. **Status:** exact new elementary PAPER theorems, independent parity-gcd verification, complete 4,999,997-odd-input finite scan through M=10 million. **Neither a universal growth upper bound nor Cap B nor twin-prime infinitude is proved. No new Lean kernel compilation.**

Related prior notes: [event localization / q recharge](2026-11-22-event-localization-and-directional-prime-clock-recharge.md), [BAD first-hit bound](2026-11-22-bad-path-prime-reuse-roughness-dichotomy.md), [two-horizon CRT overlap & all-odd scan](2026-11-22-two-horizon-overlap-capacity-and-localization.md). Reproducible companion executable [canonical_growth_travel_audit.cpp](canonical_growth_travel_audit.cpp).

## 1. Exact event-gap/energy bridge: no density or prime-factor reuse hypothesis

For ANY artificial or truly attained odd canonical start M≥7, put

    s=M+2, K=floor((7M−1)/4), C0=D(s)=2M−2,
    G=D(K)−C0=sum_event (e_i−1).

List all nonunit event indices s<n_1<...<n_N≤K, let n_0=s, e_i=d(n_i)≥3 odd, and S=n_N if N>0 else s.

**Theorem A (PAPER):** each COMPLETE interevent gap satisfies

    BOXED: n_i−n_(i−1) ≤2e_i ≤3(e_i−1).              (1)

The first step is NOT the naive implication that e_i divides the index at n_i: that alone does not bound delay, but the exact FIRST-HIT property does. Between n_(i−1) and n_i the even horizon is constant C_i. At n_i a prime p|e_i is active in one of C_i±1, and its parity-specific trigger positions are a residue class modulo2p. If n_i−n_(i−1)>2p an earlier trigger would have occurred, contradicting n_i being the first nonunit event after n_(i−1). Thus gap≤2p≤2e_i, irrespective of composite e_i or whether multiple primes trigger together. For all odd e≥3, 2e≤3(e−1).

Sum (1):

    BOXED: S−s ≤3G.                                  (2)

For BAD at K, the old final frozen factor-clock lemma bounds

    K−S ≤2sqrt(2K+1).

So universally,

    BOXED: BAD ==> G≥[K−s−2sqrt(2K+1)]/3
                   =(1/4−o(1))M.                     (3)

This is a NEW LINEAR necessary growth bound on BAD, versus earlier Omega(sqrtM) event/reuse lower bounds.

## 2. Mod-3 event blocks: coefficient 8/3 instead of 3

Each horizon is EVEN. An increment e=3 can occur only if 3 divides the currently active C±1:
- at even n==0 mod6, C==1 mod3, post C'=C+2==0 mod3;
- at odd n==5 mod6, C==−1 mod3, post C'=C+2==+1 mod3; the NEXT n+1 is even and 0 mod6, so its increment is necessarily a multiple of3 (either exactly3 or an odd multiple≥9). If it is exactly3, post C''==0 mod3.

Thus runs of consecutive nonunit events with increment EXACTLY3 have length at most2, and the second event of a two-3 run is at the NEXT integer index, with gap1.

If M==1 mod3, then C0=2M−2==0 mod3. No 3-event run can precede the first event with e≥5. Partition the event word into blocks, each beginning with an e≥5 followed by 0,1,or2 consecutive e=3 events.

The complete interevent gap sum and growth in each block obey:

    block                  maximal gap sum       growth
    (e)                   <=2e                  e−1
    (e,3)                 <=2e+6                e+1
    (e,3,3)               <=2e+6+1              e+3

For all ODD e>=5, the maximum of these three gap/growth ratios is 8/3, attained as an arithmetic local maximum for e=5 and a single follow-up e=3. Therefore:

    BOXED: M==1 mod3 ==> S−s ≤(8/3)G.              (4)

For other odd M, the initial run of 3-events can contribute ≤7 time units before the first e≥5 (if present), so

    BOXED: ANY odd M ==> S−s ≤(8/3)G+7.           (5)

This holds if N=0 as well. Direct original-gcd audits for all odd M<=10001 and the 10M event-jump scan checked (4) and (5).

**Sharp local model for the ratio 8/3:** take a locally assigned post-event even horizon C(20)=306. Original gcd increments for n=21,...,36 have no event until n=30, where e=5 raises C to310; the next event is n=36,e=3, raising C to312. The two-event block travels (30−20)+(36−30)=16 indices for growth (5−1)+(3−1)=6, ratio 8/3. This is a local exact recurrence segment, NOT a canonical/attained start (it violates the original-orbit bound D(20)<=40).

## 3. Stronger linear BAD growth lower bound and effective sufficient upper target

The final censored BAD gap K−S<=2sqrt(2K+1) combines with (4),(5):

    BOXED: M==1 mod3 AND BAD ==> G≥(3/8)[K−s−2sqrt(2K+1)].
    BOXED: ANY odd M AND BAD ==> G≥(3/8)[K−s−7−2sqrt(2K+1)].    (6)

Since K−s≥(3M−11)/4 and 2K+1≤(7M+1)/2:

    ANY odd M BAD ==> G≥(9M−117)/32 −(3/4)sqrt((7M+1)/2).       (7)

For M==1 mod3, replace 117 by33. Asymptotically

    BOXED: BAD ==> G≥(9/32−o(1))M ≈0.28125M.       (8)

An EFFECTIVE consequence: for ALL ODD canonical-shaped M>=2501, if

    BOXED: G(M)≤M/4,                                (9)

then terminal C±1 are BOTH prime, i.e. GOOD. Proof: the BAD bound (7) would exceed M/4 whenever M−117>24sqrt((7M+1)/2). For M≥2500 this follows by squaring and using

    M²−2250M+13401>0.

Thus the eventual **fixed linear growth upper bound G≤M/4** is ALREADY sufficient, without requiring G=o(M) or bounding N,R, or S directly. A much weaker global target than the earlier unproved S−s=o(M) / G=o(M).

For actual canonical twin-prime record M>3 we automatically have M==1 mod3, so use the stronger no-startup form.

## 4. Exhaustive numerical growth scan (finite, not universal)

An exact SPF-factored FIRST-HIT scanner was independently run for EVERY odd M in [7,10,000,000], 4,999,997 artificial canonical-shaped starts, checking the actual parity-gcd at EVERY event, and the universal (4),(5).

Summary:
    BAD total=9, largest BAD M=305.
    Last-event-late > M/2 total=21, largest M=375.
    ALL-ODD M≥377: 70 cases G(M)≥M/4, largest such M=1441.
    ALL-ODD M≥1443 through10,000,000: G(M)<M/4.
    ALL-ODD M≥10,000 through10,000,000: MAX G/M=0.1651407546846924, at M=11687 (G=1930).
    M≥100,000: max ratio=0.05357838231280138 at M=274775 (G=14722).
    M≥1,000,000: max ratio=0.014495168123884536 at M=1086431 (G=15748).
    Largest absolute growth G=69652 at M=7209299.

The global GOOD and growth hypotheses remain unproved outside this finite interval. Strongest suggested simple *testable target* is G(M)≤M/4 for all odd M≥1443; an eventually valid version is sufficient. A less stringent eventual bound G(M)≤(9/32−epsilon)M would also suffice asymptotically.

## 5. A weaker *AVERAGE* route to infinitude, with exact dyadic criterion

A universal per-M bound is unnecessary for twin prime infinitude because an ARTIFICIAL canonical GOOD terminal already provides two primes C±1≥2M−3, regardless of whether M was a genuine record or a twin-prime input.

Let I_X={odd M : X≤M<2X}. If there are arbitrarily large X for which

    BOXED: sum_{M∈I_X} G(M) ≤ (1/4)*sum_{M∈I_X} M,      (10)

then by pigeonhole there is an M∈I_X with G(M)≤M/4; for X≥2501 this M is GOOD by the proved theorem (9), and C(M)±1 is a twin prime pair of size≥2X−3. Thus (10) on unbounded dyadic blocks alone would prove infinitely many twin primes. It is strictly weaker than the pointwise growth bound on ALL starts.

This offers a concrete averaged CRT/large-sieve research target, unlike the prior attempt to exclude every BAD input. But the average estimate (10) itself remains entirely unproved. Naively treating the evolving residue as independent is invalid, since the event history makes the modulus and residue strongly correlated.

## 6. Exact relative-index gcd normal form for averaging over start M

Let t=n−(M+2)≥1 and g_(t−1)=D(M+2+t−1)−(2M−2) denote cumulative growth BEFORE the current step. The original gcd recurrence becomes the EXACT parameterized map:

    d_M(t)=gcd(M+t+2, 2t+7−g_(t−1))    if t odd (index n even),
           gcd(M+t,   2t+1−g_(t−1))    if t even (index n odd).     (11)

    g_t=g_(t−1)+d_M(t)−1, g_0=0.

The second gcd operand is independent of M **conditional on a fixed previous growth/event word**, while M appears linearly, coefficient1, in the first. Hence finite event-word cylinders determine arithmetic progression/congruence restrictions on M. This is a specific entrypoint for averaging: count starting residues M satisfying a fixed prefix, then control aggregate growth across cylinders using CRT and perhaps an entropy/discrepancy bound. It is NOT a proof that the adaptive residues equidistribute, and a finite-prefix-only CRT cannot directly control the O(M)-length cutoff.

The exact identity (11) was independently checked step-for-step using the original parity gcd for all odd M≤1001.

## 7. Missing theorem, explicit

The present tools prove: BAD must pay ≥28.125% linear horizon growth. To prove twin infinitude it would suffice to prove EITHER:
- fixed-input eventual growth cap G(M)≤M/4 along ALL odd M (strong), or
- infinitely many dyadic averaged caps (10) (weaker), or
- one such GOOD start in infinitely many dyadic blocks by an alternative method.

No such universal/dyadic bound has been established. There is no Lean compilation of the new paper lemmas.
