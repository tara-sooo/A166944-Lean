# A166944 — exact two-horizon prime-clock overlap capacity and extensive event-localization audit

**2026-11-22 JST. Status:** elementary PAPER theorem, exact 600,000-pair factor audit, and two independent exact original parity-gcd scans up to 10 million artificial odd inputs and 20 million twin-prime inputs. **Global event-localization theorem, Cap B and twin-prime infinitude remain OPEN. No new Lean kernel proof.**

Earlier context: [directional single-prime recharge and locality target](2026-11-22-event-localization-and-directional-prime-clock-recharge.md), [BAD square-root gap and recycling lower bound](2026-11-22-bad-path-prime-reuse-roughness-dichotomy.md), [CRT overlap/core energy](2026-11-22-return-overlap-CRT-energy.md), [Shevelev companion diamond](2026-11-22-shevelev-dual-reset-commuting-diamond.md).

## 1. Exact THREE-CONSECUTIVE-INTEGER prime-clock overlap theorem (PAPER)

For any EVEN horizon C≥2, define its active odd-prime clock support

    A(C)={odd primes p : p|(C−1)(C+1)}.

Take two even horizons C<C', with even delta=C'−C≥4 and n=delta/2≥2. A common active odd prime p∈A(C)∩A(C') divides at least one of

    C±1, C'±1    ==>    p | delta−2, delta, or delta+2
                     ==> p | n−1, n, or n+1.       (1)

Since p≥3 is invertible mod2, the last implication is exact. The three integers n−1,n,n+1 have pairwise coprime ODD parts (their pair differences are 1 and 2). Thus the PRODUCT of all distinct common active odd prime factors divides

    oddpart[(n−1)n(n+1)].                           (2)

In particular, for ANY real P≥7 with

    BOXED: 4≤delta<4P−2,                         (3)

all n−1,n,n+1 are positive and <2P. Each common odd prime p≥P must equal ONE of those three integers; it cannot occur as a proper divisor. Consequently

    BOXED: |A(C)∩A(C')∩{p≥P}| ≤2.                 (4)

Equality is possible ONLY when n is even, and the two shared large primes are n−1 and n+1, forming a TWIN-PRIME PAIR. The pair's side orientations are FORCED:

    n+1 | C−1 and C'+1;
    n−1 | C+1 and C'−1.                           (5)

Thus under (3), simultaneous cheap reactivation of TWO old large prime clocks is possible ONLY via a twin pair, with their sides exchanged. This is an exact simultaneous-prime CRT overlap obstruction, without assuming anything about intervening increments, event order, a frozen wheel, or actual record reachability.

**EXCEPTION delta=2 is essential.** Here n−1=0, and every odd prime divisor of C+1 is ALSO an odd prime divisor of (C+2)−1. There is NO uniform large-prime overlap bound. Such a side flip is realized by an exact single e=3 event, unlike (3).

**SHARPNESS:** the upper threshold cannot be weakened from delta<4P−2 to delta≤4P−2. For P=7, C=456, C'=482, delta=26=4P−2; primes 7 and 13 both divide C−1=455 but 7 divides C'+1=483 and 13 divides C'−1=481. They are NOT twin primes. At even index n=230, gcd(230,C−1)=5 and the event increases the horizon from456 to460; an additional growth22 produces the second candidate horizon. This is an exact local event followed by a possible **arithmetic** cumulative growth, not a claim that a full original trajectory realizes C'=482.

**CHEAP TWIN EXAMPLE:** C=846, C'=870, delta=24<26 for P=7; old clocks 13|845=C−1 and11|847=C+1, while new clocks 13|871=C'+1 and11|869=C'−1. At n=430, gcd(430,845)=5; after this event C becomes850, and the remaining proposed growth20 leads to the twin coactivation. Again, the later growth is an arithmetic horizon assignment, not certified as an original multi-event path.

**THE delta=2 REAL GCD EXCEPTION:** C=85084, C'=85086. The four primes 7,11,13,17 all divide C+1=C'−1=85085; at the valid even index n=42546, gcd(42546,C−1)=3, hence the original one-step recurrence actually gives C'=C+2, and the pre-event deficit is X(n−1)=6. Arbitrarily large sets of odd prime clocks can similarly share a single C+1 and survive a +2 side flip.

## 2. Multi-state, overlap-safe charging inequality (PAPER)

Take m strictly increasing EVEN horizons C_1<...<C_m with
- every consecutive gap at least4;
- total span C_m−C_1<4P−2.

For each odd prime p≥P, put a_p=number of i such that p∈A(C_i). Counting pairs of states that share p,

    sum_{p≥P} binom(a_p,2)
      =sum_{1≤i<j≤m} |A(C_i)∩A(C_j)∩{p≥P}|
      ≤ binom(m,2)+B.                                (6)

Here B counts state pairs (i,j) for which
- n_ij=(C_j−C_i)/2 is EVEN,
- n_ij−1, n_ij+1 are BOTH primes≥P.

In particular B≤binom(m,2), so the weaker unconditional bound is 2*binom(m,2). If there are no relevant twin-prime pairs, (6) improves to binom(m,2). This charges clock overlap WITHOUT pretending that independent primes paid disjoint growth costs.

The hypotheses automatically hold for any short-growth block of distinct **post-event horizons of events e≥5**, since passing to the next such event increases D by at least4. e=3 events are omitted from these snapshots, which precisely removes the delta=2 unlimited-flip exception.

**Potential alternate route:** if along arbitrarily large genuinely reached A166944 windows one could FORCE the left side of (6) to EXCEED binom(m,2) for prime thresholds P→∞, then the extra term B would force arbitrarily large twin-prime pairs DIRECTLY. No such excess-overlap lower bound has been proved. If all q are allowed to share arbitrarily many *separate* horizon growth intervals, this single-block theorem alone will not bound total activity.

## 3. Exact finite audits

[A Python exact factor audit](prime_clock_overlap_capacity_audit.py) checks ALL 600,000 pairs (P,C,delta), for P=7,11,17,31, even C=2..10000, and delta=4,6,...,<4P−2; 108 pairs attain two-prime overlap, and ALL have the forced twin-prime and side-swap form (35,50,20,3 by P). The sharp boundary and genuine e=3 side-flip witnesses are independently checked with integer gcd.

[An optimized exact original parity-gcd first-hit scanner](canonical_event_localization_allodd_scan.cpp) exhausts ALL odd canonical-shaped input starts 7≤M≤10,000,000 (4,999,997 starts), without requiring M,M−2 prime or actual record attainability:

    BAD cutoff (C−1,C+1 NOT both prime):           exactly9 inputs
       M=11,13,23,25,39,41,43,45,305;
       largest BAD M=305.

    Last nonunit index S with S−(M+2)>M/2:          exactly21 inputs
       M=17,23,39,41,49,57,141,143,145,147,305,
         353,355,359,363,365,367,369,371,373,375;
       largest violation M=375.

    Of the 58,979 TWIN-PRIME inputs M≤10M:         0 late violations,
                                                     2 BAD (13,43).
    Among M≥1000, the largest ratio (S−s)/M:       0.1900826446 at M=1331.

An independent factorized first-hit scanner tested ALL 107,406 twin-prime starts M≤20,000,000: 0 late violations, only the two BAD starts M13,43, maximum (S−s)/M=0.488372 at M43, and maximum ratio for M≥100,000 was 0.0246056 at M113023.

The 10M all-odd scan uses an SPF sieve for exact factorization of every frozen neighbor C±1, exact Chinese-remainder first-hit residues, then the ORIGINAL parity-specific gcd at each event. Independent direct index-by-index gcd replay confirms representative M=11,13,43,305,375,377,1331,5419,28549,355723. Finite computations are not universal proof or Lean checks.

## 4. Effective event-localization sufficiency, with EXPLICIT bound

Let M be odd and s=M+2, K=floor((7M−1)/4), S the last nonunit event (S=s if none). Already-proven BAD first-hit bounds give

    BAD ==> K−S <= 2*sqrt(2K+1).

Since K−s >=(3M−11)/4 and 2K+1<=(7M+1)/2, if S−s<=M/2 then

    K−S >=(M−11)/4 >2*sqrt((7M+1)/2)
           for all M>=247, because M²−246M+89>0.        (7)

Thus for ALL odd canonical-shaped M>=247, an exact sufficient statement is

    BOXED: S(M)−(M+2) <= M/2   ==>   GOOD at K.       (8)

The entire exhaustive ALL-odd interval 377≤M≤10M satisfies this condition. This suggests the **strong, UNPROVED universal localization conjecture** that (8)'s antecedent holds for all odd M≥377, *without* any twin-prime or reachability restriction. If true, it would yield a deterministic generator of unbounded twin prime pairs and thus prove twin-prime infinitude. Neither the 5-million-input numerical audit nor the local overlap theorem establishes the conjecture.

## 5. Exact remaining obstruction and next target

The clock-pair theorem (1)-(6) resolves the **single-short-growth-snapshot double-counting issue** and isolates only two exceptions: (i) e=3 side-flip delta=2, and (ii) genuine twin prime pair q,q+2 as simultaneous cheap large-factor returns. It is promising to analyze the real recurrence in **e>=5 post-event horizon normal form**, charge persistent e=3 flips separately (each can preserve an old q clock for only one +2 side-switch before deactivation), and derive a global multiscale overlap/activation bound.

What remains completely OPEN is a quantitative theorem forcing the total extent of the active-event region S−s to be less than M/2 (or o(M)). Many separate event horizons can be traversed with growing C, so the pairwise short-span bound does not yet constrain an entire M-sized window. The empirical universal result is a target, not a proof. The exact missing step is a GLOBAL clock-activity bound across all such short-growth blocks, including e=3 flip chains and their cross-block interactions.

No claim that Cap B or the twin-prime conjecture has been established.
