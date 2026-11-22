# A166944 — recycling upper-bound reduction and exact small-increment exhaustion

Date: 2026-11-22 JST. **Status:** a new exact deterministic fresh-prime startup inequality, improved necessary BAD recycling constant, exhaustive finite-state checks for increment thresholds <=11, genuine-record and synthetic twin-input scans. **A uniform bound on total R_M has NOT been proved. Cap B and twin-prime infinitude remain open.** No new Lean kernel compilation.

Previous precise inputs:
- [BAD event-density and recycling lower bound](2026-11-22-bad-path-prime-reuse-roughness-dichotomy.md), especially Theorem A: the old BAD coefficient 3/32.
- [exact cutoff BAD/GOOD dichotomy](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md).
- [CRT first-hit anti-resonance and bounded-budget wheel](2026-11-22-budgeted-first-hit-crt-anti-resonance.md).
- [finite-wheel phase experiments](2026-11-22-frozen-wheel-phase-budget-and-neutral-paths.md).

The aim of this turn was a universal upper bound on recycled-prime event occurrences along *attained* canonical records. The results reveal an important **reduction**: at the sqrt(M) scale, recycled-event count and total nonunit-event count are asymptotically the SAME. A full upper bound is therefore a global **event-sparsity** theorem, not a simple CRT accounting consequence.

## 1. Definitions and the exact fresh-prime STARTUP budget

Let s0=M+2 be a genuine or synthetically initialized canonical-shaped state with odd M, D(s0)=2M-2; K=floor((7M-1)/4); set

    T=K-s0; G=D(K)-(2M-2) <=2K-(2M-2)=(3/2)M+O(1).

Let N be the number of nonunit event indices in (s0,K]. Define R as the number of such events at which the increment e has AT LEAST ONE odd prime factor that divided the increment of an EARLIER event inside that same interval. An event with several repeated prime factors counts ONCE. Put F=N-R. Every one of these F fresh-only events has all prime factors previously unseen.

For each fresh-only event, choose any odd prime factor p_i of its increment e_i. The chosen p_i are PAIRWISE DISTINCT. The same event contributes e_i-1>=p_i-1 to the actual G.

Let q_1=3,q_2=5,q_3=7,... be the odd primes in increasing order. Their first F weights minimize the distinct prime-weight sum. Therefore we have the **exact and universal fresh-startup inequality**

    BOXED: sum_{j=1}^{F}(q_j-1) <= G.                 (A)

A convenient fully effective corollary for EVERY integer B>=3 is

    BOXED: 0<=N-R<= pi(B)+floor(G/B).                   (B)

Proof of (B): assign a distinct selected prime to each fresh-only event. At most pi(B) assigned primes are <=B; for the rest, e_i>=p_i>B and e_i-1>=B, so their number is <=floor(G/B).

Using the elementary classical bound pi(x)=O(x/log x) with B=floor(sqrt(M log M)), G=O(M) yields

    BOXED: N-R=O(sqrt(M/log M)), uniformly over
           ALL canonical-shaped exact trajectories. (C)

This is not an assumption about M,M-2 primality, attained records, reset phases, or the BAD hypothesis. It even holds on artificial paths with high recurrence density. The exact prime-prefix form (A) improves constants over the cutoff estimate (B), especially for moderate G.

**Important interpretation:** If N is Omega(sqrt M), then R/N=1-o(1). A putative BAD path is necessarily dominated by recycled prime factors. Consequently, proving the conjectural R upper bound below is asymptotically equivalent to proving an upper bound on total event count N, rather than an easier substitute for it.

## 2. SHARPENED unconditional BAD recycling coefficient

For an attained canonical M with C=D(K), the previous factorized first-hit theorem states that if C-1,C+1 are not both prime, then after EACH intermediate event state with s<=K, its next first hit has gap <=2*isqrt(2K+1). The final censored gap until K obeys the same bound. Thus with h=isqrt(2K+1),

    N+1 >= T/(2h).

Combining with (B), every integer B>=3 gives the **explicit lower bound**

    BOXED: BAD ==> R >= ceil(T/(2h))-1
                          -pi(B)-floor(G/B).           (D)

The generic upper bound G<=2K-2M+2 makes (D) a threshold depending only on M and B. Since K=(7/4)M+O(1), h=sqrt((7/2)M)+O(1), and (C) is o(sqrt M),

    BOXED: BAD ==> R >= [3/(8 sqrt(7/2)) - o(1)]sqrt M
                          = (0.2004459314... - o(1))sqrt M.  (E)

This strictly improves the previous 3/32=0.09375 by over a factor of 2.13. In particular every hypothetical sequence of large attained BAD records would have BOTH

    N >=(0.2004459314...-o(1))sqrt M,
    R/N ->1.

A sufficient, still **UNPROVED**, induction hypothesis is R <=[3/(8sqrt(7/2))-epsilon]sqrt M on every actually attained canonical record past an effective M0. By (C) this is essentially the same as an eventual analogous N bound. The exact R argument requires the genuine record-attainment/reachability premise when upgraded to a global result.

## 3. Exhaustive finite-state exhaustion of small-increment events

A different rigorous **partial upper bound** IS obtainable for small increments.

Fix L=3465=lcm(1,3,5,7,9,11). Define an auxiliary truncated recurrence from any state (s,C), with C even, using

    d_L(n) = gcd(n,C_L(n-1)-1,L)        n even,
             gcd(n-2,C_L(n-1)+1,L)      n odd,
    C_L(n)=C_L(n-1)+d_L(n)-1.

If the TRUE recurrence has e=d(n)<=11 at every nonunit event on a given segment (unit increments automatically qualify), then every e divides L. By induction the truncated recurrence is IDENTICAL to the true recurrence on that segment. This is an exact one-way transfer theorem, not a heuristic approximation.

The truncated recurrence depends only on the **finite state**

    (s mod 2L, C mod L),

giving exactly 2L^2=24,012,450 states. The companion [exhaustive verifier](reuse_small_wheel_exhaustion.cpp) enumerates EVERY state of this graph, checks ALL directed cycles, and computes by dynamic programming the maximum number of future nonunit transitions before the first permanently quiet cycle.

Its full exact state census:

    L       states        quiet cycles  active cycles  max #nonunits
    105        22,050          15             0             9
    315       198,450          45             0            10
    1155    2,668,050         135             0            22
    3465   24,012,450         405             0            29

The corresponding initial canonical-shaped states s=M+2,C=2M-2 have lower maxima (8,8,18,19). If M and M-2 are BOTH primes greater than 11, then M mod p is neither 0 nor 2 for p=3,5,7,11; among the 3465 odd M residue classes modulo 6930, precisely 405 satisfy these input restrictions. The **exact maximal number of small-only events from these restricted canonical states is 16** (for L=3465). These numerical constants are computer-verified finite theorems, NOT Lean-kernel theorems.

**Event-block exhaustion corollary (paper deduction + exhaustive certificate):**
- On ANY complete run of consecutive nonunit events with all increments <=11 and NO larger increment between, there are at most 29 events.
- On the INITIAL canonical run for twin-prime input M>11, before the first increment >=13, there are at most 16 such events.
- Writing H_M for the number of increments >=13 in the cutoff interval, any canonical-shaped twin input M>11 satisfies

    BOXED: N_M <=16+30 H_M.                            (F)

Proof: split the interval into H_M+1 small-only blocks. The initial block contributes <=16; each block following a large event contributes <=29; count the H_M large events once. In particular H_M>=(N_M-16)/30.

Combining (F) and BAD N>=c sqrt M gives the new **necessary** high-increment event density

    BAD and twin input ==> H_M >=[1/(80 sqrt(7/2))-o(1)]sqrt M
                         = (0.006681531...-o(1))sqrt M. (G)

This is NOT the desired R upper bound. Indeed the growth budget G=O(M) permits many events >=13; the 29-event ceiling only prevents the entire BAD-density burden from being carried by a small-increment-only engine. Proving H_M=o(sqrt M) would suffice for a complete proof but is currently also open.

## 4. Authentic and synthetic experiments: reachability is indispensable

[Exact genuine index-by-index scanner](reuse_genuine_record_scan.cpp):
- Processed original a(1)=2 recurrence through index 220,000,000, with 23 genuinely attained canonical records whose cutoff K is complete. The largest of these is M=91,793,059, cutoff K=160,637,853.
- Among the 15 complete attained records with M>=5419, the largest observed ratio R/sqrt M was 0.067066 at M=355723.
- Selected exact (M,N,R,G) records:
  (M=355723, N=57, R=40, G=2388);
  (M=22933441, N=209, R=171, G=28692);
  (M=45895573, N=37, R=22, G=1914);
  (M=91793059, N=53, R=38, G=30306).
These are finite tests, not an asymptotic upper-bound proof.

[Exact factorized first-hit scanner of synthetic twin-prime starts](reuse_twin_input_synthetic_scan.cpp):
- Scanned ALL 107,406 twin prime input pairs M-2,M through M<=20,000,000, with artificial initialization D(M+2)=2M-2.
- **165** such SYNTHETIC starts have R/sqrt M >=0.2004459314; **136** of those M>=5000, **49** M>=100000.
- Extreme witness: M=28549 and M-2=28547 are both prime. Set s=28551, D(s)=57096 and K=49960. Direct parity-gcd recurrence produces N=177, R=153, D(K)=60648; the terminal numbers 60647 and 60649 are ALSO prime. Here

    R/sqrt M = 0.90551569... > 0.20044593....

This is a **GOOD** artificial path with many reuses. Hence the desired uniform bound cannot hold for all canonical-shaped states EVEN IF their starting inputs M and M-2 are twin primes and their terminal neighbors are prime. It must exploit **actual historical reachability** of M from a(1)=2, or use a different branch-specific criterion.

An independent per-index parity-gcd replay and the factorized first-hit C++ scan agree on the stated synthetic witness. The compiled finite-wheel exploration took ~3.3 seconds for L=3465 and ~140 MiB peak resident memory in the local container; both final C++ sources were saved and verified via GitHub remote readback. No new Lean compilation.

## 5. Resulting strategic conclusion and exact open core

- The total-reuse *lower* bound for BAD is now 0.20044593 sqrt M asymptotically.
- The missing desired *upper* bound is still an open global dynamical assertion, and **R=N-o(sqrt M)** holds uniformly, so it is virtually the same as an upper bound for the NUMBER of nonunit events.
- Fixed small increments <=11 cannot sustain more than 29 uninterrupted events; this is a completed finite-state upper theorem and gives a new exact event-block decomposition.
- Large events and long-term historical reachability are the genuine unresolved components. Even very strong local congruences, finite prime wheels, and twin-prime-shaped input are insufficient, as the synthetic example demonstrates.

A viable next main theorem would bound N_M below the BAD event-density coefficient on all large **reachable** canonical states, or prove directly that a BAD path's necessary 0.2004 sqrt M events cannot be realized together with the fully inherited pre-canonical history. Neither statement has been proved here. Current status: partial upper bound for small-factor blocks, improved universal BAD recycling requirement, and a precise reduction of the full R upper problem to event sparsity.
