# A166944 — historical reachability, canonical relay, and high-reuse GOOD descendants

Date: 2026-11-22 JST. Status: new exact elementary paper deductions, a 107,406-input finite ancestry scan, and independent per-index integer certificates. **NO global upper bound on R_M or H_(>=13) has been proved. Cap B and twin-prime infinitude remain OPEN. No new Lean compilation.**

References: [recycling upper reduction](2026-11-22-reuse-upper-reduction-and-small-wheel-exhaustion.md), [BAD recycling requirement](2026-11-22-bad-path-prime-reuse-roughness-dichotomy.md), [terminal GOOD/BAD first-hit](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), and [finite-prefix CRT lifting](2026-11-22-full-history-clock-crt-and-twin-input-cutoff-sieve.md). Companion executable audits: [full genealogy scan](canonical_good_genealogy_scan.cpp) and [independent direct-gcd witnesses](canonical_genealogy_history_audit.py).

## 1. Historical reachability is a restriction on M, not an unrecorded state coordinate

For an odd M>=7, every genuinely reached or artificially initialized canonical state has

    s=M+2; D(s)=2M-2; X(s)=2s-D(s)=6.

All subsequent gcd increments are fully determined by (s,D(s)), hence by M. Different hypothetical past histories leading to precisely the same canonical M have IDENTICAL future paths. Any use of genuine historical reachability must therefore impose a restriction on the SET of attained values M (for example, membership in a certain iterated record map), not a separate hidden variable.

For ANY odd canonical-shaped input M, define the exact deterministic cutoff functional

    K(M)=floor((7M-1)/4);
    G(M)=D_M(K(M))-(2M-2);
    F(M)=D_M(K(M))+1=2M-1+G(M).

D_M is the exact original parity-sensitive gcd replay after setting the canonical-shaped initial state artificially; these starts are NOT automatically attained by the genuine a(1)=2 orbit.

If the cutoff horizon C=D_M(K) has BOTH C-1 and C+1 prime, its next first nonunit hit is at C+3=F(M)+2, with increment F(M), and new post-hit horizon 2C=2F(M)-2. This is an exact **canonical GOOD relay**. To call it the next strict RECORD one also needs to exclude earlier increments exceeding M inside the prefix; this extra condition is directly checked for all explicit relay witnesses below.

For a GOOD relay ancestry M_0 -> ... -> M_k, the exact expansion identity is

    M_(j+1)-1 = 2*(M_j-1)+G(M_j);
    M_k-1 = 2^k*(M_0-1)
            + sum_(j=0)^(k-1) 2^(k-1-j)*G(M_j).    (1)

Thus (M_j-1)/2^j is nondecreasing, with step G(M_j)/2^(j+1). If all source and target records have twin-prime input M-2,M>3, then M==1 mod 6 at both ends, hence G(M_j)==0 mod 6. These are **positive, exact inherited arithmetic identities**, but they do not supply an upper bound on G or R.

For fixed target M and a GOOD predecessor m, the horizon bound gives

    ceil((2M-1)/7) <=m<=floor((M+1)/2).

Consequently a fixed M has a finite, explicitly searchable predecessor interval, but a finite inverse search is not a global proof for all M.

## 2. A quiet-GOOD-parent relay theorem (PAPER)

Suppose m odd >=7, and both 2m-3 and 2m-1 are prime. At the canonical initial state (s=m+2,C=2m-2), these are precisely C-1 and C+1. The **first** nonunit event occurs at C+3=2m+1 with increment C+1=2m-1. Since K(m)<2m+1, there are NO nonunit events in (s,K(m)], and

    BOXED: N_m=R_m=G(m)=0, F(m)=2m-1.             (2)

If also m-2,m are primes, this is an exact GOOD canonical relay between genuine twin-prime integer pairs. This is a conditional arithmetic theorem for an artificial or actual canonical start, not an assertion that the original orbit reaches m.

**Counterexample to small-parent upper bounds, independently per-index certified:**

    parent m=237691:
      237689,237691,475379,475381 are all prime;
      K(m)=415959, N=0,R=0,G=0,F(m)=475381.

    child M=475381:
      K(M)=831916, N=186,R=157,G=6840,D(K)=957600,
      D(K)±1=(957599,957601) BOTH prime;
      R/sqrt(M)=0.22770824...>0.20044593...

Thus even an EXACT GOOD predecessor with ZERO earlier nonunit events does NOT force the child's recycled-event count below the proposed 0.20045 sqrt(M) ceiling.

Another verified quiet->busy example:

    m=9931771: N=0, F(m)=19863541, terminal GOOD;
    child M=19863541: N=401, R=357, G=41262,
      D(K)±1=(39768341,39768343) both prime.

## 3. Seven consecutive GOOD relay generations still permit high R

An independent exact per-index original-gcd replay, including all unit steps, verifies the following **ARTIFICIALLY ROOTED** record chain:

    859 -> 1723 -> 3463 -> 6961 -> 13999
        -> 28183 -> 56713 -> 113623 -> 230563.

All source and terminal twin-prime pairs in this chain are prime, all displayed transitions are GOOD canonical relays, and all interior event increments remain below the source M. The first eight sources have:

    M          N        R       G        F(M)
    859        1        0       6        1723
    1723       4        2       18       3463
    3463       6        1       36       6961
    6961       9        4       78       13999
    13999      11       4       186      28183
    28183      21       12      348      56713
    56713      19       13      198      113623
    113623     107      84      3318     230563

The last source has

    BOXED: R_113623/sqrt(113623)=0.24919892...>0.20044593...

Therefore a condition asserting only "the preceding 1,...,7 generations are GOOD" cannot suffice to enforce the proposed R ceiling. This is a FINITE counterexample to these particular lookback depths, NOT a theorem about every finite depth or genuine root attainability.

## 4. A complete FINITE 20-million twin-input directed ancestry experiment

For each of the 107,406 twin-prime input pairs 7<=M<=20,000,000, the companion C++ program computes the exact factorized first-hit path and its F(M), N_M,R_M and terminal pair primality, then builds the directed GOOD-parent map. Selected witnesses are separately validated by the original per-index gcd and trial-division prime checks in Python.

    twin-prime artificial canonical starts             107,406
    terminal BAD                                           2 (13,43)
    R/sqrt M >=c, c=3/(8*sqrt(7/2))                    165
    among those, terminal GOOD                           163
    among those, with event-free GOOD predecessor           5
    among those, with >=3 GOOD ancestor transitions        10
    among those, with >=5 GOOD ancestor transitions         5
    maximum GOOD predecessor depth among high-R states     7 (113623)

A further example M=28549 has two exact GOOD predecessor candidates 14083 (N=27) and 14251 (N=2), and the child has N=177,R=153, R/sqrtM~0.9055. A GOOD predecessor can be very quiet even when its GOOD child is very active.

**These directed paths have artificial roots** and do not constitute original A166944 records. The authentic record orbit from a(1)=2 is ONE PARTICULAR chain among all possible canonical-shaped starts; assuming all its large stages GOOD is exactly the conjectural step under investigation.

## 5. Mathematically precise next targets

The requested global upper bound on R_M or H_(>=13) remains open. The new examples show that one-parent quietness and up to seven prior GOOD steps cannot establish the desired inequality. Since the full future is determined by the reached M, any effective history-sensitive invariant P must be a restriction on reachable M, proved at a genuinely attained base value and stable under the canonical successor F.

Two viable concrete tasks are:
1. Find such a closed invariant P for the ACTUAL record-map orbit, with an event-density or terminal-primality consequence that survives the quiet->busy transition (2).
2. Avoid a global R ceiling on GOOD paths; instead prove that on a BAD path the forced Omega(sqrt M) repeated-prime returns create a CRT/first-hit contradiction or a compulsory long quiet terminal suffix.

Nothing here establishes either target. A finite ancestry scan or a fixed list of residue classes alone cannot certify an infinite orbit. No new Lean kernel proof was compiled.
