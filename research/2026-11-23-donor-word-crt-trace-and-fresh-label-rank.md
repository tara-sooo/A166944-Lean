# Twin-prime-first: exact canonical source CRT cylinders and nondegenerate donor-word lattice

2026-11-23 JST. Scoped to Issue #3, related Issue #4 and parent #1. Research attempt to import the **repeated-label/lone-label** trace-counting method in Helfgott--Radziwill, *Expansion, divisibility and parity*, §§6--7 (https://arxiv.org/abs/2103.06853 ; author's exposition https://webusers.imj-prg.fr/~harald.helfgott/Expansion_1.html). We obtained elementary paper lemmas, independent C++17/Python finite checks, a rigorous weighted trace reduction, and a concrete remaining obstacle. **NOT a twin-prime proof, NOT an asymptotic estimate of the full return sum, and NOT newly kernel-checked in Lean.** Pre-existing LOW7 finite core (time56/growth106) is Lean-verified in draft PR #5.

## 1. Exact canonical-source CRT cylinder for signed event increment words

Use the original clipped squarefree parity-GCD B-wheel on odd canonical sources M in [X,2X), X divisible by4, B=ceil(sqrt(7X)), start s=M+2, C(s)=2M-2, cutoff K=floor((7M-1)/4). Let the actual **nonunit** events up to a given prefix be i=1,...,h, with clipped increments d_i and event times n_i. Before event i,

    C_i^- = 2M-2 + G_(i-1),   G_(i-1) = sum_(j<i) (d_j-1).

For every prime p|d_i, p is odd and
  EVEN n_i: p | C_i^- - 1 = 2M-3+G_(i-1);
  ODD  n_i: p | C_i^- + 1 = 2M-1+G_(i-1).

Therefore the **necessary source residue** is exactly

    2M == k_i-G_(i-1) (mod p),
    k_i = 3 (even n_i), 1 (odd n_i).                  (SOURCE-CRT)

Fix a full *signed increment prefix word* w=((d_1,parity_1),...,(d_h,parity_h)), without fixing M, actual event times, or any cutoff. Let P(w)=product of all DISTINCT odd prime factors appearing in d_1,...,d_h. For each such p, choose the first index i with p|d_i. SOURCE-CRT fixes **one unique** M residue mod p. If a repeated occurrence of p later in w disagrees, there are zero realizations. Otherwise CRT fixes one M class mod P(w).

There are N=X/2 possible odd sources M=X+1+2j, j=0,...,N-1. As P(w) is odd, its one class in M determines one class in j. Consequently

    0 <= source_count_X(w) <= floor((N-1)/P(w))+1.  (EXACT-WORD-BOUND)

For every repeated prime p occurring at indices i<j, necessary consistency is

    p | [G_(j-1)-G_(i-1) - (k_j-k_i)].               (REPEAT-GAIN)

Unlike the earlier false conjecture that a fixed (q,r) donor PAIR determines an O(X/(qr)+1) source fibre, **the COMPLETE prefix increment sequence and the event parities are fixed here**. Adaptive growth between unspecified events prevents reducing this to pair labels alone.

If the parities are omitted, the first occurrence of p permits at most TWO residues for M (the constants k_i are 1 or3), giving the weaker bound

    source_count_X(d_1,...,d_h) <= 2^omega(P) * [floor((N-1)/P)+1].

This factor is essential: the first-event increment d=3 occurs with both residues of M mod3 at X256,1024,4096. Therefore one MUST retain the event parity or pay two-residue sieve dimension.

## 2. An independent, source-free event timing congruence

Let delta_i=n_i-(M+2) be the elapsed time from the canonical start. Each prime p|d_i also divides n_i (if even) or n_i-2 (if odd). Subtracting the corresponding twice-event-time integer from the state congruence yields

    EVEN n_i:  p | [G_(i-1) - (2*delta_i+7)];
    ODD  n_i:  p | [G_(i-1) - (2*delta_i+1)].       (TIME-GAIN)

These conditions on timing and growth are independent of the source M once a timed word (delta_i,d_i) is specified. They can prune impossible words BEFORE the source-CRT summation. They do not alone ensure that each listed event beats all other prime clocks.

## 3. Source-labelled q-return donor words: genuine rank-one pinning

For two consecutive actual q-bearing events (q>=11), suppose there are m intervening high events and each contains exactly one distinct-from-q high factor r_j>=11, with increment d_j=a_j*r_j, a_j|105. Different *positions* may share the same r. Let L be the total growth in low-only events, and c in {-1,1,3} be the correct parity-pair recharge residue. The **necessary exact** condition is

    sum_(j=1..m) a_j*r_j + L - m - c == 0 (mod q). (DONOR)

Collect the coefficients for each DISTINCT donor label r:

    A_r = sum_(j: r_j=r) a_j > 0,
    sum_r A_r*r == m+c-L (mod q).                   (LABEL-LATTICE)

If any A_r is nonzero mod q, then, once all other labels, coefficient pattern, low contribution L, and c are fixed, r is pinned to one residue class mod q. It has at most

    floor((B-11)/q)+1

integer candidates in 11<=r<=B, at most TWO for q>=B/2 (B>=22), before additionally requiring primality. This is a rank-one reduction in the PRIME-LABEL word space, not yet a source-weighted asymptotic saving.

Any donor r occurring exactly once has A_r=a_j|105 coprime to q>=11, so guarantees nonzero rank. More generally, if ALL A_r ==0 (mod q), each A_r>=q. For k distinct donor labels and sum a_j<=105*m,

    rank-zero implies 105*m >= k*q, i.e. m >= k*q/105. (DEGENERACY-BARRIER)

For m>=1, in particular m<q/105 guarantees a nonzero rank. Rank zero does not imply impossibility for longer paths: it remains a separate arithmetic class.

## 4. An exact SOURCE-WEIGHTED trace reduction

For each q-return that occurs as a (minimum-high-owner) repeated owner event on an actual M-path, retain the **FULL prefix** signed event word w ending at that repeated owner event, plus owner q. Let W_X^owner be the set of distinct such (q,w) signatures, N_X(q,w) the number of actual sources realizing them (the preceding q-ownership pattern is already determined by w). Then there is an EXACT finite identity

    R7(X) = sum_(q,w in W_X^owner) N_X(q,w).

By EXACT-WORD-BOUND,

    R7(X) <= sum_(q,w in W_X^owner) [floor((X/2-1)/P(w))+1]. (TRACE-CRT)

It is also valid with ALL repeated q-bearing tags on the left, giving a stronger proxy. Therefore **an unbounded-X upper bound on the right** below (9/224-o(1))*X*B on unbounded dyadic X implies infinite twin primes by the prior LOW7 reduction; e.g. a bound o(XB) suffices.

This removes the *unknown source multiplicity of a completely specified prefix* without a stochastic CRT assumption. The unresolved part is that the sum ranges over MANY possible signed full-prefix words, and the +1 in each CRT cylinder becomes dominant once P(w)>X. Enumerating these words with valid clock competition and showing a strong trace saving is a genuine NEW analytic task. Counting only donor labels is insufficient; it discards the earlier increment history that fixes M's CRT class.

The Helfgott--Radziwill original graph is a distinct, roughly reversible divisibility walk with uniform initial counting measure, and its original spectral theorem cannot simply be pasted onto this one-way, adaptive, coalescing clock graph. Its *distinct/repeated-label + CRT + rank/codimension* mechanism transfers at the algebraic level established above, but the required global trace estimate is OPEN.

## 5. Reproducible and independent finite findings

**Original event-jump C++ source** research/donor_rank_word_audit.cpp: all actual consecutive q hits, including q mixed/masked by other event factors, classify zero-high donor, linear single-high-factor donor, nonlinear high-composite donor. The linear records check BOTH recharge congruences, coefficient divisibility, singleton occurrence, and rank/nonrank:

    X     all q repeats    zero    linear   nonlinear   linear nonzero-rank   linear singleton
    4096      2,034         88      1,894      52            1,894              1,881
    16384    17,717        646     16,370     701           16,370             16,365
    65536    84,076       3,838    78,302    1,936          78,302             78,057
    262144  499,788      19,492   468,125   12,171         468,125            466,917

For ALL tested linear donor return paths, rank zero was not observed. This is FINITE numerical evidence, not proof of a uniform asymptotic rank result. The independent literal integer-by-integer Python audit research/donor_rank_literal_oracle.py EXACTLY reproduces C++ rank/singleton counts X256,512,1024.

**Signed prefix SOURCE-CRT** research/donor_word_crt_cylinder.py: direct exact event jump, all realised signed prefix words of depths 1..4 on X256,1024,4096. Every group has a consistent unique residue mod P(w), count<=floor((N-1)/P)+1, every timed event passes TIME-GAIN, and dropping parity already fails uniqueness at the first event d=3. For X4096, depth4: 896 distinct signed prefix groups, max group source weight65, all satisfy the bound.

The source-CRT upper bound is not a substitute for the clock-race condition: even restricted to actual REALISED signed prefix groups at X4096, the depth-1 bound sum is 5,486 versus 1,996 true source prefixes; depth-4 sum 3,425 versus 1,659 true prefixes. For LONG fully specified q-return words at the same X, the bound is much tighter: 2,076 versus 2,034 actual all-q return tags. This contrast is finite, and shows that full-history information matters; the unbounded difficulty is enumerating the exponentially branching allowed long histories rather than bounding the occupancy of each one. The published cylinder checker prints `crt_sum` for these ratios.

**Actual q-return FULL prefix check** research/donor_return_trace_criterion.py:

    X       all-q returns  owner returns  unique full signed q-return prefixes  sum CRT upper bound on REALISED prefixes
    256          115          115                115                                   115
    1024         174          174                174                                   174
    4096        2034         2015              2030                                  2076

The last upper sum is only on REALISED prefixes; these measurements do NOT establish a bound on the union of all abstractly admissible prefixes as X grows. Individual fibres and +1 contributions require global counting.

**Coalescence test** research/donor_coalescence_prefix_check.py: X256 coalesced q23 episode at (t,C,t')=(485,964,552), source weight7 and SEVEN different full signed prefixes. X2048 q67 episode (2412,4824,2481), source weight24 and 24 distinct full prefixes. X4096 q89 episode (4628,9256,4897), source weight11 and 11 distinct full prefixes. Coalescing states do not invalidate the full-prefix CRT bound; they demonstrate why compressing prefixes to the shared post-event state loses arithmetic information.

Commands:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/donor_rank_word_audit.cpp -o /tmp/donor_rank
    /tmp/donor_rank 256 512 1024 2048 4096 16384 65536 262144
    python3 research/donor_rank_literal_oracle.py 256 512 1024
    python3 research/donor_word_crt_cylinder.py 256 1024 4096
    python3 research/donor_return_trace_criterion.py 256 1024 4096
    python3 research/donor_coalescence_prefix_check.py

## 6. The exact remaining analytic goal

Build an admissible signed word/clock graph subject to TIME-GAIN, repeated-prime REPEAT-GAIN and donor-label LABEL-LATTICE plus no-earlier-clock constraints; prove that its SOURCE-CRT-weighted repeated-owner prefix trace is <(9/224-o(1))XB along infinitely many dyadic X (or o(XB)). Controlling rank-zero donor words and high-composite donor events is also required. The gap is no longer "how to count the same fully specified path from many canonical starts"; CRT does that. It is "how to bound the collection of ALL dynamically allowed paths despite its branching and source coalescence." No such bound was proved here; no Lean module was compiled for the new formulas.

Novelty check: CRT source cylinders and repeated-label congruences are elementary arithmetic; similar distinct/repeated-label lattice counting is explicitly present in Helfgott--Radziwill. No claim of an original global analytic theorem. Main unchanged.
