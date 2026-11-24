# Sparse adjacent large-prime states and pooled source-fibre energy

2026-11-24 JST. Continuation of 2388ecedf9cd4d39db8cc7e8f36eda973939e73d. Paper deductions, independent finite C++ audit, no new Lean kernel theorem. This is an alternative to estimating the full history-dependent critical-layer discrepancy; the twin-prime conjecture and the requisite source-mass estimates remain OPEN.

## 1. Actual prefix, fixed LOW7, two large-prime thresholds

Take the canonical odd sources M in [X,2X), X dyadic divisible by 4, N=X/2, B=ceil(sqrt(7X)), initial C0=2M-2, t=M+2, K(M)=floor((7M-1)/4). Use the original MIN parity clock and each original cutoff. Fix y=7, L=210, P=pi(B)-4, m=2P. The prefix is the first min(m,actual high length) selections p>7. Define Q=ceil(B/(log B)^(2/3)), a=ceil((log B)^(1/3)). In this note SMALL high means 7<p<Q and LARGE means Q<=p<=B. For sufficiently large B, Q>L+1.

Write H_s,H_l for total SMALL and LARGE selections in these prefixes and H=H_s+H_l. Put A=sum_(M,7<p<Q)(n(M,p)-1-a)_+. Then
    H_s <= N*pi(Q)*(a+1)+A = A+o(XP).
This uses prime counting and P~B/log B, not a bound on A.

The established LOW7 barrier ensures all low-only blocks have even gain 0<=e<L. The canonical Lean clock budget implies a non-twin terminal requires at least m high selections if m*(2B+3L)<3X/4-2. This holds eventually by prime counting. The strict condition and the pigeonhole below must not be assumed in finite runs where they fail.

## 2. NEW arithmetic sparsity lemma

For each post-LARGE selection of q write C for the horizon immediately after that selection. The selection is at a pre-horizon divisible on one side, so
    q | C or q | C+2.
The canonical invariant gives 2X<=C<7X. If the NEXT high selection is also LARGE, label p, its pre-horizon is C+e with 0<=e<L even. Thus p divides C+e-1 or C+e+1. For sufficiently large B the labels cannot be identical: the consecutive-p recharge requires at least p-1 gain, whereas the intervening block is LOW7 only with gain <L. Equivalently the two post-q residue classes and even e rule out p=q when q>L+1.

Define the relaxed arithmetic set S_X of pairs (q,C) with q LARGE, C even, 2X<=C<7X, q dividing C or C+2, and some DIFFERENT LARGE prime p dividing C+e-1 or C+e+1 for even 0<=e<L. This does not require the p clock to win or even to be admissible in the actual time interval.

For fixed p!=q, e and the two side choices, CRT including parity gives at most 1+5X/(2pq) choices of C. Therefore, since L is FIXED,
    |S_X| <= O(L [ X*(sum_(Q<=p<=B prime) 1/p)^2 + pi(B)^2 ])
          = O(X*(log log B)^2/(log B)^2).                        (1)
Indeed partial summation with pi(t)=O(t/log t) gives sum of reciprocals on [Q,B] = O(log log B/log B), and pi(B)^2=O(X/log^2 B). This is unconditional arithmetic counting of POSSIBLE horizon keys, not a distribution assertion about actual states. It does not require any previously selected-prime history.

## 3. NEW pooled fibre-energy and heavy-fibre alternatives

Define W(q,C) as the number of occurrences of post-LARGE key (q,C) in all actual prefixes, retaining original source multiplicity and pooling ALL ranks. Since every event strictly increases C, the same source appears in W(q,C) at most once. The key is a projection, not necessarily a complete dynamical state: different t and different histories may map to it. Hence its mass can overcount genuinely coalesced physical states, safely for the upper bounds below.

Let U be the number of adjacent LARGE,LARGE transitions in the high word, LOW7 events permitted between the two highs. Each occurrence is charged to its earlier key once; every such key belongs to S_X eventually. Thus
    U <= sum_((q,C) in S_X) W(q,C).
Let E_l=sum_(q,C) W(q,C)^2. Cauchy gives the new history-free large-side inequality
    U <= sqrt(|S_X| E_l)
      = O(sqrt(X E_l) * log log B/log B).                       (2)

Every LARGE selection is either the first high, preceded by SMALL, or preceded by LARGE. The first two classes have counts <=N and <=H_s respectively. Thus H_l<=N+H_s+U and H<=N+2H_s+U. Since every non-twin source eventually contributes exactly m=2P selections in the prefix, their number is <=H/(2P). In particular, for large X,
    #twin sources/N >= 1 - (2A + sqrt(|S_X| E_l))/(XP) - o(1). (3)
The OPEN sufficient condition liminf (2A+sqrt(|S_X|E_l))/(XP)<1 along dyadic X implies infinitely many twin primes. One stronger separate pair of sufficient inputs is A=o(XP) and E_l=o(X^2/(log log B)^2) on the same unbounded windows. This replaces unrestricted large-label multi-donor/return correlation by a pooled source-fibre second moment; it does not resolve the small-label excess.

There is also a strictly localized sufficient estimate. Define tau=floor(B sqrt(log B)) and
    J_l = sum_(q,C) (W(q,C)-tau)_+.
From (1), tau*|S_X|/(XP)=O((log log B)^2/sqrt(log B))=o(1). Therefore
    U <= tau*|S_X|+J_l = J_l+o(XP),
    #twin sources/N >= 1 - (2A+J_l)/(XP)-o(1).                (4)
The OPEN sufficient condition liminf (2A+J_l)/(XP)<1 is enough. In other words, the entire large-side obstruction can be confined to excess multiplicity in exceptionally heavy projected fibres. A universal W(q,C)<=tau would suffice on the large side, but is not established. No assumption about uniformity, conditional independence, or actual state injectivity is used in (1)-(4). The energy and heavy-tail criteria are alternatives, not claims that either implies the other.

The trivial deterministic bound from origin spacing is
    W(q,C) <= floor(2P*(B+L)/4)+1,
since all origins of this key satisfy C-2P*(B+L)<=2M-2<=C and are spaced by 4. This is much too large compared with tau asymptotically. The new estimate isolates exactly the required strengthening: control the heavy tail or second moment of these fibres. Merely citing the source-span bound would not prove (3) or (4).

## 4. Finite audit

Independent C++17 oracle at research/min_adjacent_energy_audit.cpp. Compile and run:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_adjacent_energy_audit.cpp -o /tmp/min_adjacent_energy_audit
    /tmp/min_adjacent_energy_audit 256 1024 4096 16384 65536 262144 1048576 4194304

Actually compiled and ran successfully on all listed windows. Local tested Git blob 9ad6b95912374288dc2f946ee06e91feca93b7bd; independently re-read identical at commit 1c9ffb7e4cad45d49dc5d32abee651cfd9d51928. 6140 literal parity-GCD comparisons for X<=1024. Counts all actual source prefixes with original cutoff, pools keys across ranks, enumerates the exact relaxed set S_X, verifies decomposition H_l=U+small-to-large+first-large and Cauchy for actual distinct transition keys. When Q<=L+1 the audit separately accounts for same-label adjacent transitions (zero in these tests); the asymptotic theorem excludes them. Finite S_X is the relaxed set, not the sparse asymptotic upper bound with unspecified constants.

| X | B | P | H_s | H_l | U | max W | E_l | S_X | sqrt(S_X E_l)/(XP) |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
|256|43|10|241|150|7|30|2640|302|.348791|
|1024|85|19|969|179|4|46|3577|1106|.102231|
|4096|170|35|7808|1591|187|72|46795|4722|.103689|
|16384|339|64|44894|5203|645|138|262419|17146|.0639704|
|65536|678|119|240184|22371|1685|286|1997871|67188|.0469789|
|262144|1355|213|1250359|87202|4965|629|11554760|258606|.0309585|
|1048576|2710|390|6252742|312678|13646|1195|55420560|982414|.0180434|
|4194304|5419|712|30364165|1199472|38599|1494|267188072|3758730|.0106118|

At X=4194304: 2,097,152 original sources; H=31,563,637; A=2,422,567; 24,856 distinct post-LARGE keys; 893 distinct actual adjacent LARGE transition keys; max weight of such a transition key 922. E_l*(log log B)^2/X^2=0.0000703034. The maximum W<B at every listed scale, so J_l=0 (tau>B). No large same-label adjacent transition observed. All sources in the largest window terminate at twin terminals, longest high word 189 vs m=1424. At X=256, 123/128 terminal twins; all sources terminate at twins at the other tested scales. The strict asymptotic clock prerequisite fails at these scales. In particular finite energy/mass ratios are diagnostics, not evidence of a proven asymptotic bound; the arithmetic relaxed set in these tests in fact equals the entire set of possible post-LARGE keys without the next-prime condition (L=210 is still substantial at these B).

## 5. Next mathematical task

The pooled energy is exactly a count of ordered original-source pairs sharing a projected key, possibly at different ranks. The relevant task is to bound that pair-coincidence count or, more weakly, the excess J_l, without using already short terminal trajectories. One possible route is a reverse-tree analysis of physical states (t,C) and then a controlled projection to (q,C); the projection cannot be assumed injective. At a post-q state possible predecessor horizons are C-q+1, with C constrained by q|C or q|C+2; this is only the first step, not a bound on original ancestors. Small-label A remains open, and the earlier critical-strip criterion is an independent route. No new Lean compilation or proof of infinitude. Main unchanged.
