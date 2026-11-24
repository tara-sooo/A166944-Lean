# Distance-band pair audit, first meetings, and quantized asynchronous lags

2026-11-24 JST. Continuation of 73458de887def94d00eeaf2d2d3b9c59a44b8137. New finite identities, unconditional partial bounds and reproducible audits. The full distance-band estimate and twin-prime conjecture remain OPEN.

## 1. Exact pair decomposition on the full canonical runs

Retain original M, original K(M), B, N=X/2, pre-event horizon sets V_M, minimum active factor r(C), and E_d from the parent. All pairs below are ORDERED distinct original sources. A band is d<|M-M'|<=2d, or the near band 0<|M-M'|<=B. Count the initial physical state and the true terminal state as vertices for meeting statistics, but count ONLY pre-event horizons for E_d. This avoids charging a nonexistent next event at a terminal.

Let F_d count pairs ever sharing a physical vertex (t,C), including root and terminal. At each physical vertex v let A_v be its original-source set; partition A_v by the immediately preceding physical vertex (or singleton root). For a source set A let P_d(A) be its ordered pair count in the band. The exact first-meeting count at v is

    P_d(A_v) - sum_(incoming classes A) P_d(A).

Proof: a pair with the same predecessor has already met. If it met earlier, determinism and the source-specific cutoff imply it cannot reach v via different predecessors: the forward paths agree until the earlier source terminates. Thus pairs in distinct incoming classes meet for the first time at v, and each pair is charged exactly once. Summing yields F_d. Refine the incoming groups by predecessor horizon D; the last label is uniquely p=C-D+1. This identifies the same-label first meetings, different-label first meetings, and root meetings. The root is not a last prime.

Write E_d=S_d+G_d with S_d the weight of shared pre-event physical states and G_d the weight of shared pre-event horizons at different arrival times. The exact first-meeting identity for S_d is obtained by weighting each first-meeting pair by the common suffix's sum of r(C) up to the EARLIER original cutoff (zero if neither has a shared pre-event after meeting). In particular S_d<=O(X) F_d, as in the parent, since r(C)<=p<=3(p-1)/2 and the common suffix gains O(X). This is not a new bound on F_d.

## 2. NEW unconditional treatment of the asynchronous merge term

At a common pre-event horizon C, suppose arrival times differ. Partition G_d into four disjoint types:
- G_diff: next prime labels differ.
- G_merge: next prime labels and next clock times both agree.
- G_parallel: next labels agree, next clock times differ, and the time lag is unchanged.
- G_change: next labels agree, next clock times differ, and the lag changes.

These exhaust G_d exactly. For G_merge the two trajectories meet at the next physical vertex, for the first time. Every ordered pair contributes to G_merge at most once, independently of source separation. Hence

    sum_all_bands G_merge <= B*N*(N-1) = O(X^2 B).       (A)

This is already sufficient for this part of the energy criterion, even after summing all bands. It is a genuine unconditional bound; it does NOT bound the same-label first-meeting count F_d strongly enough to control the common suffix S_d. The unweighted number of G_merge occurrences equals the number of same-label first meetings (including when a next vertex is terminal). The numerical audit independently verifies this equality.

The reverse clock interval gives another exact restriction. For different arrival times t<u at C merging on a common next event T, both waits are between 1 and 2r(C), so u-t<2r(C). If both arrivals were produced by the same preceding prime a, then their times are in the same parity-clock residue modulo 2a, so 2a<=u-t<2r(C) and a<r(C). This requires genuine incoming events, not roots. Thus a small-r(C) same-label merger cannot have two distinct arrival times produced by the same larger previous label. This is local, not a weighted ancestor bound.

## 3. NEW exact lag transition and constant-lag barrier

For an asynchronous common pre-event horizon C, order arrivals t<u and put h=u-t>0. If both choose the same prime p, the divisibility side of p is unique (p odd, p cannot divide both C-1 and C+1). Both next times are therefore the first strictly later tick of one identical periodic clock of period 2p. Consequently the next lag h' satisfies

    h' in {2p floor(h/(2p)), 2p ceil(h/(2p))},
    |h'-h| <= 2r(C)-1.

The first assertion is exact periodic-clock arithmetic, the second follows from both actual waits lying in [1,2r(C)]. In particular h'>0 is a multiple of 2p, and lag change is possible only when 2p does not divide h. The smaller arrival cannot overtake the larger in a common-label step. A zero lag is the merge case (A).

For a contiguous common-horizon run in which the next labels agree and a nonzero lag h stays CONSTANT at every step, each selected prime p divides h and 2p divides h. Let D=2 times the product of the distinct odd primes used in this run. Then D divides h. The deterministic even-multiple barrier (the previous LOW barrier applied to this finite set of labels) gives total common horizon gain <D<=h. Since r(C)<=p<=3(p-1)/2, the total weighted common-horizon length of the run is <3D/2<=3h/2. This bound holds regardless of run length, even if the constant lag is large. A run ends at a change of lag, a different-label split or termination. It does not bound the number of runs, or the total weights of G_change and G_diff. Lag rounding can both increase and decrease h, so a monotonic lag potential is not available directly.

## 4. NEW arithmetic restrictions on different-label meeting vertices

For a physical meeting vertex (t,C) with two distinct incoming primes p,q, set delta=2t-C and epsilon=0 at even t, 6 at odd t. For even t both p,q divide t and C. For odd t both divide t-2 and C+2. Thus 2pq divides delta-epsilon. As C>=2X, t<=Kmax<7X/2 and delta>=0, a nonreset meeting satisfies 2pq<=5X (the possible negative delta-6 has absolute value <=6 and cannot be a nonzero multiple of 2pq). In particular if both primes are >=3B/5, then 2pq>=18B^2/25>=126X/25>5X, so the vertex MUST lie on the reset line delta=epsilon. This is unconditional, even for long paths.

More generally take Q=ceil(B/log^(2/3) B). For fixed distinct p,q>=Q, the divisibilities on t and C give O((1+X/(pq))^2)=O(X^2/(p^2 q^2)) physical vertices in the window, since pq<=B^2=O(X). Partial summation of the prime-counting bound yields sum_(p>=Q)1/p^2=O(1/(Q log Q)). Hence the number of possible physical meeting vertices with two distinct incoming primes >=Q is

    O(X^2/(Q^2 log^2 Q)) = O(X/log^(2/3) B).

On the reset line there is only one free coordinate t, giving O(X (sum_(Q<=p<=B)1/p)^2 + pi(B)^2) = O(X(log log B)^2/log^2 B). These are bounds for candidate VERTICES, not original-source pairs. They cannot be used as F_d bounds without the incoming original-source mass factors. In particular no uniform estimate F_d=O(XB) follows just by CRT. The empirical dominant far-pair cases below suggest that working solely on distinct large labels would miss most of the obstruction.

## 5. Exact finite distance-band audit

C++ research/min_pair_first_meeting_audit.cpp includes the previously verified min_full_horizon_budget_audit.cpp. It replays every original full trajectory, stores each visited physical vertex with predecessor and next event, groups by C,t,predecessor, and counts unordered source-index pairs by sorted two pointers, multiplying by 2 for ordered pairs. For G subtypes it groups also by next label, (label,next time), or (label,wait). It verifies E=R+sum of all distinct-pair bands, the same-label first-meeting identity and nonnegative disjoint partitions. All computations here are integer counts. Run:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror -Wno-return-type research/min_pair_first_meeting_audit.cpp -o /tmp/min_pair_first_meeting_audit
    /tmp/min_pair_first_meeting_audit 256 1024 4096 16384 65536 262144 1048576

The -Wno-return-type flag is needed solely for the macro-renamed main in the included parent file. All listed windows ran successfully. The local tested source Git blob 15c506784d9fa6ea7793fef2a78a4adafa4653de was independently read back at e30f523a6201f2f3de37409487331a2493ef5bc9; included parent blob 995067c02c29590f5f64afb1bbcdc6cd482e29a2. Independent literal Python GCD replay and exhaustive pair enumeration:
    python3 research/min_pair_literal_oracle.py 256 1024
Both windows matched the C++ band results for E,G,F,sameLabel and all four G types (including zero bands). Python blob b6d638ed867928c61a4eb3d3c03a487251263e26 read back at 5edad993cb6a84ea37ac62f5df14e593b3c8e7c0.

| X | B | all selected events | max root separation at common active C | E_(B,2B]/(X^2 B) | E_(2B,4B]/(X^2 B) |
|--:|--:|--:|--:|--:|--:|
|256|43|1354|94|.008143935|.00004897007|
|1024|85|4146|192|.000503383|.000003051758|
|4096|170|30191|474|.0003994051|.00006894625|
|16384|339|161096|1026|.0001127627|.0000167022|
|65536|678|796161|2408|.00002279416|.000001787648|
|262144|1355|3946588|4832|.00001223382|.0000005296094|
|1048576|2710|19219036|8292|.000002524589|.00000009564436|

No positive E beyond 4B in these seven finite windows. This is not a uniform bound on travel or separation; the finite paths are short. The largest window X=1048576, N=524288:
- total E including diagonal =133827345196; diagonal R=730547400.
- far (|M-M'|>B) E=7807448960, G=5014759522, F=1888462; same-label F=1651606 (87.46%).
- far G_diff=789470066; G_merge=655181494; G_parallel=82947608; G_change=3487160354 (69.54% of far G).
- 36614 actual vertices have at least two distinct incoming labels; 36515 are on their parity-appropriate reset line. Only 13 have two incoming labels >=Q=683, and no far pair first-meets through two such labels at this scale. These are counts of distinct vertices or original pairs as explicitly specified, not interchangeable.

## 6. Next proof task, not just a new sufficient criterion

The original open goal E_d=O(X^2 B) uniformly per band remains. The G_merge component is now bounded by (A), and near pairs were already handled. The quantitative remaining tasks are (i) control S_d, equivalently first-meeting root-pair masses weighted by common suffix (especially same-label first meetings), (ii) control lag-changing common-label transitions using the exact rounding rule in section 3, and (iii) control different-label splits and total constant-lag run contributions. Distinct large-label meeting sparsity alone is not enough. A candidate useful estimate would bound the source-weighted total number/weight of transitions between different nonzero lag classes; no such asymptotic estimate was proved. The next step should examine upward/downward rounding, lag return cycles and their arithmetic constraints in the same-label process, and compare the contribution of first-meeting suffixes to the target. No new Lean compilation or proof of twin-prime infinitude. Main unchanged.
