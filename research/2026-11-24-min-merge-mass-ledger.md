# Source-preserving merge ledger and sparse large-label mass

2026-11-24 JST. Continues bcc8e73dcba8e7b0962012342cf5964b72e0909d (dyadic cut transfer). New unconditional estimates for parts of the full clock budget, exact original-source ledger and finite audit. The full energy estimate, late cross-cut product and twin-prime conjecture remain OPEN. No new Lean compilation.

## 1. Global representative/demotion ledger

Retain the original canonical odd sources M in [X,2X), N=X/2, B=ceil(sqrt(7X)), C0=2M-2, t0=M+2, K(M)=floor((7M-1)/4). Use every actual event up to each source's original K. Include roots and terminal vertices when forming the graph of physical vertices (t,C); only pre-event vertices contribute to R=sum_C r(C)W(C). Here r(C) is the least eligible odd prime or zero. The parent no-twin lower bound is R >= (9/32-o(1))X^2.

The union graph of actual trajectories has strictly increasing C along edges, and at most one outgoing edge at each physical vertex (some original sources there may terminate because of their smaller cutoff). Partition arriving source tags by immediate predecessor vertex; a newly injected root is a singleton. In topological order, maintain exactly one representative in each occupied vertex, the source with largest K (ties resolved by largest M). At the next vertex, each incoming class contains its old representative: if any source in that class can take the edge, the maximal cutoff can take it too. Every root starts as representative. For each incoming non-root label p=C-D+1, combine the representatives from its distinct predecessor-time classes into one maximal representative; the other representatives are demoted and assigned type SAME. Then combine all representative classes with distinct incoming labels p>=Q into one maximal representative; those demoted at this step are assigned BIG. Then combine remaining label classes, assigning type MIXED to demotions. Finally combine with a possible newly injected root, assigning type ROOT to its demotion. Each demoted tag keeps its type permanently; it never becomes representative again. No source is deleted or duplicated. The maximum-cutoff property is preserved at each combination.

At any occupied vertex, all original tags consist of its one representative and its previously or currently demoted tags. Hence
    R = R_rep + R_same + R_big + R_mixed + R_root.
Costs are measured at pre-event states AFTER applying the vertex's demotions. Terminal vertices contribute zero, and the event entering a merger is charged at its predecessor, not at its target. Every source is demoted at most once. This is a deterministic decomposition, not a probabilistic model.

For any particular physical first-crossing entry e in the dyadic cut method, restrict its original source set A_e to the desired block/side. The global ledger gives labels to all these original tags at the entry and can be used with the original cutoff-tagged suffix formula. In particular, at most one member of A_e is a global representative; the rest have already been demoted. If the global representative is not in the restricted block, A_e need not contain any representative. The audit uses this global ledger rather than rerunning a separate representative choice for every block.

## 2. NEW unconditional big-big demotion estimate

Take Q=ceil(B/log^(2/3) B). A vertex (t,C) at which BIG demotions are produced has two distinct incoming prime labels p,q>=Q. If t even, p,q divide both t and C; if t odd, both divide t-2 and C+2. For fixed p,q, counting t,C in the O(X)-sided rectangle gives O((1+X/(pq))^2)=O(X^2/(p^2 q^2)) vertices (pq<=B^2=O(X)). Prime-counting and partial summation give sum_(p>=Q)1/p^2=O(1/(Q log Q)). Thus the number of such physical vertices is O(X/log^(2/3) B). At each vertex all incoming primes divide the same C or C+2, according to parity; since Q^3>7X+2 eventually, at most two distinct incoming large primes are possible (the looser bound four also suffices). Each vertex produces at most one BIG demotion eventually.

Consequently the global count of original tags demoted as BIG is O(X/log^(2/3) B)=o(X). Each original source has total r(C)-cost at most 3/2 times its total horizon gain, hence O(X). We obtain
    R_big = O(X^2/log^(2/3) B)=o(X^2).
This counts only the newly demoted representatives and their costs AFTER demotion. It does not claim that every original source passing a big-big merger has small total weight, or that the pair energy of all such sources is negligible. The same argument bounds their contribution to the left-entry source mass in any single cut by o(X). The contribution to a cross-cut pair energy would need separate estimates. For the direct R budget, this is an unconditional removal even in long trajectories with arbitrary ancestor mass.

## 3. NEW unweighted high-label representative bound

Let y tend to infinity with B, with y<=B. Count representative event occurrences with selected prime p>=y. First remove events whose representative becomes demoted at the TARGET vertex: there are at most N such events (each source demoted once), each with r(C)<=B, so their total cost is O(XB). For the remaining representative events, at most one per target physical vertex survives as representative. In particular, the number with given (p,D,n), where D is the pre-horizon and n the selected clock time, is at most one. Without this survival qualification, distinct predecessor times can have the same (p,D,n) and must not be counted only once.

Fix p and a divisibility side sigma. Candidate D satisfy p|(D+sigma) in [2X,7X). There are O(X/p) such horizons. For r(D)<=z=floor(p^(1/4)), their summed r cost is O(X z/p). For r(D)>z both D-1 and D+1 are z-rough. Write D+sigma=p h. The two forms h and p h-2 sigma have two forbidden residues mod each odd prime ell<=z, since p>z. The standard two-dimensional upper-bound sieve already used in research/2026-11-24-min-reverse-rough-fibre.md applies uniformly here: the h interval has length O(X/p), comparable to X/p>=c p; the sum of squarefree remainder terms up to z is O(z log(2z)), negligible against X/(p log^2 p). Therefore the number of these rough horizons is O(X/(p log^2 p)). Multiplying by r(D)<=p gives
    sum_(D eligible for p) r(D) = O(X/log^2 p).
For each D and side, there are O(X/p) possible clock times n in the time window. Thus the total candidate weight is O(X^2/(p log^2 p)). Summing over primes p>=y by prime-counting and partial summation yields O(X^2/log^2 y). Together with the demoting events,
    R_rep,high = O(XB + X^2/log^2 y) = o(X^2).
This is independent of the incoming source weights and does not assume that the representative trajectories are short. It holds for a growing threshold such as y=ceil(log^2 B), as used in the finite audit. It does not bound R_rep,low for selected primes p<y.

The remaining direct clock budget comprises R_rep,low + R_same + R_mixed + R_root. One can instead continue the earlier E_late route after deleting the above negligible R contributions from the occupation measure: apply Cauchy to the remaining source-tag mass, which is at most the original W(C), with the same sieve S0. The new estimates alone do not bound the remaining mass or the cross-cut product. They are partial unconditional estimates, not a new claim of infinitude.

## 4. Actual finite audit

research/min_merge_token_audit.cpp includes research/min_full_horizon_budget_audit.cpp. Compile from the repo root:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror -Wno-return-type research/min_merge_token_audit.cpp -o /tmp/min_merge_token_audit
    /tmp/min_merge_token_audit 256 1024 4096 16384 65536 262144 1048576
All seven windows actually run. Local tested blob afde237efaac930abb027d1bb64e800606304047 read back exactly at 3030227704874da8aba4173b4c385fa0ee5a291e. Parent blob 995067c02c29590f5f64afb1bbcdc6cd482e29a2. The warning flag is for the macro-renamed parent main only. The code verifies exactly one maximal-cutoff representative in each incoming class and at each physical vertex, that an active vertex has an active representative, the exact partition of R, at most N demotions, the BIG count identity and an O(X) per-tag total bound. It includes terminal vertices, retains original cutoffs, and records tag classes at first crossing of the top-level cut J=3X-4 for left origins farther than B from J. The high-label estimate is a paper argument; the code measures all representative high events including those demoted at their targets, not the separate candidate sieve count.

| X | all selected events | R | SAME demotions | BIG demotions | MIXED demotions | ROOT demotions |
|--:|--:|--:|--:|--:|--:|--:|
|256|1354|9044|54|0|11|31|
|1024|4146|33536|233|0|26|129|
|4096|30191|331583|1052|0|143|532|
|16384|161096|2144640|4392|0|571|2167|
|65536|796161|15481975|18223|0|2403|8726|
|262144|3946588|107745566|74456|2|9932|35065|
|1048576|19219036|730547400|303843|13|40135|140665|

At X=1048576: N=524288, B=2710, Q=683, y=63; 1899448 occupied physical vertices (including terminal), 1859816 active physical vertices. Exact costs: R_rep=56594678 (R_rep,high=44537675, R_rep,low=12057003), R_same=422800021, R_big=17931, R_mixed=55953135, R_root=195181635. The top-level cut has 29 distant left tags crossing, classes at crossing REP=2, SAME=18, BIG=0, MIXED=2, ROOT=7; no far-cut pair overlap at that level in the earlier audit. These are finite diagnostics, not uniform asymptotic estimates. The dominant costs are SAME and ROOT; their bounds remain missing.

## 5. Next target

At a SAME merger, the pre-horizon D is fixed by the common incoming prime, and all distinct predecessor times lie in the exact last-clock interval of length <=2r(D). At most one representative from each prior physical state survives to that interval. The next task is to estimate the actual post-demotion suffix costs of these representatives (and of ROOT demotions on the odd reset line C=2t-6), retaining their individual cutoffs. Bounding only the number of possible predecessor times or only the number of merger vertices is not sufficient. The original late cross-cut energy can also be calculated for the trimmed tag mass; no uniform estimate of it has been obtained. Main untouched.
