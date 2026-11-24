# Coupled return matrices, rooted uniqueness and dense local-block deletion at the square-root scale

2026-11-25 JST. Continues 5b86598bc297155349a84c3dec84f2c8c5d4ea21 on the SAME research/min-cycle-forest-2026-11-24 branch. New deterministic rank theorem for simultaneous first-to-last return equations in a strongly coupled local word, and a weighted discovery bound on ALL events in the union of local words in which each label repeats within that word. This goes beyond recurrence of a single unordered edge and does not require discovery-time or rank locality. Strongly coupled words can have no repeated unordered edge combinatorially. Exact proof and finite diagnostics. No external search or Lean compilation. Full signed peak convergence and physical far-coalescence upper bound remain unresolved.

## 1. Setting and local words

Use the common independent CRT ghost for infinite odd primes or a finite initial prime segment, conditional on common initial clock parity. At executed label p the even gain increases by p-1, with completed preceding wait w<=2p. Through integer U the exact tick-history law bounds the conditional first-selection hazard of every unused p>=z0=ceil(sqrt(2U)) by 2/p^2. All discoveries and eligibility coordinates refer to the original trajectory.

Let A>=5 be the HIGH cutoff and L=2 product_(3<=ell<A)ell the LOW primorial. Between consecutive HIGH events the intervening LOW gain is even and in [0,L). Use the prefix through U whose POST-gain is <=2U. It contains all earlier states of every positive attained peak. The sum of executed label weights in it is <=3U and its gain is strictly increasing. Assume z0>max(7,L+3).

Take K>=2 integer. A local word is a contiguous segment of the HIGH-event list, with all labels >=z0, and span S between its FIRST and LAST PRE-gains at most K times its minimum label P. No intermediate HIGH label is skipped, though LOW events are not listed. Call the word dense if EVERY distinct label in the word occurs at least twice within the word. This is a definition about internal repetition, NOT whether the labels have been previously selected globally. Write its distinct labels as p_1,...,p_h, in increasing order. Its number of events is <=2K+1: all but the last supply gain >=P-1>=P/2 within S. Because every label repeats, each supplies at least one jump within S, so its maximum label is <=S+1<=K P+1. The gain cap implies all labels <=2U+1.

Define a directed graph on the labels: i->j for i!=j if an occurrence of p_j lies strictly between the first and last occurrences of p_i in the word. The dense word is coupled if this graph is strongly connected. The graph records return dependence, not the undirected consecutive-edge graph of the previous note.

## 2. Every dense word contains a coupled word

In the directed dependence graph choose any sink strongly connected component C (one with no outgoing arc to its complement); such a component exists in every finite directed graph by its acyclic condensation. For a label in C, its first-to-last index interval contains only labels in C, by the absence of outgoing arcs. Every arc within C joins intersecting first-to-last intervals, because the relevant occurrence belongs to both intervals. Strong connectivity implies that the union of these intervals is connected on the index line. The union is therefore a single interval from the minimum first index to the maximum last index of C. Every event in that interval is in C, and all occurrences in the original word of each C label lie in this interval. Thus it is itself a dense coupled word, using exactly C. Its span is <=S<=K min(C). A sink component cannot consist of a single label: that would force consecutive equal HIGH labels p>=z0>L+3 inside its first-to-last interval. Consecutive equal HIGH labels at this scale are impossible by the previous even-gain eligibility lemma (p-1+d is even in [p-1,2p-2) and not 0 or +/-2 mod p). Hence every dense word contains a coupled subword with at least two distinct labels and at least one internal edge. This reduction does not remove events from the physical dynamics.

## 3. Return matrix and rooted uniqueness

In a coupled word, fix a label p_i and let n_ij count occurrences of p_j in the segment starting at the first p_i event and ending just BEFORE the last p_i event (including the first p_i). Let N_i=sum_j n_ij, and d_i the total intervening LOW gain along that segment, so 0<=d_i<N_i L. The pre-gain difference of these equal labels is m_i p_i+a_i, with a_i in {-2,0,2}. The coefficient m_i is positive even: the difference is even, and the first p_i jump >=p_i-1>4 implies m_i>=1 and hence >=2. The equality of actual gains gives
    (m_i-n_ii)p_i - sum_(j!=i) n_ij p_j = e_i,
    e_i=d_i-N_i-a_i.                                     (1)
Let M be the h by h integer matrix with diagonal m_i-n_ii and off-diagonal -n_ij. Its dependence graph is exactly the coupled graph. In vector form M p=e. Bounds from the local word give N_i<=2K, n_ij<=2K, m_i<=K+2 (m_i p_i<=S+2), and
    |e_i| <= E0=2K(L+1)+2,
    sum_(j!=i) n_ij p_j <= sum_j n_ij p_j
          <= S+N_i <=2K P.                              (2)
In the last inequality use P>=2. Every nonzero n_ij p_j>=P.

Rooted uniqueness theorem: if
    P > E0 (2K+1)^h,                                    (3)
then EVERY principal (h-1) by (h-1) minor of M is nonsingular. In particular, given M,e and ANY one label p_r, all the other labels are uniquely determined as rational numbers by the other h-1 rows (and we can check the omitted row separately). The statement does not say that M itself is invertible.

Proof: Fix a root r and suppose a vector x with x_r=0 solves (M x)_i=0 for every i!=r. If x!=0 put y_i=x_i/p_i and change its overall sign if necessary so that B=max_i |y_i|>0 is attained with y_v=B. Write delta_i=B-y_i>=0. Subtract the equation (1) for p, multiplied by y_i, from the homogeneous row for x. For i!=r this yields
    sum_(j!=i) n_ij p_j (y_i-y_j)=-e_i y_i.
Equivalently,
    sum_(j!=i) n_ij p_j delta_j
         =(sum_(j!=i) n_ij p_j)delta_i-e_i y_i
         <=2K P delta_i+E0 B.
For an arc i->j this implies delta_j<=2K delta_i+E0 B/P by nonnegativity and (2). Start with delta_v=0 and take a directed simple path from v to r, of length <=h-1; all rows before reaching r are available by hypothesis. Propagating the inequality gives
    B=delta_r <= (E0 B/P) sum_(l=0)^(h-2)(2K)^l
                  < (E0 B/P)(2K+1)^h < B,
a contradiction. Thus the principal minor has trivial kernel. This proof uses the actual positive solution p of (1) as the comparison vector, and no generic random-matrix nonsingularity assertion. In particular strong connectivity alone, without the small-error/scale condition, is not being claimed sufficient.

## 4. Counting entire coupled-word support tuples at first discovery

Choose U,K,L so that z0>E0(2K+1)^(2K+1); this guarantees (3) for all qualifying words. There are at most
    B(K,L)=sum_(2<=h<=2K+1) h (4K+5)^(h^2) (2E0+1)^h
possible bounded integer arrays (M,e) and root indices, using a conservative sup bound |M_ij|<=2K+2. Thus
    log B(K,L)=O(K^2 log(2K(L+1))).                       (4)
The labels are listed in increasing order, so no additional uncounted permutations are needed. Discard singular root minors from this list. At the FIRST discovery among labels of a prospective support tuple, the selected prime x and its history are known. For each pattern and root index solve the nonsingular linear equations with p_r=x. At most one candidate tuple results. Filter to distinct increasing prime labels >=z0, <=2U+1, with all other labels still unused after the root's first selection and max<= (K+1) min. We may discard any candidate failing these conditions or the omitted row; every actual coupled support qualifies for its earliest discovery and at least one pattern. The candidate tuple is determined at that root's first tick and does not depend on later return success.

At least one other candidate label y must subsequently be selected for a qualifying coupled word. Choose a definite such y (e.g. the smallest other candidate). It is unused and y>=x/(K+1). Conditional on the entire history through x's first selection, its first-selection probability by U is <=min(1,2U/y^2)<=2U(K+1)^2/x^2 by summing the conditional hazard only until its first selection. This applies even if other future candidate selections are adaptive; we require only one other discovery and use no independence of the later path. For a fixed x the probability of its own discovery through U is <=2U/x^2. These two estimates can be iterated at the root stopping tick, by conditioning on the finitely many possible first ticks and their histories. The argument overcounts tuples with more missing labels, which is harmless. It does NOT condition the first-selection hazard on a future coupled word.

Mark the targets of all internal consecutive HIGH edges of all coupled words in the capped prefix, counting each event only once. Call their total prime weight W_coupled. For a fixed actual support tuple of h labels, there are <=4L occurrences in the capped prefix of each unordered pair of distinct labels: this is the deterministic CRT multiplicity theorem in 5b86598bc297155349a84c3dec84f2c8c5d4ea21 (two directions, four sign pairs, L/2 LOW gains, period 2 p q>2U). Thus the union of its marked endpoints over ALL possible coupled words with that support has weight at most 4L binom(h,2) max label <=C L (K+1)^3 x. This remains true when words overlap or appear many times at unrelated locations. A tuple can be charged to the earliest discovery and any one of its realized patterns, and the overcount by all successful patterns can only increase the upper bound.

For each possible x and pattern, the expected weight charge is therefore at most C L (K+1)^3 x (2U/x^2)(2U(K+1)^2/x^2). Summing over patterns and all prime x>=z0, the elementary prime-count bound yields
    sum_(x>=z0 prime) x^-3=O(1/(z0^2 log(2z0))).
Consequently
    E W_coupled <= O(B(K,L) L (K+1)^5 U/log(2U)).           (5)
This is a root-scale bound for arbitrary coupled local words, not just words of two labels or previously repeated edges. It uses neither roughness nor first-discovery locality. It does not assert that arbitrary sparse closed walks meet the coupling criterion. The finite-alphabet case has the identical proof (discard unavailable candidate labels). The conditional argument uses only the exact unused-label hazard at root or above and deterministic support reconstruction, not a new hazard for already-selected labels.

## 5. Covering all dense local words without repeated charges

Define W_dense to be the prime-weighted union of ALL high events belonging to at least one dense local word in the capped prefix (including the first event of each such word, and even globally fresh events if present). By section2, each dense word contains a coupled subword and hence at least one marked endpoint. Choose one marked endpoint i per dense word. Let G_i be its pre-gain and p_i its label. Every event in the chosen word has pre-gain within [G_i-K p_i,G_i+K p_i], since the word span <=K min label<=K p_i. Each label of that dense word repeats within it, so its jump <=S<=K p_i. Therefore the entire gain interval of each high event in the word is contained in
    [G_i-K p_i, G_i+2K p_i].
For a fixed anchor i take the union of these event sets over ALL words assigned to it. The actual event gain intervals [g_pre,g_post) are disjoint because gain increases. Their total gain is at most 3K p_i, and the sum of label weights is <=1.5 times gain, hence <=(9/2) K p_i (we use a loose 6K p_i). Sum over distinct marked anchors, which covers the union of all dense words; even if two anchor covers overlap, their total is a valid upper bound. No per-word charging of the same anchor is needed. We have the deterministic resource bound
    W_dense <= 6K W_coupled.
Together with (5),
    E W_dense <= O(B(K,L) L (K+1)^6 U/log(2U)).             (6)
The result concerns the entire dense-word union, not merely the closing events. Choose for large U
    K=max(2,floor((log log U)^(1/4))),
    A slowly growing with L<= (log log U)^(1/4).
The finite initial small-U regime need not satisfy these choices. Then log B=O((log log U)^(1/2) log log log U)=o(log log U), condition (3) holds eventually since E0(2K+1)^(2K+1)=exp(o(log U)), and B L (K+1)^6=(log U)^o(1). In particular
    E W_dense/U <= (log U)^(-1+o(1)) ->0.                   (7)
Both K and A can tend to infinity, although slowly. This is a genuine gain-union bound at square-root scale, not an unrestricted count of all first-to-last spans. It works even if distinct edges are never repeated. Combinatorially, for instance the word a,b,c,a,d,b,e,c,d,e has five labels each twice and nine distinct unordered edges, with strongly connected dependence graph. This is an illustration of the difference of the graph conditions, not a claim that this word is realizable by actual CRT clocks.

## 6. Consequences for the signed residual

For the existing shadow/record backward scan, at a high repeated target p>=z0 eventual p>=10L+14 and its positive preceding-LOW corrected increment is <=4p. Thus the total positive contributions at events in the dense-word union are <=4 W_dense and have expectation o(U) with the choices above. Remove these positive increments once along with the prior classes; keep the actual disjoint negative credits C_shadow,C_other,Nminus unchanged. The earlier inequality continues in the form
    E[(D(U)-[R_new-C_shadow-C_other-Nminus]_+)_+]=o(U).
A remaining positive repeated ordinary high endpoint above root cannot belong to ANY contiguous local word above root (span<=K min label) in which every label appears at least twice. This holds simultaneously over all placements of such words. In particular any window of width K z0 with all high labels >=z0, after splitting at the marked dense-word events for bookkeeping, has no contiguous subword with every label appearing twice or more. Every nonempty remaining contiguous subword must have some label occurring exactly once in that subword. With h distinct labels such a word has length <=2^h-1, by recursively splitting at a singleton. This is a structural restriction, not necessarily a better numerical length bound than the previous simple-edge bound h(h-1)/2+1 at large h. We do not turn the accounting removal into a new legal dynamic trajectory.

The method leaves windows in which a few repeated labels are supported by singleton labels, mixed-scale words containing high labels below z0, and long-span words outside K min. It does not prove that the remaining positive record increments are sublinear, nor that the first-to-last intervals of all repeated labels are globally disjoint. The full signed limit eta->0 and independent actual physical far-coalescence bound remain open.

## 7. Finite diagnostics and persistence

Saved research/min_ghost_coupled_return_matrix_audit.mjs and research/min_ghost_coupled_return_matrix_results.json; exact remote readback at 1fd87f824bb6d5608f1f58a926a750a9c1e5c12d. Run node research/min_ghost_coupled_return_matrix_audit.mjs 256 1024 4096 16384 65536. Executed script logic in the available JavaScript runtime; no separate local Node or Lean compilation. Fixed pseudorandom CRT phases, finite alphabet <=4U,128 paths per window except64 at largest. A5,L6,K12, diagnostic base=max(11,floor(z0/32)); this is below analytic root and deliberately exercises small actual dense words. No numerical estimate of asymptotic constants or calibrated coupling error.

Enumerate every diagnostic contiguous HIGH subword within span K times its minimum. For words with every label repeated, compute reachability of the dependence graph, choose a sink component, and verify its first-to-last union forms a contiguous subword over exactly its labels. Compute actual return matrix and RHS, check all gain identities and error bounds, use exact BigInt Bareiss determinants for each principal root minor, and when invertible verify reconstruction by Cramer's rule at earliest discovery root. Mark all internal edges of each distinct extracted coupled sink interval. Check actual union of dense words is covered by their chosen marked anchors' gain intervals, and union weight <=6K times the marked weight. The audit extracts one sink per dense word (sufficient for coverage), rather than enumerate candidate patterns in the expectation proof. For any actual diagnostic block satisfying (3) check all minors nonsingular; none of the observed blocks reach this scale gate. Separate synthetic strongly connected integer matrices of sizes 2 through 6 with very large positive comparison vectors and bounded errors test (3) nonvacuously, using exact determinant expansion, 240 minor checks. These are algebraic test cases, not actual ghost paths or prime tuples. Also test the five-label edge-distinct example combinatorially.

Across five windows: 9400 diagnostic local words examined (772+1186+2460+2876+2106=9400); 14 dense words and 14 distinct extracted coupled subwords, all with two labels and four HIGH events; 28 actual root minors, all invertible, 14 exact earliest-root reconstructions; 56 dense-union events of total weight720, 42 marked events of weight538. Three blocks have both labels' first times far from the local block by the diagnostic K p rule. At U65536,N64:3543 executed events,2106 local words,2 dense/coupled blocks,4 actual minor checks,2 reconstructions,6 marked endpoints of weight72,8 dense-union endpoints of weight96; all checks pass. No observed actual dense word with all labels >=analytic root, no observed coupled word with >=3 labels or with all edges distinct. The higher-dimensional rank property is tested in synthetic matrices, the edge-distinct distinction by the combinatorial word. The asymptotic probability and union estimates are analytic results, not empirical extrapolations. No Lean compilation.

## 8. Next target

The simultaneous return matrix makes strongly coupled local stock a one-parameter integer family; the sink decomposition and gain cover propagate that estimate to every event of internally dense local words. Remaining sparse local words with singleton donors may have a higher-dimensional return matrix because those donors have no internal return equation. A useful next step is to quantify how many distinct singleton donors are needed for the remaining positive repeated record surplus, or use their negative/fresh cost in a signed allocation. No main edit, no new branch, no twin-prime proof.
