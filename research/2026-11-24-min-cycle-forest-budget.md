# Full weighted cycle surplus, local cycle-rank deletion, and forest budget

2026-11-24 JST. Research-only continuation of fa0b1d50b75df0b012f731099587f5a8238830fe. New elementary paper deductions, exact finite audits; no Lean compilation. Twin-prime infinitude and the asymptotic cycle-surplus estimate remain open.

## 1. Equivalent elimination graph on prime labels

Use the original canonical MIN sources M odd in [X,2X), dyadic X divisible by four, B=ceil(sqrt(7X)), each source cutoff K(M)=floor((7M-1)/4). Keep r(C), the least eligible prime factor of C-1 or C+1, and R=sum_C r(C)W(C), with original source multiplicities. All actual pre-event horizons lie in [2X,7X). Each source has total gain O(X), and r(C)<=p<=3(p-1)/2 for each selected p.

For a finite word of selected labels p_i>=Q, obtained by deleting events below Q, let C_i be the pre-horizon, sigma_i the eligibility sign, and g_i=C_(i+1)-C_i-(p_i-1)>=0 the total intervening gain. A light gap satisfies g_i<=J. Form a multigraph on distinct labels with one edge between p_i and p_(i+1) for each light gap; loops and parallel edges retained. This is equivalent for cycle elimination to the previous graph of blocks contracted across light gaps: start with the occurrence-position graph consisting of consecutive same-label return edges and light adjacency edges. Each return edge subgraph and each light adjacency subgraph is a forest before contraction. Contracting all return edges gives the label graph; contracting all light edges gives the block graph. Contraction of forest edges preserves e-v+c. Thus both graphs have the same cycle-space dimension.

For each distinct label p let H_p be the C+sigma value at its first occurrence in the finite word. Put d_i=(C_i+sigma_i-H_(p_i))/p_i, an even integer. Every light edge i->i+1 gives the exact equation
    H_(p_(i+1))-H_(p_i) = (d_i+1)p_i-d_(i+1)p_(i+1)+g_i-1+sigma_(i+1)-sigma_i.
The H_p variables disappear in every signed cycle sum. For fixed d, g, sigma the resulting equations are affine linear in the prime labels. Fundamental cycles of a spanning forest generate the full rational elimination conditions, by the same potential argument as in the parent note. Cycle rank is not necessarily rank of the coefficient matrix on primes.

A useful nondegeneracy: on every simple cycle of length >=2 (two parallel edges permitted), every vertex label has a nonzero coefficient in the cycle sum. At a vertex the coefficient is the difference between d values of the incident occurrences plus the difference of two indicators (indicator=1 for the earlier-in-time endpoint of a light edge, 0 for later). For distinct occurrences of the same p, their C+sigma difference is positive (at least p-3>0 for large p) and divisible by 2p, so their d difference is a nonzero even integer, not cancelled by an indicator difference in {-1,0,1}. If they are the same occurrence, the two distinct incident light edges must be its predecessor and successor; the indicators differ. This proves the assertion. A single length>=3 cycle nevertheless has only one equation and does not yield rank k-1 on its k labels. Loops cannot occur for large Q>J+3, by the return recharge congruence. Loops are kept in finite diagnostics where that inequality need not hold.

## 2. Local deletion of arbitrary rank-certified cyclic components

Fix h>=2, Q=ceil(B/log^alpha B), J=ceil(log^beta B), T=ceil(B log^delta B). Consider a word of at most h consecutive positions in the Q-filtered sequence, with C_last-C_first<=T. Then 0<=d_i<= (T+2)/Q and there are only boundedly many equality patterns, sign choices and light-gap placements. For any connected cyclic component of the label graph on k>=2 vertices whose cycle equations have rational coefficient rank >=k-1, enumerate the d_i, the known light gains g_i<=J, the finite pattern and k-1 independent equations. There are at most O_h((1+T/Q)^h(J+1)^h) such choices. Each rank-certified system has at most pi(B) prime tuples, by solving for k-1 coordinates in terms of one free prime (rank k causes no problem). No other unknown gap gains need be enumerated.

For each tuple and any light edge in that component, the two distinct endpoint labels and the known gap fix a CRT class for the earlier even horizon modulo 2pq. There are O(1+X/Q^2) such horizon choices; its later endpoint is fixed. Consequently the union of ALL possible endpoint horizons of these certified components has size
    O_h(pi(B)(1+T/Q)^h(J+1)^h(1+X/Q^2))
  = O_h(B log^(h(alpha+delta+beta)+2alpha-1) B).
Choose alpha=beta=delta=1/(8(h+1)). The exponent is < -5/8, so this is o(B), and its entire source-weighted R cost is o(X^2) even with arbitrary coalescence. The same reasoning applies to a rank-certified connected cyclic subgraph, e.g. a two-edge cycle, without including unrelated tree branches. The audit below classifies full components only, not every such subgraph.

For words with span >T, in disjoint h-blocks of each source, the sum of spans is O(X); each long block contributes at most h B actual endpoint cost. Thus all long-block endpoint tags cost O_h(X^2 B/T)=o(X^2). For all sliding windows of bounded lengths, overlap is bounded by a constant depending on h, giving the analogous tagged estimate. This cannot be applied to all long cycles of unbounded rank span. Only the certified endpoint costs, not every intermediate event or all rank-deficient cycles, are deleted.

## 3. Global exact forest ledger, first without grouping small costs

For the full Q-filtered word of each original source, assign each light edge the cost r(C_i) of its earlier endpoint. Choose a maximum-weight spanning forest (Kruskal, loops rejected). Write S for total weight of rejected edges, H for the weight of earlier endpoints of heavy gaps g_i>J, and R_small for all events with p<Q. The last large event has no edge. A forest plus last endpoint contributes at most B times the number of distinct large labels, since there are at most k-1 forest edges. Therefore, summing original sources,
    R = R_small + H + S + F + last,
    F + last <= (X/2) B pi(B) = O(X^2/log B).
The exact unweighted rejected-edge count for one source is e-k+c, including isolated vertices; an empty word contributes zero. Thus a forest has at most k-1 light edges; heavy gaps are a separate term, not automatically negligible. A sufficient open condition is liminf (R_small+H+S)/X^2<9/32. This is a useful diagnostic, but choosing Q near B leaves a potentially large small-label cost.

## 4. Stronger single residual: group ALL low costs into high-edge weights

Use the established LOW-only barrier for L=2 product of odd primes <=y. Fix y=7, L=210, or take y growing with L<=sqrt B for sufficiently large B (e.g. maximal such cutoff; then y tends to infinity). Divide the full original trajectory into its initial low-only block followed by blocks consisting of a single high p>y and ALL succeeding low events up to the next high or terminal. Every low-only block has gain <L, hence total r-cost <3L/2. Each high block has weight w_i equal to its exact r-cost (high event plus its subsequent low events), with
    w_i <= B+3L/2.
The initial low-only block has cost <3L/2, including when no high occurs.

Make the connected multigraph of ALL consecutive high labels, without a light/heavy split: edge i joins p_i to p_(i+1) and has weight w_i. Loops and parallel edges retained. The last high-block weight is separate. Choose a maximum-weight spanning tree (one vertex/no edge allowed); call its weight F_M and rejected-edge weight S_M. Every tag, including every low event, is counted exactly once:
    R_M = initial_M + last_M + F_M + S_M.
For k distinct high labels, last_M+F_M <= k(B+3L/2). Hence, with S_y=sum_M S_M,
    0 <= R-S_y <= (X/2)[3L/2 + pi(B)(B+3L/2)] = o(X^2)
for fixed y or L<=sqrt B. This is unconditional, independent of coalescence, and retains original cutoffs. The forest/initial/last contribution is bounded for entire paths, not fixed-length windows. The number of rejected edges is exactly n-k, the repeat count, but their weights are chosen optimally, not assigned by chronological repeat positions.

The previously established no-twin clock inequality therefore gives a single OPEN sufficient condition
    liminf_(dyadic X -> infinity) S_y(X)/X^2 < 9/32.
In fact this liminf condition is equivalent to the existing R liminf condition for the stated L choices, because their normalized difference tends to zero. It is a reorganization of the hard estimate, not a proof of it.

NEW exact layer-cake identity: for integer u>=1, retain only edges whose weights w_i>=u in each source's multigraph, keeping the original vertex set, and write beta_M(u)=e_u-k+c_u for its cycle rank. By Kruskal the forest restricted to these edges is a maximum-size forest there; thus exactly beta_M(u) rejected edges have weight >=u, and
    S_y = sum_(u>=1) sum_M beta_M(u).
This counts weighted cycle surplus without choosing an order of equal-weight edges. To bound only the expensive part, choose growing y with L<=sqrt B. The total number of high events is O(X^2/y) by positive gain p-1>=y (up to an immaterial constant). For u0=floor(sqrt y),
    sum_(1<=u<=u0) sum_M beta_M(u) <= u0 * total high events = o(X^2).
Thus it suffices to bound the tail sum u>u0 below the same 9/32 threshold. This unconditionally eliminates low weight layers, not all low labels or all cycles. A proof of an aggregate expensive-cycle bound is missing. This formulation is different from the earlier single-prime multiplicity tail: it measures cycles in a graph of consecutive labels and can charge many repeats to cheap edges rather than the repeated label itself.

## 5. Finite diagnostics, independently checked literal clocks

Both JavaScript function bodies executed in the current runtime, exact integer arithmetic in the tested windows; local cycle matrix ranks use BigInt fraction-free elimination. The saved Node.js scripts and complete JSON results were remotely read back byte-for-byte. Both independently cross-check 6140 event/terminal decisions with the literal parity-GCD oracle at X<=1024. Total R and event counts agree with the prior full-horizon audit.

    node research/min_cycle_forest_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_lowblock_weighted_forest_audit.mjs 256 1024 4096 16384 65536 262144 1048576

First audit: Q=11, max(11,ceil(sqrt B)), ceil(B/log^(2/3) B), ceil(B/log^(1/16) B), J=210, T=ceil(B log^(1/16) B), disjoint high-word lengths up to 8/16/32, exact local affine equations and ranks of FULL connected cyclic components. The tested parameters are diagnostic, not the asymptotic choices in section 2. At X262144, Q37, R=107745566, R_small=21490816, H=54399, F=68495843, last=16471950, S=1232558. For h=8, short windows have 14530 cyclic windows, 17073 total cycle dimensions, 822 rank-certified components and 13708 deficient components; certified actual endpoint tags cost 239768 (not a union of all possible horizons). For h=16 the corresponding cyclic windows/dimensions/certified/deficient are 8641/10343/710/7931. At Q364 and Q1198 no short cyclic windows occur in these finite tests at X262144. This is not a claim of asymptotic absence. Commit be73440f5eca2bc65253154fa1243f6eb72be9b4.

Second audit: grouped costs, fixed y=3,5,7,11,13. All seven windows finished including X1048576 (524288 original sources, 19219036 events). LOW7 results:

| X | R | initial | last | max forest | surplus | chronological surplus |
|--:|--:|--:|--:|--:|--:|--:|
|256|9044|1019|2598|4166|1261|1569|
|1024|33536|3893|9165|18880|1598|3751|
|4096|331583|15600|58317|219883|37783|80515|
|16384|2144640|62679|257789|1605346|218826|533265|
|65536|15481975|250282|2116667|11906095|1208931|4136378|
|262144|107745566|1000920|9801763|89576048|7366835|36499625|
|1048576|730547400|4003834|47030474|639572753|39940339|268041338|

At X1048576, LOW7 has 6565420 highs, 4273096 distinct-label incidences, 2292324 rejected edges. Of these, only 10976 have w>=53 (their total weight 961452), 52 have w>=683 (tail excess sum max(w-682,0)=2756), none w>=2382. The total surplus 39940339 is 5.47% of R and 14.90% of chronological surplus. The maximum observed single grouped weight is 2037. These are finite results; they do not imply the layer-cake asymptotic bound. Other y values are in JSON; do not interpret larger fixed primorials as already satisfying L<=sqrt B. Commit 8db7f53de7d3d37ea26cd8884364296e43f643f6.

## 6. Exact remaining question

Local rank-certified components and long bounded-rank-span endpoint tags have negligible cost under the explicit asymptotic hypotheses. General cyclic graphs need not have enough independent equations on their prime labels; many finite components are rank deficient, and a long global cycle need not be contained in any short block. The unconditional full forest bound removes the whole forest contribution without imposing a local span. The resulting concrete open analytic target is an upper bound on the summed cycle rank of the expensive-edge subgraphs, integrated over weight thresholds, with original source weights and growing LOW cutoff (or fixed LOW7). Possible next approach: estimate the weighted cycle rank by excess edges in connected components of the threshold graph, separate repeated parallel edges from genuinely longer cycles, and look for an arithmetic anti-concentration bound that survives coalescence. A naive count of distinct vertices or unweighted cyclic components is not enough. No new Lean proof or global twin-prime estimate. Main unchanged.
