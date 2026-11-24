# Eliminate arbitrary shared donor gain: paired large-return motifs and cycle-space obstruction

2026-11-24 JST. Research-only continuation of 85aadc79dbae4d7fd114062986ff26dc6fc25c7f (return matrix rank). New elementary paper deductions, exact finite JavaScript audits. No new Lean kernel verification; twin-prime infinitude and global clock budget remain open.

## 1. Definitions and exact cancellation

Retain the original canonical MIN sources odd M in [X,2X), dyadic X divisible by 4, B=ceil(sqrt(7X)), initial t=M+2,C=2M-2, K(M)=floor((7M-1)/4). Every event selects the first lexicographic eligible (time,odd prime) and advances the even horizon C by p-1. All pre-event horizons are in [2X,7X); r(C) is the least prime <=B dividing either neighbor (zero if none), R=sum_C r(C) W(C), with original-source multiplicities. The per-source total horizon gain is O(X), and no source visits any horizon twice.

Fix alpha,beta,delta>0 and Q=ceil(B/log^alpha B), J=ceil(log^beta B), T=ceil(B log^delta B). For a fixed integer h>=4 consider the subsequence of large events (p>=Q). A qualifying motif consists of two disjoint adjacent pairs in this subsequence, whose four labels are either p,q,p,q or p,q,q,p with p!=q. Their first to last large-event rank span includes at most h positions. Between the first two and last two endpoints the total intervening horizon gains g1,g3 are at most J (excluding the endpoints themselves). The middle gain g2 is arbitrary, includes ALL events strictly between endpoints 1 and 2, and may contain smaller or large labels. It is not assumed to be LOW7 or even bounded by any primorial. Write C_i for the four pre-event horizons, sigma_i=+/-1 for their eligibility sides, i=0,1,2,3.

Same order: eligibility gives
    m p = C2-C0+sigma2-sigma0 = p+q-2+g1+g2+sigma2-sigma0,
    n q = C3-C1+sigma3-sigma1 = p+q-2+g2+g3+sigma3-sigma1.
Subtract to get
    m p - n q = g1-g3+sigma2-sigma0-sigma3+sigma1.

Reverse order: use m p=C3-C0+sigma3-sigma0 and n q=C2-C1+sigma2-sigma1. Subtract to get
    (m-1)p-(n+1)q = g1+g3-2+sigma3-sigma0-sigma2+sigma1.

Both equations have the form a p - b q = c, with |c|<=2J+6. The multipliers a,b are positive for large Q (m,n are positive even integers by parity of the horizons and signs). Neither formula depends on the internal word of the shared middle gain. They hold even when there are further p or q occurrences inside g2. In the zero-offset case, a p=b q implies a>=q,b>=p, forcing g2>=pq-O(B+J). Thus zero-offset motifs cannot have short middle gain for the indicated parameters, once B is sufficiently large.

## 2. Unconditional removal of endpoint cost

For g2<=T, the multipliers a,b are O((B+T+J)/Q). There are O(J+1) choices of c and O(((B+T+J)/Q)^2) choices of a,b. For each p prime <=B and each such choice, q is uniquely determined; requiring it to be a distinct prime only decreases the count. This bounds possible ordered pairs by O(pi(B) (J+1) ((B+T+J)/Q)^2). Counting all possible FIRST pair horizons, for fixed (p,q) and g1<=J and signs, C0 and C1=C0+p-1+g1 are determined by two eligibility congruences modulo p and q. CRT gives O(1+X/Q^2) even C0 candidates. Counting possible LAST pair horizons separately uses the analogous congruences and g3<=J, regardless of pair orientation. There is no need to enumerate g2 or its positions; each pair contributes its two endpoint horizons. Thus the union S of all possible endpoint horizons of SHORT motifs has size
    |S| = O(pi(B) (J+1)^2 ((B+T+J)/Q)^2 (1+X/Q^2))
        = O(B log^(4 alpha+2 beta+2 delta-1) B).
Here X=Theta(B^2), pi(B)=O(B/log B). If 4 alpha+2 beta+2 delta<1, this is o(B), and the FULL source-weighted cost at ALL these horizons is <=(X/2) B |S|=o(X^2), even if another source does not execute a motif there. No independence, no coalescence estimate.

For g2>T the bounded rank span gives a different argument. Per source every actual event contributes gain to at most O(h^2) middle intervals: a containing interval has both endpoint ranks within h of the event's gap in the large subsequence. Hence the sum of g2 over all qualifying motifs of that source is O_h(X). There are O_h(X/T) long motifs per source, and their four actual endpoint costs are <=4B each. Summing across X/2 sources, the cost of the actual long-motif endpoint TAGS, counted with multiplicities, is O_h(X^2 B/T). This does NOT bound the cost of all other sources visiting the same horizons, and does NOT remove events strictly inside the shared middle interval.

Take alpha=beta=delta=1/16. We obtain |S|=O(B/sqrt(log B)) and total removable actual endpoint cost O_h(X^2/log^(1/16) B)=o(X^2). This includes the consecutive four-large-event alternating case and the reversed case, with arbitrary intervening events. It is an unconditional estimate on a class of actual events, not an estimate on the entire R. The finite diagnostic cut J=210 is fixed, not the asymptotic choice. A constant J also satisfies the argument with beta=0.

For unrestricted rank span the SHORT horizon-union bound still holds, even if g2 includes arbitrarily many large labels. The LONG tagged bound uses fixed h and must not be extrapolated to unbounded rank spans. Equivalently, outside the short sparse horizon set, no two light adjacent pairs with the same unordered pair of distinct large labels can recur within a middle horizon gain <=T.

## 3. Exact general elimination graph

Take any fixed finite large word p_0,...,p_(n-1), not necessarily distinct, and signs. Write g_i>=0 for the total gain between large events i and i+1. Declare some g_i known (e.g. enumerated light gains), the rest arbitrary unknowns. Consecutive returns of a label p at positions a<b yield
    sum_(i=a..b-1) g_i = m p - sum_(i=a..b-1)(p_i-1) - (sigma_b-sigma_a).
Subtract known g_i terms on the left from the right. For each position j let U_j be the sum of unknown gap gains preceding j. Then the remaining left side is U_b-U_a. Contract adjacent positions across known gaps into blocks; U_j is constant on a block. Conversely the potential differences of successive blocks uniquely determine the unknown gaps. Fix the first potential to zero, or allow a global additive shift. Make a directed multigraph on blocks with one edge from block(a) to block(b) for each return, allowing loops and parallel edges. Edge right sides are affine linear expressions in the distinct large labels, for fixed integer multipliers and signs.

Over Q, the exact elimination condition for arbitrary unknown potentials is that each signed sum of edge right sides on an undirected graph cycle is zero (loops and two parallel edges count as cycles). Necessity telescopes. Sufficiency follows by choosing a root potential on each connected component, assigning potentials along a spanning tree, and checking the non-tree edges via fundamental cycles. One component containing the first block has its root potential fixed to zero. The cycle space has dimension e-v+c for e edges, v blocks, c weak connected components. These are independent conditions on the EDGE RIGHT SIDE vector, not necessarily independent equations on the prime variables after substitution. Nonnegative even integer gaps and MIN clock feasibility are additional constraints, not eliminated by this rational calculation.

Important obstruction: if EVERY intervening gap is arbitrary, each block is a single large position. Consecutive returns of each distinct label form a path on its own positions, and the return graph is a disjoint union of paths. It has e-v+c=0. Thus there is no nontrivial linear equality on the primes obtained by cancelling ALL arbitrary gap variables. More explicitly, the return-gap interval matrix has full row rank: change to prefix potentials, then use independence of the edge incidence rows of a forest. This does not say that there are no arithmetic or inequality constraints; it rules out a direct generalization of the previous rank deletion based purely on linear cancellation with all gaps unrestricted. Known gaps that contract the paths into cycles are the mechanism required here. The paired motif in section 1 produces parallel edges after contracting its two light outside gaps, with opposite order changing the affine right side but not the cycle count.

## 4. Exact finite audits

Executed the JavaScript function bodies in the current runtime, including exact integer checks (all arithmetic in these windows is below the safe integer limit). The two programs are separately saved as runnable Node.js .mjs files, with complete JSON output. No extrapolation from the finite results.

    node research/min_interleaved_return_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_interleaved_pair_audit.mjs 256 1024 4096 16384 65536 262144 1048576

First audit: consecutive four large positions, alternating pattern only, J=32,210, three Q cuts. All six windows executed; R and full event counts match the parent audit. Literal parity-GCD comparator for every event/terminal in X<=1024 (6140 checks). At X262144, Q=37, J=210, there are 69 motifs, of which 47 contain middle labels >7; 69 short, no long; 28 distinct short endpoint horizons have full original-source R cost 56,351. Q=364 and 1198 have none. Code and results committed/read back exactly at c445dfb0f64edc869ab6bd1f72c885a5d0a7a7f2.

Second audit: h=8, J=210, two disjoint adjacent large pairs of the same unordered pair, both orientations, with any middle events; full original cutoffs. Includes the 6140 literal comparisons for X<=1024 again. At Q=max(11,ceil(sqrt B)):

| X | Q | same | reverse | long middle | middle contains >7 | nonadjacent pairs | short endpoint union_R | full R |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
|256|11|30|7|11|11|11|2633|9044|
|1024|11|6|8|0|14|14|5115|33536|
|4096|14|1|9|1|9|8|9932|331583|
|16384|19|233|85|0|261|165|104190|2144640|
|65536|27|233|35|0|255|243|279358|15481975|
|262144|37|169|300|6|447|391|450444|107745566|
|1048576|53|733|528|16|1230|1013|2328285|730547400|

At X1048576, 524288 sources, 19,219,036 full events, 2,050,462 large events at Q53. 1,588,958 light ordered adjacent pairs, 1,261 matching paired motifs, 1,245 short, 16 long. Short endpoint union has 204 horizons, cost 2,328,285 (0.3187% of full R). The sum of actual tagged endpoint costs over all motifs (not union) is 557,808. Maximum observed middle gain 4428. No zero-offset motifs across all tested bands/windows. For Q=ceil(B/log^(2/3) B) or Q=ceil(B/log^(1/16) B) there are no qualifying paired motifs at any tested X. These are diagnostics at finite scales, not a uniform proof and not evidence that the asymptotic cutoff has appreciable coverage. Code and results committed/read back exactly at 03ef98bd6dc8a968ae86eb00e2b6c69e49a40545.

## 5. Next mathematical target

The elementary cancellation method works for cycles created by light-gap contractions, including arbitrary shared middle histories. Its exact forest obstruction identifies why arbitrary gaps cannot be erased wholesale. The finite near-top results also indicate that two-pair repeat motifs alone are unlikely to account for a large share of the full clock budget.

A sensible next target is to count cycles in a contracted return graph using a weighted choice of light gaps, not to continue enumerating only repeated ordered pairs. Specifically, for a fixed large-word span h, measure how many return rows survive elimination (e-v+c), the rank of the resulting affine coefficient system, and total endpoint R after arithmetic sparse deletion, retaining signs and original-source weights. If too many returns form a forest, the missing analytic input is a bound on gain/elapsed time or source-weighted occupancy of the forest histories. In particular the full-horizon R criterion liminf R/X^2<9/32 from the parent is still open. Main and Lean files unchanged.
