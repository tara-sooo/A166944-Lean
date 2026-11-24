# Return-matrix rank via sink components, sparse subwords, and actual MIN audit

2026-11-24 JST. Research-only continuation of 4f3d709a6dba7d35d3d1e55b75507e55f80806b5 on research/min-quantitative-palette-2026-11-24. Paper deductions (not Lean-checked), exact finite audit, no proof of the twin-prime conjecture. The method below refines the short large-return deletion argument and finite-palette theorem in the parent branch.

## 1. Return matrix

Keep canonical MIN, X dyadic, B=ceil(sqrt(7X)), original M, t=M+2, C0=2M-2, K(M)=floor((7M-1)/4). Fix LOW7 with L=210; between two consecutive high (>7) events the LOW gain is an even nonnegative integer <L by the existing even-multiple barrier. Consider a contiguous high word of length n<=h, h fixed, with k distinct primes p_i in [Q,B], Q=ceil(B/log^alpha B), alpha>0 fixed. No other high labels are deleted.

For consecutive occurrences of p_i in this word at positions a<b, let d=b-a and n_j count label j in [a,b). Let e be all intervening LOW gain and sigma_a,sigma_b the signs. Subtracting endpoint eligibility gives the exact equation
    sum_j n_j p_j - m p_i = d-e-(sigma_b-sigma_a),
where m=(C_b-C_a+sigma_b-sigma_a)/p_i is an integer. Here n_i=1, and m is positive and even for sufficiently large Q. The right side is O_(h,L)(1), and |m|=O_(h,L)(B/Q). Collect all consecutive return equations as A p=c. The number of rows is n-k.

## 2. Graph rank theorem

Draw i->j (j!=i) whenever j lies strictly between two consecutive occurrences of i. Let s be the number of sink strongly connected components. For sufficiently large B (depending on h,L,alpha), rank_Q(A)>=k-s.

Proof: for every label i add the negatives of all its return rows, defining a k-by-k matrix M (zero rows for labels with no returns). Then M p=c' with c' bounded in terms of h,L. Its off-diagonal entries are nonpositive integers, nonzero precisely on the graph edges. Write T=M diag(p), so T has row sums c'. Set D=T-diag(c'), a row Laplacian with weights w_ij=-T_ij>=Q on every edge. Choose one root in each sink SCC; every vertex has a path to some root. Let U be all nonroots and d=|U|=k-s. If d=0 the claim is immediate.

By the directed matrix-tree/forest identity for a row Laplacian, det D[U,U] is the sum of nonnegative weights of directed spanning forests oriented toward the chosen roots, with one outgoing edge from each nonroot. At least one such forest exists (choose edges reducing distance to the roots), hence det D[U,U]>=Q^d. Every entry of T and D is O_(h,L)(B): off-diagonal counts are bounded and diagonal equals row sum minus off-diagonal sum. Expanding the determinant, the diagonal perturbation diag(c') changes the minor by O_(h,L)(B^(d-1)). For fixed d and alpha, Q^d/B^(d-1) tends to infinity. Therefore det T[U,U] is nonzero for large B. Multiplication by diag(p) is invertible, and M is a row combination of A, yielding rank(A)>=rank(M)>=d.

In particular a unique sink implies rank>=k-1. This is a rank lower bound, not equality; multiple sinks may still have high rank. No probability or MIN timing rule is used in this argument, only horizon updates and the LOW barrier. The directed forest identity is the standard all-minors matrix-tree identity; it is not formalized here.

## 3. Rank-certified unconditional deletion

For fixed abstract word (equality pattern of labels), k>=2, with rank(A)>=k-1, choose k-1 independent return rows. There are O_(h,L)((B/Q)^(k-1)) choices of their multipliers, signs and LOW gains; the choices of independent row positions and word shape are bounded. For each such system one coordinate can be left free and the other k-1 coordinates solved uniquely (including the case rank k, by using only the chosen rows). The free coordinate must be prime <=B, so there are at most pi(B) possible tuples for each system. For each tuple and bounded LOW/sign choices, the first occurrences of two distinct primes fix the initial even C modulo 2 p_i p_j. Thus O(1+X/Q^2) initial horizons occur in [2X,7X). All horizons through the last high in the word, including intervening LOW events, lie in a bounded-size set of offsets from that C for each tuple and LOW choice. In total the possible horizon union has size
    O_(h,L)(pi(B) (B/Q)^(k-1) (1+X/Q^2))
    = O_(h,L)(B log^(alpha(k+1)-1) B).
If alpha<1/(k+1), this is o(B). All actual pre-event visits to these horizons, even by other sources/other words, contribute o(X^2) to R=sum_C r(C)W(C), since r(C)<=B and W(C)<=X/2. This is an unconditional upper bound on the possible horizon set, not an inference from observed words. For a fixed maximum h, rank>=k-1 requires n-k>=k-1, so k<=floor((h+1)/2). One common alpha<1/(floor((h+1)/2)+1) works for every qualifying word of length <=h.

## 4. Combinatorial corollary: local singleton obstruction

For large Q, consecutive equal high labels are impossible by the prior recharge bound and LOW gain <L. Hence a singleton sink SCC must be a label occurring just once in the word: a repeated label would have an intervening different high label, and therefore an outgoing edge.

If a sink SCC S has at least two vertices, all its labels repeat (strong connectivity). The intervals from first to last occurrence of its labels overlap along graph edges, so their union is a single interval of positions. No position in that interval can have a label outside S: any such position is strictly inside a member's interval, and creates an outgoing edge to another SCC, contradiction. The interval contains every occurrence of each label in S. Its induced return graph is exactly the original SCC, hence has a unique sink and satisfies the rank bound in section 2. It is a contiguous high subword.

Therefore every word of length >=2 with at most one singleton label contains a rank-certified contiguous subword: if it has a nonsingleton sink use that SCC interval; otherwise all sinks are singleton labels and there is exactly one sink, so use the whole word. A word with one distinct repeated label is impossible at these Q. After deleting the sparse horizon union of all qualifying words of bounded length <=h, every surviving contiguous segment of length 2..h of all-large high labels must contain at least TWO distinct labels appearing exactly once in that segment. This statement only concerns unbroken segments after deleting horizons, not a filtered word concatenated across deletions. The two singletons are local, not necessarily new discoveries globally. Thus the corollary does NOT yet bound global repeat budgets.

## 5. Exact actual-trajectory audit

Run:
    python3 research/min_return_rank_audit.py 256 1024 4096 16384 65536

All five windows actually completed; 262144 was attempted but timed out and is excluded. The audit uses original source cutoffs and parity clocks, exact rational rank by fraction-free elimination, directed transitive closure, and full original-source horizon mass. For X<=1024, every event and terminal is cross-checked with a literal integer-by-integer parity GCD oracle. The total R and event counts agree with the parent full-horizon audit. Local tested Git blob 7784f3f2be8ce067b84786bbac54963de2108981. Window thresholds are 11, ceil(sqrt(B)), ceil(B/log^(1/8) B), but all words are contiguous in the LOW7-filtered word; no intermediate highs are skipped. The higher thresholds are diagnostics; not every tested threshold or length satisfies the asymptotic theorem. For each qualifying observed rank window we mark all actual horizons from its first to last high (including intervening lows). union_R charges ALL original-source visits to the union of marked horizons once, including visits not themselves in a qualifying window. It is not the cost of the entire possible arithmetic set. Different window lengths' unions can overlap.

At X=65536, B=678, R=15481975, 796161 full events, 262555 high events:

|length|cut|windows|rank>=k-1 (k>=2)|one sink|observed union_R|
|--:|--:|--:|--:|--:|--:|
|5|11|162292|6735|2668|3284388|
|8|11|112575|789|308|790176|
|16|11|40954|1776|38|1569368|
|32|11|6171|1301|0|1424451|
|5|27|2967|0|0|0|
|8|27|256|0|0|0|
|16|27|0|0|0|0|
|32|27|0|0|0|0|

At all five windows, there were no length-5/8/16/32 windows whose labels were all >=Q=ceil(B/log^(1/8) B). At X=4096 (mid=14) and X=16384 (mid=19) there were respectively 7 and 10 rank-qualified length-5 mid-threshold windows. For X=65536, most length-5 all-high windows have no repeats at all (92824 of 162292), and all-large runs are even sparser. All one-sink windows in all tested bands had rank>=k-1. This is finite confirmation, not asymptotic proof. For fixed cut 11 the union_R fractions at X65536 for lengths 5/8/16/32 are approximately 21.2%, 5.1%, 10.1%, 9.2%; these are NOT unconditional removable fractions at fixed cut 11.

## 6. Remaining analytic gap and next target

The graph theorem avoids having to enumerate the ranks of arbitrary words, and the singleton corollary excludes a substantially larger family of bounded-length large-prime words without bounding coalescence. However, the finite distribution shows why only studying contiguous all-large windows is unlikely to control the global R: larger labels are mostly isolated by smaller high labels. The graph rank theorem does not remove such interleaved histories; treating all labels below Q as LOW with a bounded L would be invalid.

A next useful experiment is to classify large-label return windows allowing arbitrary smaller high donors, retaining their exact total gain and size/number separately. Compare with the existing light-background sieve in min-sieved-multidonor.md. On the analytic side, seek a bound on the number of choices of these intervening gains (or their joint modular constraints) that preserves the one-free-variable CRT saving. Otherwise return to the full-horizon weighted R or late cross-cut energy after the genuine sparse horizon deletions. The sufficient condition remains liminf R/X^2<9/32. None of the new results establishes it. Main and Lean sources unchanged.
