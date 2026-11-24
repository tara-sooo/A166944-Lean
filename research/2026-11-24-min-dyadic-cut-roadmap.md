# Dyadic source cuts: boundary-entry restriction and proof roadmap

2026-11-24 JST. Companion to the full-horizon pair budget (73458de887def94d00eeaf2d2d3b9c59a44b8137) and lag-cycle/cube-free notes. Paper deductions only, no new numerical audit or Lean compilation. The central cross-block mass estimate is OPEN.

## 1. Keep the full-horizon target

Use X dyadic, N=X/2 odd canonical sources, B=ceil(sqrt(7X)), full actual trajectories with each original K(M), pre-event horizon sets V_M, r(C) the least eligible odd factor (zero if none), W(C)=#{M:C in V_M}. Define R=sum_C r(C)W(C), E=sum_C r(C)W(C)^2, S0=sum_C r(C) over even C in [2X,7X). The earlier paper sieve gives S0=O(XB/log^2 B) and the no-twin implication gives R >= (9/32-o(1))X^2. Cauchy gives R^2<=S0 E. Thus E=O(X^2 B log B) on unbounded dyadic windows implies R=O(X^2/sqrt(log B)), hence infinitely many twins. More generally E=o(X^2 B log^2 B) suffices. This is the same central energy target, without needing to pass through the heavy-tail J. The diagonal sum R=O(X^2).

## 2. Exact dyadic source-tree decomposition

Split the ordered original source indices 0,...,N-1 by the complete binary interval tree. For an internal block I, let I_L,I_R be its two equal halves. Define W_A(C)=#{M in A:C in V_M} and
    H(I)=sum_C r(C) W_(I_L)(C) W_(I_R)(C).
Each unordered distinct root pair occurs at its unique lowest common ancestor. Hence
    E=R+2 sum_(internal I) H(I).
At any level with block size k, H(I)<= (k/2) sum_C r(C) W_(I_L)(C). Thus the sum over all I at that level is O(k X^2). Summing geometric levels k<=O(B) gives O(X^2 B) unconditionally.

For a larger level, let J be any even integer separating the left and right root horizons (C0(M)=2M-2, spaced by 4); for definiteness J is the maximum left root horizon. Every shared pre-event horizon lies above J. Remove pairs for which either original root horizon is within B of J. There are O(B) such roots in each block, hence O(kB) pairs in a block and O(XB) pairs at a level. Each pair's weighted common length is O(X) by r(C)<=p<=3(p-1)/2 and monotone total horizon gain O(X). The contribution of all such near-cut pairs is O(X^2 B) per level and O(X^2 B log B) total. No independence assumption.

## 3. Exact sparse entry interface

For remaining left sources that ever reach a horizon above J, consider their unique first crossing, with pre-event horizon D<=J and post-event horizon C=D+p-1>J. Necessarily J-p+2<=D<=J and p|D+sigma, sigma in {-1,+1}. For each fixed p and sigma, this interval has length <p; it contains at most one eligible even D. Hence there are at most 2 pi(B) possible (p,D) crossing keys, and every post-horizon is in (J,J+B). The actual first-crossing time belongs to a single progression mod 2p determined by sigma. For a band Q<=p<=B, counting times <=Kmax=O(X) gives O(X sum_(Q<=p<=B) 1/p + pi(B)) possible tagged entry vertices, not source weights. If a cut J is divisible by an even low modulus L, no p|L can cross strictly above J, by the even-multiple barrier. This last observation is optional and requires such cuts, not all balanced dyadic cuts.

For each block, left-root tags that cross are partitioned by these entry vertices and retain their own cutoff K(M). Right roots have their original start and cutoff and start to the right of J. The contribution of the remaining H(I) is exactly the weighted intersection of their forward horizon occupation measures after entry. One can propagate each population using the already defined deterministic MIN map (or reverse-clock recurrence) without storing label histories or lag cycles. For cutoff handling either retain K tags or enlarge to a common maximum and use the resulting monotone upper bound. A projected entry horizon alone is not a physical vertex; t must be retained.

## 4. Concrete open estimate and work sequence

For each coarse level of equal block size k>B, write H_far(I) for the cross product after excluding the near-cut pairs above. The OPEN estimate
    sum_(I at level k) H_far(I) <= C0 X^2 B
uniformly in X,k on the same unbounded dyadic windows suffices. It is enough to prove the stronger average-per-block scale O(k X B) at that level (there are N/k blocks); no bound for every individual pair is needed. Summing levels and using section 1 completes the paper implication. This is a reorganized correlation goal, not an established decay bound. Sparse entry keys do not imply bounded incoming original-source masses.

Recommended next steps:
1. Compute the exact cross-block energy by depth, entry-key weight distributions and contributions to H_far from each entry key, retaining original cutoff. Validate sum identity against existing energy audit. Separate a small number of highly loaded entry keys from ordinary ones; determine whether the obstruction is their incoming mass or long shared downstream occupation. Report both factors; do not infer asymptotics from short terminal runs.
2. For actual entry keys, use the exact reverse interval (last eligible time strictly before the event <= predecessor time < event time) to estimate the left-tag incoming mass. Attempt bounds with original roots restricted to one block and the first crossing, rather than all ancestors of arbitrary states. On the forward side use the actual weighted intersection after crossing, not merely a count of first meetings times the worst-case O(X) suffix.
3. Prove an average product estimate over entry keys/blocks, exploiting the CRT restrictions and clock competition. This is the genuinely unresolved arithmetic step. Reject any proposed bound that silently assumes uniform weights or that only counts unweighted vertices. Short return deletion can be applied directly to R with o(X^2) error, or consistently to the weighted E and S0 restricted to remaining horizons; cube-freeness alone cannot supply the mass estimate.
4. Formalize the finite clock-budget, occupation/energy identity and cut lemma in Lean in parallel; then integrate the proved analytic bound and standard sieve to conclude arbitrary large twins. No new analytic premise may remain in the final theorem.

The cut restriction is an elementary unconditional lemma; the rest is a precise conditional proof plan. No claim that solving the open cross-block estimate is imminent. Main untouched.
