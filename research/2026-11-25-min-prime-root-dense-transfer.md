# Actual-source dense-return deletion and LOW-block absorption in the repeat-energy hybrid

2026-11-25 JST. Continuation of 2d184f3d6d9fe87e472ebf8ced2da40aec50503f on research/min-prime-root-repeat-energy-2026-11-25. This paper checkpoint transfers the deterministic part of the coupled-return rank theorem of 0c3eaca6a03e6ec22c51c785b1975f747f9aa6ec to the actual integer MIN trajectories, without importing its independent CRT ghost probabilities. It also absorbs all very small selected primes into a medium-label moment. No Lean compilation, no external novelty assertion, twin-prime infinitude remains OPEN.

## 1. Definitions and what is being transferred
Use exactly the previous full canonical prime-root ensemble, with B=ceil(sqrt(7X)), N=number of prime roots M in [X,2X), original cutoff K(M), and total minimum-clock cost R=sum_{M,events} r(C)=O(XN). In this note K is a separate positive integer local-word span parameter (not K(M)); J is a background gain cap. Let z be a large-label cutoff. A local word means a contiguous interval of the list of actual selections with p>=z, retaining all original intervening events. Require that the intervening gain between consecutive listed selections, excluding the first listed jump, be <=J, and that the span S between FIRST and LAST pre-horizons be <=K P, where P is the minimum listed label. Dense means EVERY distinct listed label occurs at least twice within this word. The background may consist of arbitrary selected labels <z, not a fixed LOW primorial. Their gain cap is part of the class being deleted, not an assertion about all intermediate trajectories.

Mark the union of all actual events in each such dense word, including all intervening background events and the last listed event. Let D be this source-tagged union, and V_D=sum_{(M,event) in D} p, using the selected prime p (NOT just the minimum eligible r(C)). We will show V_D=o(XN) for a slowly growing K,J and z=ceil(sqrt B). This is an actual full-window deterministic-source estimate, not a ghost expectation, and concerns even events that were globally fresh before the word. The dynamics are never rerun after deleting incidences from the budget.

## 2. Coupled subword and rooted rank, with arbitrary bounded background
Every dense word has <=2K+1 listed events: all but the last contribute at least P-1>=P/2 to S. Every listed label appears before the last position at least once and thus every selected listed label is <=KP+1. Assume z>J+3 and z>=5. Adjacent equal listed labels p cannot occur: the change in their pre-horizons is p-1+d, 0<=d<=J even, and the difference after adding the two signs is an even positive multiple of p if the second is eligible. It lies strictly between 0 and 2p, a contradiction.

Use the dependence graph on distinct listed labels: i->j if i!=j and an occurrence of p_j lies strictly between the first and last occurrences of p_i. As in 0c3eaca6, choose a sink SCC. Every first-to-last interval of a label of this SCC contains only SCC labels; along an arc the two intervals intersect. Strong connectivity makes their union one contiguous interval containing exactly those labels and all their occurrences in the original word. This yields a dense coupled subword with at least two distinct labels, because a singleton sink would force adjacent equal listed labels. The subword inherits the background cap and span inequality.

For a coupled word, order its distinct labels p_1<...<p_h. For each i, let n_ij be the number of listed p_j from the first p_i through the position just before the last p_i; N_i=sum_j n_ij; d_i the total background gain there, so 0<=d_i<=N_i J. The pre-horizon difference is m_i p_i+a_i, a_i=sign_first-sign_last in {-2,0,2}, m_i positive even, m_i<=K+2. It is also sum_j n_ij(p_j-1)+d_i. Hence
    (m_i-n_ii)p_i - sum_{j!=i} n_ij p_j = e_i = d_i-N_i-a_i.
Write this M p=e (matrix M, not the original-root variable). |e_i|<=E0=2K(J+1)+2, |M_ij|<=2K+2, and sum_{j!=i}n_ij p_j<=S+N_i<=2KP. Every nonzero n_ij p_j>=P. These are the exact hypotheses of the deterministic rooted uniqueness argument in 0c3eaca6, now verified with arbitrary bounded background. For completeness, if x solves all rows other than root r and x_r=0, normalize by the actual positive solution p, take y_i=x_i/p_i, choose sign so max |y_i|=b>0 occurs at v with y_v=b. Put delta_i=b-y_i>=0. Subtract y_i times the inhomogeneous equation from the homogeneous row. For each graph arc i->j with i!=r this gives
    delta_j <= 2K delta_i+E0 b/P.
Along a simple path v->r of length <=h-1 this would imply b < (E0/P)(2K+1)^h b, impossible when P>E0(2K+1)^h. Thus every rooted principal minor is nonsingular under this scale gate. This is an elementary deterministic statement, not a distribution assumption. A coupled word need not have an invertible FULL matrix.

## 3. New actual-horizon CRT count for coupled anchors
For every coupled subword fix its combinatorial pattern: length <=2K+1, its word over the sorted label indices, each intervening background gain in [0,J], each sign, and the integers m_i in [2,K+2]. These data determine M,e as well as all offsets between listed pre-horizons once the labels are known. The number of patterns is at most
    F(K,J)=exp(O(K log(2K(J+1)))).
Indeed one may allow (2K+1)^(2K+1) words, (J+1)^(2K) background arrays, 2^(2K+1) signs, (K+3)^(2K+1) m-arrays, and sum over lengths and h. This enumeration does not assume which patterns are realizable; discard singular minors.

Set K=max(2,floor((log log B)^(1/4))) and J=floor((log log B)^(1/4)) for large B, and z=ceil(B^delta) for a fixed 0<delta<1 (the proposed choice delta=1/2). Then F, all matrix determinant bounds, and every fixed power of K,J are (log B)^o(1). The rank scale gate holds eventually uniformly in P>=z.

Fix a pattern and the smallest prime label p_1 in a dyadic band U<=p_1<2U, U>=z. The rooted minor at p_1 determines every other p_j uniquely, via Cramer's rule
    D0 p_j = a_j p_1+b_j.
The integers D0!=0,a_j,b_j have absolute values exp(O(K log(2K(J+1)))) by the elementary determinant expansion. For a realizable pattern and any j!=1, a_j cannot be zero for large B (it would give p_j at most the determinant bound), and b_j cannot be zero: p_1 divides D0 p_j, but p_1>D0 in absolute value and p_1,p_j are distinct primes. These assertions are only used in the asymptotic scale regime.

There are at most O(U (log log B)^2/log^2 B) candidates for p_1 in the band with p_j also prime, for any one chosen j!=1. To see the uniformity, solve the linear congruence a_j p_1+b_j=0 mod |D0|; when solvable, p_1 is in one progression of step |D0|/gcd(a_j,D0). Parametrize its consecutive integer progression indices (at most O(U) of them). The two labels are integer linear forms in that index with nonzero leading coefficients and nonzero determinant (because b_j!=0); coefficients and determinant have polylogarithmic size. Ignore sieve primes below a sufficiently large fixed power of log B so that no such prime divides the leading coefficients or determinant. For primes up to U^(1/4), each remaining sieve prime excludes two different residues, since both target prime values exceed U^(1/4). The uniform two-form upper-bound sieve from 1bd657be, section 2, applies, with the usual squarefree remainder O(2^omega(d)), summed O(U^(1/4) log U), and Euler product O((log log B)^2/log^2 B) because log U>=delta log B. Shorter progression intervals only improve the main term; the remainder bound remains valid. This imports the earlier established sieve estimate, not ghost independence.

Given the tuple, consider the first two listed labels p,q of the coupled subword; they are distinct and >=U. If C is the first pre-horizon, their signs sigma,tau and first background gain d give
    p | C+sigma, q | C+p-1+d+tau.
Thus C lies in one residue class modulo pq, and there are O(X/U^2) possibilities in the actual [2X,7X) horizon range. The +1 is absorbed because U<=B and B^2=Theta(X). Each possible (C,p) anchor has weight p<=2(K+1)U. No assumption about how many roots visit that horizon is made. Summing over candidates and all patterns yields a bound on the total selected-prime weight of the union of possible coupled first anchors, with pattern repetitions permitted:
    S_anchor << F(K,J)(K+1) X (log log B)^2/log^2 B
per band, hence over O(log B) bands
    S_anchor <= X (log B)^(-1+o(1)).
For the narrower top cutoff z=B/log B one can dispense with the two-form sieve entirely: count p_1 by O(U/log B), and there are only O(log log B) bands. This gives the same X log^(-1+o(1)) order. The wider sqrt(B) cutoff uses the extra sieve factor.

## 4. New unconditional source-tagged dense-union deletion
Each actual dense word contains a coupled subword; choose its first listed event as anchor. Within one source, for each distinct chosen anchor, take the union of all words assigned to it. All event gain intervals in that union lie in
    [C_anchor-K p_anchor, C_anchor+2K p_anchor].
Indeed the original dense word has span <=K times its minimum, at most K p_anchor; its final listed label occurs previously, so its final jump is also <=K p_anchor. Actual gain intervals of different events of one source are disjoint. Since p<=3(p-1)/2, the sum of selected labels in this entire union is <=(9/2)K p_anchor, conservatively <=6K p_anchor. This also counts the background events, without charging the same anchor separately for every overlapping word. Each source visits each pre-horizon at most once. Summing over source tags,
    V_D <= 6K N S_anchor <= XN (log B)^(-1+o(1)) = o(XN).
The same upper bound holds for the clock cost R_D, since r<=p. This is unconditional relative to the established deterministic and sieve inputs and works after arbitrary physical mergers. It also holds if the original ensemble is all odd roots, replacing N by X/2.

Only actual marked incidences, not all possible tags at every surrounding horizon, are deleted here. We do not claim their quadratic energy is small; remove them at the linear budget stage. In particular no finite-window transfer from the independent two-coordinate CRT ghost was needed. This removes a class of multi-donor returns, including edge-distinct coupled words; it does NOT remove arbitrary multi-donor words, long spans, large background gain, or isolated repeated labels fed by singleton donors. A wholly unmarked contiguous subword satisfying the span/background/size conditions cannot itself be dense, so it must contain a label occurring exactly once within it. This is a combinatorial constraint, not an estimate of all remaining words.

## 5. New LOW absorption: remove very small labels from the moment target
Independently choose a growing LOW boundary y with even primorial L=2 product_{3<=p<=y} p <= (log log B)^(1/4), maximal for large B (so y->infinity slowly). Retain the previous hybrid parameters Q=ceil(B/log B), k_p=floor(sqrt(log B))+floor(A/p^2), A=floor(B^2/(log log B)^2), and previous light-donor horizon set mathcal A. The fixed-primorial barrier gives total gain <L in each contiguous block of actual selected labels <=y, including initial and final truncated blocks. Since r<=p<=3(p-1)/2, the LOW clock cost satisfies
    R_low <= (3/2)L (N+# actual selections with p>y).
This is the original full run, not a run after removing events.

Partition ONLY events with p>y into disjoint classes in this order: first k_p uses of that label in its original source (base); horizons in mathcal A (light deletion); marked dense union D; remaining medium y<p<Q; remaining high p>=Q. Charge all LOW blocks separately using the preceding bound. The contribution of the base to the number of p>y events is at most N[k pi(B)+A sum_{p>y}1/p^2], k=floor(sqrt(log B)). Multiplying this by L gives
    O(N L B/sqrt(log B)+N L B^2/(log log B)^2)=o(XN).
The previous baseline r-cost was o(XN). The count of events at mathcal A is <=N S_A/3, since r>=3 and a source visits any C only once. Its additional LOW charge is o(XN), because S_A=O(X(log log B)^2/sqrt(log B)) and L grows sufficiently slowly. The dense union event count is <=V_D/3, so its LOW charge is also o(XN). Finally, ALL high p>=Q events (including deleted ones, harmless overcount) number O(XN/Q), by total original gain O(XN) and p-1>=Q-1. Hence their LOW attachment cost O(L XN/Q)=o(XN). Initial blocks contribute O(NL)=o(XN).

Thus, letting n_m(M,p) denote the actual retained medium multiplicities, all LOW cost plus retained medium cost is bounded by
    R_low+R_m <= o(XN)+sum_{M,y<p<Q}(p+(3/2)L)n_m(M,p)
               <= o(XN)+sqrt(N * sum_{y<p<Q}(p+(3/2)L)^2 * Z_m),
    Z_m=sum_{M,y<p<Q}n_m(M,p)^2.
The coefficient sum is O(Q^3/log Q), since L=o(Q) and pi(Q)=O(Q/log Q). The same Cauchy calculation as the previous hybrid therefore shows that the OPEN bound
    Z_m=O(N B log^3 B)
is sufficient. All selected primes <=y, including very large multiplicities of 3,5,7,..., have disappeared from this moment requirement. Their cost has not been assumed negligible independently: it is controlled by the number of non-LOW events, including the retained medium moment.

For retained high events define W_h,late and E_h,late exactly as before, but after base, light and dense removal, and with gain radius T=B log^(2-epsilon) B. The earlier prime-source near-origin upper bound and Cauchy with S0 continue to apply to this smaller incidence measure. Consequently the new joint OPEN sufficient condition on the SAME unbounded dyadic windows is
    Z_m=O(N B log^3 B) AND E_h,late=o(X^2 B).
Both quantities are now defined on strictly more restricted incidence families than in the preceding hybrid. It implies R=o(XN), contradicting H<=2R+2BN if no twin terminal exists. The two asymptotic bounds themselves remain unproved. No assumption of independence or of mixing between prime-root trajectories has been made.

## 6. Finite audit (nonvacuous actual coupled words)
Standalone ECMAScript research/min_prime_root_dense_transfer_audit.mjs, commit acd48edd9d73768e695b1fca486d4880f35fcda1, blob 1b3c6137e950943a089e2798fdb4dcec8788fd12, exact remote readback. Run:
    node research/min_prime_root_dense_transfer_audit.mjs 256 1024 4096 16384 65536 262144
Executed its audit function in the ECMAScript tool runtime, not a separate Node executable. All prime roots, actual original cutoffs; exact SPF clock and literal parity-GCD comparator at the two smallest windows (1724 comparisons per mode). Three modes: analytic z~sqrt B, K=2 at tested scales, J=1; diagnostic z=7,J=2,K=6; wide z=17,J=12,K=6. For each candidate dense word find a sink SCC, check the actual gain equations and the two CRT congruences at the extracted anchor, use exact BigInt Bareiss determinants and Cramer's rule for every nonsingular root minor, and check disjoint gain-interval union charge per original source, plus N times the distinct observed anchor support weight. No analytic scale-gate example is reached in these finite dense-word samples; the nonsingular actual examples verify the algebra, not the general asymptotic rank condition. The analytic mode finds no dense words. The diagnostic uses fixed LOW y=3,L=6 and the earlier *fixed* k baseline (not the adaptive cap, which erased everything in the previous finite run), without the relaxed light-horizon deletion; it tests nonzero medium/high costs, LOW block absorption and the dense union accounting separately. The combined asymptotic theorem is a paper deduction, not an extrapolation or a claim that the audit checks every prior deletion simultaneously.

| X | diagnostic dense words | distinct observed anchors (C,p) | dense union prime weight | dense union clock cost | LOW clock cost | retained medium moment |
|--:|--:|--:|--:|--:|--:|--:|
|256|7|1|525|287|561|153|
|1024|0|0|0|0|1398|194|
|4096|2|2|174|120|8196|5106|
|16384|3|1|162|126|38283|37297|
|65536|31|13|1809|1325|160368|192152|
|262144|107|33|6954|4844|692823|1157672|

All three modes and six windows passed. Diagnostic total 150 dense words, 300 nonsingular rooted-minor checks and 300 affine reconstructions. Wide total 107 dense words, 214 nonsingular minors/reconstructions; multiple overlapping words may use the same anchor. At X262144 diagnostic anchor weight with original multiplicity is 1637 versus distinct anchor support weight 513; actual total R=16687054 matches the previous prime-root audit, with 616116 events. For the wide mode X262144: 84 dense words, 69 distinct per-source chosen anchors, weight 1317, 23 distinct physical (C,p) anchors, support weight 429, union weight 4812 and clock cost 2872. LOW block gain max 4 in every run, consistent with L=6. All medium-attachment Cauchy inequalities checked using BigInt after multiplying by 2. These tests do not enumerate every relaxed affine family or independently check the asymptotic sieve bound; no new Lean theorem or compilation.

## 7. Remaining work
The source-weighted dense-word estimate is now available directly on the actual trajectories, not merely on the ghost. For the high residual, focus on sparse short words (singleton donors), long spans and large intervening background, with real original-root masses. For the medium residual, investigate deleted-prime returns above the adaptive caps after removing the full LOW block, rather than spending effort on individual 3/5/7 multiplicities. One possible next step is an aggregate donor-interval charge for medium repeated labels that separates disjoint donor gain from heavily overlapping intervals; no such aggregate contraction is claimed here. Main and other research branches untouched.
