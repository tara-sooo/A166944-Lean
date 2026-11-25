# Rare near-B divisor exposure in shallow histories: CRT plus Kraft, with mixed first-meeting deletion

2026-11-25 JST. Continues 396976cb39d54785b6c502bb24d7786c5e247973 (reverse ancestry Kraft and expiry) and 065b449cd0a91b1ec0a6660cd7ddf231fbe2044d (short-slab merge bounds). New unconditional bound on the NUMBER OF ORIGINAL ROOT TAGS exposed to a large divisor before the third medium event. It handles one shallow and one arbitrarily complex history at certain first meetings. This is a root/linear-clock deletion, not a negligible-energy estimate for the deleted roots. Remaining high-complexity and small/medium-incoming meetings and twin infinitude remain OPEN. Paper proofs, not Lean-compiled.

## 1. Parameters and actual prefix

All original odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), start (s,C0)=(M+2,2M-2), K=floor((7M-1)/4). H=4B, a=2B, assume H+2B<=min_M(K-s), eventually. Include actual prefix states through the first post-event vertex after the relative H boundary (if any), as in the parent note. Stop at a twin. All horizons are even, strictly increasing under events and lie in [2X,7X). The event waits are <=2r(C), and elapsed time along completed events <=3 times their total gain.

Put ell=log log B, S=max(1,log ell), L=largest even primorial <=6 S^(1/4), with associated LOW cutoff y. Thus L=ell^{o(1)}, and each contiguous LOW-only block has even gain in [0,L). Set

    Q=ceil(B / exp(sqrt(ell))),  P=floor(B^(1/4)).

Eventually y<P<Q<=B, log Q~log B, Q=o(B). Selected labels are LOW (p<=y), MEDIUM (y<p<Q), LARGE (p>=Q). This Q is wider than the Q=B/S^(1/4) used in the preceding Kraft two-medium theorem; do not import that theorem's bound on the product of arbitrarily many LARGE branching factors to this new Q. Here the analysis is before the FIRST LARGE selection.

A horizon C is exposed if for some odd prime Q<=p<=B,

    p | C+b for some b in {-1,0,1,2}.

The shifts -1,+1 detect potential LARGE next labels, and 0,+2 detect potential LARGE incoming labels. This deliberately overcounts actual events. Mark an original root if its actual prefix ever visits an exposed horizon BEFORE its first LARGE selection, with at most TWO MEDIUM selections already completed. The state just before a first LARGE event is included; a final post-event state is included if no LARGE event has yet occurred. The entire root is marked permanently even if it later has a long complex history.

## 2. Number of exposed horizons

Let A be the set of exposed even C in [2X,7X). For each p and shift, the number of C is O(X/p+1). By Chebyshev prime counting, summing over the dyadic subbands from Q to B gives

    sum_{Q<=p<=B} 1/p
       = O((1+log(B/Q))/log Q)=O(sqrt(ell)/log B).
    |A| = O(X sqrt(ell)/log B + B/log B)
        = O(X sqrt(ell)/log B).                         (1)

The estimate is an upper bound on possible horizons, not on the sources that reach them. The next two sections bound that source multiplicity without assuming any random distribution of histories.

## 3. All-small shallow histories: explicit CRT on actual labels

Consider an exposed state C before any LARGE event, with k<=2 MEDIUM labels q_1,...,q_k, ALL <=P. Compress the forward LOW blocks to their actual even gains e_0,...,e_k in [0,L). Then

    C = 2M-2 + sum e_i + sum_i(q_i-1).

For a fixed word q, offsets e, and each post-event horizon J_i after q_i, J_i is C minus a fixed suffix of gains. The exact MIN post-event arithmetic gives q_i|J_i or q_i|(J_i+2). For each i choose the actual side b_i=0 or 2 (the two sides are disjoint for odd q_i). Thus C must satisfy one specified congruence modulo q_i. Exposure imposes one further congruence modulo a prime p>=Q, p distinct from every q_i.

With repeated q_i, check consistency of congruences and use each distinct prime only once. Put D=p product_{q distinct} q. Since k<=2, D<=B P^2=O(B^(3/2))=O(X). CRT gives at most O(1+X/D)=O(X/D) possible C (restricting to even C can only reduce the count). For each such C and fixed word and offsets, the original root M is uniquely reconstructed. A given source-state exposure might have multiple witnesses; overcounting is valid.

Sum over p, four exposure shifts, the O(L^{k+1}) offsets and the 2^k post-event sides. For the word sum with at most two positions, the repeated-label case uses sum 1/q, not sum 1/q^2. Hence it is O((1+ell)^2), by the usual harmonic prime upper bound sum_{q<=B}1/q=O(log log B). This bound follows by the same elementary Chebyshev dyadic summation. The total number of original source-state incidences in this class is

    O(X L^3 (1+ell)^2 sqrt(ell)/log B)=o(X).             (2)

This counts original tags, including those already coalesced. The CRT word encodes the actual initial horizon, so there is no hidden multiplicity factor from ancestors.

## 4. Mixed shallow histories: a uniform Kraft cap

The other case has at most two non-LOW selections and at least one MEDIUM label q>P, before any LARGE selection. Use the adaptive reverse complexity of 396976cb:

    kappa_M(C)=L product_i L/pi_{J_i}(q_i),
    sum_{M visiting C} 1/kappa_M(C)<=1,
    L/pi_J(q) <= min(2L d_y(J),4L log(7X+2)/log q).

Here d_y(J) is the number of eligible reverse prime divisors of J(J+2). Uniformly d_y(J)=O(log B/ell), since the product of d distinct primes is at least d!, and J(J+2)=O(B^4). For q>P, log q >= (1/4+o(1)) log B, so its factor is O(L). For the possible other label the factor is O(L log B/ell). Therefore every mixed shallow history in this class has

    kappa_M(C) = O(L^3 log B/ell).                      (3)

The Kraft inequality bounds their actual count at each C by the same quantity (even if many tags reach the same physical state). Combining with (1),

    #mixed exposed source-state incidences
       = O(X L^3/sqrt(ell))=o(X).                       (4)

The saving is from the actual large-ish label in the history, not an assumed independence of its selected primes. Since L^3=ell^{o(1)}, (2) and (4) together prove the main theorem:

    #marked original roots = O(X L^3/sqrt(ell)
                               + X L^3 (1+ell)^(5/2)/log B)
                          = o(X).                      (5)

Indeed the number of distinct marked roots is at most the number of exposed source-state incidences. No trajectory is rerun with a different clock or cutoff.

## 5. Consequences for the original energy route

Delete ALL incidences of the marked original roots, before and after the marking state. The slab linear cost per root is <=B, so the removed budget is

    R_del <= B #marked roots=o(XB).                     (6)

Under a no-twin window, the retained roots still contribute R_kept=(N-o(X))B. Hence Cauchy with the original S0 shows that E_kept=o(XB log^2 B) on unbounded dyadic windows still suffices for twin infinitude, just as for the original energy. We have NOT proved E-E_kept=o(XB log^2 B): a rare root can have many partners. This is an admissible linear-budget/root restriction, not an unconditional small-energy bound for the deleted pair class.

(i) FIRST LARGE selection after <=2 MEDIUM selections. Every root making such an event is marked: at its pre-event horizon the selected p>=Q divides C-1 or C+1. Thus outside the marked roots, any first LARGE selection must have at least three MEDIUM selections already completed.

(ii) ONE shallow and ONE arbitrarily complex first-meeting history. Suppose two distinct roots first share a physical vertex v=(t,C) where at least one of the incoming labels is LARGE (the other may be small/medium or a root injection), and at least one history has <=2 MEDIUM selections before/at v. The shallow tag is marked. If it has already selected a LARGE prime, its first LARGE selection occurred while still shallow, by monotonicity of the medium count, so (i) applies. Otherwise the incoming LARGE prime, even if from the OTHER history, divides C or C+2, so the shallow tag visits an exposed horizon before its own first LARGE selection. This is exactly the marking condition. The result also holds for ANY first meeting at an exposed horizon with at least one shallow history, including an exposed root injection. More generally, if the common suffix after first meeting reaches an exposed horizon before the shallow tag completes a third medium selection and before any large selection (or it chooses a large label then), that tag is marked too. Thus such mixed-history pairs are absent from the retained energy for their entire shared suffix. There is no bound on the other tag's original ancestry; this is a genuine one-sided extension of the earlier good-good result, but only in this exposure class.

(iii) Retained shallow occupation cannot reach the late slab, eventually. For an unmarked root, a state with <=2 completed MEDIUM events has no previous LARGE event, and if there is a next event its label is <Q (otherwise that state would mark the root). The gain before such a state is at most 2(Q-1)+3(L-2), by the LOW barrier. Its arrival age is <=3 times that gain and the next wait <=2Q. Therefore its entire waiting interval ends by relative age <=8Q+9L=o(B). In particular for sufficiently large B every retained occupation in [2B,4B) has already completed >=3 MEDIUM selections. Every surviving retained root has the same property by age 2B. This conclusion includes partial waiting intervals; a twin has no occupation. This is stronger than a small total current-good cost for this restricted class, with a different Q. It does not assert that three medium events force termination.

## 6. Fixed-depth extension for two subfamilies

For any FIXED k>=1, replace P by B^delta with fixed 0<delta<1/k, keep the same Q and L. The identical CRT argument bounds the class of at most k non-LOW selections, ALL <=P, before first LARGE, by

    O_k(X L^(k+1) (1+ell)^k sqrt(ell)/log B)=o(X).

Here the product of distinct small moduli times the exposure prime is <= B^(1+k delta)=O(X); repeated labels cost a harmonic sum once per distinct prime (only finitely many partitions of k positions).

Also the Kraft argument bounds at most k non-LOW selections with AT MOST ONE <=P and every other >P (but <Q). For all the >P factors use O_delta(L); the possible small factor costs O(L log B/ell). Thus the complexity is O_{k,delta}(L^(k+1) log B/ell), giving O_{k,delta}(X L^(k+1)/sqrt(ell))=o(X). This covers all words of length <=2 as above, and two subfamilies of longer words. It does NOT cover arbitrary fixed k>=3, where two or more small labels may interleave with large-ish labels. For each fixed k the constants can depend on k,delta; no growing-k uniformity claimed.

## 7. Actual finite audit

Standalone ECMAScript research/min_clock_shallow_high_audit.mjs, exact remote readback at becd9fb1ef92f3e0d5bfb13a3e45d0762ea099a6, blob d821d72ac2d3cbdc2e0474fc37f57b6d0edf0928. Run:

    node research/min_clock_shallow_high_audit.mjs 1024 4096 16384 65536 262144

Executed actual audit function in available JS runtime on all five windows with analytic Q and with diagnostic Q=ceil(.95B). This is not a separate local Node invocation. 4658 literal parity-GCD clock comparisons at X1024 per mode. All original source paths and final post-event vertices preserved. Builds the high-divisor support for all four offsets, counts relaxed CRT words exactly (CRT on C/2 with repeated congruence consistency), verifies injection of actual all-small source-state incidences into CRT tuples, verifies actual mixed complexity cap, counts first meetings using incoming physical predecessor classes, checks every marked pair involving a shallow history and an incoming high label has its shallow tag flagged, verifies entire root linear-cost deletion and actual kept occupation. Fractional energy/complexity use floating-point tolerances. Counts are integer in these windows. At X<=16384, P<=y, so all-small nonempty medium words are absent; X>=65536 tests p=5 including repeated-label tuples. No exact suffix-energy enumeration required since the entire flagged roots are removed.

Analytic Q (ceil(B/exp(sqrt(ell)))):

| X | Q | all roots | flagged roots | first high while shallow (distinct roots) | shallow+incoming high first meetings (unordered) |
|--:|--:|--:|--:|--:|--:|
|1024|26|512|481|123|1055|
|4096|48|2048|1939|410|3793|
|16384|90|8192|7793|1164|17201|
|65536|173|32768|31074|3874|88797|
|262144|333|131072|123243|11554|377088|

At X262144 B1355,P6,L6,y3, analytic Q333: exposed horizons372737; actual all-small exposure incidences180422 vs relaxed CRT tuple upper count4660125; mixed exposure incidences162469, max mixed root mass17; unique flagged roots split99192 small-first and24051 mixed-first. 52060 first exposures had only incoming-side divisibility (no pre-event-side large factor). All first meetings5477756; marked meeting class377088 includes any incoming large label and at least one shallow history, not necessarily exactly one. R=2373997.5, kept R=75274, E=184229117.19, kept E=373728.49. This finite analytic mode removes 94% of roots: it does NOT exhibit the eventual o(X) saving, and the finite lower remaining energy alone is NOT evidence of the asymptotic result. The asymptotic proof is (2)-(5).

Narrow diagnostic Q=ceil(.95B):

| X | Q | flagged roots | first high while shallow | shallow+incoming high first meetings |
|--:|--:|--:|--:|--:|
|1024|81|87|0|0|
|4096|162|341|21|159|
|16384|323|732|11|113|
|65536|645|4200|43|1768|
|262144|1288|13185|131|7389|

At X262144 narrow Q1288: exposed horizons17836; all-small actual8690 vs CRT upper151782; mixed8295 max mass15; retained roots117887, R_kept2117995, E_kept147054925.40, 7389 marked first meetings. At both thresholds all tested retained shallow occupation in the late slab is zero, though the deterministic asymptotic age gate 8Q+9L<=2B is not generally satisfied at these sizes. The latter observation is finite only. The narrow diagnostic does not represent the widening analytic Q and is not an extrapolation of (5).

## 8. Remaining task

New root deletion handles shallow exposure to high divisors with one arbitrarily complex incoming history, using actual source tags rather than a count of physical merge vertices. The main remaining first-meeting terms include both deep histories and mixed shallow/deep histories at small/medium-incoming, unexposed horizons. The general fixed-depth extension still misses interleaved multiple small and large-ish medium labels. A useful next target is to count actual roots whose first third-medium transition reaches a horizon in a prescribed rare factor set, using exact time constraints in addition to the reverse word, rather than assuming a uniform distribution or repeatedly relabeling the same energy criterion. The asynchronous residual and full E_kept bound remain OPEN. Main unchanged, no new Lean compilation or proof of the twin-prime conjecture.
