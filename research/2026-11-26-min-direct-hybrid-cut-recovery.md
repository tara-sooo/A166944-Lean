# Hybrid barriers and a cut-adjusted deficit: recovery confined to actual cut crossers

Continuation of [7e9cef2](https://github.com/tara-sooo/A166944-Lean/commit/7e9cef2f5237005bd799b1e77b6bec1cdd727154) on the independent direct-arithmetic branch. The previous segmented recovery bound charged arbitrary other high nonresets and incurred a low-run error. A new potential removes that error exactly: only events crossing a specified small-prime-product cut can contribute a negative change. Combining this with hybrid modular barriers preserves the root-or-B count constant while restricting B to actual cut crossers. It also improves the root-sparse gain lower bound by a growing factor. Paper proof, not Lean kernel verification; no twin-prime contradiction.

## 1. Cut-adjusted ordinary deficit

Use the established adaptive MIN rule. A nonunit event has label p, side e=+1 even or -1 odd, I=(1-e)/2, gain g=p-1, wait w>=1, pre/post horizon H,Z=H+g, pre/post ordinary deficits d,d', and adjusted D=d'-6I. Thus d'=d+2w-g. For p>=5, D is a nonnegative multiple of 2p; a nonreset has d'>=2p. A1 means p>=47, p>=5d+15, D=2p; A0 is the same label/deficit condition with D=0. For p>=47, all remaining events are B, by the deterministic roughness theorem. Far and near are the square-band classes of 8b30078 with fixed epsilon0 in (0,1).

Fix integers R>S>=47 and define K=K_S=2 product of odd primes<=S. Let
    L(H)=K floor((H-1)/K), rho(H)=H-L(H) in (0,K],
    u=d+3+rho(H)=2t+3-L(H).
The strict preceding cut is used, so at H itself a multiple of K the residue is K, not 0. For an event write c_K=(L(Z)-L(H))/K, the number of multiples of K in [H,Z). Then exactly
    u'-u=2w-K c_K.                                    (1)
No p<=S can cross a cut: if p divides K and H=e modp, J-H for a cut J is even, nonnegative, and congruent to -e modp, with minimum at least p-1. Thus it cannot lie in [0,p-1). Consequently every event with c_K=0 increases u, including every p<=S event. Also
    K c_K <= g+K.
For a crossing event c_K>=1, g<=K(c_K+1)<=2K c_K, because the gap between consecutive cuts is K. These elementary bounds include exact endpoint conventions.

## 2. Segmented cut-adjusted logarithmic budget

Let T=R/5+K, Psi=max(T,u), Phi=log Psi. Mark ALL A1 events with p>R, count m, and remove each unmarked A1 (p<=R) as a separator. At a separator the pre-potential is exactly log T since d+3<=p/5 and rho<=K. Retain segments with at least one mark. If the last retained segment ends at the full block's right endpoint, trim it just after its last mark; all other retained segments end at a separator's pre-state. This does not remove marks. At every marked A1, Psi_pre<=p/5+K and Psi_post>=2p, so
    Phi_post-Phi_pre >= ell = log(10/(1+5K/R)).
At a noncrossing event Phi is nondecreasing. Every retained unmarked nonreset that strictly reduces Phi has p>S, is not A1, and hence is B. Denote the set of these events by Jset, its cardinality j. Its loss at one event is bounded by
    log(Psi_pre/Psi_post)
      <= log(1+(K c_K-2w)/Psi_post)
      <= gamma = log(3/2+K/T),
and also <=K c_K/T. Indeed Psi_post>=max(T,2p), K c_K<=g+K<=p+K, so (p+K)/max(T,2p)<=1/2+K/T. Thus only actual crossing events whose adjusted potential decreases are charged, not arbitrary intervening B events. For each retained reset q that reduces Phi, q>S and the loss is <= log_+((q+6+K)/T), by d+3<=q+6. All reset counts are <=N+1, where N counts actual canonical visits in the full time interval (start,end], by seven-tick normalization before another p>=7 event, with at most one pending boundary visit. This applies to finite canonical prefixes too, allowing termination in place of the last visit.

If all pre-horizons in the block are <=Y, write C=floor sqrt(Y+1). The sum of retained segment endpoint log differences Delta is at most
    E=log(max(T,2C+9+K)/T).
Each segment ending before a separator has nonpositive difference. The only remaining possible positive difference is the trimmed segment ending at a marked A1, where d'<=2C+6. In particular the bound does not involve the possibly large final deficit of the full block.

Summation gives two exact finite inequalities
    ell*m <= Delta + gamma*j + sum_reset log_+((q+6+K)/T),       (2)
    ell*m <= Delta + (K/T) sum_{v in Jset} c_K(v)
                        + sum_reset log_+((q+6+K)/T).          (3)
Replace Delta by E and the reset sum by (N+1)log_+((C+6+K)/T) if desired. There is no low-run error term and no charge from noncrossing events. The coefficient ell may be nonpositive for arbitrary finite diagnostic cutoffs; all subsequent estimates choose it positive. Inequality (3) remains valid with a subset of the recovering B weighted by cuts and the others bounded by gamma per event. All of these are deterministic identities/inequalities for one actual ray, not a residue-probability model.

## 3. Hybrid barrier family

For each odd prime p<=R, use its allowed barrier residues 0 only if p<=S, and {0,2,...,p-3} if S<p<=R. Call an even J satisfying all these conditions a hybrid barrier. It is a multiple of K and no p<=R can cross it, by the ordinary modular-cut calculation. Put P=P_R=product of odd primes<=R,
    A=product_{S<p<=R, p prime} (p-1)/2,
    alpha=A/P.
CRT shows exactly A hybrid barriers per period of P even positions (absolute length 2P). In any half-open even-horizon interval of gain G, their count differs from alpha*G/2 by at most A. Every jump of gain g covers at most alpha*(g/2+P) hybrid barriers and at most g/2 even positions. The jump intervals partition a contiguous gained interval; these statements hold for arbitrary translates.

In a crossed window [X,lambda X] on an infinite canonical ray, lambda>1 fixed, the first-crossing block has G=(lambda-1)X+O(sqrt X), C=floor sqrt(lambda X+1). The earlier near-square packing bound gives near gain <=G/2+O(sqrt X) and near count O(sqrt X). Only high p>R can cover hybrid barriers. Subtracting the high-near capacity gives residual normalized far-barrier coverage at least
    G-N_g-2P(N_c+1) >= G/2-o(X)
provided P=o(sqrt X), where N_g,N_c are high-near gain/count. Let B_K count all far B events with p>S crossing at least one K-cut, and F_K be their gain. Let b_B count hybrid barriers covered by high-far B with p>R. All such events are included in B_K. The previous A1 gain ceiling 5G/14+O(C) applies to the high-far A1 subset, whose count is <=m. The high-far A0 count <=N+1 by normalization, with gain <=C(N+1). Consequently
    G/7-o(X) <= 2P*m + (C+2P)(N+1)+ 2 b_B/alpha,      (4)
    2 b_B/alpha <= (C+2P) B_K,
    2 b_B <= F_K.
These bounds use the new hybrid family, not all old dense barriers, which need not cross K.

## 4. Root-or-crossing-B count theorem

Take R=floor(c0 log X), S=floor(a0 log R), where 0<c0<1/(8log2), 0<a0<1/(4log2) fixed. For sufficiently large X, R>S>=47, K<=2 R^(4a0 log2)=o(R), T=(1/5+o(1))R, ell=log10-o(1), gamma=log(3/2)+o(1), P log X=o(sqrt X) by the established elementary Chebyshev bound. E and each reset loss are O(log X).

Every charged B of Jset is either near (at most O(sqrt X) in the window) or included in B_K. From (2),
    m <= O(B_K+sqrt X+(N+1)log X).
Insert this in (4) and use P log X=o(sqrt X) to get
    (C+o(sqrt X))(N+B_K) >= G/7-o(X),
and hence
    N+B_K >= ((lambda-1)/(7sqrt(lambda))-o(1))*sqrt X. (5)
For lambda=16 the constant is 15/28. This is the previous count theorem with a strictly restricted counted population: every counted B must physically cross a multiple of K_S. It allows B resets in B_K and does not require all B_K events to reduce Phi. No claim about B count at the original R cutoff alone. The estimates are uniform for the chosen constants and sufficiently large crossed windows beyond the initial root.

## 5. Stronger root-sparse gain bound

Suppose N=o(sqrt X) along crossed windows. In (2)-(3), bound the loss of near recovering B by gamma O(sqrt X), and use the weighted (3) for the far ones. By K c_K<=g+K,
    ell*m <= (F_K+K B_K)/T + O(sqrt X+(N+1)log X).
Every p>S gives gain>=S, so B_K<=F_K/S. Substituting this estimate in (4) (and using 2b_B<=F_K) yields
    [alpha^(-1) + 2P(1+K/S)/(T ell)] F_K >= G/7-o(X).   (6)
The terms O(P sqrt X+P(N+1)log X) are o(X); there is no need to multiply the reset's full gain by P. For the growing cutoffs above, Bertrand's postulate provides a prime in (R/2,R], above S. Its factor in A is Omega(R), so alpha^(-1)=P/A=O(P/R). Since K>=S, T~R/5 and ell~log10, (6) proves
    F_K = Omega(S R X/(K P)).                          (7)
Previously the bound for all far B p>S was Omega(S X/P). The new bound for just crossing far B gains the factor R/K -> infinity, and K<=2 R^delta with delta=4a0 log2<1. Thus in particular F_K=Omega(S R^(1-delta) X/P). This is not a uniform linear bound as S grows.

For any fixed integer S>=47, take a sufficiently large fixed R>S to ensure ell>0. Then the proof of (6) works with fixed K,P,alpha,T,ell,gamma and gives F_K=Omega(X) in root-sparse windows. Moreover each crossing event obeys g<=2K c_K; its cuts are disjoint from those of other events. Thus at least F_K/(2K)=Omega(X/K) distinct multiples of K in the interval are crossed by far B. In this fixed-cutoff case a positive fraction of those cuts must be crossed by far B, not just an unspecified positive fraction of the total gain attributable to p>S. Constants depend on the fixed S,R,lambda,epsilon0.

## 6. Narrow-band recovery and a weighted tradeoff

Suppose additionally that the count of far B with p>R crossing K is o(sqrt X) (weaker than requiring all far B above R sparse). Then in (4), the A0 and B capacities are o(X), so the marked A1 count satisfies
    m >= ((lambda-1)/14-o(1))*X/P.
This is much larger than sqrt X log X. In (2) discard the near and p>R far B recovery contributions, bounded by gamma times their counts, and all reset/boundary terms. Let J_band be the remaining recovering B nonresets in Jset, all far and S<p<=R. Write j_band for their count and F_band for their gain. Each crosses at least one K-cut and strictly decreases Phi, with K c_K>2w by (1). Then
    j_band >= (log10/log(3/2)-o(1))*m,                 (8)
    K sum_{J_band} c_K >= (log10/5-o(1))*R*m,          (9)
    F_band + K j_band >= (log10/5-o(1))*R*m.          (10)
For (9) use (3) with the gamma bound on omitted recovering B, not the potentially large weighted cut length of near events. Equation (10) follows from K c_K<=g+K. As F_band>=S j_band, this yields F_band>=Omega(S R m/K)=Omega(S R X/(K P)). If j_band=O(m), K=o(R) forces F_band=Omega(R m), so the average selected label among these recovery events is Omega(R). Conversely if F_band=o(R m), then j_band=Omega(R m/K), many more than m. These are actual events in a single ray with a specified decreasing modified potential, not merely a count of all nonreset B; they need not strictly decrease ordinary d because rho may fall.

## 7. What repeated labels alone can bound

For a fixed p>S, p is coprime to K, and cut residues J=kK cycle through all p residue classes every p cuts. Geometric crossing by p is impossible at (p-1)/2 of these residues, possible (as a necessary test) at (p+1)/2. Thus among L consecutive K-cuts, at most ((p+1)/(2p))*L+O(p) can be crossed by p. Each crossing event owns at least one distinct cut, so its multiplicity in a block of horizon width G is at most this bound with L=G/K+O(1). Also the pre-horizons H=e modp with H even allow at most G/p+O(1) occurrences counting both sides. These bounds give O(min(G/p,G/K)+p) for crossing events with p fixed. They are too large compared with X/P at the growing cutoffs, since P is much larger than both K and R; the new result is a joint recovery/crossing bound rather than a contradiction based on repeated use of one label. No upper bound on the full B population sufficiently small to exclude an infinite ray was obtained.

## 8. Diagnostics and persistence

[Audit a451db8](https://github.com/tara-sooo/A166944-Lean/blob/a451db86446bf95b073fb7a884160e75c9d935ff/research/min_direct_hybrid_cut_recovery_audit.mjs), blob 746136a6d30937122f3ba0d303b6ef82ba8e064e. Exact remote readback. Run node research/min_direct_hybrid_cut_recovery_audit.mjs 50000 180. Actual ECMAScript executed in tool runtime, not a separate Node process.

24,998 odd canonical roots M5..50000, 452,868 actual events, 3,929 A1, all terminated within the 180-event cap. 633,421 block/cutoff tests including the CRT witness; 32,939 retained segments, 287,145 exact BigInt local cut-update checks, 253,840 noncrossing checks, 38,246 separator checks, 633,421 logarithmic and 633,421 weighted budget tests each. Diagnostic R=47/101/1009, S=5/7/11/13/47 with S<R. Smaller S below47 checks the non-A1 nonreset property and the B classification whenever p>=47. K and cut counts are exact BigInt; logarithms and numerical budget comparisons use floating point tolerance 1e-8. Some cutoffs have ell<=0, included only as finite inequality diagnostics. All assertions passed.

Hybrid periods (S,R)=(3,5),(5,7),(5,11),(7,13),(11,17) have (P,A)=(15,2),(105,3),(1155,15),(15015,30),(255255,48), checked by complete periods. 121,895 block/cutoff and 2,264,340 per-event hybrid checks, all passed. These small cutoffs verify barrier geometry and capacity, not the asymptotic class theorem.

Reconstructed the prior 9,962-digit canonical root with event word7687/5233/3541/2389/1621/1093/733/7369, 22,195 literal BigInt GCD ticks and 20,600 stage-residue checks. At R1009,S5 (K30) the new potential charges six decreasing crossing B nonresets, two marked A1, no resets, weighted K cut length14610 and recovery gain14604. This witness is finite and does not establish an infinite ray or a macroscopic crossed-window instance. The asymptotic theorems follow from the symbolic estimates, not from fitting these data. Main and sibling branches unchanged. No Lean executable/kernel verification, external novelty claim, or proof of twin infinitude.

Next: use the strict condition K c_K>2w on charged B, or vary the cuts to constrain the simultaneous recovery of one actual trajectory. The fixed-label capacity estimate in section7 by itself cannot yield the needed contradiction. Under finite twins all sufficiently large canonical roots give infinite rays and must satisfy the count, gain and weighted recovery bounds above, but those bounds remain compatible with finite twins.
