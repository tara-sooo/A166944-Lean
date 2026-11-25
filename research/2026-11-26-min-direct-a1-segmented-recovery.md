# Segmented A1 recovery eliminates the dense-small-A1 escape from the root-or-B count alternative

Continuation of [c14ee7f](https://github.com/tara-sooo/A166944-Lean/commit/c14ee7ffe048cda988aa547d5e9ce78e704f63c6) and [1924deb](https://github.com/tara-sooo/A166944-Lean/commit/1924deb3d9c5a23fc6f07a796ad579520006f631). The earlier truncated logarithmic potential counted other high nonresets, which could include unmarked A1. A new segmentation removes all unmarked A1 from the charged recovery intervals. Together with the A1 gain-share ceiling and dense modular barriers it proves a root-or-far-B count bound at a lower growing prime cutoff, and a linear far-B gain bound at every fixed cutoff in root-sparse windows. It does not prove twin infinitude or A166944. No Lean kernel verification.

## 1. Notation and segmented budget

At each actual event, pre/post ordinary deficits d,d' obey d'=d+2w-(p-1); adjusted D=d'-6I, I=0 even side or1 odd. A1 means p>=47, p>=5d+15, D=2p. A0 means the same size/deficit test with D=0. By 3f1448b these are the only two possibilities when the test holds. B means failure of that test at p>=47, i.e. d>(p-15)/5. Far has the earlier square-band definition: not k^2<=eps0*x at sufficiently large center x=(p+q)/2, k=(q-p)/2, H=pq+e; use fixed 0<eps0<1 and the previous center threshold. The near event count on pre-horizons in [X,lambda X] is O_eps0,lambda(sqrt X).

Take any finite contiguous event block of a canonical ray at sufficiently large H, all pre-horizons <=Y. Fix integers R>S>=47. Set
    T=R/5, Phi(d)=log(max(T,d+3)),
    K_S=2 product_{odd primes p<=S} p,
    epsilon=log(1+K_S/T), C=floor sqrt(Y+1).
Mark ALL A1 with p>R, whether near or far. Denote their count by m. A marked event increases Phi by at least log10: d+3<=p/5 and T<p/5, d'+3>=2p+3. An unmarked A1 has p<=R and therefore Phi(d)=log T at its pre-state. This last identity enables a segmentation not used in the previous budget.

Remove the unmarked A1 events themselves and split the block into maximal consecutive segments between them. Keep only segments containing at least one marked event. Let b be the number of kept segments, so b<=m. No kept segment contains an unmarked A1. Every kept segment ending just before an unmarked A1 ends at Phi=log T. The sum of their endpoint potential differences Delta is therefore at most Phi(d_end)-log T, where d_end is the full block's final deficit: all non-final segments have nonpositive difference, and the only segment potentially ending at a higher potential is the one ending at the full block's endpoint. This remains true when the final segment is not kept or when no segment is kept.

Within the kept segments count:
    n = nonreset events with p>S other than marked A1;
    J = those among n with d'<d;
    z = resets with p>S.
Every event counted by n is genuinely B (not an A1 with p<=R, since these were removed; not A0, since nonreset). The loss of Phi at each decreasing nonreset is <=log(3/2), and at a reset q is <=log_+((q+6)/T), as in 1924deb. Low-label runs p<=S have total gain <=K_S by the primorial cut, hence total Phi loss <=epsilon per run. There are at most m+n+z+b<=2m+n+z such runs across all kept segments. Summation proves
    m log10 <= Delta + J log(3/2)
                 + sum_{kept high resets q} log_+((q+6)/T)
                 + epsilon(2m+n+z).                 (1)
This is a finite inequality even if epsilon is large. Its improvement over the old budget is that n now counts only B nonresets, with no other A1 contribution, and discarded segments need not be controlled.

On an infinite ray each reset with p>S has a distinct canonical reentry within seven ticks before the next p>=7 event. Thus z<=N+1 for N actual canonical visits in the full block's time interval (start,end]. At most one root is pending at the right boundary. For finite prefixes the same inequality is true: a reset followed by termination without an actual visit cannot be followed by another high reset. Let B_S^all count ALL B events with p>S in the full block (including resets if failing the test), and B_S count only far ones. Then n<=B_S^all. We obtain
    (log10-2epsilon)m
      <= (log(3/2)+epsilon) B_S^all
       + (N+1)[log_+((C+6)/T)+epsilon]
       + Phi(d_end)-log T.                            (2)
Using the actual selected J and resets in (1) retains a more precise inequality. No independent-random assumption is used.

## 2. Combined root-or-far-B count theorem

Consider an infinite canonical ray and its block from the first horizon >=X to the first >=lambda X, fixed lambda>1. Pre-horizons in [X,lambda X), G total gain = (lambda-1)X+O_lambda(sqrt X), C=floor sqrt(lambda X+1). Choose
    R=floor(c log X), 0<c<1/(8 log2),
    S=floor(a log R), 0<a<1/(4 log2).
For sufficiently large X, S>=47, S<R, K_S<=2 R^(4a log2)=o(R), epsilon=o(1). Also P=P_R=product odd primes<=R <=X^(4c log2), so P log X=o(sqrt X). The canonical deficit bound gives Phi(d_end)-log T=O_lambda(log X) (the bound does not require low deficit at the endpoint). Near events of any class have count O(sqrt X); thus B_S^all<=B_S+O(sqrt X). From (2),
    m <= O(B_S+sqrt X+(N+1)log X).                    (3)

Recall the previous high-far barrier residual L0=G-N_g-2P(N_c+1), with high-near gain/count N_g,N_c. Then L0>=G/2-o(X), where the error is uniform in the ray by square packing and P=o(sqrt X). Write m1 for high-far A1 count at cutoff R, m0,F0 for A0 count and gain at that cutoff, b_B for barriers covered by high-far B at cutoff R, alpha=alpha_R. By the gain-share bound of c14ee7f,
    L0 <= (5/14)G+O(C)+2P m1+F0+2P m0+2b_B/alpha.
Here m1<=m (marked includes all near and far A1), F0+2P m0<=(C+2P)(N+1), and 2b_B/alpha<=(C+2P) B_S since S<R and each jump has that normalized barrier capacity. Hence
    G/7-o(X) <= 2P m+(C+2P)(N+1+B_S).                (4)
Substituting (3), and absorbing P sqrt X=o(X), P log X=o(sqrt X), proves
    (C+o(sqrt X))(N+B_S) >= G/7-o(X).
In particular the new theorem is
    N+B_S >= ((lambda-1)/(7 sqrt(lambda))-o(1))*sqrt X.   (5)
All asymptotic errors are uniform for a fixed lambda,eps0,a,c and sufficiently large crossed X beyond the initial root. For lambda16 the leading constant is 15/28. B_S refers to actual far events failing the low-deficit test, with p>S of order loglog X. They may be resets or nonresets. In particular every counted event has d>(p-15)/5 and q-p>2sqrt(eps0*p) at sufficiently high H. No lower bound at the ORIGINAL log X cutoff is asserted. If N=o(sqrt X), (5) supplies Omega(sqrt X) far B at this lower cutoff without any additional assumption on A1 count. This removes the old dense-small-A1 alternative from the count theorem by transferring its recovery requirement to B.

## 3. Stronger consequences when B is sparse at the higher cutoff

Suppose along a sequence of crossed windows N=o(sqrt X) and B_R=o(sqrt X), where B_R is the high-far B count with p>R. The previous gain-share/barrier inequality gives
    m1>=((lambda-1)/14-o(1))*X/P.
This is much larger than sqrt X log X because P<=X^delta, delta<1/2. Now apply (2), with m>=m1, N=o(sqrt X), epsilon=o(1). Reset and boundary terms are o(m1). Removing the O(sqrt X) near B yields
    B_S >= (log10/log(3/2)-o(1))*m1
        >= ((lambda-1)log10/(14 log(3/2))-o(1))*X/P.  (6)
In this regime the numerous smaller A1 forced by c14ee7f require comparably numerous far B events at the lower cutoff, not merely other high nonresets. Since B_R=o(sqrt X), the count in (6) still holds for S<p<=R, up to the lower-order error. All these far B events have total gain at least S times their count (integer p>S). Thus at least Omega(S X/P) gain lies in this lower label band. The previous log-budget count n could include intermediate A1 and did not imply this statement. For c=1/(16 log2), R of order log X, P<=X^(1/4), S of order loglog X, the count is Omega(X^(3/4)) and gain Omega(X^(3/4) loglog X). The recovery B events counted in (6) are nonresets as well: use n in (1) rather than B_S^all and the same upper bound by near nonreset B count. The displayed lower bounds therefore also hold for far nonreset B in the band under the two sparsity hypotheses. It is not claimed that all counted B nonresets strictly decrease d; (1) distinguishes J, but the low-run error can still involve n.

## 4. Linear far-B gain for every fixed cutoff in root-sparse windows

The same proof permits fixed integer S>=47 of arbitrarily large size. Choose a fixed R>S so large that epsilon=log(1+5K_S/R)<(log10)/4. Then P and alpha are fixed positive constants (possibly extremely large/small). For a crossed window with N=o(sqrt X), the A0 capacity and endpoint/near errors are o(X); the gain-share ceiling implies
    G/7-o(X) <= 2P m+2b_B/alpha.
Write F_S for total gain of far B with p>S, so 2b_B<=F_S by even-position counting. Also B_S<=F_S/S. From (2) with a fixed positive coefficient on its left,
    m <= A (F_S/S+O(sqrt X))+O((N+1)log X+log X),
    A=(log(3/2)+epsilon)/(log10-2epsilon).
Consequently
    [1/alpha+2P A/S] F_S >= G/7-o(X).                (7)
Thus for every fixed S>=47, root-sparse crossed windows require Omega_(S,lambda,eps0)(X) gain from far B with p>S. No uniform positive fraction as S->infinity is claimed; choose R deterministically as a function of S. This is stronger in gain than (5) at a fixed cutoff and is not a statement about the entire nonreset class.

For growing R,S as in section2 and N=o(sqrt X), the same computation of (7) is valid with A bounded uniformly and errors o(X), because P log X=o(sqrt X). It gives
    F_S >= Omega(X/(alpha_R^(-1)+P_R/S)).
Since A_R=alpha_R P_R=product_{odd primes<=R}(p-1)/2 >= (R/2) for large R up to a harmless constant (indeed it grows exponentially in the number of primes, and one may use the elementary prime-count lower bound, or simply the existence of a prime in (R/2,R] by Bertrand and its factor), A_R>=S for S=O(log R). Hence F_S>=Omega(S X/P_R). Even without this comparison the displayed denominator bound is valid. The cutoff R may also be chosen much smaller, for instance of order loglog X, with S of order logloglog X; then the bound is of order X divided by a fixed power of log X, multiplied by S. The proof only requires S<R, S>=47, epsilon bounded below log10/4, P log X=o(sqrt X). This does not establish a universal linear bound at a growing cutoff.

## 5. Verification and limitations

[Audit eff4a8e](https://github.com/tara-sooo/A166944-Lean/blob/eff4a8e874be00fceb9dd7b02756dc504515d2bc/research/min_direct_a1_segmented_recovery_audit.mjs), blob 7b5cc8baa849a9e70e5473316afc5f3c159340b6, exact remote readback. Run node research/min_direct_a1_segmented_recovery_audit.mjs 100000 180. Actual ECMAScript function executed in tool runtime, not separate Node process. 49,998 odd canonical roots, 1,020,339 events, 9,591 A1, 49,989 stopped before cap, 9 cap-unresolved. Across full and suffix prefixes, R=47,71,101,151,1009 and S=5,7,11,47,53 with S<R: 2,106,087 block/cutoff incidences (including the separate CRT witness), 143,856 kept segments, 140,511 separator tests, 934,424 low-run checks, 789,942 selected high-nonreset classification checks, 4,212,174 logarithmic budget checks, 2,106,087 root bounds. All passed. Smaller S below47 are diagnostic only: the code checks non-A1 high nonreset, and B classification where p>=47. Log tests use floating point with tolerance1e-8; the theorem is the exact symbolic argument above. Large K_S is represented as Number for the numerical upper-bound tests, not exact integer arithmetic at those cutoffs. No observed macroscopic crossed window claimed.

Reconstructed the earlier 9,962-digit actual canonical root with labels7687,5233,3541,2389,1621,1093,733,7369. 22,195 literal BigInt gcd ticks and 20,600 stage-residue checks passed. The new budget at R1009,S47 counts two marked A1, six high nonreset B, all six decreases, zero resets. The test uses relative ticks and a conservative upper bound on reset labels (none present); near is false for the huge horizons and small labels. At those finite cutoffs epsilon is large, so the asymptotic small-epsilon conclusion is not inferred from this example. This demonstrates the budget remains compatible with the sharp finite recovery construction.

Under finite twins every sufficiently large canonical root gives an infinite ray. Equations (5)-(7) apply to each such ray but do not contradict finite twins. The new conclusions constrain the population of far B events, including the abundant small-label recovery regime, but neither bound their maximum possible frequency nor force a twin terminal. Main and sibling branches unchanged. No Lean executable/kernel verification, no external novelty claim.

Next: investigate far B events in the narrow band S<p<=R on one ray, especially their high predeficit and the possible repeated use of small labels, or find a different stopping invariant. The new root-or-B alternative is stronger than a marginal lower bound on A1, but the abundance of far B itself remains compatible with the known necessary conditions.
