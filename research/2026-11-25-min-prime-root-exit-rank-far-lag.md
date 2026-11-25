# One-edge rank stability, exit synchronization, and the same-label far-lag high target

2026-11-25 JST. Continuation of eb93941e0f5a85372237d2b290323802960e2fd2 on the selected prime-root branch. The preceding macrogrid mask controls synchronous high pairs through old cohorts but leaves asynchronous high separate. Here derive an independent polynomially small LINEAR deletion of new waiting mergers at high-event exits. Then a bounded-degree lag graph and a constant-size selected-prime partition reduce the remaining high-energy problem to the already existing synchronous target plus only asynchronous pairs of the SAME selected high prime with sufficiently separated actual departure ticks. In particular it is no longer necessary to establish an independent little-o estimate for all different-label asynchronous high energy. Paper deductions and reproducible finite audit; no general far-lag estimate, no Lean compilation, twin-prime infinitude OPEN.

## 1. Setup and exact one-edge rank increment

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, N=Theta(X/u) prime original roots M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, Q=ceil(B/u). Original canonical MIN prefixes and all terminal snapshots unchanged. A completed event at physical prevertex v=(C,t) selects p<=B with actual wait w>0, least eligible prime r(C)<=p, postvertex v+=(C+p-1,t+w), and w<=2r<=3(p-1). Let R_all=sum of original r costs <=1.5 NH. Natural high means p>=Q and r>p/sqrt(log p). As before the stronger support sieve gives S_*=sum_C r(C)=O(XB/u³); thus high energy o(F) suffices for high proxy clock o(NT). Actual high wait is at most twice proxy.

Define d_M(v)=#{original tags M'>=M visiting v}, including M itself and original terminal snapshots. By deterministic continuation and original source-ordered stops, this is nondecreasing along the entire original recorded path; at an original root d_M=1. If M completes its outgoing edge at v, all d_M(v) counted tags actually complete that same edge (no extension beyond stop). Its one-edge increment
    gamma_M(v)=log(d_M(v+)/d_M(v)) >=0
has exact telescoping sum log d_M(terminal)<=log N per root. Thus sum gamma<=N log N. These are ranks in the FULL original source ensemble, not ranks after any accounting deletion.

Choose delta=sqrt(Bu/H)=Theta(u^(5/8)/sqrt B), eventually <1. Remove every currently retained high hit for which gamma_M(v)>delta. Since r<=B and the number of marked hits per root is <=log N/delta,
    R_jump <= B N log N/delta = O(N sqrt(B H u)).
This holds regardless of other incidence masks. This step can use all completed hits, including those whose poststate is their actual terminal snapshot. The analytic finite audit caps delta at .5 to avoid oversized small-scale thresholds.

## 2. Single physical predecessor at a high exit

For each actual poststate v+=(J,s) and each selected high label p, group the remaining actual tag incidences with that exact exit and label. All these hits have the identical prehorizon C=J-p+1 and hence identical r(C), but may have different arrival ticks t. Choose the smallest original source M0 among the currently retained incidences in this group. Let v0 be its actual physical prevertex. Keep only the tags of the group that have prevertex v0; discard every other tag's current hit. This is a hit mask only, not a rerun or a deletion of later original path segments.

All larger original tags that visit v0 follow the same completed edge as M0, and hence visit v+. Among original visiting tags >=M0 at v+ the number not already present at v0 is exactly d_M0(v+)-d_M0(v0). Every discarded incidence belongs to this latter set. By the retained one-edge gate, the number discarded at this exit key is <=(exp(delta)-1)d_M0(v0). Since M0 completes its event, d_M0(v0)<=n_v0, the full original completed mass at v0. Multiply by the common r(C). The chosen physical prevertex v0 can occur for at most one exit key because its completed successor and selected label are deterministic. Therefore
    R_foreign <= (exp(delta)-1) sum_chosen v0 r(C_v0)n_v0
              <= (exp(delta)-1)R_all = O(delta NH).
No comparability of r across different incoming labels is required. The result works with arbitrary prior tag deletions, noncontiguous retained source order, and at original terminal snapshots. This also works for all selected labels if desired, but only the high incidence use is needed. Same-label waiting mergers that were not yet synchronized at the recorded prevertex are eliminated from the remaining high pair ledger, without needing a quadratic estimate of their total original energy.

Together the two masks give
    R_exit <= O(N sqrt(B H u)) = O(NT u^(5/8)/sqrt B)=o(NT). (1)
Actual removed wait is <=2R_exit. The error relative to NT tends to zero faster than any fixed inverse power of u. The result is a LINEAR incidence deletion, not a claim that the removed synchronous/asynchronous pair energies were themselves o(F). On remaining hits:
    same C, same selected p, same actual exit tick s
      implies same actual physical prevertex (C,t).
In fact the converse also holds by deterministic selection. The result is independent of the earlier macrogrid construction; can be applied before or after its masks. Its per-key smallest-source choice is calculated from the current retained hits; all ranks and budgets remain on original paths.

## 3. A constant-label Cauchy reduction

At a fixed C, a possible selected high p divides either C-1 or C+1 and satisfies p>=Q. The two odd integers are O(X). Since Q³>7X+2 eventually, each has at most two distinct such prime factors. Thus there are at most four possible selected high primes at this horizon. This is a deterministic divisor bound, NOT a claim about the number of observed physical states or source tags. No least-factor or time-independence assumptions are used.

For an arbitrary retained incidence set after the exit mask write n(C,t) for its physical prevertex mass, n(C,p,s) for its mass at selected label p and actual exit tick s, n(C,p)=sum_s n(C,p,s), n(C)=sum_p n(C,p). Section 2 and determinism give an exact one-to-one correspondence between the nonempty prevertex and (p,s) buckets at a given C. In particular
    E_phys = sum_C r(C) sum_t n(C,t)²
           = sum_C r(C) sum_(p,s) n(C,p,s)².
It includes the diagonal, which is O(NT)=o(F). Let E_same be the high energy including diagonals and all pairs with the same selected p, whether synchronous or asynchronous:
    E_same = sum_C r(C) sum_p n(C,p)².
By the constant-label bound and Cauchy,
    E = sum_C r(C)n(C)² <= 4 E_same.                       (2)
Consequently no separate bound on different-label async cross-products is needed if we establish E_same=o(F). This is an alternative sufficient target for the total remaining high energy. It is not a claim that all those cross-products are zero, or that an arbitrary weighted subset of pair products satisfies (2). Apply (2) to the actual retained incidence set BEFORE subsequent pair-energy accounting; that accounting may then be restricted to the same-label terms. Any old absolute pair payment on the full set remains an upper bound on the corresponding subset.

## 4. Near exit-lag graph and far-only asynchronous target

At fixed C and odd p the sign of p|(C+sigma) is unique, because p cannot divide both C-1 and C+1. The original actual exit tick s belongs to exactly one residue mod 2p: s=0 mod 2p for sigma=-1 (even), s=p+2 mod 2p for sigma=+1 (odd). Thus any two DISTINCT physical prevertices remaining with the same C,p have distinct exit ticks whose difference is a nonzero multiple of 2p. For any integer K>=1 a given (p,s) bucket has at most 2K other same-label buckets with |s-s'|<=2Kp. For the graph of these unordered bucket pairs, using 2ab<=a²+b²,
    E_near,same(K)
      = sum_C 2r(C) sum_(unordered near same-p distinct buckets) n_i n_j
      <= 2K E_phys.                                     (3)
No bound on any individual bucket mass is assumed. This is an upper bound on the entire near sector after the linear mask, and hence on any remaining pair subledger. If one wants a bound also for different labels, use the condition |s-s'|<=2K min(p,p'). For each possible p', its exit residue modulo 2p' gives at most 2K+1 ticks in that window (including possible equal ticks at different labels). With at most four labels per horizon, the total degree is <=4(2K+1), hence E_near,all(K)<=4(2K+1)E_phys. Again this does not bound arbitrary far different-label energy, which is unnecessary by (2).

Define E_far,same(K) to be the ordered distinct-tag pair energy at common C with common selected p but |s-s'|>2Kp. Then exactly
    E_same = E_phys + E_near,same(K) + E_far,same(K),
and consequently
    E <= 4[(2K+1) E_phys + E_far,same(K)].               (4)
For every fixed K this is a constant-factor bound. A new sufficient high condition is E_phys=o(F) and E_far,same(K)=o(F) for any fixed integer K>=1, on the same unbounded dyadic sequence. More generally assuming E_phys=o(F), one may require only
    lim_(K->infinity) limsup_(X along that sequence) E_far,same(K)/F = 0.
Indeed divide (4) by F, take limsup at fixed K, then K->infinity. Equivalently one can choose a sufficiently slowly diverging integer K(X) if the far-lag condition and E_phys allow it; no specific diverging rate follows from little-o alone. The same-label far pair shares the projected successor horizon J=C+p-1, but its poststates have different ticks. Its original input lag obeys |t-t'|>=|s-s'|-2r(C), because both actual positive waits are <=2r(C); its post-deficit difference is 2|s-s'|. In particular a far pair for K>=1 has disjoint waiting intervals at that horizon (both actual waiting intervals have length <=2p, and their exit separation exceeds 2p). These are actual phase-lattice constraints, not a probabilistic independent clock claim.

The preceding macroblock synchronous Hall condition continues to suffice for E_phys=o(F), after the same old absolute energy payments and total o(F) capacities; the new incidence mask cannot increase it. To combine with older pair accounting, first restrict the high incidence set by the actual linear masks, then bound the full E_phys and full far same-label sector by their respective old paid pieces plus residuals; the bounded-degree argument uses full E_phys, not an old unpaid flow scalar. The unchanged medium actual residual o(NT) is still needed. This gives a strictly weaker sufficient task than separately bounding all async high energy: close exit lags are controlled by synchronization, and different selected labels can be omitted by constant-size Cauchy. The new far same-label condition itself is OPEN. A next arithmetic approach is to study nonzero phase-lattice lag changes on actual projected common-edge chains with distinct high labels, using the macroblock rank/formation mask to control transitions toward synchronization. Merely observing that the lag is a multiple of p at one hit does not bound the cumulative far tail. No Lean compilation or twin-prime proof.

## 5. Finite verification

Source research/min_prime_root_exit_rank_audit.mjs at cc8712b5fe2ee71049cb4170c07d02060c39ceec, blob a1d9c9a4d8bd47fbc97db093dc25872c22100a5a, exact remote readback. Ran 18 actual tests in available ECMAScript runtime, not separate Node process:
    node research/min_prime_root_exit_rank_audit.mjs diagnostic 256 1024 4096 16384 65536 262144
    node research/min_prime_root_exit_rank_audit.mjs stress 256 1024 4096 16384 65536 262144
    node research/min_prime_root_exit_rank_audit.mjs analytic 256 1024 4096 16384 65536 262144

All passed. Standalone original MIN factorized parity clock with literal per-tick GCD comparison on X<=1024; independent original descending rank by reverse source traversal, original successor and terminal membership, telescoping log budget, rank cost bound, actual same-label exit groups, foreign rank and completed-mass bound, chosen prevertex uniqueness, exact removal partitions for proxy and actual wait, zero retained distinct-prevertex pairs sharing (C,p,s), phase congruence and lag transfer, exact total/synchronous/same-label async/different-label async energy partition, local label Cauchy, near graph bounds for K=1,2,4 and the full far-only envelope. Floating logarithms use tolerance. Diagnostic/stress T=4B, Q=max(5,ceil(B/8)), r>p/2, delta=.2/.5. Analytic T and Q and relative high predicate as in the paper, delta=min(.5,sqrt(Bu/H)). This is an ISOLATED new high mask on original natural high incidences, not the previous cumulative macroblock ledger; no medium computation, no new Hall-flow residual claim.

| X / mode | raw high actual | rank removed actual | foreign removed actual | retained actual | same-label same-exit distinct-pre pairs before -> after | far same K=1 | far same K=4 |
|---:|---:|---:|---:|---:|---:|---:|---:|
|256/diag|1464|267|15|1182|56 -> 0|300|84|
|1024/diag|3908|1168|29|2711|88 -> 0|550|52|
|4096/diag|32485|8341|284|23860|374 -> 0|13580|552|
|16384/diag|176121|67694|2207|106220|2377 -> 0|68614|8016|
|65536/diag|1292149|525437|14220|752492|11116 -> 0|357516|20172|
|262144/diag|7958300|3282030|102982|4573288|50995 -> 0|2818904|322314|
|262144/stress|7958300|2137952|455941|5364407|50995 -> 0|3703692|329512|
|262144/analytic|7971454|3097572|153563|4720319|50067 -> 0|2874168|331384|

Largest analytic: 20390 roots, 616116 completed events, 636506 original rank checks, rank log total 27179.8653568, 9720 rank-marked hits and 371 additional foreign tags across 302 nonempty foreign groups (max7). 3494 retained exit/prevertex buckets, 89 chosen exit groups with actual terminal tags at poststate. Before rank filter 50067 same-label distinct-pre pair hits sharing actual exit (ordered weight45842602), after rank filter2814 (weight2244784), after foreign mask zero. Remaining actual high4720319, proxy5260037 (different units). E=90129259, E_phys=73958743 (includes diagonal5260037), same-label async12042588, different-label async4127928. Observed max3 selected labels. Same-label near K1=9168420, K2=11000252, K4=11711204; far respectively2874168,1042336,331384. 643 distinct-bucket pair checks, 533 same-label lag transfer checks. These finite results exercise positive same-label async far tails and nonzero terminal-containing exit groups; the far fraction is not an asymptotic estimate.

Main and other branches unchanged. Paper proof and finite ECMAScript verification; no Lean compilation and twin-prime infinitude OPEN.
