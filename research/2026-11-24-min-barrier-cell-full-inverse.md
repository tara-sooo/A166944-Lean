# Barrier-cell admission caps with full inverse-prime stopping

2026-11-24 JST. Continues b7cc769a4fc6dd25bc8ce4becd9b9c6b0d2b4162 on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions from the established MIN barrier, per-prime upper-bound sieve, and capped clock moment; exact finite diagnostics. Not Lean-checked. No full anti-concentration bound or twin-prime proof.

## 1. Separate the low-block budget from the prime cap

Canonical odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), t0=M+2,C0=2M-2, original individual cutoffs K(M). Let Y tend to infinity, 11<=Y<=B, L=2 product_(3<=p<Y prime)p. Use cells (jL,(j+1)L] of even horizons, closed at the right, open at the left. This convention is essential: a LOW step with p<Y cannot leave its cell, by the exact earlier even-multiple barrier, and at the right endpoint no such prime is eligible.

Process the cells in increasing horizon order. At the beginning of a cell ALL incoming tags from earlier cells and all initial tags with C0 in this cell are known. Each tag enters the cell at most once since the horizon strictly increases at events. Before processing any events in the cell, if its total admission mass m is >=T, stop ALL these tags at their actual attained entry states (initial states for root injections). This is a new accounting stop, not a claim of a physical coalescence or a common clock or horizon. If m<T, process the original MIN events in the cell. LOW labels p<Y are never stopped inside a processed cell. For all p>=Y, use the FULL inverse-prime projected threshold
    tau_p=ceil(B^2/p).
Stop the whole proposed key (p,C) when its actual mass reaches tau_p. Continue otherwise under original clocks and original individual cutoffs. Exits to later cells are recorded at their actual attained states. Cells cannot receive further arrivals from earlier cells after their processing begins. Within-cell arrivals are not counted a second time in the admission test. The rule changes only the accounting truncation, not the MIN evolution before truncation. In particular one must NOT stop only the later arrivals to an already processed cell; the batch-at-entry rule is what makes every cell stop population >=T.

Write S_c,S_p for the total masses of cell and prime stops, S=S_c+S_p. Stop cohorts disjoint, number of cell stops J_c<=S_c/T, number of prime stops J_p<=S_p/B.

## 2. Global budget: no intermediate prime band

For executed high keys p>=Y, mass <=B^2/p. Using the earlier S_p^cost=O(X/log^2 p) bound on the sum of r(C) over eligible horizons for fixed p,
    R_hi <= O(X B^2 sum_(p>=Y prime)1/(p log^2 p))
         = O(X B^2/log^2 Y).
For a processed cell and one admitted tag, the sum of p-1 over ALL its low events in that cell is <=L: its horizon increases, and all low steps remain inside the cell. This holds even if high steps intervene. Each low r(C)<=p<=1.5(p-1). Consequently the low cost of the entire cell is at most 1.5 L m <1.5 L T. There are O(1+X/L) cells meeting the whole horizon window. Thus
    R_lo <= O((X+L)T),
    R_pre <= O(X B^2/log^2 Y + (X+L)T).
This avoids charging a whole L for every high incidence, the loss that forced the truncation Z in the previous rule. Choose Y=c log B with fixed sufficiently small c>0, so L<=sqrt B by Chebyshev, and T=ceil(X/log^2 Y). More generally any Y tending to infinity with L=o(T), L<=X suffices with this T. Then
    R_pre=O(X^2/log^2 Y)=o(X^2).
On a hypothetical no-twin window the old per-unstopped-nontwin lower cost Omega(X) applies unchanged, so S=N-o(X).

For all prime stops, no restriction p>=Z is now necessary: I_p=sum_(prime stops)1/p<=S_p/B^2, J_p<=N/B. Their source-weighted hypothetical post-height sum H_p<=6N+4R_pre+4BN. Apply the established capped-clock-mass moment with scale D:
    G_virt,p <= D J_p + 0.5 sqrt(D H_p I_p)
             = O(X D/B + X sqrt(D)/log Y).
For integer D tending to infinity with D=o(log^2 Y), all prime-stop virtual variance is o(X), and the mass in prime-stop clock classes of size <=2D is o(X). Also the within-clock terminal variance is >=S_p/2-o(X). This is a bound for ALL prime stops p>=Y; the former unresolved interval Y<=p<Z no longer needs separate treatment at these prime stops. It is NOT a bound on the virtual variance of the additional cell stops.

## 3. Exact boundary gateways at cell stops

At a stopped cell (J,J+L], root injections are at most floor(L/4)+1, since original C0 have spacing 4. Their total over stopped cells is <=J_c(floor(L/4)+1)=O(N L/T)=o(X). Every other tag entered by an executed crossing event with label q>=Y (a low label cannot cross). Write A for the pre-horizon, C=A+q-1 for the actual entry horizon, u for the crossing time. Necessarily
    A<=J<C<=J+L,
    J-q+1<A<=J,
    q divides A-1 or A+1.
For each fixed boundary J and q, the interval for A has length <q, so at most one A per divisibility side is possible, hence at most TWO projected crossing keys (q,A), independently of L. Restricting to even A and to C<=J+L only reduces the count. This is substantially different from counting arbitrary last-large gateways to a small-label stop: there one sums over O(L) unknown low gains. Here the gateway is the very event entering the stopped cell.

For fixed cell, gateway projected key and actual u, the tags form a physical class, with post-height h=2u-C>=0. All have the same actual state. Group the non-root cell-stop tags by cell and projected crossing key, subdividing by actual clock. Each source counted exactly once. A crossing key cannot send tags to more than one destination cell, since C=A+q-1 is fixed. For each projected group, its mass <=B^2/q because the crossing event executed under the full inverse cap. Also possible clocks have period 2q (the side at A is fixed); heights separated by at least 4q. All weighted gateway heights sum to <=6N+4R_pre. This gives both a capacity estimate and a clock-moment estimate.

For any label band E subset [Y,B], put W_E=sum_(q in E prime)1/q, K_E=number of such primes. Let S_c(E) denote the cell-stop source mass with gateway label in E. Then
    S_c(E) <= 2 B^2 J_c W_E
           <= O(X log^2 Y W_E).
For the same population the number J_g of projected gateway groups is <=2 J_c K_E, and I_g=sum_group 1/q<=2 J_c W_E. If U_g(a)=sum_(actual physical gateway classes)min(m,a), the previous moment argument gives
    U_g(2D) <= 2D J_g + sqrt(D H_g I_g)
             <= O(D log^2 Y K_E + X sqrt(D W_E)).
The last inequality uses T=ceil(X/log^2 Y) and the global budget. Both bounds hold for ANY band; no clock lag restriction, parent-height index restriction or fixed prime ratio is required. The first bounds the entire cell-entry mass; the second bounds mass in small physical classes and the deficit from within-class variance S_c(E)/2.

In particular for Q=B/log^alpha B, fixed alpha>0, W_[Q,B]=O(log log B/log B), so the CAPACITY bound already shows S_c([Q,B])=o(X) with Y=c log B. More generally take Q=B^(1-1/log^3 Y); then W_[Q,B]=O(1/log^3 Y) by the elementary upper prime-count bound and partial summation, so S_c([Q,B])=O(X/log Y)=o(X). Thus nearly-top gateway labels cannot carry a substantial cell-stop population. This is a genuine deletion, not merely physical concentration of that population.

For a broader band take Q=B^(1-1/sqrt(log Y)), and D=floor((log Y)^(1/4)), which tends to infinity. Then W_[Q,B]=O(1/sqrt(log Y)). Using K_E<=B, the first term D log^2 Y B=o(X) for Y=c log B (also for any Y<=c log B), and the second term O(X/log^(1/8) Y)=o(X). Hence all but o(X) tags of this broad near-top cell-entry band have physical gateway class mass >2D, and the total within-class variance is >=S_c([Q,B])/2-o(X). This is stronger than the capacity bound in that broader band, where the latter can exceed N. It uses the boundary crossing to avoid an L multiplier. No claim that the band contains a substantial fraction of the cell stops.

## 4. Split-free physical target for both stop types

For the set consisting of all prime-stop tags and the broad near-top cell-stop gateway tags, retain original paths up to their respective proposed prime stop or executed boundary gateway. Use the physical clock refinement (include singleton root injections). Retained paths cannot split after sharing an actual high clock state: deterministic future, original individual cutoff only truncates, and any retained pair has to reach an accounting stop. If a shared proposed high key is a prime stop, it is a stop for both. If shared executed high event enters a stopped cell, both stop upon entry to that cell. In particular the gateway is the final retained high event for both. One may use the executed high event clock as endpoint in the cell case; it uniquely determines the entry state. Terminal classes for this accounting forest are physical classes, not the virtual cell or prime unions. The sum of true physical merge variance equals their total within-class variance.

For D=floor((log Y)^(1/4)) from section3 and d=floor(D/log^(1/2+epsilon)(2D)), the preceding harmonic near estimate bounds near proxy by o(X), even after arbitrary restriction to these tags. Therefore on hypothetical no-twin windows
    S_c(q<Q) + 2 P_phys,far >= N-o(X),
where root injections at cell stops are absorbed in o(X), Q=B^(1-1/sqrt(log Y)), and P_phys,far refers to the specified forest restricted to prime stops and q>=Q cell entries. In particular all prime stops are treated physically, and the additional unresolved term is the cell-entry population below Q. The inequality does NOT imply that P_phys,far is small or that low-gateway cell stops are rare. It is a different remaining problem from the previous intermediate-prime-band term. The new rule should not be described as proving an overall improvement in anti-concentration.

The earlier idea of replacing the low-multiple barrier with the next wheel-admissible horizon is invalid: a low step can jump over a horizon at which no low prime divides either neighbor. Example p=5, C=16, admissible horizon 18 (neighbors 17,19), and step p-1=4 reaches20. The proof above uses actual multiple barriers, never assumes such a wheel-admissible horizon is uncrossable.

## 5. Finite audit

Saved research/min_barrier_cell_inverse_audit.mjs and results JSON at defd5cda73bbe10e43411d455684a3bae512540c (exact remote readback of both files). Executed X=256,1024,4096,16384,65536,262144. Finite Y=11 or13 (L=210 or2310), inverse numerator A=max(2,floor(B/4))*B instead of B^2, cell cap T=max(floor(L/4)+1,ceil(X/256)). Compare full inverse prime-only rule and cell+inverse rule. This finite T is deliberately much smaller than the analytic T=X/log^2Y, and in small windows L is not o(T). Verify actual cutoffs and prime clocks (literal GCD for X<=1024), root conservation, each low step stays inside its cell, low budget per cell, all-at-entry mass test, crossing identities, <=2 projected crossing keys per label per cell, source-weighted height and capped mass moment inequalities, prime stop reciprocal sum. The capped diagnostic uses a=8, and near-top diagnostic q>=ceil(B/2), not the asymptotic Q. No spatial variance computed in this audit.

At X262144,B1355,A457990,T1024:
- Y11, both rules have S629 all prime stops, no cell stops (max admission715), R107069391, low cost10503384. One prime stop p743 with U8,H3774, all629 in one clock class. All130443 unstopped roots twin terminals.
- Y13, full inverse alone: S629, no cell stops by definition, max admission1274, R107069391, low cost12572668.
- Y13, combined: S16921, all cell stops (15 cells), R95205719, low cost11031812, rootsCell8663, crossing tags8258. 132 projected crossing groups, U1060 for a8, weighted H6441232, I1.5256901481. Of 2149 tags with gateway q>=ceil(B/2), 2100 in classes >8; U225 over34 projected groups. All114151 unstopped tags twin terminals.
The many root-injection stops in this finite combined run are consistent with L/T>1; they are not evidence of the asymptotic L=o(T) bound. The new cell cap can increase the number of stopped roots relative to prime-only full inverse; it is a proof-budget device, not a numerical optimization claim. At X256 some prime-only runs have five non-twin natural terminals with original cutoff. All retained.

## 6. Next obstruction

The full inverse cap is now compatible with a growing transparent LOW cutoff, without a separate intermediate band of prime stops; its low cost is controlled by cell admissions. The unresolved cell-stop entry mass comes from labels below Q, and the physical far first-coalescence bound remains open. The boundary gateway arithmetic may permit a sharper source-weighted estimate, because each q gives at most two possible projected keys at a fixed boundary. A further possible route is to use boundary-specific admission thresholds or count physical gateway classes at such boundaries before cell stops. No proof of the global deficit, no main edit, no new branch, no Lean compilation.
