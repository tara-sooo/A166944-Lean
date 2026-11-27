# Negative MIN: exact capped cheap survival and the remaining long-time moments

## Verified checkpoint (2026-11-27, Issue #10)

Core source: `research/lean/NegativeMINCore.lean` at
[8518b018](https://github.com/tara-sooo/A166944-Lean/blob/8518b018e598ef6c58d18cd741634e3df560d648/research/lean/NegativeMINCore.lean),
blob `479ed9b770e7ee0cc30c4034a6ec821038778923`.
Pinned Lean v4.33.1 [CI run 46016806448](https://github.com/tara-sooo/A166944-Lean/actions/runs/46016806448) succeeded.
146 theorem declarations in the complete file (not 146 new results); prior checkpoint a9f0cc2 had 54. No sorry/admit. The audited theorem dependencies are subsets of propext, Classical.choice, Quot.sound.
Only narrow cached Lean core checking; no Mathlib fetch or full repository build. The uncompiled real-scale Mathlib adapter remains separate.

### 1. Fixed-cohort first contact

For actual canonical roots in the same synchronized window, Contact requires both births and equality of the complete physical state at the same clock. Once contact occurs it persists. The count of higher-priority (smaller A) roots in the full selected fiber is nondecreasing, including new births. Retain the initial prefix for which this inclusive rank is <= M. This is a real irreversible FullCapped death-age policy.

For S a fixed selected set, let C(A,B) be the number of observation ticks with Contact, for A<B. The firstContactOffset is the count of noncontact ticks in [0,T); contacts that predate observation have offset 0, and no contact has offset T. Lean proves C=T-offset. Each selected lost tick has >=M distinct smaller contacting selected roots. Summing over time and roots charges each unordered pair exactly once:
```
M (|S| T - liveTicks) <= sum_{A<B in S} C(A,B).
```
Verified declarations: contact_mono, rankDeath_fullCapped, firstContact_spec, contactTicks_add_offset, rankDeath_integrated_loss. Initial green [8a13c95](https://github.com/tara-sooo/A166944-Lean/actions/runs/46015069237).

### 2. Exact budget-priority selection

Let inc be a nonnegative integer charge per actual tick depending only on State. Define pathCost by additive prefix sum from birth; after contact both roots incur the same future increment. Lexicographic (cost,A) priority is therefore preserved after contact. The full contacting rank is nondecreasing, and cheapness (cost <= b) holds on an initial interval. Define cheapRankDeath by the initial prefix satisfying both predicates, NOT a policy that reactivates previously deleted roots.

At every physical tick, including before observation, its live fiber is exactly the lowest-cost M cheap roots (all if fewer); count = min(M, m), where m counts all actual trajectories with prefix cost <= b in that fiber, independently of the policy. The proof uses a distinct-root list, order totality, maximal selected rank and minimal rejected rank. This also proves FullCapped. For ANY FullCapped death-age policy whose per-root completed prefix costs (including killing tick) are <= b, cheapRankDeath has at least as much integrated live time (cheapRankDeath_optimal). Its own completed prefix cost is <= b+delta, delta a uniform bound on inc. This distinction matters for a killing tick that crosses the budget.

Verified: rankClip_length, contact_priority_mono, cheapRankDeath_exact, cheapRankDeath_fullCapped, cheapRankDeath_budget, cheapRankDeath_optimal. Green milestone [89ecb17](https://github.com/tara-sooo/A166944-Lean/actions/runs/46015448003), final run above.

Exact integration: cheapMasses is the list of uncapped cheap fiber sizes over all u in [0,T), window IDs J and physical centers x visited by full trajectories. No repeated keys. Let S=sum m, Q=sum m^2. The checked identity is
```
liveTicks (cheapRankDeath inc R T M b) R T = sum min(M,m).
```
With K>=M, K>0, 2Q<=KS, the checked threshold lower bound is MS<=2K liveTicks. It follows from MKm<=K^2 min(M,m)+Mm^2. This is an unconditional finite inequality, conditional only on the displayed numerical moment hypothesis, not a proof of the asymptotic hypothesis.

An additional paper-level sharper inequality, not yet Lean-formalized, follows from min(M,m)>=Mm/(M-1+m) for integer m>=1, M>=1, and Cauchy-Schwarz:
```
liveTicks >= M S^2 / ((M-1)S+Q)       (S>0).
```
Because cheapness is an initial interval for each full actual path, if ell_b(A) is its observation length within budget, the pair contribution to Q is
```
Q = S + 2 sum_{A<B,same window} max(0,min(ell_b(A),ell_b(B))-tau(A,B)).
```
Here tau is the clipped firstContactOffset. Thus the pair moment can be studied through first contacts without counting all histories at each tick; this identity is a mathematical deduction, not a checked declaration.

### 3. Exact weighted cost and conditional twin extraction

For integer weights wN,wQ, weightedInc is wN times the narrow indicator z<p<Y0 plus wQ times 2q(x) on Y0<=p<Y1 with p^3<=(2q(x))^5 (the original d=3/5 roughness threshold). The charge is zero on idle ticks for Y0>0. qmin<=p for nonzero winner p. Therefore inc<=delta=wN+wQ(2Y1).

Lean verifies weightedCost_sum: sum of completed prefix costs equals wN*narrowCount+wQ*mediumCharge exactly, with original prefixAge. cheapRankDeath_weightedBudget bounds this by N(b+delta), where N=|roots R|.

The original ScaledLiveEstimate on this constructed policy is NOT proved here. Conditional on that exact estimate and 2Q<=KS, K>=M, K>0, 6<=T, 0<Y0, Lean proves twin_lower_of_cheap_moments:
```
D M S - 2 K (N(b+delta)+err) <= 2 K D B0 M T twinCount.
```
The subtraction is truncated Nat subtraction. A strictly positive left side yields a twin center, above any B with B+3T+6<R (twin_above_of_cheap_moments). There is no assumed infinite supply of twin centers, no axiom or redefinition of the target.

### 4. Actual arithmetic constraints on the unresolved histories

Verified winner_source_pin, repeat_pin_gap, actual_repeat_gap, repeat_relay_gain, tick_wall, evolve_wall_gain, repeat_forces_escape, winner_le_age.

For repeated winner p>=5 at pre-tick ages i<j on the same even canonical root, x_i-x_j>=2(p-1) and x_{i+1}-x_j>=p-1. Both source centers are even and congruent to +/-1 mod p; after the first tick the center decreases by p-1. If every firing in a contiguous segment divides an even positive integer Q0, the quotient floor(x/Q0) is constant along that segment and the gain is <Q0. Thus when Q0<=p-1 at least one intervening nonzero winner does NOT divide Q0. The p>=5 restriction is essential to the repeat argument. Also a winner at pre-age k is <=2(k+1)+7, using the original birth-height bound. These are actual full-rule theorems; no hypothetical capped or restricted dynamics replaced the orbit.

Provenance: repeat-spacing and primorial-cell ideas were developed in sixth-branch papers, including [record-return forests](https://github.com/tara-sooo/A166944-Lean/commit/f8b242186833d37c9b728dbd99819c560c3461b1) and [prime insertion and regular prefix protection](https://github.com/tara-sooo/A166944-Lean/commit/26ad4eab14f0ab0862c9d0313a26a625488a4f44). The Lean escape result composes these arithmetic restrictions on the original dynamics. It does NOT justify charging overlapping repeat intervals for different primes as disjoint, nor establish small total repeat cost.

### 5. Finite independent event-driven audit

Source [68bfa3a](https://github.com/tara-sooo/A166944-Lean/blob/68bfa3a4223a831ab9044f04ae11ecad2d038aba/research/lean/negative_min_rank_contact_audit.mjs), blob bfa1a43dcb7b5a3a2510279ddc169c16e152bc15. Independent full actual trajectories and greedy birth/merge/budget deletion. Executed ECMAScript on R=12000,48000,192000, total 42003 roots, 8100234 counted checks; remote source fetched and same audit reexecuted. Reproduction: node research/lean/negative_min_rank_contact_audit.mjs 12000 48000 192000. Proxy finite charge is 8 for 5<p<47, 2q for 47<=p<T/2 and 4q^2>=p, otherwise zero. Not the asymptotic d=3/5 scaling. Caps 4,16,64; budgets 32,128,256. R=192000, M=16, b=128: final-cheap cohort 0.36598856 of roots, its integrated capped survival 0.34764856; full prefix-cheap S/(NT)=0.44945647, dynamic clipped survival 0.42665501, Cauchy lower bound 0.27712633. Values include actual twin centers. No extrapolation. Audit verified first-contact identity, exact fiber sizes after every event, irreversible deaths, cost overshoot and moment lower bound.

### 6. Next mathematical target, not a replacement for the original criterion

Use original R-dependent horizon, cap, narrow/medium weights and normalized mean budget with L=log R. Set b=o(L^(-1/4)) in normalized cost units, with overshoot negligible (integer scaling/rounding and real asymptotic bridge still uncompiled). In terms of s=S/(NT), q=Q/(NT), the sufficient finite-moment route is
```
s >= c/(log L)^2,     q <= L^(2.35-epsilon)
```
for some constants c>0, epsilon>0 along unbounded slabs. With M~L^2.1, take K=max(M,ceil(2Q/S)) (and at least 1). Then the verified threshold inequality gives eta>=Ms/(2K) >> L^(-1/4). Combine with original WeightedEstimate and negligible mean cost to obtain the original quantitative twin count >> R/L^2.35. Neither s nor q estimate is proved. This is a sufficient subroute, not a weakened conjecture or a claim that these estimates are necessary.

Conversely, under finite twins AND the original weighted analytic upper bound, the exact budget policy has eta=o(L^(-1/4)). If the displayed s lower bound holds, the sharper Cauchy inequality forces q/(L^2.35/(log L)^4) -> infinity along such slabs. So this subroute gives a precise obstruction: excessive long-time collisions or disappearance of cheap paths, not a problem of selecting a better uniform-budget policy. This deduction uses the paper-level Cauchy formula and the still-unverified analytic estimate.

The sixth branch's selected regular initial seeds establish only subpolynomial-age protection. They do not establish either displayed long-time estimate. The repeat escape condition might support a decomposition of cost by prime scales, but overlapping repeat intervals must be treated separately. Prime insertion signed defect control and large-scale transfers remain open.

Possible extension (paper-level, not implemented): budgets b_A per root, order by C_A(n)-b_A, then A; use signed priority to avoid Nat truncation. After contact the order persists, so clipping all individually cheap trajectories is possible without reactivation by the same rank argument. Given any actual admissible policy choose b_A equal to its completed prefix cost; its live trajectories are individually cheap at all live ticks. The resulting policy retains at least its integrated time and costs at most sum b_A+N delta. This avoids mistaking the uniform-budget restriction for a necessary consequence of the original mean-cost target. It does not bound the required moments or prove CheapSurvival.

Open: CheapSurvival at T'=R^(1/2-o(1)); original WeightedEstimate formalization and independent mathematical review; real-scale Mathlib bridge and exact quantitative conclusion. No full twin-prime proof. Issue #10 remains open.
