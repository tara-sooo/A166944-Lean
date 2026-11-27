# Negative MIN: exact aggregate-budget and net-value optimization; two-source rough sieve

Continuation of 5cfd69c, Issue #10. 2026-11-27 JST (continued through the date boundary). The original deterministic MIN and window/cost definitions are unchanged. No proof of twin infinitude.

## 1. Individualized budget, no overshoot

Use the original pre-tick age i and completed prefix cost C_A(i), including the event causing deletion. At a live age i require C_A(i+1)<=b_A, not C_A(i)<=b_A. Within a physical fiber prioritize lexicographically (C_A(i+1)-b_A,A). Once two roots contact, both future cost increments are identical, so the order is preserved. For a finite root set encode signed score by the nonnegative offset B-b_A, B>=max b_A. Contact rank is nondecreasing; the budget test is antitone. Hence retain an initial prefix, never reactivate, and at every physical tick (including pre-observation) realize min(M,m) for the full set of roots which can pay the next tick.

If d is any FullCapped policy, assign b_A=C_A(prefixAge(d,A)), B=sum b_A. The new reserve policy has at least the original live time: every root alive in d can pay its next tick. Its cost per root is <=b_A, even for the killing tick, because at the last live age the next tick was reserved. Thus totalExpense is no greater. The exact theorem payDeath_dominates proves this, including FullCapped; arbitrary nonnegative integer state-dependent charges. No uniform budget or bounded one-step overshoot hypothesis. Verified 2492105, run 46018173618.

For S=sum uncapped affordable fiber sizes and Q=sum squared sizes, min(M,m)>=Mm/(M-1+m) for m>=1, M>=1. Cauchy yields M S^2<=liveTicks*((M-1)S+Q). Kernel proof clip_sharp uses the symmetric integer cross inequality 2Mab<=min(M,a)*((M-1)b+b^2)+min(M,b)*((M-1)a+a^2), followed by finite double sums. No division at S=0. payDeath_sharp_moment connects the exact reserve policy. Verified 0a57cfb, run 46018735277.

## 2. Exact net optimization eliminates budget choice

For an arbitrary nonnegative state charge inc and integer observation reward D, let F_A(i)=D*min(T,max(0,i-observeAge(A)))-C_A(i). All costs from birth are included. At physical tick v in a window, w_v=D*1_observed-inc(v); w_v is common to all roots at v. Define P_A(i)=max_{j<=i}F_A(j), d_A(i)=P_A(i)-F_A(i), g_A(i)=P_A(i+1)-P_A(i). Then
    d_A(i+1)=max(0,d_A(i)-w_v),
    g_A(i)=max(0,w_v-d_A(i)),
    0<=g_A(i)<=D.
In particular d_A=0 iff F_A(i)>=F_A(j) for every preceding j. Equivalently every past suffix cost is at most its observation reward. Nonproductive time can repay earlier cost; the predicate is not a uniform bound on full prefix cost. Before observation all g=0.

At every node of the actual coalescing forest, provisionally keep M roots with smallest debt. Future debt maps are common and nondecreasing after contact. A fixed root-ID tie rule alone could change rank after two unequal debts collapse to equality, so use reverse chronological debt history, then ID. Encode full-root debt digits with variable radix base_t=1+sum_A d_A(t), place_t=product of earlier bases, code_t=d_A(t)*place_t+code_(t-1) (global integer clock from epoch 3-R). This puts the current debt first and retains the previous order as tie-break. Full-root contact rank is monotone. The initial prefix with rank<=M defines debtDeath; full physical fiber equals rankClip of all born roots, including pre-observation. Its cap is kernel-checked.

The provisional greedy policy need not maximize net reward if paid all the way to its death: some earlier debt is never recovered. Instead truncate every provisional root at an age attaining the maximum prefix net score before its provisional death (bestPrefix). This only shortens prefixes, thus preserves FullCapped. The resulting net score equals the sum of g_A over provisional live ticks by the running-maximum telescope, including prebirth charge accounting and zero pre-observation profit. This gives optimalNetDeath.

For any other admissible policy, its net score is at most its sum of full-trajectory record increments. On each physical fiber, g_A is nonincreasing with debt priority. Therefore the top M selected by the provisional rank maximizes that sum. Proof uses threshold counts: for integer t=0,...,D-1 the predicate g_A>t is downward closed in priority, so clipping commutes with filtering and the threshold cardinality is exactly min(M, full threshold count). Summing over t and all physical observation bins proves global optimality. The net optimum is exactly
    V_M = sum_{u,J,x} sum_{t=0}^{D-1} min(M, #{A in full fiber(J,x,u):g_A>t}).
There is no remaining selection variable in the right side. For unit reward this is just capped debt-zero time at uncharged ticks. Unlike a uniformly cheap-cohort condition, this optimizes the exact signed net objective over ALL irreversible FullCapped policies, even ones with large aggregate cost. The provisional debt rank and retrospective peak truncation are constructive (potentially very inefficient mixed-radix arithmetic); the separate forest DP is efficient enough for finite controls.

The verified 3b182c9, run 46020345095, includes policyNet_eq = D*liveTicks-totalExpense, debtDeath_fiber_profit_max, optimalNetDeath_fullCapped, optimalNetDeath_optimal, twin_above_of_optimal_net. Exact threshold formula and source-form additions are in the next checked checkpoint, recorded in Issue #10. The arithmetic sieve below is paper-level, not a Lean theorem.

## 3. New criterion for twin extraction

Let L=log R; preserve original T=horizon(R), M~L^2.1, cost c=prefixMean, s=L^(-1/4). The original OPEN WeightedEstimate is eta<=twinMass+C*c+err, err=o(s). For a price lambda_R with lambda_R>=C eventually,
    max_admissible (eta-lambda_R*c) <= twinMass+err.
Thus if the exact optimum is >=c0*s on unbounded slabs (c0>0), twinCount >> R/L^2.35. There is no need to prove cheapness and lifetime separately. Since C is unknown, suffice lambda_R->infty or a lower bound on unbounded slabs for every fixed lambda>0 (constant may depend on lambda). For the original CheapSurvival obligation itself, lambda_R*s->infty would additionally ensure c<=1/lambda_R=o(s) from positive net (eta<=1); this stronger price is not required for direct extraction.

To connect the original real weights to integer D use wN=ceil(D lambda_R T exp(-L^.6)/(k+1)), wQ=ceil(D lambda_R). Divide policyNet by DNT. Round-up changes net by at most (narrowCount+mediumCharge)/(DNT)=O(1/D): every firing p>=3 consumes p-1 gain, q<=p, so 2q<=3(p-1), and total gain per prefix <=3T+6. This is a paper-level bridge, D can grow e.g. floor(L^2). The previous real-scale Mathlib adapter is still uncompiled. The original WeightedEstimate remains an explicit hypothesis, not obtained from optimizing.

## 4. Four-form upper sieve for short rough repeats (same label)

Use actual synchronized prefixes, including pre-observation and killing ticks; each live pre-tick physical fiber has <=M roots, and for each center only O(1) windows can visit it. Write q(x)=min(lpf(x-1),lpf(x+1)), label p is rough when q(x)>=p^(3/5)/2, exactly p^3<=(2q)^5. Let P=exp(L^gamma), P<=p<=Y1=exp(L^.85) (or p<=3T+7 for this count), K<=L^b, fixed gamma,b>0. For two rough firings of the same p>=5, x>y, pins x=p u+e, y=p(u-2k)+f, e,f in {-1,1}, k>=1. This uses source evenness and the earlier repeat-gap theorem. Consider pairs with 1<=k<=K, not all repeats. The four forms
    u, u-2k, pu+2e, p(u-2k)+2f
have no prime divisor below p^(3/5)/2 other than possibly p (which is beyond the sieve cutoff). For ell>=7 outside
    Delta=2pk(pk-f)(pk+e)(pk+e-f)
there are exactly four forbidden residues modulo ell. Delta!=0 and log|Delta|=O(L) uniformly. The nonzero factors follow p>=5,k>=1 and e,f=+-1.

Apply the same Selberg quadratic diagonalization as 66f63e3 section 2, now local density g(ell)=4/ell on good primes ell<=D_s=p^.01. For squarefree d<=D_s weights |lambda_d|<=d, error O(D_s^6); G(D_s) lower bound from Euler product on good ell<=D_s^eta for small fixed eta. Under product measure inclusion probability 4/ell, expected log d<=O(eta log D_s), so at least half mass lies d<=D_s. Omitted primes dividing Delta remove at most O((log L)^4) of the Euler product: split at L, Mertens for ell<=L, and sum of 1/ell over ell>L dividing Delta <= log|Delta|/(L log L)=O(1/log L). Thus G>=c(log p)^4/(log L)^4. Interval of u has length O(R/p) and scale >=R^(1/2-o(1)); D_s^6 negligible. For fixed p,k,e,f:
    #possible x << (R/p)(log L)^4/(log p)^4.
The same argument works if an additional local prime is omitted. No independence of histories is invoked.

At the later source y, its clock is a unique class modulo 2p, determined by f. All clocks for actual slab roots that can visit y lie in an interval of length O(T) by birth and gain geometry. Hence O(1+T/p) possible clocks, O(M) tokens per clock across O(1) windows. Charge 2q(y)<=2p, so contribution per tuple <=O(MT) since p<=3T+7. Union bound over candidate keys counts a later repeat even if several earlier events qualify, without treating intervals as disjoint. Divide by NT and sum p,k:
    normalized short rough-repeat charge
      << M K (log L)^4 sum_{p>=P} 1/(p(log p)^4)
      << M K (log L)^4 / (log P)^4.
Chebyshev/partial summation gives the last bound. At gamma=.65,b=.1,M~L^2.1 this is O(L^(-.4)(log L)^4)=o(L^(-.25)). Thus one part of the high-medium repeated rough charge is negligible for EVERY capped prefix policy, not just light terminal fibers. Repeats whose preceding rough occurrence has k>K, and events with only one rough source, are not bounded by this argument. Large first-use mass remains.

## 5. Four-form distinct-label short relay sieve

Let p,r distinct primes >=P, later r<=Y1, earlier p<=3T+7, both sources rough. Total intermediate gain E between the first jump's arrival and second source is even and nonnegative. Let D0=p-1+E; y=x-D0. For E<=B=L^b<P-1, equality p=r is impossible by repeat relay gain. Fix p,r,e,f,E: x=e mod p, x-D0=f mod r, one CRT class mod pr. Since r<=Y1 and p<=3T+7, pr<=R^(1/2+o(1)), interval progression length scale R/(pr)>=R^(1/2-o(1)). For ell>=7 not dividing 2pr D0(D0-2)(D0+2), the four forms (x-e)/p, x+e, (y-f)/r, y+f forbid four distinct residues of the progression parameter, corresponding to x mod ell=+-1,D0+-1. D0>=4, all discriminant factors nonzero, log|Delta|=O(L). Both q thresholds exceed P^(3/5)/2. Apply section 4 with D_s=P^.01, error negligible; count << R/(pr)*(log L)^4/(log P)^4.

Later clock key count O(1+T/r), charge <=2r, inherited mass <=O(M), total per tuple <=O(MT). Summing E and labels (harmonic prime sums O(log L) each):
    normalized later charge of distinct rough short relays
      << M (B+1)(log L)^6/(log P)^4.
At gamma=.65,b=.1, this is again o(L^(-.25)). This includes relays entirely made of small labels <=z=sqrt(log L), since primorial wall gain Q_z=exp(O(z))=L^o(1)<B. No assertion that all relay gains are small. The result uses p,r sub-square-root product, so differs from the near-square-root modular-hyperbola method; it also needs BOTH rough sources.

## 6. Clock sieve for imbalanced short relays, without first-source roughness

Now p,r in [P,Y1], distinct, E<=B, with only later source q(y) used (no roughness of earlier source needed). Firing clock gap Delta_t satisfies 1<=Delta_t<=3E+2q(y): each completed intermediate stationary segment wait <=3 gain, and final wait <=2q(y). This is the same actual first-event bound as the Lean core and earlier arithmetic ledger. For fixed x,y,p,r,e,f,E and a specified gap d, the two clock pins are CRT modulo 2pr, or incompatible. There are O(1+T/(pr)) first clocks in the O(T) range, and O(B+q(y)) choices of gap. Since p,r<=Y1=R^o(1), pr=o(T), the weighted count per tuple (charge 2q and live mass <=O(M) at later clock) is
    << M T q(y)(B+q(y))/(pr).
Count spatial keys with CRT alone O(R/(pr)); suppose q(y)<=p L^(-c), B<=p L^(-c), and use q(y)<=r. Then the factor q(y)(B+q(y))/(pr)<=2L^(-c). Summing p,r and E gives
    normalized charge << M (B+1)L^(-c)(log L)^2.
Choose c=3,b=.1,M~L^2.1: O(L^(-.8)(log L)^2)=o(L^(-.25)). No q-roughness condition or extra sieve necessary. This includes some previously nonrough predecessor events. Still open: first high-band event, long spatial relay, balanced short relay with only later rough source. Neither these local small terms nor the net optimization itself proves positive large-scale record profit.

## 7. Reproducible audits

A. research/lean/negative_min_net_value_forest_audit.mjs @ b6f517039ab23f4c9f53a02bf2ffc91b6f05833c blob 3a2ddd055182f533daea2d834d5a914abea553b4. Independent dynamic programming on actual literal gcd-tick merging forest. At node, conditional optimal-value function for k retained tokens is concave. Its incoming marginal slots have debt=max(0,-prior slope) plus birth zero slots. Take M smallest, add common signed tick reward, sum positive marginal slopes. Backward reconstruction selects predecessor maxima or extra required slots; forward token identity check proves feasible irreversible flow. Also compares top-M debt multiset with untruncated profiles. Exhaustive brute force on 1200 synthetic forests, and actual R=12000,48000 (10002 roots, 616462 physical nodes, 3462135 root-ticks, 137051 events). 19748686 counted checks. Fixed finite proxy charge 8 for 5<p<47, 2q for 47<=p<T/2 with 4q^2>=p, otherwise zero; reward1, prices0/1/4/16, caps1/4/16/64. R48000 M16 price16: net .1848958396, life .2824836412, normalized charge .0060992375953. Not the growing-scale weights. Includes existing twins.

B. research/lean/negative_min_rough_repeat_sieve_audit.mjs @ 37c4dbe256e6a936c06339534e0f726c201469b1 blob 7c32bffb7f48466434a85497b682e395d1d4f3ed. Actual event calendar R12000,48000,192000, 42003 roots, 775263 events, 57637 rough repeat pairs; 1212300 counted modular checks. p in [11,T], original p^3<=(2q)^5. Root-ID capped prefix at each event, previous rough source on same root. At R192000 cap16, normalized total .8289119997, short k<=4 .0237614550, short fraction .0286658355. First-use dominates this finite control; no extrapolation.

C. research/lean/negative_min_two_high_sieve_audit.mjs @ 1315b9d8f177271fb7d9b6f8d26b4dfacc080859 blob 7795dab24af3d29c69f11f7316767de21fd16430. Same slabs 42003 roots, 225549 successive high-event pairs, 181210 short E<=8, 171534 both rough; 4376912 counted checks including actual relay time, modular roots, clock CRT spacing and cap charge. P=11,B=8, finite imbalance q*4<=p and B*4<=p; not asymptotic parameters. At R192000 cap16 charge 17309550, short both 11663020, short imbalanced 656850 (classes may overlap). All scripts executed in ECMAScript, fetched from pinned remote commits and rerun with matching outputs. Reproduce with node. No claim of external analytic review.

## 8. Next target

The exact signed-net optimum gives a clean target: on unbounded original slabs show capped full-root record increments of lambda-priced reward have mass >>L^(-1/4). One can now study local suffix cost excess / reflected debt, including busy periods that repay narrow and rough-medium charges. Four-form and clock sieves dispose of specific pair patterns uniformly in cap; use remaining first-event supply, long relays and mixed-roughness balanced transitions to estimate record-debt recovery. Different prime repeat intervals cannot be charged as disjoint. Original WeightedEstimate, analytic growing-scale lower bound and real-scale Mathlib bridge remain open. No proof of CheapSurvival or twins, no weakened target.
