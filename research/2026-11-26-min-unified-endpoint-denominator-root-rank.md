# Endpoint-frozen denominator and ideal root-rank lifetime kernel

2026-11-26 JST. Continues [ed0661721670](https://github.com/tara-sooo/A166944-Lean/blob/ed066172167054ad66a143186fd738069e9e72c4/research/2026-11-26-min-unified-entropy-age-continuous-lifetime-cut.md), [6bdfbedd6573](https://github.com/tara-sooo/A166944-Lean/blob/6bdfbedd6573b9d6ab4e7c9c98c5e79ec872fcf0/research/2026-11-26-min-unified-lifetime-layer-founder-budget.md), [96656afaa7c2](https://github.com/tara-sooo/A166944-Lean/blob/96656afaa7c25e44cfc8278d663c053b356e7129/research/2026-11-26-min-unified-historical-founder-forest.md). New: actual merge entropy (including retirements) controls the change in normalized pair denominator when frozen at the end of a short gain slab; a grid-free endpoint-snapshot sufficient test with only polylogarithmically many layers, fixed pair intervals and no within-slab cohort tracking. Under the finite-twin contradiction hypothesis, further replace each endpoint denominator and terminal interval by a root-order-statistic kernel with o(NT) error. An additional birth-root-rank harmonic envelope uses no endpoint snapshots. These are reductions, not a constant-margin estimate or proof of twin primes. No Lean compilation.

## 1. Frozen ensemble and parameters

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Actual original prime-root MIN prefixes, C0_i=2M_i-2 for prime M_i in [X,2X), total completed gain <H, wait <=2p<=3(p-1), actual terminal horizon F_i. No extension of stopped tags. Under finitely many twins, eventually every tag is gain-stopped, hence
    C0_i+T <= F_i < C0_i+T+B.                         (1)
We use (1) ONLY in sections 5-6. The prior certificate under this hypothesis is NT/2-o(NT)<=B_old+(3+o(1))(D_l,old+D_h,old). All exact old masks through ed06617 preserved, including original first-meeting age, final weighted/physical maturity, bad tags, original source eligibility and induced both-small payment. Original grids P_j averaged with their unchanged common denominator, P_max<=B^.25, c_a=3(1+2/u^.25), b0=ceil(b_min)=ceil(H/[512 L0 B u ell³ sqrt(tau)]). Positive backward source full slot b>=b0, per ordered pair clock <=c_a P/b, joint row/column caps c_a P per atom. Forward unchanged. All actual original counts, pair meetings and charge weights remain frozen.

Use eta=ell^(-1/4), h=eta H, L=floor(B^(1-ell^(-1/2)/4)), and previous tag eligibility E_i=[M_i^++h,F_i-h] with empty intervals for tags failing old tagwise domain conditions. M_i^+=max(J_i,A_i^+) is the final weighted and first physical maturity from 78700a0. For each ordered distinct pair with actual first meeting V at projected horizon C_V, retain a STATIC admissibility test (at least one original incoming branch >=L, plus any chosen already established fixed pair tests). Define I_ij=E_i intersect E_j intersect [C_V+a_ij,infinity), with a_ij=eta H log(R_V/r_ij)/log N from ed06617; can intersect the old uniform age too. Failed static test or no meeting gives empty interval. Use half-integer endpoints as in ed06617 to preserve all integer boundary tests; changes lengths O(1) and lower age remains nonnegative eventually. We deliberately omit the induced both-small gate in the relaxed endpoint test: original residual is still a subset, and on the SAME original source domain that relaxed omission costs at most O(eta NT) by the potential lemma of 6bdfbed. No old exact mask undone.

Set D=max(1,floor(eta H/log(2+N))), xi=sqrt(eta). For sufficiently large X, xi<1/4, D+2<h and B+D+2<h. Partition projected coordinates into disjoint slabs [zD,(z+1)D), integer z. At endpoint e=(z+1)D use the crossing cohorts at e- (left limit; completed slot [C,J) contains e- iff C<e<=J). A tag contributes to this endpoint iff it actually crosses e-. This handles tags terminating exactly at e and excludes roots starting at e. All slab and threshold choices made for this mathematical construction; the original source ensemble is unchanged.

## 2. Actual entropy budget, independent of gain stopping

At each actual true vertex V with population n_V, actual incoming branch counts a_j (including singleton root injections), retiring e_V, use Phi(n)=n log n with Phi(0)=0. Define
    G_V=Phi(n_V)-sum_j Phi(a_j)>=0.
Exact edge cancellation over the original finite true graph gives
    sum_V G_V = sum_V [Phi(n_V)-Phi(n_V-e_V)]
              <= N(log N+1).                         (2)
Root injection contributes Phi(1)=0, every tag retires once; derivative on n>=1 is <=1+log N, and Phi(1)-Phi(0)=0. For any subset of incoming tags the merge entropy is at most G_V: the function Phi(sum a_j)-sum Phi(a_j) is nondecreasing in each a_j (partial derivative log(sum a_j/a_j)>=0 for positive a_j, extend continuously). This is an actual-flow entropy, distinct from the historical log-growth potential of ed06617.

Fix one slab [l,e), restrict the original histories to tags that really cross e-. On this restricted flow, up to e- there are no retirements; births can occur within the slab. Along any such surviving tag, the induced group size is nondecreasing. If a source cohort G at K in [l,e) has full b and n members surviving to e-, these n all belong to ONE endpoint cohort Q of full size q. For n>0,
    log(q/n)=sum of log-growth increments of this end-survivor group from K to e-.
At each actual merge V in the slab, the induced growth increment summed over its active surviving incoming tags is its induced merge entropy <=G_V. Integrate the identity for all surviving tags over all K in the slab. Each increment can be counted for at most D gain units before its event. Hence
    integral_slab sum_G n log(q/n) dK <= D sum_(V:C_V in slab) G_V.  (3)
At n=0 term zero. The sum may use only original positive b>=b0 slots or all crossing cohorts. The grid version with P sum over K in slab is bounded by (D+P) sum G_V because a tag can have at most D/P+1 grid atoms before a given event in the slab. At a projected horizon multiple actual meetings are ordered by true tick; at a left boundary K count crossing slots after their actual departure, no event double-counted between slabs. Unary movement does not spend entropy.

Similarly the sum of b-n at K counts tags that are actually crossing K but stop before e-. Each retiring tag can appear in at most its own terminal slab for this purpose, so
    integral sum_G(b-n) <= ND,
    P sum_{K,G}(b-n) <= N(D+P).                       (4)
No uniform lower bound on b along a continuing actual history is needed.

## 3. Endpoint denominator approximation and gate

At any old positive backward source (K,G), b>=b0, every pair counted by its exact residual or the relaxed fixed intervals has both members alive at e- because E_i implies F_i>=K+h and D<h (rounding harmless). Write A for its relaxed ordered numerator, A<=n². Its normalized value is A/b. On the same set of pairs, freeze the denominator to max(b0,q), where q is the endpoint cohort mass. Since b>=b0, n<=b,q, when q>=b0 and q>=b the positive difference is bounded by
    A/b - A/q <= n(1-n/q) <= n log(q/n).
If q<b or max(b0,q)<=b the difference is nonpositive. Conversely the excess of the frozen value over A/b is <=b-n, since max(b0,q)>=n. Thus on the same domains the absolute integrated or grid error is bounded by (3)+(4).

Use endpoint gate q>=(1-xi)b0. If q<(1-xi)b0 while b>=b0, then n<=q, b-n>=xi b, and A/b<=b<=(b-n)/xi. All such original source clock can be paid or upper-bounded by (4)/xi. This is a global bound, not a pointwise assertion that q>=b. Notice that using q>=b0 without a slack gate would not give this retirement estimate near the threshold.

Define the new endpoint-only scalar
    U_end = sum_slabs sum_(Q at e-, q>= (1-xi)b0)
                 [ sum_(ordered distinct i,j in Q) |I_ij intersect [l,e)| ]
                    / max(b0,q).                    (5)
This is an explicit finite sum of pair interval lengths. If a pair is counted at K in I_ij and both members cross e-, both actually crossed K and had already met, because its birth lower endpoint is >=C_V and each trajectory covers every projected coordinate from origin to terminal by completed jumps. Their crossing slot at K is the same. For original positive sources, their surviving pairs thus map uniquely into Q at e-, with exact first meeting unchanged. Formula (5) may include pairs in slots at K not satisfying original positive-source or b>=b0 conditions, so it is an upper envelope after the small error, NOT an asymptotically equal replacement of the entire old U_cont. Its useful feature is that interior cohort identities and varying denominators no longer appear. Only endpoint cohorts, original first births and pair interval endpoints remain.

For grid P the same finite sum using P times the number of grid multiples in each interval replaces lengths. Each interval quadrature error <=P; sum over pairs in Q divided by max(b0,q) <=q. Each tag occurs in at most H/D+2 endpoint snapshots, so the total error of this grid sum relative to (5) is <=NP(H/D+2). There are O(X/D)=O(u^.25 log N/eta) slabs, polynomial in logarithms, and actual total snapshot membership O(N(H/D+2)). Combining (2)-(4) and the gate, the original exact remaining backward clock satisfies
    B_old <= c_a U_end + O(c_a N[(D+P_max)(log N+1+1/xi)
                                    + P_max(H/D+2)]).
For the chosen D,xi this error is o(NT): D log N=O(eta H), D/xi=o(H), P_max times all logarithmic factors is o(H). Thus (5) is a new sufficient scalar with no within-slab tracking. Keep the minimum with U_ind and U_cont. It can be larger than either because of domain relaxation and omission of dynamic induced gates, even though the denominator approximation on identical pair sets has only o(NT) error. No lower bound or strict uniform saving of (5) relative to the old envelope is claimed.

## 4. Relation to founder and lifetime bounds

Each endpoint Q induces a tree of only its actual members, with no retirements until e-. It can be evaluated by the previous founder budget and pair first-meeting cuts. The fixed denominator now permits arbitrary STATIC pair masks (including the earlier physical-birth size, root spacing when expressed as a fixed threshold, and age bounds) to be evaluated by exact intersections of intervals. If one retains an old K-dependent mask, its permitted subset of the slab can replace the interval in (5); the denominator approximation still holds for its exact numerator, but the simple interval quadrature bound requires fixed intervals or a proved complexity bound. Do not infer independence of the old grid-dependent source weights. The new test is for the relaxed normalized upper envelope, not an equality of the original clock.

## 5. Ideal common gain terminal and root ranks (conditional on (1))

At any actual endpoint Q define
    r_Q(e)=# {i in Q : C0_i+T>=e}.
By (1) the ideal terminal is no later than the actual terminal. Moreover every historical member of Q's abstract component whose C0_i+T>=e is in Q: it was previously an actual member of this history, cannot have stopped before e, and deterministically follows its common suffix. Conversely the counted members of Q belong to that historical component. Hence r_Q(e) is exactly a ROOT ORDER STATISTIC of the historical component, even though that component contains retired members. The left-limit convention includes equality. No ghost trajectories added. The difference q-r_Q comprises only overshoot tags with C0_i+T<e<=F_i. Since each overshoot has length <B, 
    D sum_(slabs,Q) (q-r_Q(e)) <= N(B+D).             (6)
This is independent of number of mergers.

Every pair counted in (5) on [l,e) has both ideal terminals >=e, because F_i>=K+h, F_i<C0_i+T+B and h>B+D+2. Thus its ordered count is <=r_Q². Replacing its denominator max(b0,q) by max(b0,r_Q) gives a pointwise increase at most q-r_Q: use A<=r_Q². Integrated total <=N(B+D)=o(NT) on identical groups. To remove the actual endpoint mass gate, use the ROOT-RANK gate r_Q>=(1-2xi)b0. For a lost old endpoint group q>=(1-xi)b0 but r_Q<(1-2xi)b0, q-r_Q>xi b0. Its original capacity <=r_Q<= (q-r_Q)/xi. Total over slabs <=N(B+D)/xi=o(NT) by (6). The relaxed new gate may admit extra groups; we only use a one-way sufficient upper bound.

Also replace the terminal upper endpoint F_i-h in E_i by C0_i+T-h (same half-integer rounding), holding its lower endpoint and all fixed birth-age masks unchanged. Denote new tag and pair intervals E_i^*, I_ij^*. The removed interval length per tag <=B+1. Within each slab the eligible old tags are in the ideal rank subset, and denominator max(b0,r_Q)>=r_Q, so the two-orientation normalized row loss from removing a tag at a K is <=2. Sum of all affected K across the disjoint slabs <=2N(B+1) in continuous units. This is a valid relaxation comparison even when two affected tags share a pair. Thus define
    U_rank = sum_slabs sum_(Q: r_Q(e)>=(1-2xi)b0)
                  sum_(ordered i!=j in Q) |I_ij^* intersect [l,e)|
                          / max(b0,r_Q(e)).          (7)
All nonempty pair terms involve only root-rank members of Q. Therefore B_old<=c_a U_rank+o(NT) under (1). Formula (7) can use historical components at endpoint plus the ideal root terminal test instead of listing active overshoot members. The condition on historical membership is always the component generated by actual mergers before the endpoint crossing; no subsequent ghost mergers. If desired, choose the original actual Q gate and new denominator, then the difference on the same set of pairs/endpoint groups is O(N(B+D)); the near-threshold gate above is what permits an expression based solely on root ranks. (7) is not claimed <=(5) because its gate is relaxed and denominators smaller. All old masks remain preserved in the exact residual.

## 6. A further snapshot-free birth-rank upper envelope

Still assume (1). For a pair i,j with C0_i<C0_j, first actual meeting V, define R_i(V)=# historical members of the union component immediately AFTER V whose origin C0>=C0_i. The older-root orientation is unrelated to the earlier smaller-historical-branch choice in a_ij, which stays fixed. At any slab supporting I_ij^*, e<=K+D<C0_i+T, so every historical member counted in R_i(V) has ideal terminal >=e. Every such tag was alive at V (its actual terminal cannot precede V since e>C_V), and reaches the shared endpoint cohort. Hence r_Q(e)>=R_i(V). All intervals of the same pair over slabs are disjoint. It follows directly that
    U_rank <= U_birth_rank :=
        2 sum_(i,j:C0_i<C0_j, actual allowed first birth V)
                    |I_ij^*|/max(b0,R_i(V)).
Here pairs with no support may be included for an upper bound, even if not meeting rank gate. Can replace |I_ij^*| by (T-h-(C_V-C0_i)-a_ij)_+ + O(1) when nonempty (also retain individual maturity bounds and later root origin). Do not sum O(1) without normalization; at most N²/b0= o(NT).

For fixed older i, R_i(V) is nondecreasing along its actual history, starting from 1 before any merge (at injection). At birth vertex V, #younger partners meeting i for first time <=Delta R_i(V), the increase of this historical tail count at that vertex. Each younger partner comes from another historical component, and is counted once. Therefore
    sum_(j younger, meeting i at V) 1/max(b0,R_i(V))
                   <= Delta R_i(V)/max(b0,R_i(V)).
For Psi(x)=integral_1^x dt/max(b0,t), monotonicity of 1/max(b0,t) gives Delta R/max(b0,R_new)<=Psi(R_new)-Psi(R_old). With all eligible younger pairs having latest possible endpoint C0_i+T-h, a further simple envelope is
    U_birth_rank <= 2 sum_i integral_(C0_i)^(C0_i+T-h) Psi(R_i(x)) dx
                      + O(N²/b0),
where R_i(x) is the cumulative historical tail count along its actual history at horizon x; set it constant after termination for this upper bound only (an abstract count, NOT an extended trajectory). To see this, bound each pair length by (C0_i+T-h-C_V)_++O(1), telescope the cumulative harmonic increments at every x, and use Fubini. This loses old age/maturity masks and may be much looser than (7); it makes the dependence on the growth of origin ranks explicit. Psi(x)=(x-1)/b0 for x<=b0 and (b0-1)/b0+log(x/b0) for x>=b0. It is not proved small. The useful denominator in (7) also counts younger tags attached between V and the endpoint; the birth-rank approximation discards this beneficial growth. No estimate of the new rank statistics strong enough for the final constant is obtained.

## 7. Sufficient route and limitations

Under finitely many twins, combine original certificate with (5) and conditional (7):
    NT/2-o(NT) <= c_a min(U_ind,U_cont,U_end,U_rank)
                    +(3+o(1))(D_l,old+D_h,old).
Thus liminf [min(U_ind,U_cont,U_end,U_rank)+D_l,old+D_h,old]/(NT)<1/6 suffices. U_birth_rank is an optional upper bound on U_rank, not a further minimum improvement. All estimates of endpoint denominator errors use original full source denominators. The reduced endpoint objective has no dynamic interior cohort denominator, and the conditional rank objective uses only origin cutoffs and actual historical merger information. No proof of the needed strict constant margin, and no claim that the remaining forward defects are small. Main and independent branches unchanged; no Lean compilation.

## 8. Reproducible numerical audit

[Final standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/86aaf779a3c9ad1b390001540cdedcf49455b293/research/min_unified_endpoint_denominator_audit.mjs), exact committed readback verified. Nine final-source runs passed in ECMAScript runtime: four ordinary X1024,4096,16384,65536, three focus X4096,16384,65536 and two extra X65536 gainFactor2 scales .5,1. Reproduce: node research/min_unified_endpoint_denominator_audit.mjs 1024 4096 16384 65536. Derived from 55ae21f. Finite b0=L=2m, m=max(2,floor(scale sqrt B/3)), h=floor(.02H)+.5, D=max(2,floor(h/2)), xi=.25, eta=.25, finite fixed age proxy. These are finite diagnostic parameters, not the analytic scales. Uses actual MIN paths, compressed arrival vertices and actual terminal flows. Checks exact actual entropy telescope (2), actual endpoint partition, source survivor subset uniqueness, independent first birth/static age intervals, local denominator difference and gate loss, all integrated/global grid budgets and independent endpoint pair sum/quadrature. No full induced or cumulative analytic masks; old source-domain comparison uses only b>=b0 and finite static masks. First attempt had duplicate variable declaration, corrected before running final source. Separately tests ideal root cutoff on the ACTUAL REACHED-root subensemble, restricting denominator for that diagnostic alone; it does not assume all finite tags reach T. Checks pointwise rank subset, continuous overshoot area, endpoint overshoot count, normalized denominator change and ideal terminal interval shrink, using larger finite strip B+D+1 for endpoint rank test. Does not implement the conditional historical-rank gate or birth-rank harmonic envelope as a separate empirical test. No literal gcd oracle or Lean verification.

Largest ordinary X65536: N5709,140255 completed events, no finite T reaches, D61,b0=16, entropy sum10331.694604 equals retirement entropy, 1926 source slab pieces,37926 endpoint pair/slab incidences,114641 original source pair/slab incidences. Old relaxed integral120230.963650, frozen-on-old119917.369406, endpoint119917.369406. Positive denominator difference313.594244 <=growth budget8771.323963; actual gate loss0. In the extra X65536 gainFactor2 scale .5, N5709,129305 completed events,564 reaches, D20,b0=8, entropy10244.422825,8697 source pieces,255513 endpoint pair/slab incidences,385168 source pair/slab incidences. Old relaxed integral487060.390527, frozen-on-old486883.961763, endpoint490098.543884 (domain relaxation can increase capacity); positive difference1388.111554<=growth area7079.113671, negative1259.060567<=retirement area19834, gate loss47.377778<=retirement/xi. Grids:
|P|old relaxed grid|endpoint grid|endpoint grid vs integral abs error|
|---:|---:|---:|---:|
|6|487333.600023|490572.272721|473.728838|
|30|488137.625075|491347.005670|1248.461786|
|210|467774.015417|470238.656287|19859.887597|
Actual reached-root subensemble of this extra run: 7829 crossing slots, continuous overshoot area54620, denominator-error area1168.742780; 9051 endpoint cohorts, endpoint overshoot area54300, denominator difference1204.421236, terminal-strip change47612.478791, 3901 positive pair cohorts. All bounds pass. The largest focus X65536 has2886 finite reaches, zero qualifying ordinary large slots, but its isolated reached-root endpoint diagnostic has46401 cohort checks, endpoint overshoot area294780, denominator difference100.467388, terminal-strip change3481.797547. No empirical estimate of the asymptotic error or constant-margin contraction inferred.
