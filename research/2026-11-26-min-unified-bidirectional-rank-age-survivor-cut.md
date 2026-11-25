# Bidirectional root-rank age and endpoint-survivor birth cut

2026-11-26 JST. Continues [ef0953b7bcba](https://github.com/tara-sooo/A166944-Lean/blob/ef0953b7bcba6adb829f7b1adbcb0c1d669dfece/research/2026-11-26-min-unified-endpoint-denominator-root-rank.md), [ed0661721670](https://github.com/tara-sooo/A166944-Lean/blob/ed066172167054ad66a143186fd738069e9e72c4/research/2026-11-26-min-unified-entropy-age-continuous-lifetime-cut.md), [96656afaa7c2](https://github.com/tara-sooo/A166944-Lean/blob/96656afaa7c25e44cfc8278d663c053b356e7129/research/2026-11-26-min-unified-historical-founder-forest.md). New: three telescoping historical growth budgets (total mass, lower origin rank, upper origin rank), a stronger factorized first-birth age mask with o(NT) exact payment; endpoint-relative two-sided rank thinning on actual surviving members, with an unconditional O(rho NT) cost in the endpoint envelope; arithmetic support for large induced birth ranks; exact branch census of the new relaxed endpoint objective without enumerating all pairs. The rank threshold is on the actual endpoint-induced history, not merely historical membership. No proof of the final strict constant bound or Lean compilation.

## 1. Frozen ensemble and previous reduction

X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Original prime roots M in [X,2X), C0_i=2M_i-2, true initial state (M_i+2,C0_i). Original deterministic completed MIN paths, gain p-1, total gain <H, w<=2p<=3(p-1). Original terminal F_i, including terminal snapshots. Under finitely many twins eventually every original tag reaches T, so C0_i+T<=F_i<C0_i+T+B. This last condition is used only for the ideal-rank version, not for exact age payment or actual endpoint rank cuts.

Keep all old exact masks through ef0953b, original grids P_j with P_max<=B^.25, common average denominator, c_a=3(1+2/u^.25), b0=ceil(b_min)=ceil(H/[512 L0 B u ell³ sqrt(tau)]). Original positive backward full source slot b>=b0. Ordered pair clock per source atom <=c_a P/b and either-role tag clock <=2 c_a P. Each tag crosses <=H/P+1 strict atoms. Original weights, actual first meetings, original incoming branch labels and original full source populations not recomputed. Under the finite-twin hypothesis NT/2-o(NT)<=B_old+(3+o(1))(D_l,old+D_h,old).

Use eta=ell^(-1/4), h=eta H, L=floor(B^(1-ell^(-1/2)/4)). Old eligible tag intervals E_i=[M_i^++h,F_i-h] on non-Bad terminal-nonmoving tags with actual physical maturity, empty otherwise; ideal E_i^* has F_i replaced by C0_i+T. M_i^+=max(J_i,A_i^+) unchanged. For pairs retain the old actual-first-meeting static condition that at least one original actual incoming branch has mass >=L. Retain old fixed age conditions; other old exact masks are still applied, though not all are used in the new relaxed envelope. Old endpoint slabs [l,e) of length D=max(1,floor(eta H/log(2+N))), endpoint actual crossing at e-, gate q>=(1-xi)b0 where xi=sqrt(eta). Ideal endpoint subset Q^* consists of actual endpoint members with C0+T>=e; its size r, gate r>=(1-2xi)b0, denominator max(b0,r). In the actual version use Q and r=q, gate q>=(1-xi)b0. Both have the old valid entropy freezing and grid quadrature errors o(NT).

## 2. Three historical potentials and strengthened actual first-birth age

Use the original historical forest (96656af). At any true vertex V with incoming historical components H_j, disjoint root sets, and union H, for each actual active incoming tag i in H_j define
    m_i^- = |H_j|,   m_i^+ = |H|,
    p_i^- = # {k in H_j : C0_k<=C0_i}, p_i^+ similarly in H,
    s_i^- = # {k in H_j : C0_k>=C0_i}, s_i^+ similarly in H.
All three include i and are >=1. Historical sets include retired members but do not extend their actual trajectories. The tag's three counts are nondecreasing along its own actual trajectory; only actual mergers change them, and each is initially 1 and at most N. Put
    g_i(V)=log(m_i^+/m_i^-)+log(p_i^+/p_i^-)+log(s_i^+/s_i^-).
Then along each original actual life, sum_V g_i(V)<=3 log N. Summing only active memberships,
    sum_(V,i) g_i(V)<=3N log N.                          (1)
At most 3 log_2 N active incidences per tag have g_i>=log 2.

Define a_i(V)=eta H g_i(V)/log N. For an actual first-meeting pair i,j at V, the old a_ij of ed06617 is eta H times the larger of the two total-mass log gains divided by log N. The smaller historical incoming component has mass <=m_i^+/2, so a_ij>=eta H log 2/log N. Hence max(a_i,a_j)>=a_ij. Pay all exact old surviving backward atom fractions for which K<C_V+max(a_i,a_j). Assign a fraction to a violating member with a_i>a_ij (ties fixed); old surviving pairs already passed the old a_ij age, so at least one such member exists. For a fixed actual membership (V,i), all such assigned partners at any source atom have combined two-orientation clock <=2 c_a P. The atom count in [C_V,C_V+a_i) is <=a_i/P+1. Only a_i>a_ij>=eta H log 2/log N need be counted. Thus (1) gives the total extra payment
    B_rank_age <= 2 c_a [3 eta NH + 3 NP_max log_2 N] = o(NT).  (2)
No N² overhead from small positive log increments; the old age condition is used precisely to avoid that. Any old additional age bound remains. No historical retired member is assigned actual residence. The new condition is static for each first birth and its active members, independent of grid or endpoint. It detects changes in root-order ranks even at balanced historical mass ratios; no lower bound of constant order H is claimed for every pair.

## 3. Actual endpoint-survivor induced ranks and relative birth cut

Fix one slab and an endpoint set Q_r equal to Q for the actual version or Q^* for the conditional ideal version. It has r original tags all actually present at e-. Use the induced original history tree of all its members, including members with empty E_i, so eligibility never changes these rank counts. At any actual true vertex V before the endpoint write S(V) for Q_r members present at V. For i in S(V), define
    t_i(V)=# {k in S(V):C0_k>=C0_i}, 
    v_i(V)=# {k in S(V):C0_k<=C0_i}.
They are nondecreasing along i's actual history to this endpoint (no induced retirements), and bounded by the corresponding historical ranks at that vertex. These are endpoint-specific, not global historical ranks, and use the original true vertex including tick. No eligible interval is used to change the rank after choosing the endpoint set.

Orient each unordered pair by increasing root C0_i<C0_j (not the same as old smaller-branch routing). Let rho=ell^(-1/4). Impose at its actual first meeting V:
    t_i(V)>=rho r,  v_j(V)>=rho r.                       (3)
For a fixed older i in Q_r, its distinct younger partners with first meeting at a vertex where t_i(V)<rho r lie in the nested upper-rank sets along that history before the threshold is first crossed. Their union has cardinality at most rho r (strict inequality and i included only improve it). The same argument for a fixed younger j counts distinct older partners with v_j(V)<rho r. Count each pair once per orientation for an upper bound; assign suffix failures first, then prefix failures if desired. At every K in the slab the total normalized ordered pair count removed by (3) is <=4 rho r²/max(b0,r)<=4 rho r. This holds even if eligibility intervals and arbitrary prior pair masks are intersected, as those only reduce the numerator. Each original tag occurs at <=H/D+2 actual endpoint snapshots. Summing continuous lengths,
    U_removed <=4 rho D sum_(slabs,Q_r) r
              <=4 rho N(H+2D)=o(NT).                   (4)
The analogous grid estimate replaces D by D+P_max, which is o(NT) as well. This is a payment in the endpoint envelope, not a claim that the corresponding original source ratios were already exactly the endpoint ratios. Use the old denominator freezing error once for the entire remaining source measure, then (4). It is valid unconditionally on actual endpoints and conditionally on the ideal endpoint subsets. The induced-rank condition is stronger than using historical ranks at birth with the same r, with the same bound (4). Also stronger than a suffix test relative only to the older tag's final tail rank. The two directions are counted separately, not assumed disjoint.

## 4. Arithmetic consequence in the finite-twin ideal kernel

In the ideal version Q_r all have C0>=e-T. At a surviving birth with C0_i<C0_j, (3) supplies at least rho r distinct original prime origins in [C0_i,C_V] (upper tail) and at least rho r in [e-T,C0_j] (lower prefix). These are actual endpoint survivors at V, not historical retired tags. Use the old uniform one-form prime interval upper sieve: an interval of horizon length D0 contains at most C(1+D0/log(2+D0)) such roots, with absolute C. Because r>=(1-2xi)b0 and rho b0=B^(1-o(1)), for sufficiently large X the inversion gives an absolute c>0 and
    C_V-C0_i >= c rho r log(2+rho r),
    C0_j-(e-T) >= c rho r log(2+rho r).                  (5)
The first inequality also holds in the unconditional actual endpoint version; the second requires ideal cutoff or may use actual H in place of T. In particular any K in the new ideal pair interval satisfies
    K-C_V <= T-h-c rho r log(2+rho r)+O(1).
Together with the new lower bound max(a_i,a_j), this gives explicit permitted support. It controls both the actual age of the older root at birth and the origin of the younger relative to the endpoint's lifetime window. It does not imply a lower age of the younger member at birth; the prefix count is of older roots. The root-rank upper tail can be used for support even if it contains tags not themselves eligible for pair weights. The old true birth and all old masks are unchanged.

A further endpoint-only zero-support test: if a birth node's full induced mass is <rho r, it cannot support any surviving pair by (3). A sharper per-member support bound uses the actual rho r-th root of the induced node, not the sieve constant. These conditions refine a relaxed capacity by o(NT) payments. Since rho r log r can be o(T) for r near b0, no uniform constant-fraction age reduction follows. The earlier birth-rank harmonic envelope is optional, and has not been proved small.

## 5. Exact branch census for the relaxed endpoint objective

For each slab [l,e), endpoint Q_r, and actual birth vertex V in its induced original tree, let j range over the original actual incoming groups with Q_r members; mark j large if its ORIGINAL full actual incoming mass >=L. For each i in group j define its individual interval
    I_i(V) = [l,e) intersect E_i intersect
             [C_V+max(a_i(V), old fixed uniform age), infinity)
in the actual version; use E_i^* in the ideal version. Keep the same half-integer endpoint convention from ed06617 for integer grids. All pair-specific age from ed06617 is implied by the new max of member ages, since its age was the max of their total-history log increments. If an extra old pair-specific predicate is not factorized, either retain it separately or omit it to obtain an upper envelope; the following census uses exactly the specified static actual-large test, new ages and induced-rank tests. It does not assert equality for arbitrary previous exact masks.

For fixed K in the slab let X_j(K)={i in branch j:K in I_i(V)}, x_j=|X_j|, n=sum_j x_j, n_s=sum_(j not large)x_j. Without (3), the number of ordered distinct admissible first-birth pairs at V is EXACTLY
    n² - sum_j x_j² - n_s² + sum_(j not large)x_j².       (6)
Each pair from different incoming groups has its first actual meeting precisely V, including root injection. This identity uses actual group labels, not historical component size as actual branch mass.

With (3), define X_j^tail(K) subset of X_j passing t_i(V)>=rho r, X_j^pre(K) similarly for v_i(V)>=rho r. For any root origin c set Y_j(c,K)=# {k in X_j^pre(K):C0_k>c}. Then the exact ordered admissible count at V is
    C(V,Q_r,K)=2 sum_j sum_(i in X_j^tail(K))
                  sum_(k!=j, j or k large) Y_k(C0_i,K).  (7)
This uses only per-branch sorted root counts and individual birth intervals, with no enumeration of ordered pairs required for evaluation. Counts are strict in root order; all original prime origins distinct. The term Y can be computed by binary search on a sorted list or by a cumulative rank sweep. Because membership intervals have fixed endpoints in each slab, C is a piecewise constant finite function. Optional old fixed root-gap restrictions can be incorporated by increasing the root threshold in Y when they are of that form; no unproved factorization of arbitrary pair masks. This is an exact census of the newly defined relaxed upper envelope.

Define U_end,2 (actual) and U_rank,2 (ideal) by
    sum_(slabs,Q_r passing respective gate) 
       1/max(b0,r) sum_(V in induced actual tree) integral_l^e C(V,Q_r,K)dK.
By first-meeting uniqueness this equals the previous endpoint pair-interval sum with stronger ages and (3), so U_end,2<=U_end, U_rank,2<=U_rank on identical respective domains. The age mask payment (2) is applied to the original exact measure BEFORE freezing. The rank payment (4) is applied in the frozen endpoint bound. For the discrete original grids, each pair's new interval is still a single intersection of fixed intervals in each slab, and (3) is constant per slab/pair. Thus the previous NP_max(H/D+2) quadrature error remains valid without a factor for the number of vertices. No need to approximate each birth-node integral separately by an unrelated error. The resulting exact residual satisfies B_new<=c_a U_end,2+o(NT) unconditionally, and B_new<=c_a U_rank,2+o(NT) under the finite-twin hypothesis. Forward unchanged. The relaxed capacity is not identical to the actual old clock, and the full old dynamic induced/source masks can still be used via the minimum of valid envelopes.

## 6. Updated sufficient route

Under finitely many twins,
    NT/2-o(NT) <= c_a min(U_ind,U_cont,U_end,2,U_rank,2)
                   +(3+o(1))(D_l,old+D_h,old).
A sufficient criterion is liminf [min(U_ind,U_cont,U_end,2,U_rank,2)+D_l,old+D_h,old]/(NT)<1/6. Because U_end,2 and U_rank,2 reduce their earlier respective endpoint domains, this is no stronger than the previous sufficient test. The new rank-age budget and induced survivor rank cuts are structural reductions, not a proof that the strict inequality holds. The actual forward defects remain to be bounded, and even the new backward scalar has no established constant-fraction upper bound. Main and independent branches not modified. No Lean compilation.

## 7. Numerical audit

[Final standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/23a3d09e76a1ed053714ccb548577ef328ec009b/research/min_unified_bidirectional_rank_birth_audit.mjs), exact remote readback verified. Nine final runs passed in ECMAScript runtime: four ordinary X1024,4096,16384,65536, three reach-focused X4096,16384,65536, two extra X65536 gainFactor2 scale .5,1. Reproduce: node research/min_unified_bidirectional_rank_birth_audit.mjs 1024 4096 16384 65536. Derived actual finite MIN generator from 86aaf77. Finite b0=L=2m with m=max(2,floor(scale sqrt B/3)), D=max(2,floor(h/2)), h=floor(.02H)+.5, eta=rho=.25, age proxy as previous. Uses ACTUAL full endpoint sets q>=b0, not the relaxed gate or ideal conditional rank subset. Uses finite physical first-maturity and terminal strips, finite historical age rounded down to floor(a)+.5, and original actual-large branch mask; no full weighted-final, Bad, exact cumulative masks or original source weights. Checks all three log growth sums independently per original tag using sorted historical root sets, exact original first meetings, old/new age interval nesting and normalized age budget, nested younger/older partner census for the two rank cuts, elementary origin spacing (not asymptotic sieve), and independent branch census using per-branch sorted-origin counts, compared to explicit pair interval enumeration for continuous sums and each grid. Final source uses full actual endpoint-survivor ranks at birth, not historical ranks; earlier intermediate run used historical ranks, then both directions and induced ranks added and all nine rerun. No direct diagnostic of ideal-rank endpoint subset in this file, no empirical asymptotic estimate, no literal gcd oracle or Lean verification.

Largest ordinary X65536: N5709,140255 events,0 finite T reaches;155875 historical active membership checks,20084 positive additional prefix/suffix growth incidences,577 qualifying endpoint groups,78457 pair/slab checks,15510 branch census pieces,2654 suffix and249 prefix partner-count checks,16552 elementary spacing checks. Old endpoint integral119917.369406, three-growth age integral52539.114249, two-sided induced-rank integral48001.005678. The new rank deletion4538.108571. All grid sums match branch census. Extra X65536 gainFactor2 scale .5:564 reaches,129305 events,144737 historical active membership checks,19675 positive rank growth,5366 endpoint groups,340869 pair/slab checks,73395 independent branch census pieces,15441 suffix and3087 prefix partner-count checks,152227 spacing checks. Old finite endpoint integral486851.543884, new age336586.119964, final induced rank294052.681631, rank deletion42533.438334. Earlier historical-rank version297673.798636 (strictly larger). Grid final:
| P | pair interval sum | branch census |
|---:|---:|---:|
|6|294240.048422|294240.048422|
|30|294555.507618|294555.507618|
|210|284448.726434|284448.726434|
Extra scale1 old136830.710392, new age87353.290023, final rank75115.054016. Focus runs have no qualifying finite endpoint group, but nonzero rank-growth checks. These are finite unit-cap relaxed objectives with fixed eta/rho=.25 and finite target, not the analytic o(NT) reductions or an estimate of the strict asymptotic constant. No final contraction inferred.
