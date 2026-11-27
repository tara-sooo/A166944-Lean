# Negative MIN: first-cell exit certificates, adaptive coarse inverse codes and reverse-flow packing

2026-11-27 JST. Continuation of [e173792](https://github.com/tara-sooo/A166944-Lean/commit/e1737924a0793604fd6428ce21ebf4e1667aef21). The objective remains unconditional twin infinitude, independent proof verification and Lean formalization. Rather than lose the signed cancellation by bounding absolute boundary fluxes, develop an alternative certificate using monotonic cell paths. First derive a deterministic long-wait bound at the first exit, identify the ordinary upper-sieve obstruction to a fixed polynomial roughness target, then allow multiple exits and adaptive per-cell observation by arithmetic inverse codes and a reverse subprobability flow. These are paper-level sufficient reductions, not the missing asymptotic estimate.

## 1. First-cell exit and waiting certificate

Use the Negative MIN clocks in 5e932c4 and e173792: root A even and divisible by 6 in [R,2R], birth b(A)=3-A/2, postheight h=n+x/2>=0, and position x decreases by p-1 at a firing with odd prime label p. All eligible clocks, not merely the least factors, participate in selecting the first hit and least label at a tie. Let S=sqrt(2R+1), T=ceil S. In this note each root is observed from its own birth through elapsed T, not through the former synchronized retirement. These observations are actual prefixes of the synchronized paths; gain <=2T+6 and all positions remain in [R-2T-6,2R]. The soft support criterion in 1d0e2c5 does not require synchronized observation if a valid inverse weight is supplied.

Fix Q divisible by 6, M=Q/6, and cells [jQ,(j+1)Q). Labels p|Q cannot cross a boundary downward (e173792). Stop just BEFORE the first completed exit from the root's own cell, or at elapsed T if no exit has occurred. Write x for the selected position, G=A-x<=Q-2, and v for the elapsed time when x was reached. Every completed prior wait w_i <=2q(x_i)<=2p_i<=3(p_i-1), where q(x) is the smaller least prime factor of x-1,x+1. Hence v<=3G.

If the exit is caused by p after a wait w, nonnegative height after that event gives
    v+w+3 >= (G+p-1)/2.
Therefore
    w >= (p-1)/2 - (5/2)G - 3,
    q(x) >= max(3, (p-1)/4 - (5/4)G - 3/2).          (1)
If no exit has completed by T, then the last wait has lasted at least T-v; the periodic least-factor clock gives
    q(x) >= max(3,(T-3G)/2).                          (2)
The inequalities remain valid when their nontrivial right sides are negative. The selected x is always in the initial cell, so its root multiplicity is <=M regardless of the elapsed clock. The same multiplicity cap holds if selecting the maximum-weight visited position before the exit. For any chosen subcohort C of roots, with any of these selections,
    sum_{distinct selected x} w_R(x) >= M^-1 sum_{A in C} w_R(x(A)).
The soft weight w_R is that of 1d0e2c5: q*=min(q,S), d=log(S/q*), w_R=(log q*/log S)^2/[(1+d)(1+log(1+d))^2]. It is increasing in q. Thus (1),(2) give a direct certificate using only actual exit labels and internal gain, without endpoint entropy or synchronization. One may also take one maximum-weight representative per initial cell, or the union of all visited pre-exit positions. These have exact cell-disjoint support. No asymptotic lower bound for the certificate is established.

## 2. A necessary correction to polynomial-scale optimism

For fixed epsilon>0, Q=log^(a+o(1))R, define s_P the fraction of roots with no exit by T or first exit label p>=P=R^epsilon (epsilon<1/2). By (1),(2) every selected pre-exit position has q(x)>=c_epsilon R^epsilon for large R. The ordinary two-dimensional upper sieve already gives O(R/log^2 R) such centers, INCLUDING twins. Since each has at most M preimages,
    s_P = O(M/log^2 R).
At fixed polynomial q scale the weight lower bound has order 1/[log R (loglog R)^2]. Consequently the resulting crude lower certificate N s_P/(M log R (loglog R)^2) cannot exceed the O(R/log^3 R) non-twin capacity at a strictly better logarithmic exponent. In particular a supposed sufficient condition a+b<2 with s_P>=log^(-b)R is incompatible with the unconditional upper sieve. This is a real obstruction to that use of the first-exit bound, not a contradiction in MIN. The remedy must distinguish near-square-root roughness or use the full heterogeneous weights, not just polynomial roughness.

For 0<alpha<1, set P=S exp(-(log R)^alpha), or a fixed positive multiple thereof. For Q polylogarithmic, (1),(2) imply q*>=cP on the cohort with no exit or p>=P. Thus w_R>=log^(-alpha+o(1))R (the loglog factors are subleading). A sufficient condition is
    s_P >= log^(-b+o(1))R,    a+b+alpha<3               (3)
on unbounded slabs, with Q=log^(a+o(1))R. The ordinary upper sieve requires a+b>=2 in the exponent, which leaves a nonempty possible range when alpha<1. More explicitly the ratio of the lower support to R/log^3 R must diverge. The no-exit part alone has q*>=cS and weight bounded below by a positive constant for Q=o(T); hence s_noexit >> M/log^3 R with ratio tending to infinity suffices. Neither abundance statement is proved. For Q=6 the canonical root lies on its lower cell boundary and every actual first jump exits; the certificate is then simply a condition on rough canonical roots, so do not treat it as a dynamical improvement.

## 3. Coarse inverse code without clocks

An actual path has a strictly decreasing sequence of distinct visited cell indices j_0>j_1>...>j_k; ignore all within-cell jumps. At a crossing landing at even x in cell j, the preceding position is x+p-1 and p|x or p|(x-2). A crossing from the adjacent cell j+1 has only one possible source CELL, independent of how many labels or landing positions can generate it. If the source is >=j+2, the label p>Q. Define the finite candidate set
    D(j)={floor((x+p-1)/Q)>j+1:
          x even in cell j, p odd prime dividing x or x-2,
          p>Q, p-1<=2T+6, x+p-1<=2R}.
Use only x in the positive actual domain (or a superset with x>=4). Every actual nonadjacent predecessor is in D(j). No label, landing position or clock must be encoded for the inverse CELL step. At each x the number of eligible distinct factors >Q is <=2 log(2R)/log Q. Thus
    |D(j)| <= min(Q log(2R)/log Q, 1+floor((2T+6)/Q)).
Rounding harmlessly upward gives uniform D>=1.

For any observation X(A) at a root-dependent elapsed tick <=T, read the cell prefix backward from cell(X). Compress adjacent inverse steps into nonnegative run lengths g_0,...,g_k, where k is the number of nonadjacent transitions in that prefix. Between runs choose the actual source cell by rank in D(j) at the current decoded cell. At the final decoded root cell choose the offset A modulo Q among M canonical offsets. This decodes A uniquely from the observation cell and the code, independent of the actual clocks. A code can be invalid or decode another root; only an upper bound on total valid mass is required.

For example use probability 1/[(k+1)(k+2)] for k, the same probability law for each run length g, uniform ranks, and uniform root offset. Since these are normalized sequential laws and invalid codewords can be discarded, per-cell Kraft mass is <=1. This does NOT require an arbitrary root-dependent observation choice to be synchronized, nor even to be deterministic if all possible prefixes are counted with distinct words. For the present one observation per root, distinct roots have distinct decoded words. The corresponding code length is
    ell=log M + log((k+1)(k+2))
             + sum_i log((g_i+1)(g_i+2))
             + sum_nonadj log |D(j)|.
On a selected cohort with fraction s_R, use the weighted support inequality or Jensen:
    sum_{distinct X} w_R(X) >= sum_A exp(-ell(A)) w_R(X(A))
                        >= N s_R exp(-E_C ell - E_C c_R(X)),
where c_R=-log w_R. Thus a strict liminf of [E_C ell+E_C c_R-log s_R]/loglog R below 3 suffices. Unlike the former fine factor-gap code, intraceil motion and the label identities of adjacent exits are free.

A mean-based variant uses geometric laws: for mean kbar=E_C k and mean gbar=E_C sum_i g_i, entropy/cross-entropy of a nonnegative integer with mean t is bounded by h(t)=(1+t)log(1+t)-t log t, with h(0)=0. Choose geometric law of mean kbar for k and a single run law of mean gbar/(1+kbar) for each of its k+1 runs. Expected code length satisfies
    E_C ell <= log M + h(kbar)+(1+kbar)h(gbar/(1+kbar))
                          + E_C sum_nonadj log |D(j)|.   (4)
The zero-mean cases use point masses. This is a valid analytic reduction even if the means depend on R and cohort. For a bounded number of nonadjacent moves, it can exploit compression of many adjacent moves. No useful asymptotic bound on kbar, gbar or roughness has yet been obtained.

## 4. All-cell reverse-flow packing

A separate, simpler certificate charges all visited cells, not just one chosen observation or the final cell. Let alpha_j in [0,1] be a stop probability at cell j and choose nonnegative reverse weights P(j,i) on i>j, supported on i=j+1 and D(j), with sum_i P(j,i)<=1-alpha_j. Fix any valid root-cell offset code of weight 1/M per root. For each root-cell visit along its actual decreasing cell path j_0,...,j_r define
    k(A,j_r)=(alpha_{j_0}/M) prod_{t=1}^r P(j_t,j_{t-1}).     (5)
The empty product is 1. Let K(j) be the sum of weights of all roots visiting j. The weight of births in j is <=alpha_j. Every arriving root visited a unique preceding cell i>j and contributes its previous weight times P(j,i). Since paths never return to a cell,
    K(j) <= alpha_j + sum_{i>j} P(j,i) K(i) <=1
by descending induction over the finite domain. Equivalently, these are subprobability weights of distinct reverse root words. The induction does not rely on randomization of MIN, on independence of CRT residues, on endpoint multiplicity, or on a common clock.

Within each visited cell choose for each visiting root the actual position with largest w_R (any tie rule). A root contributes once to that cell, so the total weight attached to any position is <=K(j)<=1. Hence
    sum_{all visited positions} w_R(x)
          >= sum_A sum_{j visited by A} k(A,j) max_{x visited by A in j} w_R(x).   (6)
The same proof permits using only some root-cell visits, or selecting by the product of the code weight and roughness. More generally the run-length code of section 3 can be used for ALL cell visits: for each fixed j every root visits it at most once, and each distinct decoded root has distinct codeword, so its total Kraft weight is <=1. This gives a heavy-tailed alternative to the exponential per-step discount in (5). Neither bound requires division by a worst-case final fiber. Both remain conditional as routes to infinitude: an asymptotic lower bound on the right of (6) exceeding non-twin capacity is missing.

For fixed alpha=1/2, adjacent probability conditional on continuation 3/4, and the remaining probability uniform over D(j), set the adjacent probability to 1 if D(j) is empty. This simple policy was tested; it heavily favors births/early visits, and can reproduce support already contributed by known twins at births. A finite ratio above bad capacity is not evidence for the missing asymptotic lower bound. Other policies could depend on j and actual arithmetic candidate sets, provided their rows remain substochastic. The next substantive step is to derive analytic lower bounds on weighted near-square-root observations before the inverse weight decays, or use signed flux correlations from e173792 if these prefix certificates cannot avoid early roughness scarcity.

## 5. Executed audits and limitations

Three scripts were executed as actual ECMAScript functions before commit and after exact remote fetch, using the same prime-factor clock implementation as prior notes. The first script initially had an omitted default increment argument in the local uncommitted test; fixed before first commit. Its first committed capacity scan used the wrong parity when T odd; corrected in f19ca71 and the corrected capacity matches e173792's predecessor audit on the expanded slab. No Node process or Lean kernel was invoked, no independent analytic reviewer, no external novelty claim. The following are the corrected checkpoints.

A. [First-cell-exit audit f19ca71](https://github.com/tara-sooo/A166944-Lean/blob/f19ca71672488be5dd2e134351a4e275bcf06d5d/research/min_local_negative_first_cell_exit_audit.mjs), blob 3e0c961161baf3b4d2352e2197fd8f57baecb149. Six slabs R=12000..2000000, 622004 roots, 2366012 root/width controls; checks cell confinement, age/gain, first-exit and no-exit waiting inequalities, multiplicity and support. At R=2e6, T=2001:
    Q      no-exit fraction   no-exit or p>=S/4   proxy support lower   best per-cell actual weight
    6      .037029            .063273             3262.2116             15277.4638
    30     .081804            .139845             1373.8626             13940.2794
    210    .199632            .341085             415.4671              7579.2960
    2310   .585715            .786232             54.2853               867
Finite non-twin capacity on the expanded synchronized slab 3501.2104. None of the wait-bound-only lower certificates in this largest control exceeds it. Actual weights include existing twin centers; at Q=6 all weight comes from births. Large Q buys longer protected prefixes at the cost of greater multiplicity. No asymptotic near-square-root cohort bound inferred.

B. [Coarse prefix code audit f9785f7](https://github.com/tara-sooo/A166944-Lean/blob/f9785f7a37424d4f24cba01250e1dcd63199f9d4/research/min_local_negative_coarse_prefix_code_audit.mjs), blob 3a4df3b38c2b925115e2ab181f4d288cb49ba42d. Four slabs through R480000, 122004 roots, 2435016 completed root events, 1830060 prefix controls, exact reverse decodes, per-cell Kraft checks, Jensen and weighted support checks. For each Q=6,30,210, choose maximum q in the first 1,2,4,8 or all visited cells. At R480000 Q6, two cells: exact position score H(A|X)+E c=5.15639, code score 6.79364, weighted certificate 1353.4190; all cells: exact score 3.91285 but code score 24.43221 and weighted certificate 1189.8661. At Q210 all cells: exact score 3.91285, code score 7.59916. The simple universal code is too expensive for many actual nonadjacent transitions; the arithmetic candidate sets alone do not give the needed entropy asymptotic. A larger root-dependent observation range improves roughness but not necessarily the code-weight certificate.

C. [Coarse reverse flow audit 765df50](https://github.com/tara-sooo/A166944-Lean/blob/765df50ec00c303fb0e99f3c2e54acf761495aff/research/min_local_negative_coarse_reverse_flow_audit.mjs), blob 53e6098a3591f39fef44666f8a8dfcd91ff997ab. Six slabs, 622004 roots, 15877617 completed root events, 101117095 counted visit/capacity checks. Actual path visits, all-cell induction capacity, per-position weights, selected versus all-cell certificate. Largest control R2e6 Q6 alpha=.5 conditional adjacent=.75: all-cell certificate 9865.5898, best one per root 9739.9115, actual support 15297.0275, max cell weight .943118, finite non-twin capacity 3498.6369 (narrower elapsed-T slab than A). Ratio 2.81984. It includes known twins at births and is not asymptotic evidence. Five policies and three widths tested; this simple policy was best among those tested at each slab, not globally optimal.

The earlier signed boundary moment target and terminal/repeat time balance remain open. No unconditional twin infinitude proof or Lean formalization; no changes to main or sibling branches.