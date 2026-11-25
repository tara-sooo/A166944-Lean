# Joint forward/backward clock kernel and pooled long-wait birth capacity

2026-11-26 JST. Continues [7b846939ff42](https://github.com/tara-sooo/A166944-Lean/blob/7b846939ff42fc8a652c9f7585909cbd4a97aa9d/research/2026-11-26-min-unified-wait-birth-arrival-refinement.md), [56e329bc7ccc](https://github.com/tara-sooo/A166944-Lean/blob/56e329bc7ccc9da30d26e8e6981e07fdfb6589ec/research/2026-11-26-min-unified-birth-pair-lifetime-support.md) and [673f23837f86](https://github.com/tara-sooo/A166944-Lean/blob/673f23837f86cc5af8732aa01bd45923f5c04f3f/research/2026-11-26-min-unified-massive-word-partition.md). Independent source heads verified unchanged at preflight: prime-root 1a4005f2f336ede61cca1a9656c158a559338b72; stable-heavy e1ad9e2b434c652699e1bc9a0797887631e0ea6d. New: pooled long-wait birth capacity using arrival-time concentration, a single joint substochastic row/column kernel for BOTH backward compatible clock and forward defect clock across the low/high pursuits, and a joint two-sided reachability upper bound on the entire residual objective from original one-tag histories, word/slot populations and admissible destination sets. This is a direct upper-bound route, not another small deletion asserted to give a constant contraction. The required constant margin remains open. No Lean compilation.

## 1. Frozen quantities

Retain original dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Original prime roots M in [X,2X), C0(M)=2M-2, completed gain-stopped MIN paths with gain g=p-1 and wait 1<=w<=2r<=3g, gain per tag <H. Under finitely many twins eventually every original root reaches T, and W_all>=N(T-6)/2.

Use the full-partner route of 673f238 and all subsequent masks through 7b84693. Keep exactly the original grids P_j, number m=Theta(u/ell), P_max<=B^.25, P_min>=B^.125/O(u), a=u^.25, sharp good-cell capacity c_a=3(1+2/a). Phase wheel L0 largest even primorial<=ell, A=L0/2. Rank parameter tau>=1/log ell, tau->0. Same old original stable source slots and original phase populations n_c, b_v, a_v. Old low pursuit L_l=ceil(H A P_j/(a P_max ell tau²)) on usable grids, and high L_h=ceil(B exp(1/tau)); both are below original stable future room. All populations, masks and source charge fractions frozen. The old exact residual backward birth clock is B_wait,rem and the old exact residual full forward defect energy is D_all,rem. Under finitely many twins,
    NT/2-o(NT) <= B_wait,rem+(3+o(1))D_all,rem.
We will use forward energy in CLOCK units c_a D, not mix units in row/column estimates.

## 2. Pool all long-age births at one actual waiting episode

Let V=(J,q,v) denote an actual completed exit slot at prehorizon J with selected exit label q and departure v. For all full original members of this slot record their original arrival times t_i<v at J. Partition them into disjoint arrival-time sets A_i; unlike a true-birth branch key, this partition uses ALL arrivals to the same completed waiting episode. Root arrivals included. Define relaxed lifetime counts L_i(x)=# {M in A_i: C0(M)+H>x}, L(x)=sum_i L_i(x), for x>=J. They vanish for x>=J+H. One may instead use actual original terminal horizons for stronger upper estimates.

Any pair with a first meeting at J in which one is waiting and the other jumps, with waiting age h>R (R=floor(sqrt u) in 7b84693), must have two different arrival times at J with absolute gap >R. Both members execute the same eventual exit V by determinism and the common later source. Each such pair belongs to exactly one V, even if many different births occur in the same waiting episode. Keep all exact charges and all old masks; only pool the long-age wait-jump birth sector by V. Root injection as later arrival need not be included in the true long wait-jump sector; allowing it in the upper envelope is harmless.

For a fixed grid P and source boundary K>=J, the suffix from V can cross K at most once. Let x_i be the numbers of original members of A_i present in its actual source exit slot, x=sum x_i. If the source lies at V itself, the same statement holds. Then x_i<=L_i(K), x<=b where b is the full original source slot population, and any positive resampled compatible clock has b>=b_min of 590c137. At that boundary, the total backward long-age charge pooled at V is <=2 c_a P S(x_i)/b, where
    S(x_i)=sum_(i<j,t_j-t_i>R) x_i x_j
with times ordered increasingly. This uses the actual per-pair per-atom bound c_a P/b and both orientations. Each contributing pair has this first meeting, not a further meeting after convergence. All later source masks can only decrease charge.

Fix ANY interval I of arrival times of width R. There is no long-age pair with both arrivals in I. Write x_out=sum_(t_i notin I)x_i, x_in=x-x_out. Even granting every outside-outside pair, S<=x_in x_out+x_out²/2. Thus for x>0,
    S/b <= x_out - x_out²/(2x).
The function f(z,x)=z-z²/(2x) for 0<=z<=x is nondecreasing in both z and x (partial derivatives 1-z/x and z²/(2x²)). Choose I maximizing the sum of L_i(K) within I, and define
    M_R(K)=max_z sum_(z<=t_i<=z+R)L_i(K),
    S_R(K)=L(K)-M_R(K).
Then x_out<=S_R(K), x<=L(K), so
    S/b <= S_R(K)-S_R(K)²/(2 L(K)).
Define value zero when L=0. No monotonicity of S(x_i)/sum x_i for an arbitrary graph of allowed pairs is assumed (that general monotonicity need not hold).

Other simultaneous bounds are S/b<=L/2, S/b<=sum_long L_i L_j/b_min, and the pairwise harmonic sum sum_long L_i L_j/max(b_min,L_i+L_j), by applying 56e329b to each arrival-time pair. Therefore put
    F_R(K)=min( L(K)/2,
         S_R(K)-S_R(K)²/(2 L(K)),
         sum_long L_i(K)L_j(K)/b_min,
         sum_long L_i(K)L_j(K)/max(b_min,L_i(K)+L_j(K)) ).
Each term is nonincreasing in K: for the concentration term, S_R is the minimum over intervals I of their outside mass, all nonincreasing, and L is nonincreasing; use the monotonicity of f. This gives the simultaneous episode envelope
    Bbar_long(V) <= 2 c_a mean_P [ P sum_{K multiple P,J<=K<J+H} F_R(K) ]
                 <= 2 c_a [ integral_J^(J+H) F_R(x) dx + P_max F_R(J) ]. (1)
An additional old-ancestry lower restriction K>=J+D_s/2 can be incorporated in the sum. This upper bound is no larger than the corresponding sum of arrival-pair harmonic envelopes, and can be much smaller for a waiting episode with many arrival groups. In particular if an R-window contains all but an epsilon fraction of lifetime mass, F_R<=epsilon L. If all arrival times lie in one R-window, charge is zero.

The total B_wait,rem is unchanged by pooling. Do not substitute a count of individual arrivals for distinct episodes. For a long episode r(J)>R/2 by the old age bound. As an independent support fact, the number of possible true episodes (J,q,v) with fixed actual exit label q and r(J)>R/2 is O(XH/[q² log²(2+R)]): use the two-form sieve at J±1 in J=q h-sigma, exclude 2,q, then O(H/q) possible exits at fixed J from its single residue modulo 2q. The two-form proof is the one in 7b84693/aa04b0 with cutoff min(R^(1/40),q^(1/40)) unnecessary here; one can use R^(1/40) excluding q, as forms have distinct roots for every other odd sieve prime. There are O(X/q) parameter points, q<=B, R=sqrt u. This support fact and (1) can be combined without knowing every individual birth key. The total of (1) over episodes has not been shown small. The numerical envelope below remains quite loose even after pooling.

## 3. A common joint kernel for both pursuits and both transport directions

Fix one grid, projected crossing atom and original phase class of n=n_c tags. Let G_v be the full original physical slot of size b_v and S_v its stable subset of size a_v. Let n_stable=sum a_v. Use the actual per-atom assigned retained good focal clock w_i^l,w_i^h for original tag i (assigned source-cell waits divided uniformly over crossed atoms). Their sum w_i<=c_a P, zero for nonstable focal tags. These are the EXACT original full-partner route clock weights before compatibility and subsequent birth/defect payments.

On a grid with both pursuit lengths available, L_l>>L_h eventually uniformly: L_l>=H A P_min/(a P_max ell tau²)=B^(15/8-o(1)) whereas L_h<=B ell+1. Thus equality of longer words implies equality of shorter words. Every positive high row has a singleton physical-slot high word by d7cc573/673f238, and hence its longer word also contains precisely the same stable tags of that slot. It follows that for every positive high row, its compatible and different-word stable partner sets are IDENTICAL whether evaluated with its own high word or the longer low word. This is not a claim that the two partitions agree on all rows or that first defects occur at the same gain; the latter use the original sector pursuits. For a grid with low available use the longer word partition omega; otherwise use the high partition. Then BOTH active sectors can use the SAME two kernels:

    F_ij = 1/n if i,j stable and omega_i != omega_j, else 0,
    A_ij = a_omega_i/(n b_v) if i stable and j in G_v, v=slot(i), else 0.

F is forward differing-word pair weight in clock units; A is the backward compatible clock after the exact same-slot resampling of 590c137. In particular j in A need not itself be stable. F and A have disjoint supports because same physical slot implies same word. At each stable focal i,
    sum_j (F_ij+A_ij) = (n_stable-a_omega_i)/n+a_omega_i/n
                      = n_stable/n <=1.
For nonstable i the row is zero. The missing row mass is the unstable-partner part of 673f238.

For a stable column j in slot v, word omega, the F column sum is (n_stable-a_omega)/n and the A column sum is a_v a_omega/(n b_v)<=a_omega/n. For a nonstable j only the A term is present, also <=1. Therefore the nonnegative joint kernel K=F+A is substochastic in BOTH directions:
    sum_j K_ij<=1, sum_i K_ij<=1.                        (2)
Consequently the exact combined source measure w_i K_ij has row sum<=w_i and column sum<=c_a P. All subsequent payments, source-dependent masks and actual routing only reduce this nonnegative measure. This includes the old compatible concentration and boosted mass masks, the first-birth pair masks, all projected/true birth thin masks, and all forward thin masks. The new bound is one shared column capacity in CLOCK units, not two independent caps of c_a P each. It applies across both low and high sectors as well: use w_i=w_i^l+w_i^h and the common kernel identity for positive high rows. If high words were not singletons at active high sources, this combination of the two sector kernels would need a separate proof, and a naive sum of column caps could be larger. No change to the original pair selection rule or destinations.

An immediate application: for any original tag at an atom, its summed clock-unit involvement in BOTH routed directions, in either ordered role, is <=w_i+c_a P<=2 c_a P. A tag may occur in both roles and a pair may have diagonal A weight (later paid). This is a joint source budget; it does not say a backward target and forward target share the same destination or have the same pursuit length.

## 4. Direct joint reachability bound with no pair matching at destinations

Choose a set T_B of true birth states U=(t,J) containing the first meeting states of all desired residual backward charges. Choose a set T_D of projected PREhorizons E containing all desired residual forward first-defect destinations. These can include additional possible keys. For the full residual, one may choose the exact residual supports projected as above, or any independent arithmetic superset. Define masks for each original source tag i at its actual source atom K:

    B_i=1 if its original true history contains a state U in T_B at horizon J<=C_source-D_s/2,
    D_i=1 if its original completed future path from source posthorizon J_source has an event
        at a prehorizon E in T_D with 0<=E-J_source<L_max,
    L_max=max of usable pursuit lengths on that grid (L_h if only high).

When a source backward charge remains, both its pair members visited the SAME first meeting state U and satisfy the old-ancestry condition; hence BOTH B_i,B_j equal one. A backward resampled partner need not be stable at source; use its own original history. When a forward charge remains, at first defect both actual members have the SAME prehorizon E before either chooses its different or lag-changing edge. Even if only one member's selected label is eligible for the particular retained destination, projecting to E makes BOTH D_i,D_j equal one. Their original stable future room guarantees the completed events. The coarse projected target avoids an erroneous assumption that both selected labels or true times agree at the defect. For a more precise label-specific target a union/column bound can instead be used, but not the intersection bound with those sharper masks.

For each original phase class at one atom define
    beta_v = # {j in G_v:B_j=1}/b_v,
    d_tot = # {j stable:D_j=1},
    d_omega = # {j stable:omega_j=omega,D_j=1}.
All are one-tag history/future counts, not pair comparisons. From the exact kernels in section 3, the sum of CLOCK-unit desired remaining charges from this class/atom is at most
    Q_atom = sum_(i stable) w_i [
          B_i (a_omega_i/n) beta_(slot(i))
          + D_i (d_tot-d_omega_i)/n ].                 (3)
Indeed backward contributions can only lie in A on B_i=B_j=1, and forward in F on D_i=D_j=1. Both contributions use the same total w_i, not two copies of the clock; summing all partner coefficients gives the displayed expression. Discarded charges only reduce it. In particular
    Q_atom <= sum_i w_i 1_{B_i or D_i}
           <= c_a P # {original tags at this atom:B_i or D_i}.
The first inequality follows since each row of K has mass<=1, including when BOTH masks are true. This is a joint intersection bound with at most one clock contribution per original tag, unlike summing independent projected occupancy upper bounds for the two directions. It can be strictly smaller even when the union mask is dense, due to small beta_v or small different-word D population.

Sum (3) over all original grid boundary atoms/classes and average over the SAME m grids, denoting the result Qbar(T_B,T_D). Then for desired residuals (all, if target supersets are complete),
    B_wait,rem+c_a D_all,rem <= Qbar(T_B,T_D).          (4)
One may combine (4) with the long-wait bound (1) on that subset, or take minima with other valid upper bounds. The masks can be computed from each tag's own trajectory plus word populations, without computing all pairwise first births or first defects. No claim of reduced computational asymptotic complexity without specifying the support-building algorithm.

For a route independent of the EXACT charges, construct admissible target supersets as follows. For each birth type include true states of all arithmetically allowed pair keys not excluded by necessary branch size, age, lifetime upper envelope versus absolute cutoff, and old source eligibility (relax any uncertain extra condition). The pooled long episode envelope can exclude an episode only if it proves all relevant original key charge cutoffs (or an additional valid pooled payment with its own budget); do not infer that individual birth keys are paid merely because the aggregate envelope is relatively small. For forward, each sector has original n(C,p) and capacity Dbar_s(C,p)<=2 C_s' n(C,p) from the full route. Exclude a key if this capacity upper bound is below its existing absolute thin cutoff (or another already proved exclusion); include prehorizons of remaining possible keys. The target sets built this way contain the exact residual support, independently of unknown actual pair charges. Relaxations can make them large. In particular using T_B,T_D as ALL possible states/prehorizons makes (4) nearly the old source-clock bound and gives no contraction.

Under finitely many twins, previous exact partition and o(NT) masks imply
    NT/2-o(NT) <= Qbar(T_B,T_D).
Thus a direct sufficient test, for the complete residual targets, is
    liminf_(dyadic X) Qbar(T_B,T_D)/(NT)<1/2.           (5)
A cruder sufficient test is the average raw union occupancy in the final upper bound of (3) strictly below NT/6 (since c_a=3+o(1)); occupancy here includes the factor P per boundary/tag. The new test is a different sufficient upper-bound route, not a logically weaker condition than the preceding exact residual inequality, since Qbar is an upper bound. Its purpose is to obtain a constant-margin estimate through joint accessibility and class concentration without pairwise destination enumeration. Neither (5) nor the cruder occupancy threshold is proved. In particular neither a joint capacity alone nor a local improvement of (1) establishes a positive global delta. Main and independent source branches unchanged. No Lean compilation.

## 5. Finite audit

[Final standalone source](https://github.com/tara-sooo/A166944-Lean/blob/3817cae2f6ee2fcbc98c7a91ad973974876c5e6b/research/min_unified_joint_kernel_wait_episode_audit.mjs), exact remote content readback verified at that commit. Seven final-source runs passed in ECMAScript runtime, four ordinary and three focus. Reproduce: node research/min_unified_joint_kernel_wait_episode_audit.mjs 1024 4096 16384 65536. Finite T=min(8B,floor(X/2)) ordinary or floor(B/2) focus, grids [6,30,210], wheel6, raw cap c=9, finite L_l=floor(B/8), L_h=floor(B/32) with minima and ordering as code, actual room>=L_l instead of entropy, cut=3, R=8, Y=max(5,ceil(sqrt B)). Explicitly omits finite high rows if short word is not singleton; no such omission was needed in these runs. Computes original actual clock, common nested word kernels, both pair transports, backward first meeting by actual intersecting wait intervals, exact compatible/defect/unstable partition and combined column cap. For finite birth diagnostics pay diagonal, source slot <3, recent gain<2; pool h>8 non-root-later pairs by their actual eventual common exit slot, compute lifetime envelope (1) in discrete form and compare to sum of pairwise ARRIVAL harmonic envelopes, not the actual previous charged-key support. For target test choose independently fixed horizons divisible by 10, backward long sector with recent deletion, forward all actual word defects, compare actual target-routed clock to (3) and union mask. This arbitrary finite target does not cover all old analytic residuals, so the test verifies inequality for a selected subset only. No numerical test of analytic support construction, earlier cumulative masks, integral form, global sufficient test (5), literal gcd oracle or Lean. Final update adds target-mask verification; all seven runs repeated successfully.

Largest ordinary X=65536: 5709 roots,140255 completed events, no diagnostic T reaches, W=2395330, 19839 cached distinct tag first meetings. Across P=6,30,210 respectively combined column checks 65913,31059,9063; common-kernel checks 17404,17404,9289; actual forward defect checks 16317,7052,1644. Long-wait episode envelope checks 901,851,699. At P=6 actual long clock 516949.014950; pooled envelope118550864.385794 vs pairwise arrival envelope135631278.695901. P=30 pooled112782572.900266 vs129635090.522824; P=210 pooled91814752.434112 vs104638132.187360. The finite pooled upper bound remains orders of magnitude above actual long charge. Combined active-column capacity sum P=6 is20547918 vs separate active-column cap sum22174398; this compares raw finite capacity bounds, not actual clock totals or an asymptotic saving.

| P | selected target actual charge | joint intersection upper bound | union clock upper bound |
|---:|---:|---:|---:|
|6|232382.385963|1566566.515933|1766622|
|30|221188.057920|1547779.413030|1741126|
|210|203059.514373|1427226.061870|1563864|

Target intersection checks 144587,66794,17892 respectively. Largest focus X65536:2886 reaches,75256 events, W1238683, 7303 cached pairs; 51545 combined column checks,1454 pooled episode checks. P=6 selected target actual23814.932736 <= joint352210.180163 <= union532257. No inference of a global constant-margin upper bound; the finite diagnostic target is illustrative only. The mathematical contribution is pooled birth capacity and a shared upper-bound mechanism for the two clock transports.
