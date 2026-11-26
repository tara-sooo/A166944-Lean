# Hypothetical infinite MIN worlds XI: coupled prime-factor graph, reuse toll and rational factor strips

2026-11-26 JST. Independent continuation of [aef03d1](https://github.com/tara-sooo/A166944-Lean/commit/aef03d14e390358f0b9b0cc1583cd98376e74d61). Sources [V semiprime entry sieve](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md), [IX rational clock](https://github.com/tara-sooo/A166944-Lean/blob/9733fd234d882609b87ad2cef1fba038f93b5935/research/infinite-orbit/rational_clock.md), [X cofactor capacity](https://github.com/tara-sooo/A166944-Lean/blob/aef03d14e390358f0b9b0cc1583cd98376e74d61/research/infinite-orbit/cofactor_support.md). Sibling preflight direct [d8a84b0 mandatory cross-label buffer](https://github.com/tara-sooo/A166944-Lean/blob/d8a84b0a98c00f921b5d94dc9b341709034d00c5/research/2026-11-26-min-direct-mandatory-cross-label-buffer-transport.md), unified [79b2a00 source-preserving cross-buffer recycling](https://github.com/tara-sooo/A166944-Lean/blob/79b2a00f01bfc53eb80133830248d5afd0072c2e/research/2026-11-26-min-unified-cross-buffer-recycling.md). Here the two prime coordinates of a selected semiprime are treated jointly, including when a prime changes its role. This is separate from the direct causal height matching: neither result is a second independent credit for the same resource. Paper deductions and finite diagnostics, not Lean verification or a claim of external novelty.

## 1. The ordered factor graph

Fix a physical contiguous block of actual adaptive MIN events with pre-horizons H in [X,lambda X), fixed lambda>1. Select ANY ordered list of complete events for which
    p>=T>=eta sqrt X, p²<=H+1,
    H=pq+e, e=1-2s, q prime.
Here p is the actually selected prime, q the selected-neighbor cofactor; q>=p by eligibility and odd integral divisibility, as in X. Both are Theta(sqrt X), though q may exceed B=floor sqrt(lambda X+1). The selected prime p<=B. We assume T>=5, and use T->infinity for asymptotics. In particular every positive ordinary-deficit event 2w>p-1 in this band belongs to this class for sufficiently large X: all neighbor factors >=(p-1)/4, and three such factors (including p) exceed lambda X+1. The semiprime condition may also hold for short, reset and nonpositive events; no wait restriction is used in sections 1-3.

Associate the event with an undirected prime-factor edge {p,q}, oriented from smaller p to larger q, allowing a loop p=q. The graph here records ONLY actual visits along a ray. The products P=pq strictly increase over the selected list: if event i precedes j, H_j-H_i>=p_i-1 and P_j-P_i=H_j-H_i+e_i-e_j>=T-3>0. Hence no unordered edge occurs twice, including at opposite sides of the same product. This also bounds all visits whose factor support is in a set of s primes by s(s+1)/2; if separate selected-label and cofactor supports have sizes s_p,s_q, use min(s_p s_q,s(s+1)/2). Unlike a generic simple graph, each prime has the temporal role separation below.

Suppose prime v occurs as a selected label at an event. At that event P>=v². At every later event where v is the cofactor, P_later<=v² since the selected label is <=v. This contradicts strict product growth. Thus a prime may occur first as a cofactor and subsequently as a selected label, but NEVER as a cofactor after it has been selected. A square edge (v,v) is the sole possible equality P=v², and occurs at most once; thereafter v cannot be a cofactor. More precisely all strict cofactor occurrences of v have H<=v(v-2)+1, and all selected-label occurrences have H>=v²-1. In an interval [h,h+D] a prime appearing in both roles necessarily has v² in [h-1,h+D+1] (a square counts as both). The possible handoff primes lie in a translated interval of length O((D+2)/T+1), independent of the actual number of events. For D>=T^(1+epsilon) with fixed epsilon>0, the usual one-form translated upper sieve gives O_epsilon,lambda,eta(D/(T log T)) candidate primes. This is a count of handoff-prime identities, not the number of visits or the tag multiplicity. No assumption of statistical independence.

## 2. Shared-factor toll, including changes of role

For ANY two distinct visits i<j sharing a prime v, the difference of their products is a positive multiple of 2v: the other factor at each visit is odd, including square cases. Thus
    H_j-H_i >= 2v-2.                                 (1)
This applies across arbitrary other selected and unselected events, not just consecutive visits of v in one role.

If the two visits are consecutive in the selected list, write E=H_j-(H_i+p_i-1) for the physical intervening UNSELECTED gain. Then (1) gives
    E >= 2v-p_i-1 >= p_i-1.                          (2)
Here v>=p_i regardless of whether the shared factor is the earlier selected label or its cofactor. This improves the narrow-band same-cofactor bound of X for genuine semiprimes, and has NO narrow-band or wait hypothesis. Reuse of the earlier label, reuse of the earlier cofactor, and transfer from earlier cofactor to later label all fall under one toll. Sharing both distinct primes would imply equal products and is impossible.

If the earlier cofactor v>p_i is the later selected label, the product change is at least v(v-p_i), since q_j>=v. Hence there is a stronger directional bound
    E >= v(v-p_i)-p_i-1.                             (3)
In particular a cofactor-label handoff cannot occur via bounded relay at these scales. Equation (3) is useful when the prime gap v-p_i grows; it is not an assertion that any such handoff occurs. Conversely an earlier selected label becoming a later cofactor is impossible at any relay length by section 1.

Let k be the selected event count, F its gain, U all complementary gain. Partition consecutive selected transitions according to whether the two factor sets overlap. The relays are disjoint, so summing (2) gives the exact budget
    sum_(shared adjacent pairs i->i+1) (2v_i-p_i-1)
         <= U,
    sum_(shared adjacent pairs i->i+1) g_i <= U.       (4)
One may replace the individual bound by max of (2),(3) where applicable, without adding the two. In particular the number of shared adjacent pairs is <=U/(T-1), and for the complementary adjacent pairs with disjoint factor sets the source gain is >=F-U-(B-1). For any fixed delta>0, pairs with E>delta T have source gain at most (B-1)U/(delta T). Consequently if F>=rho X and U=o(X), all but o(k) consecutive selected transitions have disjoint factor sets AND E<=delta T, for each fixed delta>0. Their source gain is F-o(X), since B/T=O(1). A variant with E=o(T) is obtained by choosing delta(X)->0 sufficiently slowly that U/delta=o(X). This identifies a necessary dominant population with FOUR distinct primes in close successive semiprime events, even if both individual prime supports grow without bound. Nonadjacent factor reuse is still possible and is not charged to the complementary U.

For an original tagged family one may sum (4) once per selected list on each tag, weighted by its actual nonnegative multiplicity/weight. No independence of tags or disjoint physical trajectories is required. If the selected list contains only positive semiprime events then short high events outside it are part of U; this is not a bound for the arbitrary all-high population if many selected short events have composite cofactors. A macro positive population with U=o(X) is a particular hypothesis, not a consequence of finite twins or unified. Even in that population disjoint-factor transitions may be plentiful.

## 3. Local incidence capacity

Equation (1) also implies that, for every fixed v, its visits in any pre-horizon interval of length D have count <=1+floor((D+2)/(2v)). Proof: first-to-last horizon span is at least 2v(m-1)-2 by product differences. This one bound includes both roles and squares, rather than allowing separate full capacities for label and cofactor. If Pset is the distinct prime support and k_sq the number of square edges, the total factor-incidence count is 2k-k_sq. Hence
    2k-k_sq <= sum_(v in Pset) [1+floor((D+2)/(2v))].
For D<2T-2 every pair of selected events in the interval has disjoint factor sets. At larger D this is an interval packing bound, not a bound on global graph degree independent of D. Since k_sq is at most the number of primes with v² in the interval enlarged by 1, there are O(D/(T log T)) such square candidates on D>=T^(1+epsilon). At macroscopic scale the total square-event gain is O(X/log X), even allowing all waits. This follows from the one-form upper sieve (or the prime number theorem globally).

## 4. Rational strips in prime-factor space

The new question is whether a high population can realize its required factor diversity while keeping the two factors in a near-fixed ratio, e.g. p almost equal to q. This is DIFFERENT from IX's ratio of clock and horizon. Fix coprime positive integers u,v (u/v>=1), independent of X. Write
    m=v q-u p.
Consider only events satisfying |m|<=K for an integer K>=0, possibly depending on X. The exact zero line m=0 has no prime pairs at high scale unless u=v=1 and q=p: since v|p and p grows while v is fixed, v=1; then q=u p prime forces u=1. The square case already costs at most O(X/log X) gain.

For each nonzero m, all integer solutions p,q to vq-up=m form one affine progression
    p=p_0+v z, q=q_0+u z.
At each odd prime f>2 not dividing uv m the two linear forms have distinct forbidden roots modulo f (determinant m). Omit primes dividing uv, the fixed small primes and those dividing m. Use the fixed-dimensional translated Selberg upper bound from V/direct with two forbidden roots at the remaining primes. In a global window the z interval has length O(T), padded to N=ceil(C T) for fixed C; sieve cutoff floor(T^(1/24)) is below both p,q. The O(z_cut^6) error of that bound is absorbed in N/log² T. Uniformly in nonzero m, the number of possibilities is
    <<_(u,v,lambda,eta) T J_2(|m|)/log² T,
    J_2(n)=prod_(f prime>2, f|n)(1-2/f)^(-1).
This upper counts prime pairs without requiring opposite-neighbor roughness or actual MIN times, so it is valid for every actual ray. The exceptional factors for uv are fixed constants.

The mean singular factor is bounded: J_2(n)=sum_(d|n) a_d with squarefree d, nonnegative multiplicative a_d and a_f=(1-2/f)^(-1)-1=O(1/f) for f>2 (a_2=0). Then
    sum_(1<=n<=K) J_2(n) <= K prod_(f>2)(1+a_f/f) << K.
Sum over nonzero positive and negative m with |m|<=K, both sides e, and weight each event by at most B=O(T). At most one actual visit per product (section 1); even counting both sides is an upper bound. Thus the gain on any actual ray from the rational strip is
    F_strip <<_(u,v,lambda,eta)
              X K/log² X + 1_(u=v=1) X/log X.        (5)
If K=0 and u/v !=1 the count is zero eventually. For arbitrary K the upper can be capped by actual total G=O(X). No opposite-neighbor roughness gain is claimed beyond the two prime forms. The same estimate for a FIXED finite collection of reduced rational ratios follows by summation, with constants depending on that collection.

In particular a macro semiprime high population cannot concentrate on |vq-up|=o(log² X) for any fixed finite collection of ratios, regardless of all relay budgets and deficit magnitudes. Equivalently the union of strips |q/p-u/v|<=o(log² X)/sqrt X (fixed factors v) carries o(X) gain. Near the diagonal q=p, this excludes a macro population with q-p=o(log² X), including squares. The argument requires actual prime cofactor; it cannot simply be applied to all fast high events. The relative width tends to zero; it does NOT exclude concentration within any fixed positive-width ratio interval.

## 5. Uniform localization and original-tag transfer

Let the pre-horizons lie in ANY translated subinterval of length D inside [X,lambda X), with D>=T^(1+epsilon), fixed epsilon>0, D=O(X). At fixed m,u,v,e, along the affine lattice above, the product increases with p and q, and between two valid candidates the product difference is at least T(v+u) times the z difference, since both factors >=T. Thus valid z lie in an interval of length O(D/T+1), padded to N=ceil(C(D/T+1)). Use cutoff floor(min(T,N)^(1/24)); log cutoff is comparable to log T (constants depending epsilon), and its sixth power <=N^(1/4). The same two-form bound gives O((D/T) J_2(|m|)/log² T), uniformly in translate, also for negative or large m (no loss depending on m except J_2). In the diagonal square case, p lies in an interval of length O(D/T+1), and a one-form sieve gives O(D/(T log T)) candidates. Therefore the actual strip gain in the subinterval satisfies
    F_strip(D) <<_(u,v,lambda,eta,epsilon)
                D K/log² X + 1_(u=v=1) D/log X.      (6)
This holds even in the short original-lifetime scale D=X/polylog X and for arbitrary physical subsets of selected events in that lifetime. Summing over original tags, if each lifetime has span at most D, gives O(N D K/log² X+N D/log X) for a fixed finite ratio collection. No shared-trajectory independence, no new boundary credit, no omitted-mass conclusion. Not applicable with the same logarithms to the much shorter D=Theta(T log² T) recycling bins of the latest direct/unified work; one can retain log(2+min(T,D/T+1)) instead and a padded (D+T) prefactor. We do not assert a stronger log² T saving on such short bins.

The two results give complementary necessary conditions on a hypothetical macro semiprime high population with little complement: most adjacent factor edges must be disjoint with very short intervening gain, and its joint factor ratios cannot stay in finitely many logarithmically thin rational strips. They do not establish a bound on general four-distinct-prime transitions. It remains possible for a population to use many prime identities and broadly distributed ratios.

## 6. Finite diagnostics and preservation

[Audit 093f8f1](https://github.com/tara-sooo/A166944-Lean/blob/093f8f102713472c41af332ddae3bb75e2cf90fc/research/infinite-orbit/factor_pair_audit.mjs), blob63cec28ee30c4eea7ab99d031d509706bc3699df, exact remote readback. Run node research/infinite-orbit/factor_pair_audit.mjs. Actual ECMAScript executed in available runtime, not separate Node. All assertions pass.

X=4096,16384,65536, pre H in [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1). All 64,512 canonical odd roots in those windows and 9,959 targeted intermediate starts with valid exact high arrival clocks, shortest/longest waits and three arrival-position samples at sparse horizons. Targeted starts have no established canonical ancestry. 74,471 total start incidences, 74,191 actual finite stops, 280 exits, zero cap unresolved; 1,616,573 actual MIN events. 85,254 high visits, 74,841 actual prime-cofactor visits, 40,565 positive-drift high visits (40,563 semiprime; two finite exceptions), 629 square-edge visits. 126,037 roughness checks, 33,827 prime-cofactor certificates where the explicit cube inequality holds; 162 independent literal tick gcd checks.

Three list configurations on each path: all semiprime high, positive semiprime high, narrow semiprime p<=floor(1.5T). 84,534 nonempty lists, 59,553 consecutive pair controls, 1,142 adjacent shared-factor toll checks, 2,218 arbitrary-distance repeated-factor controls, 84,534 aggregate nonreuse controls. Zero cofactor-to-label switches observed; the directional estimate (3) is paper algebra, not exercised by an actual switch in this scan. The role-order restriction was checked on every list. No distinct physical count is inferred by summing overlapping list/source incidences.

| X | all-semiprime pairs | shared | positive-semiprime pairs | shared |
|---:|---:|---:|---:|---:|
|4096|3341|96|1447|19|
|16384|7454|81|2972|52|
|65536|25679|320|11065|37|

Actual canonical shared-factor example X4096:
    H=7068,t=3607,p=37,q=191,s=0,w=19, J=7104;
    H=7140,t=3660,r=37,q_next=193,s=1,w=5.
Relay E=36 exactly equals 2*37-37-1=36. Actual canonical close disjoint pair: H=4140,p=41,q=101,s=1,w=11, then H=4182,p=47,q=89,s=1,w=23, E=2. These demonstrate the distinct alternatives, not the macro hypothesis U=o(X).

Independent integer-lattice census (NOT actual MIN events): enumerate all prime products pq with p in [T,B], q>=p and H=pq+-1 in the window, compare with direct affine parametrization at m for ratios 1,3/2,2,5/3,3,4/3 and K=0,2,8,32. 72 global set equality controls; 6,964 candidates on each enumeration route (overlapping strips), 216 translated-bin count equalities at D=ceil(X^.75) with three offsets. Counts include both sides, even if not eligible first clocks; they are necessary candidates only. At X=65536 all such product/side candidates number 11,642; diagonal strip K=0,2,8,32 has 86,100,174,500 candidates; ratio 3/2 has 0,24,106,350. These finite exact censuses test parametrization/localization, not the asymptotic sieve constants or macro supply. No Lean kernel verification.

## 7. Remaining problem

This closes neither the full joint graph capacity nor the deep fast branch with composite cofactors. The dominant disjoint-factor transition class under small complement may contain enough four-prime configurations; the ratio-strip bound only rules out concentration at very narrow rational factor ratios. Next: investigate simultaneous clock and product equations for close four-distinct-factor transitions, and use actual upward-to-downward matched pairs from the sibling lanes without assuming the downward cofactor is prime. Alternatively construct a relaxed survivor using diverse factors and test it against this strengthened registry. No full all-constraint infinite survivor, uniform uncapped mixed-run bound or finite-twin contradiction. Main and sibling branches not modified by this work.
