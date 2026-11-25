# Negative-drift discounted boundary certificate and all-label rough projected support

2026-11-26 JST. Continues [5249a07f2773](https://github.com/tara-sooo/A166944-Lean/blob/5249a07f2773d4a7b9c28ecfb7542cdca40f5649/research/2026-11-26-min-unified-weighted-boundary-flux.md) and [26afc6c22b41](https://github.com/tara-sooo/A166944-Lean/blob/26afc6c22b41bfe11caff113b7ba21cec618d786/research/2026-11-26-min-unified-recycled-flux-certificate.md). Independent heads checked unchanged: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New: credit actual or guaranteed negative drift against even previously admissible boundary flux, retain threshold 1/4, all-mass payment of relatively small-r long crossings including part of the previous short sector, and a uniform two-stage projected rough support sieve with label-dependent caps including short labels. No proof of the final upper inequality or Lean compilation.

## 1. Adaptive boundary credit

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Original prime-root MIN completed prefixes, through first crossing T or original stop. For an event at C, selected odd p<=B, gain g=p-1, wait w<=2r<=2p, deficit increment delta=2w-g, negative increment D=(-delta)_+. Total gain G<H, deficit nonnegative, initial 6. Under finitely many twins all original tags reach T eventually. Use P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1). Let y be the largest prime dividing P, y=Theta(u), P>=B^.25/O(u). Grid flux f0=P n where n is number of strict crossings C<=K<C+g. Every crossing requires p not dividing P and hence p>y. Old admissible means p<kappa P or r>=g/u. Old bad means neither; then D>0 and f0<=cstar D.

On every original event define a NEW consumption weight gamma:
    gamma=f0/D on old bad events;
    gamma=min(1,f0/D) on old admissible events with D>0;
    gamma=0 on all remaining events.
Thus 0<=gamma<=cstar and gamma=0 whenever there is no crossing. For an admissible event define discounted flux f=f0-min(f0,D)=max(0,f0-D). For an old bad event f=0. This is f=f0-gamma D in both cases. Use the same original frozen LIFO level matching, with NEW charge c_ij=gamma_j |L_ij|. In particular the new charge ledger is different from the old targeted ledger; do not assume its old thin-source or pair payments remain valid without proof. Write R_new for the total new noninitial matched charge, I_new for initial stock. The exact identity is
    sum f + R_new = P n_all - I_new,
    0<=I_new<=6cstar per original tag.
No trajectory, matching, or terminal is altered. This credits previously admissible negative-drift crossings, not just old bad ones. The added matched charge is an intermediate accounting quantity, not part of the final objective.

## 2. The source-cell excess argument transfers

Let k be the first crossing event at or after a positive source i carrying any new charge to sink j. Such k exists and k<=j. If k=i, it is old admissible (positive delta implies r>g/4). If k is old bad and i does not cross, total gain from source prehorizon to k prehorizon <=P, so cumulative positive drift <=5P; old bad drop >=(1-4/u)(p_k-1)>5P eventually. Every level born at i is then gone no later than k. Because all nonzero gamma sinks cross, j=k. This charge is the SAME as the old charge on that sink, since gamma unchanged on old bad events. Its source label <=P+1, sink label >=kappa P, intervening gain <=P. The earlier disparate short-pair mask (rho=ell) bounds all such first-bad charges by U_bad=O(NT/ell). This argument does not use a bound on the other new charges. Discard just these charges, and let R' be the rest.

For source i put E'_i=(R'_i/cstar-3g_i)_+ <= E_i=(delta_i-3g_i)_+<=4. Disjoint positive-source and negative-sink gain intervals give
    R' <= cstar(3G+sum E'_i)/4
on every tag, as in 5249a07. Every source of R' is assigned to its old-admissible first crossing k. Let l_k be total gain of the immediately preceding noncrossing events since the prior crossing or root, so l_k<=P. By the forbidden-word lemma in 5249a07 (sum E_i<=L+4 on any contiguous segment), the assigned excess at k is <=l_k+8 including its own E_k. Summing the exact new ledger and this bound yields, over all tags,
    sum_admissible (f_k+cstar(l_k+8)/4)
      >= (1-3cstar/4) sum G - NP - 6cstar N - U_bad.
There are at most NH/P+N crossing events, l_k sums O(NH), and cstar=1+o(1), hence under finitely many twins
    J_actual := sum_admissible (max(0,P n_k-D_k)+l_k/4)
       >= (1/4-o(1)) NT.                                (1)
Compared to the preceding cell objective this is a pointwise decrease: the difference on each original event is min(P n_k,D_k). For n_k>0 split the objective uniformly into the n_k original crossing atoms. Thus each actual atom has weight between 0 and 5P/4. The same frozen boundary masks of 5249a07 transfer at at most 5/4 times raw flux cost. They need not be recomputed.

There is a projected upper envelope using only prehorizon and selected label: D_k>= (g_k-4r(C_k))_+, since w<=2r. Set
    f_proj = max(0,P n-(g-4r)_+)
on old admissible crossings and zero on old bad. Then
    J_proj=sum_admissible (f_proj+l_k/4)
satisfies J_actual<=J_proj<=old F_cell, also pointwise for uniformly divided atoms. Each of their corresponding residual inequalities liminf J_rem/(NT)<1/4 suffices, for any already justified identical frozen boundary masks; the old F_cell condition implies the projected condition, which implies the actual condition. Strict separation on asymptotic realized MIN trajectories not claimed. For an objective entirely determined by the projected crossing event, use f_proj+P/4 instead of f_proj+l_k/4, uniformly divided by n. This dominates J_proj and is <= old F_count. No waiting time or level matching is needed to evaluate that projected objective.

## 3. All-mass deletion of relatively small-r long jumps

Choose kappa'=u^(1/8), epsilon=u^(-1/8); kappa' grows but kappa'/kappa->0. On old admissible crossings with p>=kappa' P and r<=epsilon g, one has g-4r>=0 eventually, P n<=g+P. Therefore
    f_proj<=4r+P<=4epsilon g+P.
The fully projected weight f_proj+P/4 is <=4epsilon g+5P/4. Sum over original events, using disjoint gains and count <=NH/(kappa' P-1), to get O(NH(epsilon+1/kappa'))=o(NT). This is an all-mass deletion for BOTH discounted objectives, even if a projected cohort contains every eligible root. It includes an entire range formerly in the short sector kappa'P<=p<kappa P and small-r part of the previous rough sector g/u<=r<=epsilon g. Neither of these was payable solely from the previous rough cap. Do not delete their raw undiscounted flux; only the new objective is small.

For all other p>=kappa'P, the cell addition P/4, including any difference between P and l_k, totals O(NT/kappa')=o(NT). On short p<kappa'P retain P/4, a projected overestimate. Consequently a history-free sufficient objective is
    J_star=sum_(old admissible remaining after weak-long trim)
           [max(0,P n-(g-4r)_+) + (P/4) 1_(p<kappa'P)].
The old admissible condition is still used for small p, and automatically holds for retained long p eventually because r>epsilon g>g/u. J_star is an upper envelope for the actual discounted residual up to o(NT), with nonnegative original boundary atoms and weight<=5P/4 per atom. It is pointwise <= the preceding sector objective F_R+(5/4)F_S, since kappa'<kappa; this comparison uses the same old masks. Under finitely many twins J_star>=NT/4-o(NT). Thus its residual criterion with threshold 1/4 is valid. The new objective is not a proof that short crossings are negligible.

## 4. Uniform two-stage rough projected support, including SHORT labels

The earlier 26afc6c rough support sieve counted p>=kappa P only. We extend to every p>y with r(C)>=g/log(2+p), including small/short labels, with a cutoff that adapts to p. A necessary key (K,C,p) satisfies K multiple of P, a=K-C even in [0,p-2], and p|(C+sigma), sigma=+/-1. For fixed K,p,sign at most one a is possible. In the full O(X) horizon domain, let z=floor(p^(1/40)) and z0=min(y,z). For all sufficiently large X, p>y->infinity and z<g/log(2+p). Thus all odd primes <=z avoid dividing C±1, by the roughness predicate.

First, because K divisible by all primes <=y, the two forms a-1,a+1 avoid all odd primes <=z0. On the even a interval of length O(p), the dimension-two Selberg upper sieve gives at most O(p/log²(2+z0)) values of a. Its error O(z0^8) is absorbed since z0<=p^.025. For bounded sieve cutoffs the same estimate with an enlarged absolute constant follows trivially. This step works even if z<y: no missing large-prime sieve is needed.

Second, for fixed a,p,sign, CRT gives one progression K modulo Pp, since p>y. Its parameter length is O(X/(Pp)) with a containing interval of comparable length and X/(Pp)>>B^.75. On this progression the quotient (K-a+sigma)/p and the opposite neighbor K-a-sigma are affine functions of the parameter with slopes P and Pp, respectively. At any odd prime t with y<t<=z both slopes are invertible and the two forms have distinct roots, since their relation is multiplication by p and translation -2sigma. They avoid these primes by roughness. For z>y, the same Selberg upper sieve gives an upper density O((log(2+y)/log(2+z))²); for z<=y use the trivial bound with density 1. The usual explicit quadratic weights (dimension two, squarefree divisor support <=z) give remainder O(z^8), absorbed uniformly by X/(Pp) times that density. For completeness, the denominator sum of squarefree products of 2/(t-2) over good primes with product<=z is bounded below by a constant times (log(2+z)/log(2+y))² when z>y. If y exceeds z^a0 for a fixed small a0, that ratio is bounded and the d=1 term suffices. Otherwise restrict primes to y<t<=z^a0; their product expansion normalized as a probability measure has independent inclusion probability 2/t. Expected log product is O(a0 log z), so at least half the mass has product<=z by Markov for sufficiently small a0. Mertens product gives the required lower bound. The same all-odd-prime argument applies to the first sieve. No lower bound on prime tuples or observed key density used.

Multiplying both estimates and summing signs,
    # rough keys (K,C,p) for fixed p
       << [p/log²(2+z0)] [X/(Pp)] [log²(2+z0)/log²(2+z)]
       << X/[P log²(2+p)].                               (2)
The cancellation of log²(2+z0) is the point of the two-stage argument. No need that log p=Theta(u). This covers even p just above y, where only the first sieve may be effective. The cutoff and progression size ensure the estimate is uniform. All retained long crossings from section 3 satisfy this rough predicate eventually, since log p=Theta(u) there and epsilon >>1/log p.

## 5. New label-dependent projected caps

For each fixed boundary key (K,C,p) aggregate the remaining J_star atom weights over original tags. Each original tag contributes at most 5P/4, hence effective mass n_eff=aggregate/(5P/4) is no larger than the number of actual contributing tags. Pay the entire remaining weight at a key when n_eff is at most an applicable cap below. All caps and masks refer to original frozen keys and objective weights, not revised trajectories.

For every p>y (rough or not), use the trivial per-p support O(X/P) (at most two C per K and p). Use
    m_plain(p)=H/(p u ell²).
The total cost <=O(XH/(u ell²) sum_(p>y)1/p)=O(NT/ell). This improves the old uniform short cap H/(kappa P ell) for sufficiently small p (ratio kappa P/(p u ell)).

For rough p>y use (2) and
    m_rough(p)=H log²(2+p)/(p u ell²).
Total cost likewise O(NT/ell). At p near the old short threshold kappa P the improvement over the old short cap is of order u/ell; for smaller p it may be much larger. For rough p>=P^(1/2) use the stronger
    m_mid(p)=H log²(2+p)/(p u ell),
since the prime reciprocal sum over P^(1/2)<=p<=B is O(1) (log P=Theta(u)). Cost O(NT/ell). In particular at p comparable to P this cap is Theta(Hu/(P ell)), versus old H/(kappa P ell), a factor Theta(kappa u). This comparison concerns effective mass in the new ledger versus old actual mass; it does not assert identical realized key weights.

For all retained long crossings p>=kappa'P, log p=Theta(u); summing (2) over p<=B gives O(XB/(P u³)) support. Use the old strong rough cap
    m_long=Hu²/(B ell)
now also on retained long p below kappa P. Total cost O(NT/ell). Take maximum of applicable caps, with previously justified old masks by priority; the union cost is still O(NT/ell). There is no hidden sum over dyadic p scales: the displayed reciprocal prime sums are the entire budget. Unrestricted nonrough short keys remain, as do heavy rough short and long keys. No claim that most raw flux is paid.

## 6. Remaining sufficient condition

The actual discounted objective is bounded above by the projected one and J_star up to O(NT/kappa') after the weak-long trim. Both the old and new projected thin payments are o(NT). The new sufficient condition is therefore
    liminf_(dyadic X->infinity) J_star,rem/(NT)<1/4.
It is implied by the previous sector-weighted condition for identical old masks, with further justified deletions. The actual discounted-cell criterion is still weaker than the projected upper envelopes at the same threshold. The proof only provides reductions and the lower bound under finitely many twins; no arithmetic upper bound below 1/4 has been obtained. In particular nonrough short crossings p<<P can have weight comparable to P regardless of their gain, and huge projected masses remain possible in the available estimates. Main and independent branches unchanged; no external novelty claim or Lean compilation.

## 7. Finite diagnostic audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/f33d125f23737b5726e87cb4d0124fe892a6caf3/research/min_unified_discounted_boundary_audit.mjs), exact remote readback at f33d125f23737b5726e87cb4d0124fe892a6caf3. Eight runs in ECMAScript runtime passed (five normal, three reach-focused). Reproduce:
    node research/min_unified_discounted_boundary_audit.mjs 256 1024 4096 16384 65536
Finite T=min(8B,floor(X/2)) or floor(B/2), P=6 or 30, kappa=2, old bad r<g/8, kappa'=1.5, epsilon=.25, cstar=4. Uses actual per-tag max gamma for packing tests; all first-old-bad charges deleted in finite ledger, including finite disparity exceptions. Checks original event geometry and actual/guaranteed discount domination, exact new LIFO charge identity, first-crossing assignment, disjoint endpoint packing and effective excess at most l_k+8 using the prior forbidden-word lemma, finite weighted lower bound before replacing excess with l_k, weak-long per-event and total gain inequality, projected atom aggregation and illustrative thin key payment (aggregate<=2P). Rough keys grouped by actual r>=g/log(2+p). No exhaustive relaxed support census or numerical test of sieve asymptotics, analytic caps, history-free J_star, prior cumulative boundary masks, literal gcd oracle, or limiting 1/4. Finite cell inequalities are diagnostics, not proofs of those analytic statements.

| X/mode | old cell | actual discounted cell | projected discounted cell | weak-long projected trim |
|---:|---:|---:|---:|---:|
|256|2835.5|2197.5|2801.5|98.5|
|1024|9139|7235|9069|279|
|4096|81518|65234|80988|2095|
|16384|470127.5|376305.5|464139.5|21911.5|
|65536|2898517.5|2392555.5|2870743.5|86304.5|
|4096 focus|38589.5|32327.5|37777.5|291.5|
|16384 focus|235941.5|201755.5|232275.5|4346|
|65536 focus|1568847|1344557|1548101|21736.5|

Largest normal: 5709 roots,140255 events, no full reaches, 25026 old admissible negative-drift crossing events. Actual discount505962, guaranteed projected discount27774; 3095 weak-long original events, gain111130, paid projected cell86304.5. New matched charge691260.986045, first-old-bad2591.111478 (no finite disparity exceptions), effective excess19185.563473,46605 source and38166 cell checks. After weak trim projected sum2784439 across82764 keys,81300 rough keys with weight2755383. Rough-short tag-boundary incidences39901, rough-long415231. Largest focus: 2886 full reaches,75256 events, actual discount224290, projected20746, weak trim21736.5. 19739 source and10399 cell checks; new matched charge265772.685522, first-old-bad4755.786957 including finite disparity exception6.666667. On reached tags finite lower bound278023.429083; actual discounted cell1073555.5, projected1239493.5. Diagnostic weights are not asymptotic estimates; particularly the finite kappa', epsilon and sieve rough predicate need not make every retained long event rough. No upper contraction inferred.
