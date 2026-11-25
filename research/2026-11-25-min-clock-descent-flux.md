# Physical post-state pair deficit flux and short-wait descent transfer

2026-11-25 JST. Continues 3bd47c5889e99949c2c66f456b9700b048b9780a (downward deficit cutsets) and 842e743d7219abf6ad143288fe22ea3f321f36e4 (upward deficit cutsets). New: an exact pair deficit conservation law, also separately at each integer level, using the actual physical post-state forest and expiration; a downward level second-moment bound valid even for arbitrarily short selected waits; a separate accounting of descent at pair birth; an unconditional small birth charge bound; and transfer to actual late clipped energy for same labeled post-state short-wait pairs. Does not establish the necessary full positive-drift bound or general heavy birth bound, nor the remaining projected energy or twin infinitude.

## 1. Actual physical forest and conventions

Use the original all-odd MIN short prefixes: dyadic X, N=X/2, B=ceil(sqrt(7X)), H=4B, a=2B, G=2H+B+6, original odd M in [X,2X), start (t,C)=(M+2,2M-2), K=floor((7M-1)/4). Assume H+2B<=min(K-M-2). Include first event post-state at/beyond relative H or terminal twin. Each selected p<=B, actual full wait w<=2r(C)<=2p, horizon gain p-1, total selected gain<=G, deficit d=2t-C in [0,12B+6]. An actual reset is a post-state d=6s where s=t mod2. All horizons in [2X,7X). Natural late weight is the intersection of full wait [t,t+w) with original relative [a,H), divided by 2r(C); R<=NB,E=sum r U². Existing natural MED and retained HIGH sufficient scales and LOW transfer unchanged.

Fix any subset of original roots. Form the graph of ACTUAL recorded physical post-states v=(t,J), including root and crossing/terminal states. Each v has at most one outgoing successor in this graph; deterministic MIN implies that all continuing tags at v have the same next event. The outdegree statement concerns this observed short prefix under the common range gate, not different future continuation beyond K. Strict horizon increase gives a forest directed towards successors. Distinguish the first COMMON RECORDED POST-STATE from the first meeting during a stationary wait (the latter may be earlier).

Let n_v be #original tags recorded at v, o_v be #tags continuing from v to its successor, n_e be actual tag count on incoming edge e=(u,v). Incoming edges partition nonroot tags; there is at most one root tag at v. All counts refer to original realized paths, not to new trajectories after pruning. Put P(n)=n(n-1), counting ORDERED distinct-root pairs, and define
    b_v=P(n_v)-sum_{e into v} P(n_e),
    x_v=P(n_v)-P(o_v).
These are respectively newly common recorded-state pairs (first such meeting) and pairs ending their shared recorded suffix at v (at least one root stops at v). They are nonnegative. Every pair once present in a common recorded state shares its subsequent events until the first stop. Thus each pair is born and expires exactly once. For v with no continuation o_v=0. The crossing state may lie beyond the actual relative H; the exact flux uses full original recorded waits, while section 5 uses clipped late occupation. It must not be read as a conservation law for a pair of separately clipped clocks.

## 2. Exact flux, including every integer level

For e=(u,v) put delta_e=d_v-d_u=2w_e-(p_e-1). Define
    A_shared=sum_e max(delta_e,0) P(n_e),
    D_shared=sum_e max(-delta_e,0) P(n_e),
    F_birth=sum_v d_v b_v,
    F_end=sum_v d_v x_v.
Summing (d_v-d_u) P(n_e) over edges and using P(n_v)-b_v=sum_in P(n_e), P(n_v)-x_v=P(o_v), gives
    D_shared + F_end = A_shared + F_birth.             (1)
In particular, for each individual ordered pair, D+d_last=A+d_first along its common recorded suffix. This applies irrespective of the number of resets, lengths of intermediate excursions, selected labels, or how small the waits are. Positive and negative drift at the event that first brings the pair together are NOT counted in shared edges of that pair.

For every integer lambda>=1 replace d_v by indicator(d_v>=lambda) in the same telescoping proof. Write U_shared(lambda), D_shared(lambda) for the ordered pair counts crossing lambda upwards and downwards on common edges; B(lambda)=sum_{d_v>=lambda} b_v, X(lambda)=sum_{d_v>=lambda} x_v. Then
    D_shared(lambda)+X(lambda)=U_shared(lambda)+B(lambda). (2)
This is exact layer-by-layer, not just after summing. Each shared downward crossing at a given level can be matched to a distinct earlier upward crossing of that level since pair birth, or to its initial occupancy of the level. Indeed the up/down indicator transitions alternate. An unmatched initial level can be used only once per ordered pair, even if the two roots visit many high descent blocks. Summing (2) over lambda recovers (1). The expiration term is a useful subtraction: it counts drift still present at the end of the common prefix and is not a descent expense. This applies to arbitrary subset of downcrossing witnesses from the previous cutset paper; matching all events is a deterministic upper envelope, not an independence assumption.

## 3. Downward witness second moment with the birth entry correction

For labeled physical post key (v,p) and level lambda let n_{v,p,lambda} count tags selecting p into v whose predeficit d is >=lambda>d_v. This counts full events, even those with short waits. For fixed v,p all predecessor horizons are J-p+1, but the predecessor times can differ. Let Q_down=sum_{v,p,lambda} n_{v,p,lambda}². The diagonal part L_diag=sum over actual tag-events max(-delta_e,0)<=NG. At a given (v,p), two tags in the SAME incoming edge contribute their shared negative drift; two tags in DIFFERENT incoming edges e,f contribute min(max(-delta_e,0),max(-delta_f,0)) and are born at v. Let J_entry be the total ordered distinct-child correction over same-label pairs. Thus exactly
    Q_down = L_diag + D_shared + J_entry.              (3)
For distinct incoming labels or a root child there is no same-label downward witness product at that birth. Formula (3) is not an assertion that every pair entering v through different children shares the previous physical wait. Their downward level overlap is evaluated directly from the two actual predecessor deficits.

Define J_entry,nr by restricting the entry correction to NONRESET post-states. For a nonreset downward p, p>=5 (p=3 never decreases), d_v>=2p, and each entry-level product is at most p-3<=d_v/2. Hence at every nonreset v its correction J_v<=d_v b_v/2. More precisely, for any birth pair contributing entry correction, d_v+its entry level count<=max(d_u,d_{u'}), since the entry count is min of the two positive drops (zero if either did not descend). For reset vertices take J_v,nr=0. Define the actual nonreset birth budget
    F_nr=sum_v (d_v b_v+J_v,nr).
A pair born at v is charged at most 12B+6 units in this budget, and at most 1.5 d_v. Restrict (3) to nonreset downward post-states and/or any actual assigned witness subsets (nonnegative counts no larger than the full groups). The resulting squared moment is bounded by
    Q_down,nr <= NG + A_shared + F_nr - F_end.         (4)
Here A_shared and F_end are those of the WHOLE recorded common suffix forest. The full negative flux includes reset descents, so replacing it by nonreset negative flux is an inequality. Do not discard the birth entry correction even when the two arriving tags select the same p: they may have arrived at their preceding horizon at different times. Equation (4) includes no inverse powers of the small-wait fraction.

## 4. Paying small birth charges and transferring to full upward occupation

For m>=1 set f_m(n)=n² for n<=m and 2mn-m² above m. It is convex, superadditive on nonnegative masses, and its derivative is bounded by 2m. At each physical v its merger increment is f_m(n_v)-sum_in f_m(n_e)-root_v f_m(1)>=0. Sum these increments over the forest: it telescopes to sum_v(f_m(n_v)-f_m(o_v))-N f_m(1), which is <=2mN since total n_v-o_v=N. At n_v<=m the increment equals b_v. Hence total b_v for such small birth vertices is <=2mN. For low-deficit birth vertices d_v<=m use the simple source separation bound: all pairs born share a horizon and their source distance <=G/2, so total b_v=O(NB). Charge <=1.5m per birth pair there. Taking the UNION of n_v<=m or d_v<=m,
    F_nr,small = O(NB m).
With m=floor(u^(5/2)), u=log B, this is o(XB u³). Remaining F_nr,heavy comes ONLY from births with BOTH n_v>m and d_v>m. It is a birth budget, not the count or future energy of the same pairs. No inequality on unrestricted heavy birth charge has been obtained. Note that at a nonreset physical v with two different positive incoming labels p,q>=5, 2pq divides d_v-6s; thus if p,q>sqrt(6B+3) they cannot both occur there. At reset v, d_v<=6, the birth deficit budget is already small (and reset entry correction was excluded). Heavy birth therefore retains the same-label case and mixed-label cases with at least one smaller label. This observation does not cap masses of those cases.

Let E_+^full be the ALL-LABEL projected quadratic occupation of actual positive-drift events with full, UNCLIPPED natural weights w/(2r(C)), including the cutoff-crossing wait. Let E_+,off^full exclude its diagonal. For positive drift, w>(p-1)/2>=p/3, r<=p, so
    delta_e<=2w<=24 * r(C) [w/(2r(C))]^2.
For each edge multiply by P(n_e); at a fixed pre-horizon, edge groups consist of disjoint sets of original tags (each tag visits C at most once). Summing shared edge contributions thus gives
    A_shared <=24 E_+,off^full <=24 E_+^full.
Together with (4),
    Q_down,nr <=24 E_+,off^full + F_nr,heavy - F_end
                 + O(XB u^(5/2)).                     (5)
This gives a full-prefix upstream-energy relation even for the short-wait witnesses not handled by the previous rough downcrossing second moment. It uses ALL positive labels, not only the rough HIGH or MED ones, and cannot be substituted for the existing late-slab sector estimates. Subtracting F_end is exact in the preceding flux identity; (5) may be loose due to positive-energy majorization.

## 5. Cheap descent gain and actual late energy

Let 0<eps<1/2. Call an actual selected event cheap if its FULL wait w<=eps(p-1). Such an event has negative drift and drop >=(1-2eps)(p-1). Consider all ordered distinct-tag pairs selecting the SAME p into the SAME nonreset physical post-state v, with BOTH selected waits cheap. This includes pairs in a common incoming edge, and pairs born through distinct pre-times at the same pre-horizon. Define the gain quadratic moment G_cheap,nr by summing p-1 over these actual pair incidences. It is not an occupation energy. Each pair contributes at least (1-2eps)(p-1) shared downward levels at that post key, whether it was already common or newly born. Hence
    (1-2eps) G_cheap,nr
        <= D_shared + J_entry,nr
        = A_shared + F_nr - F_end.                    (6)
The left restricts to cheap nonreset same-label pairs, while the right permits all common-edge negative drift. Equation (6) resolves the lack of a lower bound on their full wait; no factor eps^-3 as in the rough-only estimate. It does not say G_cheap,nr is negligible. The analogous bound for reset entries needs their separate J_entry rather than the small-deficit argument.

For an actual late-slab pair of the same class with clipped weights z_i,z_j, their common predecessor horizon has r(C) and full waits w_i,w_j. Since z_i<=w_i/(2r)<=1 and likewise for j,
    r z_i z_j <= min(w_i,w_j)/2 <=eps(p-1)/2.
Therefore the actual late ordered offdiagonal energy C_cheap,nr of these pairs, in any sector or smaller proportional mask, satisfies
    C_cheap,nr <= eps/[2(1-2eps)] *
                      (A_shared+F_nr-F_end).           (7)
Using (5)'s positive energy majorization and birth split gives an upstream sufficient estimate for this specific actual occupation class. This remains true for original root pruning. No general same-horizon assertion for pairs selecting different post keys is made.

For completeness, if one wants to include pairs with only ONE cheap endpoint at the same labeled nonreset post key, let U_alpha be all actual late weights at that key, V_alpha cheap weights. Put E_post=sum r U_alpha²<=E (disjoint actual key assignment at each C), E_V=sum r V_alpha²<=C_cheap,nr+R (the cheap diagonal costs <=R). The energy incident to cheap weights WITHIN these keys is <=2 sqrt(E_post E_V)<=eta E+E_V/eta, eta>0. This handles an arbitrary expensive partner at that key, not other post keys. For example, if the stronger upstream estimate A_shared+F_nr,heavy=O(XB u³) were available, choose eps=u^-1/8 eventually, eta=sqrt(eps): then (7) and the diagonal bound give o(XB u³) additive error plus o(1)E. This is conditional; the full-prefix positive energy and heavy birth budget are currently uncontrolled at that scale. The audit measures actual same-key mixed products, but not this hypothetical asymptotic estimate. Existing linear clock deletion for cheap events is separate: no general license to discard natural MED or its assigned LOW destination clock. Neither (6) nor (7) bounds arbitrary asynchronous different-key pairs.

## 6. Actual verification

Standalone research/min_clock_descent_flux_audit.mjs, final verified commit bd447b6cdc338605fd20c01c628b4a7149251b28, blob 5229bbff7a6252bb3360772d84c5bedef223abf5. Run
    node research/min_clock_descent_flux_audit.mjs 1024 4096 16384 65536
All 12 final JS function runs (four X windows times three modes) succeeded in the available runtime; independent exact remote readback. Original canonical simulator and literal parity-GCD comparison at X1024 (4658 checks); construct actual physical post-state graph; deterministic successors, counts, pair conservation, drift flux; independent difference-array integration of level masses by actual labeled post key versus direct child-pair min-drop formula; verify all-layer identity (2), integrated sums, nonreset entry cap and small birth union; cheap gain and actual late clipped within-key ordered product. Additional independent sampled root-pair replay checks first recorded common state and consecutive common suffix. Floating tolerance only for fractional weights, integer flux/level integrals exact in tested ranges. No previous masks/deletions cumulatively applied. Analytic mode finite eps=min(1/8,u^-1/8)=1/8 and m=floor(u^2.5); diagnostic eps=1/16,m4; wide eps=1/4,m16. Finite modes not asymptotic estimates; no full-prefix positive-energy bound established. No separate Node invocation, no Lean compilation.

Largest X65536, B678,N32768, 794415 selected tag-events, R_late402074. Actual graph 114079 vertices,110663 edges,92440 label-key groups,max vertex mass238. Ordered first recorded common pairs 1882504 (941252 unordered), same expiration count. Positive shared drift A=770615916, negative D=229240464, birth deficit F_birth=363145844, expiry F_end=904521296; both sides of (1) equal 1133761760. All 8142 integer levels checked, 766 independent sampled common-pair histories. Full downward diagonal3903590, entry correction6082684 (including resets), Q_down239226738. Nonreset entry correction134252, F_nr363280096. Full positive projected energy308442393.05, offdiagonal304596672.68; this is not late energy. Analytic m108 small-birth UNION charge143219256, heavy residual220060840 (no double count of low-deficit/small-mass intersection). At finite m4 the small union is716812; m16 is11869936. These are charge budgets, not actual paid late energy.

Analytic eps1/8: cheap nonreset shared downward level offdiag79544928, same-key entry cheap level offdiag0, actual G_cheap,nr87555112, nonreset cheap diagonal levels1038972. Actual late cheap nonreset same-post-key ordered offdiag34352.10604 (all HIGH in this mode), diagonal-inclusive34871.61248. Same-key cheap/expensive cross product15.09623, total within-key incident offdiag34367.20228. Diagnostic eps1/16: actual gain moment60605128, late same-key cheap offdiag28300.82795 (MED6380.31594/HIGH21920.51202), mixed15.09623. Wide eps1/4: gain moment145790292, entry cheap level75696, late same-key cheap offdiag156699.80001 (MED41501.40471/HIGH115198.39530), mixed19866.58815. Nonreset post-key full late natural diagonal-inclusive energy18881124.37074 in all modes, not all projected energy. The measured same-key components are not cumulative residual reductions; no numerical upper bound beyond (7) is asserted for remaining terms. Full moment and late energy have different units and scopes.

## 7. Remaining direction

The previous small/short-wait descending witness obstruction now has an exact pair flux accounting, with only first recorded common-state births creating new deficit credit. The next substantive problem is to bound the HIGH-deficit LARGE-mass birth budget, including same-label different-pretime arrivals, or to exploit the actual expiry subtraction and positive-drift sector structure. To finish the original proof one still needs late projected energy for different-key and nonsynchronized pairs, the joint sufficient MED/HIGH bounds and Lean formalization. Main unchanged; twin-prime conjecture OPEN.
