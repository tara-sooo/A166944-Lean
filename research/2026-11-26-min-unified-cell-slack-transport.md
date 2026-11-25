# Cell slack discount and direct half-clock/overshoot transport

2026-11-26 JST. Continues [eebc7e2c5923](https://github.com/tara-sooo/A166944-Lean/blob/eebc7e2c5923ef3e390023cc08307342144f5a2d/research/2026-11-26-min-unified-whole-cell-discount.md), using the graded rough support of [5b562489c22e](https://github.com/tara-sooo/A166944-Lean/blob/5b562489c22e59bf34c2d245342026d340a68437/research/2026-11-26-min-unified-short-boundary-pairs.md). Preflight independent heads unchanged: prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New: retain BOTH endpoint capacity slacks in the cell certificate, replace the old objective pointwise by a smaller one at the SAME threshold 1/4, obtain a direct partition into at most half actual waiting weight and positive overshoot decreases, trim all previous very small/large labels regardless of current label, and count the remaining carry and wait witnesses. No proof of the remaining strict upper bound or Lean compilation.

## 1. Setting and improved inequality

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, P largest even primorial <=B^.25, y its largest factor, kappa=u^.25, kappa'=u^.125, cstar=(1+2/kappa)/(1-4/u)=1+o(1). Original MIN completed prime-root prefixes, gain-stopped as before; under finitely many twins all reach T eventually. Event i has gain g_i=p_i-1, wait w_i<=2r_i<=2p_i, delta_i=2w_i-g_i, D_i=(-delta_i)_+, V_i=(delta_i)_+, E_i=(delta_i-3g_i)_+. Total gain G<H, actual wait<=3G. All original deficits nonnegative, initial6.

Partition actual events into cells ending at a strict crossing of one or more grid multiples of P, plus an uncompleted terminal cell. For a completed cell k write G_k for its full gain, W_k for its actual wait, D_k=sum D_i, V_k=sum V_i, E_k=sum E_i, l_k for its noncrossing prefix gain <=P, f0_k=P n_k. Old admissible classification is p_k<kappa P or r_k>=g_k/u at the last event; old bad otherwise. In the parent adaptive whole-cell charge ledger f_k=(f0_k-D_k)_+ on admissible cells and zero on bad cells. At admissible cells gamma=min(1,f0_k/D_k) for all negative events, zero if D_k=0. On bad cells gamma=f0_k/D_last at the last event only. Terminal suffix gamma=0. Thus gamma<=cstar. Exact frozen LIFO matching yields F+R_new=P n_all-I_initial, F=sum f_k, I_initial<=6cstar. The earlier first-bad-cell source payment U_bad=O(NT/ell) remains valid unchanged (see eebc7e2 section 2); let R' be remaining target charge. Every contributing source is positive and belongs to an admissible completed cell. The consuming events can be anywhere in the original prefix. Both endpoint capacities now use actual deficit variation, not the looser 3g+E and g:
    R'/cstar <= sum_admissible V_k,
    R'/cstar <= sum_all_original_events D_i.
Multiplying the second by 3 and adding, then using F+R' >= G-P-I_initial-U_bad per tag with the bad payment understood in aggregate, gives
    sum_admissible [f_k+cstar(V_k+3D_k-3G_k)/4]
      + sum_other_cells cstar(3D_k-3G_k)/4
        >= (1-3cstar/4) sum G - NP -6cstar N -U_bad.       (1)
The other cells include the terminal suffix. Their summands are NONPOSITIVE because D_k<=G_k. Dropping them increases the left side. The same is true of replacing each admissible summand by its positive part. Replacing cstar by 1 changes the total by o(NT), since absolute sums V,D,G are O(NH) and positive clipping is 1-Lipschitz. Identity V_k-D_k=2W_k-G_k gives the exact simplified local score with coefficient 1:
    L_k = [f_k+(V_k+3D_k-3G_k)/4]_+
        = [max(f0_k,D_k)-G_k+W_k/2]_+.                 (2)
On inadmissible cells set L_k=0. Under finitely many twins, sum L_k >= NT/4-o(NT).

Moreover V_i+3D_i-3g_i<=E_i pointwise: at positive events V_i<=3g_i+E_i; at negative/zero events 3D_i<=3g_i. So L_k<=f_k+E_k/4. The old forbidden-word estimate gives E_k<=l_k+8; hence L_k<=A_k+2 where A_k=f_k+min(l_k,E_k)/4 is the parent actual objective. Define
    J_k=min(A_k,L_k).
Then 0<=L_k-J_k<=2 and the total replacement costs O(NH/P+N)=o(NT) because each completed crossing event crosses at least one distinct grid multiple. Under finitely many twins
    sum J_k >= NT/4-o(NT).                               (3)
The new exact pointwise comparison J_k<=A_k means ALL previously justified original boundary-atom masks transfer with no cost increase by equal division over n_k atoms. This is a new sufficient objective, not an independent proof of the upper contraction. No assumption of terminal deficit being small or independence between tags.

## 2. Projected-word upper envelope

For completeness a no-wait upper envelope can be obtained with only the projected word and least factors. W_k/2<=sum r_i, D_k<=G_k. A sharper bound uses convexity on 1<=w<=2r of (g-2w)_+ + w/2: its maximum is at an endpoint, and, for odd p>=3 and r>=3, equals max(g-3/2,r). Indeed the lower endpoint is g-3/2 (also at g=2); the upper is (g-4r)_++r, which is either r or g-3r<=g-3/2. Therefore define
    Z_k=[max(f0_k-G_k+sum r_i, sum max(-3/2,r_i-g_i))]_+.
This dominates L_k on admissible cells. The previous projected word score Wword_k of eebc7e2 is (f0_k-sum(g_i-4r_i)_+)_+ + min(l_k,4 # {i:r_i=p_i})/4. The new word score Jword_k=min(Wword_k,Z_k) satisfies J_k<=Jword_k<=Wword_k. It uses only the complete original projected word, not just the last crossing key. Thus its residual inequality at 1/4 suffices, and is implied by the previous word inequality on identical frozen masks. No strict asymptotic separation asserted.

## 3. Direct partition into half-clock weight and decreasing overshoot

Let b_k be the posthorizon of crossing k minus the LAST boundary crossed by that event, so 0<b_k<=min(P,g_last,k). For the first completed cell set b_0=C_origin-(P ceil(C_origin/P)-P), in (0,P]. For EVERY completed cell, including multi-boundary events,
    f0_k-G_k=b_(k-1)-b_k.
Since D_k<=G_k, (2) implies
    J_k<= W_k/2+(b_(k-1)-b_k)_+.
The following is an exact allocation of J_k, not two independent upper estimates. Freeze it on the full original ensemble:
    beta_k=(J_k-W_k/2)_+,
    omega_k=J_k-beta_k.
Then 0<=beta_k<=(b_(k-1)-b_k)_+, 0<=omega_k<=W_k/2. Allocate beta_k to the preceding crossing's LAST raw grid atom (or the initial virtual atom for k=1). Allocate omega_k uniformly over all actual occupied tick transitions of cell k, with per-tag coefficient omega_k/W_k<=1/2 (completed cell has W_k>0). This includes the last event's wait. Each original event belongs to at most one cell; no congestion from repeated/nested interval transport. Each preceding crossing receives at most one carry, bounded by min(P,g_prev). Original projected wait-key (C,p) receives at most w/2<=r(C) per tag; physical tick-key (C,p,j) at most 1/2 per tag. The first/last atom and occupied tick are distinct types of destinations. For any previous source boundary mask, discard the corresponding allocated fractions using the uniform n_k division, or define the transport of the remaining cell charge by scaling these fixed proportions. This can only reduce the destination loads. For any old actual-clock mask of cost U, pay its allocated tick charge at cost <=U/2, without needing a density lower bound or a cohort bound. This differs from the prior upper capacity 2 per tick for generic targeted charge: the new certificate is already at quarter-gain threshold.

The carry must be paid with respect to the preceding RAW boundary atom, not its possibly much smaller discounted objective; if the raw atom is paid by an old raw F mask, carry transfer costs at most the raw mask cost. A mask justified only for discounted weight cannot automatically pay that carry.

## 4. All-mass carry trim and narrow-band thin caps

Pay all virtual root carries <=NP=o(NT). Take eta=ell^(-1/2). For any actual preceding crossing of label q<=eta P, its carry<=q<=eta P; there are <=NH/P+N crossing events overall, so total O(eta NT+NP)=o(NT). For any preceding label q>=kappa'P (INCLUDING all old bad), each carry<=P and each such preceding event can have only one successor cell, with <=NH/(kappa'P-1) such events. Thus total O(NT/kappa')=o(NT). Unlike the previous adjacent-short trim, neither statement restricts the current label or its boundary count. Only the carry portion is paid, not the entire current score.

Every remaining carry key (K,C,q) has eta P<q<kappa'P, K its preceding last boundary, and is admissible (q<kappa). Fixed q has O(X/P) possible keys, since C even in [K-q+2,K] with q|(C+sigma), at most two per K. Its effective carry mass is aggregate/P, <=distinct original contributing tags. Use the new plain cap
    m_carry(q)=H/(q ell²).
Indeed the reciprocal sum in this narrow band is O(ell/u), because log q=Theta(u) and the number of dyadic intervals is O(ell). The full summed payment cost is
    O(XH/ell² sum_(eta P<q<kappa'P) 1/q)=O(NT/ell).
Use the graded sieve from 5b56248: a(r)=log²(2+r)/(1+log log(2+r))²; at each fixed q sum over candidate boundary keys a(r(C))=O(X/P). Hence the stronger cap
    m_carry,grade(q,r)=H a(r)/(q ell²)
has the same budget, even for nonrough q. For keys with r>= (q-1)/log(2+q), the stronger old rough support O(X/[P log²(2+q)]) yields cap H log²(2+q)/(q ell²) and cost O(NT/ell). The new plain/graded caps gain a factor u/ell over the previous mid-label projected boundary caps of 5b56248 (for corresponding weight-normalizations, not a pointwise statement about the actual mass). The reason is the narrow carry-label band, not a new lower bound for prime tuples. Pay via union/max as applicable.

## 5. Graded projected and physical wait caps in the SAME allocation

For fixed selected p<=B, count possible prehorizons C with r(C)>=R, 3<=R<=p. For each eligibility sign write C=p a-sigma, a in an interval of length O(X/p). Sieve the two forms a and p a-2sigma by odd primes <=R^(1/40), which are less than p, and have distinct roots. The two-form upper bound, with error O(R^.2) absorbed by X/p>=c B, gives O(X/[p log²(2+R)]) candidates; bounded cutoffs trivial. Apply the same summable tail integration as 5b56248 to obtain sum_C a(r(C))=O(X/p) uniformly in p. Each C has O(H) possible original occupied times in its deficit slab. No short label excluded.

Let projected effective mass at (C,p) be its aggregate allocated wait charge/r(C), <=number of original tag-visits, and physical effective mass at (C,p,j) be twice its allocated charge, <=original continuing tag count. Pay projected mass <=
    m_proj=H a(r)/(r u ell²),
and physical mass <=
    m_tick=a(r)/(u ell²).
Both costs O(XH/(u ell²) sum_p 1/p)=O(NT/ell); for p>=sqrt P the same proof using the O(1) reciprocal sum allows replacing ell² by ell. At r comparable to a large p, one can instead use log²(2+p) in the caps on the rough subset, by the earlier support sieve. Also previous absolute actual-clock payments can be reused with coefficient 1/2 as above. The full projected and physical wait ledgers are different marginals of exactly the same allocated charge. Freeze before masks and pay their UNION once: a charge unit associated to both keys is not counted twice. Projected effective mass does not imply synchronous physical mass. No assertion that all small-r wait charge is payable.

The resulting sufficient condition is
    liminf_(dyadic X->infty) (beta_rem+omega_rem)/(NT)<1/4,
where the two terms are the residuals of this exact partition after justified original and destination masks. By J<=A and pointwise transfer, the previous actual whole-cell sufficient condition implies this new one. Even discarding all carry would still leave a clock estimate to establish; the gain baseline is not proved small by transport. The possible heavy carry band, projected heavy wait and heavy physical waits remain. This is a genuine objective reduction and new support/cap reduction, not a proof of the final inequality. No external novelty claim or Lean compilation. Main and independent source branches unchanged.

## 6. Finite audit

[Standalone source](https://github.com/tara-sooo/A166944-Lean/blob/63c7420c608d3829dd8132a2b3fc446a92bcbb61/research/min_unified_cell_slack_transport_audit.mjs), commit 63c7420c608d3829dd8132a2b3fc446a92bcbb61, exact remote readback. Eight runs in ECMAScript runtime (five normal and three focus), all passed. Reproduce: node research/min_unified_cell_slack_transport_audit.mjs 256 1024 4096 16384 65536. Finite T=min(8B,floor(X/2)) or floor(B/2), P=6 or30, kappa=2, alpha=1/8, eta=.4, previous-long cutoff1.5P. These are diagnostic substitutes. The audit independently reconstructs original paths and adaptive cell LIFO, tests actual max-gamma source/sink capacity, signed inequality (1) before replacing coefficient or clipping, actual pointwise comparison, convex endpoint bound, projected word envelope, exact overshoot identity even at first cell and multi-boundary crossings, half-clock allocation, per-predecessor carry capacity, all-mass carry partition and projected/physical marginal sums with union accounting. Finite first-bad deletion includes finite disparity exceptions. Illustrative projected cap aggregate<=2r normal/.5r focus and physical cap<=1 normal/.25 focus; does not numerically test the analytic cap rates, carry-key thin masks, cumulative historical masks, or a literal gcd oracle. The finite actual gamma may differ substantially from 1, so (3) is not a finite 1/4 test.

| X/mode | previous actual | new actual J | previous word | new word | carry | half-clock allocation |
|---:|---:|---:|---:|---:|---:|---:|
|256|2144.5|1118.5|2801.5|2351|127|991.5|
|1024|7077|3438.5|9067|7747|371|3067.5|
|4096|64265.5|32366|80977|71738.5|2404.5|29961.5|
|16384|372079.5|188025.5|464100.5|408039|11613|176412.5|
|65536|2374056|1181243|2870622.5|2566400|48815|1132428|
|4096 focus|29630.5|15161.5|37414.5|32596|4553.5|10608|
|16384 focus|188258.5|95775.5|230335.5|203657.5|23006|72769.5|
|65536 focus|1278810|626685|1539135|1375223|109600.5|517084.5|

Largest normal: 5709 roots,140255 completed events, no T reaches,84315 admissible cell checks,55146 noninitial remaining LIFO incidences,136617 convex word checks. 2345 zero-score cells,25446 positive carries. Carry trim root3240.5, previous bad541, small0, long23848; remaining21185.5 on2280 keys. Wait allocation1132428 on29052 projected and569009 physical keys; finite projected payment223264.199740, physical193463.845631, overlap143669.892232, residual859369.846860. Largest focus: 2886 reaches,75256 events,20840 admissible cells,25305 LIFO incidences,69187 convex checks. Carry root38235,bad1320,small2815,long30112,remaining37118.5 on1507 keys. Wait517084.5 on25122 projected and465074 physical keys; finite union residual474374.500692. New actual score on reached tags491887; many roots stop before diagnostic T. Actual score reduction relative to previous is about half at these finite scales; not an asymptotic result and not a test of strict 1/4 contraction. No Lean verification.
