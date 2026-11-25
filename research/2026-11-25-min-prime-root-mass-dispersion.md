# Heavy recent-contact support and multiscale source-cell dispersion

2026-11-25 JST. Continuation of b076ed8fcd902eb06b5f3d211c8fba6e994cd934 on research/min-prime-root-repeat-energy-2026-11-25. Two additional unconditional reductions of the gain-stopped prime-root hybrid. First, a mixed shallow/recent-high projected first-contact class is controlled even when the recent side has arbitrarily large ancestry mass and several intervening non-LOW selections. Second, high-event incidences can be restricted to thick and dispersed source cells on a growing nested family of scales. Uses the earlier first-contact budget, reverse set expansion and r-support sum, not a random transcript assumption. The deep/deep thick contact problem and medium moment remain OPEN; no Lean compilation or external novelty claim.

## 1. Setup and the longer recent-high window

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, l=log u, T=floor(X/u^(1/4)), N prime roots in [X,2X), N=Theta(X/u). The original MIN path is stopped at the first post-gain >=T or original terminal/cutoff. Include the final vertex. Each source's gain G_M<T+B and r-cost <=1.5 G_M. At each C a root appears at most once. For distinct roots with a common horizon let J be their first common horizon in the FULL original prefix lists. For any subset of retained actual high pre-event incidences their ordered pair energy is <=3 min(C_end(M)-J,C_end(M')-J)<=3(T+B), even when times differ or projections split/recontact. These are the inequalities of a5e1119 and 5b545e4.

Use the growing LOW primorial L<=l^(1/4), cutoff y, with gain <L in every contiguous LOW block. Depth is the number of completed non-LOW selections, including repeats. A vertex is shallow if depth<=k. At most (k+1)(L/2+1) vertices of each source are shallow; this includes root and possibly terminal. Thus V_sh=O(NL(k+1)) shallow incidences in total.

A vertex is w-recent at cutoff P if its latest selection p>=P exists and at most w completed non-LOW selections have followed that selection. LOW steps are not counted in w. The anchor itself and the final vertex are allowed. This is the longer recent definition used in parallel short-clock paper fa2d2d214de5, now on the gain-stopped prime-root ensemble. Assign each recent vertex to its own latest large selection. Every large selection can be assigned at most (w+1)(L/2+1) subsequent vertices, because after each non-LOW selection at most L/2 LOW steps follow before the next one. Each source has <=G_M/(P-1) large selections. Therefore the actual total recent incidence mass is
    V_rec <= (w+1)(L/2+1) sum_M G_M/(P-1)
          = O(NT L(w+1)/P),                         (1)
for P->infinity. This does not require the recent suffix to be regular, the original history to have bounded complexity, or a bounded number of reverse keys at C.

## 2. Rare heavy support controls mixed first contacts without any partner mass restriction

Define A_H={C: number of original w-recent tags at C > H}. This is an ACTUAL, trajectory-dependent horizon set, not a relaxed CRT support. Marking it is not equivalent to assuming its tags can be computed arithmetically. Equation (1) gives the deterministic size bound
    |A_H| <= V_rec/H = O(NT L(w+1)/(P H)).             (2)

Apply the reverse expansion of b076ed8 to this set, which works for ANY set regardless of how it was chosen. In the even horizon interval [2X-2,7X], let d_y(D) count odd primes y<p<=B dividing D or D+2, h=ceil(20l), g=max(2,hL), and exceptional candidate edge mass D_edge=sum_{d_y(D)>h} d_y(D)=O(X/u^4). The last bound is the earlier elementary divisor-tail calculation, using sum 2^omega(n)<=sum tau(n)=O(X log X). A reverse non-LOW step chooses an even LOW offset e<L, then a candidate p>y at D=C-e, then predecessor D-p+1, with invalid horizons discarded. Deduplicate every layer. For any set S the expanded size is <=g|S|+D_edge. Iterating and including a final LOW offset gives
    # original roots visiting A_H at depth<=k
       <= O(L g^k (|A_H|+D_edge)).                   (3)
No prime-root density saving in this cardinality bound is assumed. In particular it remains valid for sets made from the original source incidence counts.

Delete the entire original tag of every such shallow visitor. Choose, for a simple explicit set of parameters,
    P=ceil(B/u^(1/2)), H=ceil(B u^(1/2)),
    k=w=floor(l/(8 log g)).
Then k,w->infinity, g^k<=u^(1/8). Since T=Theta(B^2/u^(1/4)), (2) gives |A_H|=O(N L(w+1)/u^(1/4)). Equation (3) is at most
    O(N L^2(w+1)/u^(1/8) + L u^(1/8) X/u^4)=o(N).
Thus the new entire-root deletion costs o(NT) in linear clock and selected weight. It can be unioned with the previous rare-root deletion. It does NOT imply the removed tags' pair energy is negligible.

For any pair of surviving roots whose first projected contact J has a shallow side and a w-recent side, J is NOT in A_H, since the shallow tag would have been deleted. This holds if the recent group was huge or small and regardless of the two compressed last labels, including the same-label asynchronous exception of b076ed8. Charge each such first pair to its shallow incidence; there are <=H possible recent partners at its C. Hence their count is at most H V_sh=O(NL(k+1)H), and the whole ordered future energy is
    E_mix << NT L(k+1) H
          = O(T^2 B L(k+1)/u^(1/4))=o(T^2 B).        (4)
Both root deletion and this actual pair-energy bound are required. The preceding thin group rule is not used, and neither side is required to have small Kraft complexity after the first contact.

A general condition on parameters is L g^k [NT L(w+1)/(PH)+X/u^4]=o(N) and N L(k+1)H=o(TB). For example one can bring the large cutoff almost down to the hybrid Q=B/u while keeping diverging depths:
    P'=ceil((B/u) exp(sqrt(l))),
    H'=ceil(B u^(3/4) exp(-sqrt(l)/2)),
    k'=w'=floor(sqrt(l)/(4 log g)).
Here P'/Q is a subpower of u tending to infinity, P'<B eventually, and g^k'<=exp(sqrt(l)/4). The ratio of the root count (3) to N is O(L^2(w'+1) exp(-sqrt(l)/4))+o(1); the ratio of (4) to T^2 B is O(L(k'+1) exp(-sqrt(l)/2)). Both tend to zero because L and depths are at most fixed powers of l. The primary audit uses the simpler P,H above, not these additional asymptotic choices. This result still does not cover arbitrary contacts where BOTH histories are deep. No restriction on the depth of a contact without a recent side follows from (4).

## 3. A source-cell bound independent of contact complexity

After any preceding root or incidence deletion, let I be any actual retained high-event incidence set (p>=Q=ceil(B/u)). At a C let W(C) be its original-tag mass. For an integer cell width d partition roots by fixed consecutive half-open intervals [X+jd,X+(j+1)d), j>=0. Write W_{d,j}(C) for the mass from that cell, and U_d(C)=sum_j W_{d,j}(C)^2. This partition is of source values, NOT of current horizons, actual physical times or compressed keys.

The same-cell aggregate energy obeys
    F_d=sum_C r(C) U_d(C)
       <= O(NT + NT d/log d),                         (5)
for d->infinity, d<=T. Proof: the diagonal is <=O(NT). Any two distinct roots in the same cell have separation <d. Uniform prime interval upper bounds give O(Nd/log d) unordered candidate pairs. Each contributes <=3(T+B) by section 1. This upper bound is on all future overlaps, not only first contacts, and remains true under any accounting deletions.

For the full high event support the prior sum is
    S0=sum_{even C in full horizon interval} r(C)
       = O(XB/u^2),
where noneligible horizons contribute zero. This was used in 6d2f6bf9, 2d184f3 and a5e1119. At a high pre-event C every visiting root has C-T<2M-2<=C. Its possible source interval has length T/2, so it intersects at most ceil(T/(2d))+2 cells. This is the only source localization used in the next step.

### 3a. Thin source cells: unconditional linear deletion

Mark all incidences from each nonempty cell at C with W_{d,j}(C)<=m. This is a deletion of actual high event tags, not entire roots. Its total r-cost satisfies
    R_thin(d,m) <= m (ceil(T/(2d))+2) S0.            (6)
For d=o(T), take m=floor((d/B) u^(3/4)). Then the bound is O(NT/u^(1/4)), uniformly in d for B<=d<=B u^(5/4). This estimate does not rely on the labels of the incoming/outgoing events, relative expensive clock, first-contact classes, or the original first-contact time. It is also valid on any smaller input incidence set.

### 3b. Effective dispersion, not just number of occupied cells

At a nonempty C define its effective number of source cells (inverse concentration)
    D_d(C)= W(C)^2/U_d(C).
By Cauchy it is between 1 and the number of occupied cells. It is small when a few cells dominate the mass, even if many other cells are occupied. For any current high incidence set, all horizons with D_d(C)<=K have total energy <=K F_d, simply because W^2<=K U_d pointwise. Cauchy over C, with the same S0, bounds the LINEAR cost of deleting all their high incidences by
    R_disp(d,K) <= sqrt(S0 K F_d).                  (7)
There is no claim that deleting thin cells in (6) removes only negligible quadratic energy.

For B<=d<=B u^(5/4) take K=floor(B u^(3/2)/d), which tends uniformly to infinity. Since log d~u, (5) gives K F_d=O(T^2 B/u^(1/4)) (the diagonal contribution is also smaller). Hence (7) is O(NT/u^(1/8)). This handles unbalanced distributions with more than K occupied cells, which a simple occupied-cell-count test would miss.

### 3c. Nested multiscale thinning and dispersion

Take d_j=B 2^j for j=0,...,Jmax=floor(log_2(u^(5/4))), with integer B as defined. These are nested aligned partitions. Use m_j=floor(2^j u^(3/4)), K_j=floor(u^(3/2)/2^j). First perform thin-cell deletion at each scale in increasing j, on the currently remaining tags. Coarser cells are unions of entire finer cells. Thus no finer cell that survives is partially depleted by a later coarse-scale deletion: its previously established lower bound W_{d_j,a}>m_j remains true. Then calculate all D_{d_j}(C) on this final thinned set, and delete entire high horizon incidence sets where any one scale has D_{d_j}<=K_j. Deleting whole horizons leaves all statistics at the surviving C unchanged.

By (6) and (7), summing O(log u) scales,
    R_newcells = O(NT (1+l)/u^(1/8)) = o(NT).       (8)
The count of additional deleted high incidences is <=O(NT/Q), by gain alone, so the extra LOW block attachment O(LNT/Q) is negligible. No clock-only deletion is inserted into a selected-weight seed. Equations (6)-(8) are accounting operations only on original tags.

Every nonempty surviving high horizon now simultaneously satisfies
    W_{d_j,a}(C)>m_j for every occupied cell a,
    D_{d_j}(C)>K_j,
at EVERY scale in the nested family. Thus a retained high horizon must have many substantially populated source cells and a genuinely dispersed mass profile. More explicitly at the fine scale d=B its effective cell count exceeds u^(3/2) up to floors and every occupied cell contains >u^(3/4) tags; at the coarse end d~B u^(5/4), effective count exceeds order u^(1/4), and every occupied cell contains >order u^2 tags. These conditions are on actual source sets, not on all candidate primes in the cell. They do not imply that a thick cell corresponds to a single physical state or a single compressed key.

The asymptotic proof covers the growing nested ladder; the audit exercises two nested scales d0,d1 (d1=d0 times an integer) and exact formulas at finite diagnostic parameters. The two-scale statement also follows directly from (5)-(7) with d0=B,d1=B ceil(u), m0=floor(u^.75),m1=floor(u^1.75),K0=floor(u^1.5),K1=floor(sqrt(u)). If one recomputes later arbitrary incidence deletions, cell thickness/dispersion could be lost; in the hybrid these steps are to be applied LAST to the high set.

## 4. Revised residual criterion and remaining obstruction

Union the new entire-root deletion with the old rare-root deletion; the surviving root count is N-o(N). Keep all the earlier accounting marks on their original full prefixes (restriction cannot increase the bound). Perform the nested source-cell deletions last on the high incidences. Equations (4) and the old first-contact energy exclusions apply to this smaller incidence set, since they use a uniform bound for any subset; the pair class in (4) is now absent from the remaining energy target, though individual tags need not be removed for that pair estimate.

Let E_disp,bad be the sum over unordered pairs avoiding all established whole-pair exclusions (including the new surviving shallow/recent class) of their ordered energy on the new thinned, dispersed high set. Its full energy equals E_disp,bad+o(T^2 B), including the negligible diagonal. This does not assert equality with the unthinned energy up to a negligible error, because (6) is only linear and root deletion is only linear. The previous small/medium Cauchy and LOW charge still apply. Consequently the joint OPEN bounds
    Z_m=O(N B log^3 B), E_disp,bad=o(T^2 B)
on the same unbounded dyadic windows imply R_surv=o(NT), contradicting the per-root lower bound R_surv >=(N-o(N))(T-6)/4 in twin-free windows. No proof of either residual estimate.

A remaining energy mechanism must now support thick, spread-out sets of prime roots on all the chosen scales, not merely one very thick compressed group, and no shallow/recent-high first contact from the new range can be responsible for the leading pair energy. This does not rule out a single compressed group whose roots themselves are widely distributed, deep/deep same-label asynchronous contacts, or long medium-label histories. The next actual arithmetic problem is a bound on the number of simultaneously thick source cells reached at a costly horizon (or their cross-cell first-contact products); the new dispersion inequality identifies a precise complementary regime. In particular, a uniform O(K_j) effective cell count on one ladder scale for the final retained horizons, with the constants/thresholds adjusted within the same savings, would imply the high linear budget is negligible. No such uniform upper bound has been derived.

## 5. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_mass_dispersion_audit.mjs, final exact remote readback at 5a7e775684ce2ea0e083901a3fd77abe723b957c, blob 91a846372871977650ea15dd0c6a05dd247528b6. Run:
    node research/min_prime_root_mass_dispersion_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node invocation. Four modes x six windows, all 24 passed (the initial three modes were rerun after switching to effective dispersion, the fourth adds a diagnostic). Literal parity-GCD comparisons at X256/1024: short1183, four1707, gain1719, skew1707. All actual roots and full vertices with original gain prefix. Tests recent/positive non-LOW suffix and shallow vertex counts, exact heavy support count, deduplicated reverse expansion edge bounds and actual shallow root inclusion, no surviving heavy shallow/recent first pair, first contact pair budget, exact full high E before/after new root pruning and cell deletions, each source cell localization, nested thickness preservation, both effective dispersion conditions and disjoint linear and energy partitions, same-cell energy independently reconstructed by pair sweep and bounded by the same-cell first-pair count. Integer arithmetic at tested sizes. Audit uses full p>=Q set and isolates the new reductions, not entire cumulative previous marks. It does not test the analytic prime-sum bounds, the growing asymptotic number of scales, or the alternate near-Q parameters of section 2.

Modes short T=B, four T=4B, both P=ceil(B/4) (small guard), L6,y3,k=w=2,h8, H=5 or 12 respectively. Fine cell width floor(B/8) (min4), coarse 4 times fine; m0=2,m1=3,K0=2,K1=1. Skew is four with K0=4,K1=2, exercises extra concentration exclusions when raw occupied-cell count is large. Gain uses the simpler section 2 asymptotic T,P,H,k,w formulas (finite guards, L6), two-scale cell settings in section 3c. At finite B k=w=0, no heavy horizon, and the dispersion residual is empty; not a test of limiting behavior. Positive non-LOW suffix and nonempty final residuals exercised in diagnostic modes.

| X | four-mode marked roots | surviving mixed shallow/recent first pairs | final high horizons | final high energy |
|--:|--:|--:|--:|--:|
|256|0|149|0|0|
|1024|0|195|0|0|
|4096|17|624|1|15075|
|16384|50|1188|16|578918|
|65536|195|3514|77|8511354|
|262144|663|7797|297|107851459|

At X262144, B1355, N20390, four T5420: 612685 events, 633075 vertices, R16602377, 61873 recent incidences of which40774 have positive non-LOW suffix, 93532 shallow vertices. 1524 heavy horizons, max recent mass101, reverse layers1524/9509/38434, relaxed roots5196, actual removed663 (clock646169). 20729 mixed first pairs (12138 with positive recent suffix),12627 at heavy horizons, zero of these heavy pairs survive; 7797 surviving mixed first pairs, full ordered energy4558212. Full high E216308331, after actual root pruning190991417, after fine/coarse thin deletion139711878, after effective dispersion107851459. Linear high cost after root pruning9398111, fine thin2357226, coarse thin764205, dispersion3065033, retained3211647. Final diagonal3211647, surviving shallow/recent energy1629992, remaining pair103009820, exact sum107851459. Fine and coarse within-cell energies47584927,97507397 before thinning, 56512 and146968 same-cell first pairs among surviving roots, respectively.

At X262144 short T1355: 1064 roots flagged, 7601 relaxed, 8563 heavy mixed first pairs all removed; 3674 mixed first pairs survive. High E89384449 ->76187374 after root pruning ->55344585 after thinning ->21195682 after dispersion, final diagonal931948, mixed217290, remaining20046444, 110 final horizons.

Skew mode at X262144 excludes 11 additional concentrated horizons (clock134958) for which both raw occupied-cell counts exceed their cutoffs; their effective dispersion does not. Here final high E52146833, 66 horizons, final diagonal1127195, mixed548388, remaining50471250. At X65536 skew finds 3 such concentrated horizons. These are nonvacuous finite checks of inverse-concentration vs simple count; none of the diagnostic removal fractions are estimates of asymptotic savings. Main and other branches unchanged.
