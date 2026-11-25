# Projected first contact on the short clock slab: growing recent-high keys and whole-pair bounds

2026-11-25 JST. Continues f83cb64cd8d883e3fdbb0dcfff3b9773f552e3ac (reverse-growth/degree pruning) and the relative-clock slab at 25473614cf384cff0d8af534e34404cd774ae053. The parallel prime-root gain-stopped first-contact result 5b545e4e74e4590870d8a16af372e297cf31a462 motivates using projected contact instead of physical synchronization. Here use ALL odd original roots, fractional relative-clock occupation, and a growing non-LOW window after the last high event, rather than only a LOW suffix. New unconditional negligible WHOLE-PAIR terms, after o(X) exceptional-degree root deletion. The residual energy remains OPEN. Paper proof, no Lean compilation.

## 1. Setup

Dyadic X, N=X/2 odd original M in [X,2X), B=ceil(sqrt(7X)), start s=M+2,C0=2M-2, original K(M)=floor((7M-1)/4). H=4B,a=2B. Assume H+2B<=min_M(K(M)-s), eventually. Keep actual prefix through the first post-event vertex at or beyond s+H if any, or twin terminal. Include root and terminal in full projected horizon list V_M. C strictly increases, and total gain including the final crossing event is <=2H+B+6. No modification of the wheel.

Let ell_M(C) be the wait duration intersected with relative [a,H), w_M(C)=ell_M(C)/(2r(C)) for positive active r, zero at terminal or outside occupation. Thus 0<=w<=1 and R_M=sum r w<=B. Put R=sum R_M, W(C)=sum w, E=sum rW^2. The target E=o(XB log^2 B) on unbounded windows suffices via the previous clock certificate. Under a hypothetical no-twin window R=NB. Root deletion of o(X) entire tags preserves R=(N-o(X))B, so the same energy target on retained roots suffices; this does not assert that deleted pair energy is negligible.

For each M and visited J define tail budget R_M(J)=sum_{C in V_M,C>=J}r(C)w_M(C), and terminal/final horizon C_end(M).

## 2. NEW for the fractional slab: first projected contact pays for the whole pair

For distinct original roots sharing at least one projected horizon (even with different arrival times), let J=min(V_M intersect V_M'). This is FIRST PROJECTED CONTACT, using full prefix lists including root and terminal, not merely retained occupied incidences. If neither path is at its root at J, their incoming primes must differ. Indeed the same incoming p implies common predecessor horizon J-p+1, contradicting minimality. Unlike first physical meeting, this applies before synchronization and does not assert that future paths agree.

For the whole unordered pair define its ordered energy (both orders)

    e(M,M')=2 sum_C r(C)w_M(C)w_M'(C).

Because w<=1 and r(C)<=p<=3(p-1)/2 at any occupied state, all its later overlaps, including splits, recontacts and synchronized suffixes, satisfy

    e(M,M') <= 2 min(R_M(J),R_M'(J),
                     1.5(C_end(M)-J),1.5(C_end(M')-J))
             <= 2B.                                    (1)

If either path ends at J, its tail occupation is zero. Proof uses the full common projected support C>=J, the per-source clock budget, and telescoping gains from J; there is no assumption of common suffix or equal absolute times. By the gain cap, any contacting pair has |M-M'|<=H+B/2+3. There are O(XB) such unordered pairs. Occupied-only horizons have the smaller H+3 support, but the larger bound is needed for counting full-prefix contacts that might include the final crossing state.

Two immediate whole-pair deletions:
- Near roots |M-M'|<=d=floor(4 log B): total O(dR)=O(XB log B), including the diagonal O(R).
- First contact at which min(R_M(J),R_M'(J))<=Z=log^(3/2) B, OR min remaining gain<=Z: by (1) the total is O(XBZ)=o(XB log^2 B). This extends the earlier late physical-first-meeting deletion to every projected first contact, including later asynchronous recontacts. Audit uses the clock-tail part as the shortTail class (the remaining gain bound is checked on every pair, but not separately classified).

## 3. Bounded-depth ancestors: upgrade from physical meeting to projected contact

Set ell=log log B, S=max(1,log ell), L largest even primorial <=6 S^(1/4), y associated LOW cutoff. Let T=ceil(20 ell), g=max(2,TL), D={C:d_y(C)>T}, d_y=#odd p>y,<=B dividing C or C+2. By f83cb64, exceptional edge sum Dedge=O(X/log^4 B). Choose

    k_g=floor(3 ell/(2 log g)).

Remove whole original tags visiting D while completed non-LOW depth<=k_g. The previous rare-set pullback bound gives O(L g^k_g (|D|+Dedge))=o(X) roots removed. This is only the degree pruning, not the separate high/rough root pruning; the latter may also be applied without invalidating the following estimates. Let GOOD mean depth<=k_g for retained paths.

By the previous bounded reverse branching argument, every horizon has at most

    m_g=(L/2) sum_{i=0}^{k_g}(TL/2)^i=O(L log^(3/2) B)

GOOD original tags. In each root's entire prefix, GOOD states lie in at most k_g+1 LOW blocks (including zero-length blocks) with <=L/2 vertices per block. Thus the number of GOOD visits of a root is <=(k_g+1)L/2. This remains true at terminals.

Count every unordered pair whose first PROJECTED contact is GOOD-GOOD. At the contact each endpoint is a GOOD visit, and it has at most m_g-1 other GOOD tags there. Summing over all roots and their GOOD visits gives

    F_gg_proj <= (N/2) * ((k_g+1)L/2) * (m_g-1)
              = O(X L^2 (k_g+1) log^(3/2) B).
    E_gg_proj <= 2B F_gg_proj = o(XB log^2 B).           (2)

The extra poly(ell) factors are log^{o(1)} B. Unlike the physical expiry lemma, the two paths need not follow the same suffix and they may already be different-time contacts. The whole later pair energy is nevertheless removed. This is an energy bound on actual retained original pairs, not a count of physical vertices.

## 4. NEW growing recent-high windows at arbitrary absolute depth

Take P=ceil(B/log^(1/8) B), k=floor(ell/(8 log g)). Eventually P>y, k->infinity. Call a selected label high in this section if p>=P. This is a DIFFERENT cutoff from the earlier shallow-exposure Q.

At a visited horizon C, a history is RECENT if its most recent high selection p has post-event horizon J and at most k further non-LOW selections have occurred before the current C (all intervening high selections would reset the most recent key). Call (J,p) the recent key. LOW blocks before/after those intervening events have their actual gains <L. A RECENT history is REGULAR if the actual post-horizons of all the subsequent non-LOW selections (strictly AFTER the high anchor J) have d_y<=T. No restriction on the number of earlier selections, earlier exceptions, or d_y(J) itself is made. In particular these can be deep histories even after root-level degree pruning.

Each root has at most O(B/P)=O(log^(1/8) B) high hits by the short-prefix gain cap. After each high hit, the RECENT window contains at most (k+1)L/2 visited vertices (including the anchor and any endpoint). Thus across all roots, the number of recent ORIGINAL SOURCE incidences, including irregular ones, is

    V_rec <= O(N (B/P)(k+1)L)
          = X log^(1/8+o(1)) B.                       (3)

Fix C. The number of REGULAR recent keys is bounded as follows. Reverse the suffix of length at most k non-LOW steps and its LOW offsets. At every actual post-horizon of those non-LOW steps there are <=T candidate labels; discard other branches in this relaxed reverse enumeration. At the end an even LOW offset reaches the anchor J. Hence there are at most (L/2) sum_{i=0}^k(TL/2)^i candidate anchor horizons. For each J there are <=floor(2 log(7X+2)/log P)=O(1) distinct primes p>=P dividing J or J+2 (product of the candidate odd primes divides J(J+2)). Consequently

    number of regular keys at each C <= m_rec
       = O(L g^k)=log^(1/8+o(1)) B.                   (4)

This is a count of KEYS, not of root tags; each key can have a huge actual ancestry. Regularity is only local to the last k steps, so it does not require the entire deep history to avoid exceptional degree.

Important structural fact: two RECENT histories at their FIRST PROJECTED contact cannot have the same key (J,p). If J<C, both visited J already. If J=C, both visited J-p+1 already. Thus a recent group cannot produce new first contacts internally at the current horizon. This argument is valid even if one or both suffixes are irregular, and independent of physical arrival times. It extends the LOW-only recent key used in the parallel gain-stopped note to k growing intervening non-LOW selections.

## 5. NEW two whole-pair deletions, including deep histories

(A) RECENT-GOOD: at least one history is RECENT (regularity not required), and the other is GOOD at first projected contact. For each recent incidence at C there are at most m_g possible partners. Thus

    F_rg <= m_g V_rec = X log^(13/8+o(1)) B.
    E_rg <= 2B F_rg = o(XB log^2 B).                   (5)

The recent history may be arbitrarily deep. No assumption about its full ancestor mass is needed. This handles additional one-shallow/one-deep pairs beyond the previous high-exposed root deletion: the current contact need not itself have any high divisor, and the high anchor can be separated by a growing number of intervening selections.

(B) RECENT-THIN: both histories RECENT, and at least one is REGULAR and belongs to a thin regular key group at C. A regular key group consists of actual retained RECENT REGULAR source tags with that same key; thin means its mass is <=tau=log^(3/2) B. Count from the OTHER recent incidence (arbitrary depth, regularity optional). At most m_rec keys can contribute thin regular partners; same-key contact is impossible, though including it would only increase the bound. Each contributes <=tau actual tags. Hence

    F_rt <= V_rec m_rec tau
         = X log^(7/4+o(1)) B.
    E_rt <= 2B F_rt = o(XB log^2 B).                   (6)

Both histories may be deep; the non-thin side can have arbitrary original source mass and may contain exceptional degree in its recent suffix. We use no assumption of uniform mass across keys. The small quantity is an actual source count within each regular thin group. This extends the earlier single-LOW-block recent-key method both in depth and in allowing irregular partners.

The proofs of (5),(6) use only the number of visits and the local uniform caps, not physical first-meeting/expiry. By (1) they cover the entire later pair including asynchronous and synchronized overlaps. Classes can overlap; impose an arbitrary disjoint priority (as in audit) or union upper bound.

More generally take P=B/log^beta B, k=floor(theta ell/log g), thin tau=log^gamma B with fixed beta,theta,gamma>0, beta+theta+gamma<2. For GOOD depth k_g=floor(alpha ell/log g), alpha<2 and alpha+beta<2, (2),(5),(6) all give the target little-o. Degree-pruning root count remains o(X). This is a quantitative tradeoff between recent-window length, large-label threshold and allowed local group mass.

## 6. Exact energy decomposition and remaining term

On the retained family after degree pruning, split distinct unordered pairs by first projected contact with priority:
1 near,
2 short clock tail,
3 both GOOD,
4 RECENT-GOOD,
5 RECENT-THIN,
6 remaining.

The diagonal is O(XB). The first five ordered energy sums are o(XB log^2 B) by (1)-(6), even if an arbitrary subset of the occupied incidences is retained later (using the original full first contact and nonnegative weights). Root deletions affect the linear lower bound; pair deletions affect the energy sum. They must not be conflated.

Thus the original short-clock certificate follows if on unbounded windows the REMAINING whole-pair energy is o(XB log^2 B). A remaining pair is separated beyond d, has substantial remaining clock budget at first contact, is not both GOOD, has no recent-good combination, and if both are recent neither is regular thin. In particular both-deep pairs with two distinct thick regular keys remain, as do pairs lacking recent high anchors. This is not a claim that the remaining class is small. The new bounds reduce actual high-depth and asynchronous pair terms, rather than counting more rare physical vertices.

## 7. Actual finite audit

Standalone ECMAScript research/min_clock_projected_recent_audit.mjs, exact remote readback at f6b5ae194937b49ee30a2beb5f6e4e5fc50ec4e8, blob 8fe05c016c98bac26b54e32061679323b6126a08. Run:

    node research/min_clock_projected_recent_audit.mjs 1024 4096 16384 65536

Actual audit function executed in available JS runtime for all four windows and three modes (12 runs), not a separate local Node invocation. 4658 independent literal parity-GCD comparisons at X1024 per mode. All original source paths followed, including final post-event vertices. Actual degree-based root deletion, reverse leaf/key caps, per-root visit caps, exact first projected contact and distinct incoming label/key assertions. For each current root maintain a local map of earlier root partners and their first-contact class; accumulate all later projected overlap contributions with fractional weights, separately same-state energy, and check (1) per pair. Independent direct E=sum rW^2 matches the diagonal plus six classes. Integer counts exact, fractional energy checked with floating tolerances. The analytic k_g and k both evaluate to zero on all tested windows. Diagnostic k_g=5,k=3,P=ceil(B/4),T=6,tau=Z=12; degree mode uses T=4 and same other settings, intentionally exercising exceptional suffixes and many root deletions. Diagnostic finite thresholds do not satisfy the asymptotic depth regime.

Largest X65536, B678,N32768, analytic no degree deletion: all energy18998125.55, first projected contact pairs2603741, of these144654 same arrival time and2459087 different arrival times. 796598 later first physical synchronizations. The large fraction of asynchronous first projected contacts is why the earlier physical-first-meeting decomposition alone cannot count these pair classes.

Largest diagnostic X65536: 944 roots deleted by shallow degree condition, retained31824, full retained E16529423.70, R373244.5. First projected contacts2438629, asynchronous2301117 (94.36%), same arrival137512; later first physical synchronizations758272. 25348 high hits, recent source visits126942, regular125380; max regular key count4 and max group mass274, max GOOD mass61. Independent overlapping class counts: recent-good468065 (378141 with not both good); recent-thin26182, of which7180 both-deep and6774 both-deep with at least one current C differing from its high anchor. The extended audit explicitly tracks the number of intervening non-LOW selections: 6630 of those both-deep thin contacts have at least one positive non-LOW suffix length; 237877 of the not-both-good recent-good contacts have a positive non-LOW suffix on the recent side. All 12 runs were rerun with these counters and unchanged energy/class totals.

Disjoint priority class energies, rounded, at X65536 diagnostic:

| Class | First contact pairs | Ordered slab energy | Same physical state part |
|---|---:|---:|---:|
|near|114727|1165394|1161232|
|short tail|2244940|25764|25370|
|both GOOD|12346|2807387|2803264|
|recent-GOOD|8931|2322962|2317058|
|recent-thin|336|106714|106714|
|remaining|57349|9882663|9696324|

Diagonal218538.64; the remaining term is about 59.79% of retained E, not negligible at this finite setting. The two new recent classes together contribute about 2.43 million after earlier priority classes. In the degree diagnostic at X65536, 25172 roots removed, retained E676873.87, recent visits22552 of which17177 regular; recent-thin class16 pairs with ordered energy3296.45, remaining295946.07. This demonstrates nonvacuous irregular suffix filtering, but is not a negligible-root asymptotic test.

## 8. Next proof task

The remaining term now explicitly includes thick recent key intersections and high-depth paths with no recent high anchor. An arithmetic count of possible intersecting keys alone cannot bound the mass product of two thick groups. Need a new estimate on actual incoming original-tag masses (or a weighted time/gain argument that bypasses their product). One useful next step is to distinguish first projected contact of two thick distinct recent keys by their last-high times and anchor distances, using the exact clock interval and CRT constraints from the earlier recent-large merger note; retain the residual asynchronous cases separately. No proof of full energy or twin infinitude. Main unchanged.
