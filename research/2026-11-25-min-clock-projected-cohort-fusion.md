# Projected connectivity forests and destination-weighted cohort fusion

2026-11-25 JST. Continues bc057caad390631a6a94b6bcab5ca3bb690c0fb6 (wide primorial transfer), a16e49ac73e59de5b649b03bbb260723dbd212ba (cubic-log support), fa2d2d214de5c446c546913b66cdc851028a8e53 (first projected contact), and adapts the physical truncated potential of the parallel branch research/2026-11-25-min-prime-root-physical-tail-potential.md. New unconditional whole-pair projected connectivity light/light bounds, and a destination-weighted formation potential for fractional relative-clock occupation, including asynchronous projected pairs. The intermediate-sector relaxed target permits polynomial-size component cutoffs. No complete bound for heavy attachments/mergers, no Lean compilation or twin-prime proof.

## 1. Setup

Dyadic X, N=X/2 odd original M in [X,2X), B=ceil(sqrt(7X)), s=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B. Assume H+2B<=min(K-s), eventually. Use actual original full MIN prefix, including root and first post-event state at/beyond relative H, or twin terminal. Strict C growth, C<=2t, total gain <=G=2H+B+6. At active C the wait<=2r(C), r<=selected p. Let w_M(C) be wait clipped to relative [a,H), divided by 2r(C), zero if not occupied. Sector-specific w may further restrict by selected labels or arbitrary nonnegative incidence masks (0<=masked w<=natural w). For any such family,

    R=sum_C r U, E=sum_C r U^2, U(C)=sum_M w_M(C),
    R_M<=B, R<=NB, e(M,M')=2 sum_C r w_M w_M'<=2B.

Here e denotes ordered energy of the unordered pair. Distinct contacting roots have |M-M'|<=G/2, even if only root/final vertices contact. All projected horizons in [2X,7X). Under no twins the full natural R=NB. The least-factor support S(T)=O(XT/log^3(2+T)), S(B)=O(XB/log^3 B), is inherited. The previous wide transfer allows arbitrary primorial L_z<=B^lambda and T=B^delta with 0<lambda<delta<1. Natural MED energy o(XB^(2-2lambda-delta) log^3 B), and retained HIGH energy o(XB log^3 B) with o(XB) HIGH linear loss suffice. MED masks require amplified-loss or actual destination-cost accounting as in bc057ca.

## 2. NEW localized projected connectivity forest

Partition source values M-X into half-open cells of width 16B. Use TWO partitions, shifted relative to one another by 8B. Every pair of contacting roots belongs to a common cell in at least one partition, because its separation <=G/2<8B eventually. Assign it to the unshifted partition if covered there, otherwise to the shifted partition. This is a pair-assignment convention, not duplication of energy. At any horizon J, tags visiting it have sources in an interval of width G/2, so at most two cells of each partition have visitors at J.

In each cell start with singleton components, one per original retained source (the forest may contain any frozen subset of all roots). Sweep horizons in increasing order. At each J, merge ALL distinct current components having at least one visiting tag at J into one component. The tags of a merged component remain joined forever for this bookkeeping, even if their subsequent projected paths diverge. Build an explicit rooted forest by making each merger a parent of the merged components. Each leaf is an original source. There is no expiry: this is historical connectivity, not the actual currently active physical group.

A directly contacting pair belongs to the same component by its first actual common horizon, so it has a unique lowest common ancestor in its assigned forest. Its first CONNECTIVITY horizon can be strictly EARLIER than its first direct projected contact, through third-party roots. This is not a new physical or direct projected meeting; no assertion the two paths share a suffix. Its whole actual future energy is nevertheless <=2B. Every pair of leaves in the same final component is counted once by the cross-child products at its lowest common ancestor, including pairs that never directly meet (safe upper count).

### Arithmetic arity lemma

At a horizon J a visitor has incoming label p (selected on its immediately preceding event), or label 0 if it is its root. For p>0, p divides J or J+2. If two visitors have the same incoming p>0, their preceding horizon J-p+1 is identical, so they are already in the same component in the given cell before processing J. Label 0 belongs to at most one root at a given J. Hence DISTINCT components being merged have disjoint sets of incoming witness labels. In particular arity d<=D(J):=1+#odd p<=B dividing J(J+2). This holds even if the component contains many tags that do NOT visit J, and independent of physical times or earlier depth.

Since product of all distinct factors divides J(J+2), whose log is O(log B), and product of d distinct primes >=d!, Dmax=O(u/log u) with u=log B (the weaker O(u) also suffices below).

With ell=log u, define D0=ceil(40 ell)+1. If D(J)>D0, at least one of J,J+2 has >20ell distinct odd prime factors (up to harmless rounding). By sum_{n<=7X+2}2^omega(n)<=sum tau(n)=O(X log X),

    #exceptional J = O(X u^(1-20 log 2)) = O(X/u^12).

At most FOUR cell mergers occur per J across the two partitions. This arithmetic exception bound is for merger vertices, not actual pair masses.

## 3. NEW whole-pair light/light energy

For a threshold m>=1, call a child component light if its size <m, heavy otherwise. At a merger with child sizes n_i, let s be the sum of light sizes. The number of unordered newly connected light/light pairs is

    L_v = (s^2-sum_{light i} n_i^2)/2.

If the new total n<m, charge the pair to its maximal light subtree. Those subtrees are disjoint, so the number of such pairs across one partition <=Nm/2. If n>=m, every member of each light child crosses the heavy threshold for the FIRST time at this merger. Consequently sum s over all n>=m mergers <=N. At normal arity d<=D0,

    L_v<=s^2/2<=D0*m*s/2.

At exceptional horizons use the crude L_v<=Dmax^2*m^2/2, and count at most four cell mergers per horizon. Combining across the two partitions, the total number of light/light formed pairs obeys both

    F_LL=O(N Dmax m),
    F_LL=O(N D0 m + X u^(-12) Dmax^2 m^2).              (1)

The first estimate is useful at polynomial thresholds, the second at polylogarithmic thresholds. Actual contacting pairs assigned to a partition are a subset of these leaf pairs. Since their entire energy <=2B, for arbitrary natural or masked sector weights,

    E_LL <=2B F_LL.                                    (2)

No absolute-depth restriction, recent-high anchor, uniform projected mass cap, exceptional-root pruning, or common physical suffix is needed. Even a light/light formation event that also joins already huge groups is included; its own light children are disjoint from the heavy ones. All later asynchronous and synchronous overlaps of its assigned light/light pairs are counted. The classification is on HISTORICAL component sizes at first connectivity, not on visit counts of those roots at that J.

In particular m_h=floor(u^(11/4)) gives E_LL=O(XB u^(11/4)(1+ell))=o(XB u^3). More generally any m=o(u^3/(1+ell)) at a fixed polynomial-log scale is admissible in the second bound. Unlike small-total-merger bounds, (1) includes light-light products at mergers whose parent contains a huge heavy child. No bound for large-child cross products follows merely from small arity.

Heavy formation facts: heavy births (merger of only light children whose new mass >=m) are at most N/m per partition, since their leaf sets are disjoint. At mergers with h>=1 heavy children, sum(h-1) is at most the number of heavy births, and the total mass of light children attaching there <=N. These statements hold without monotonicity of actual active tag counts because the bookkeeping components never split. They do not bound energy of a heavy component that absorbs many small children: a combinatorial comb with successive singleton attachments has O(N) mergers and quadratic cross-pair count even with no heavy-heavy merger. This is a limitation of the potential approach, not a constructed MIN counterexample.

## 4. NEW destination-weighted cohort forests

The full projected forest may join large numbers of irrelevant roots through indirect contacts. For each final evaluation horizon C fix a sector/mask and keep ONLY tags with positive actual weight w_M(C). Give each of them the fixed leaf weight w_M(C), between 0 and 1. Keep their ORIGINAL full prefix histories through C, even where their sector/mask weight at earlier horizons was zero. The weights are held constant throughout this auxiliary forest; they are not the actual time-dependent occupancies at those earlier horizons.

Construct the projected connectivity forest as above for this single cohort, processing J<=C, without source-block partitions (all these sources are already within the local support interval). Every leaf reaches C, so the final component contains the whole cohort, with total mass U(C). At a merger let a_i denote the SUM of leaf weights in child i, a=sum a_i. Exactly

    sum_mergers (a^2-sum a_i^2) = U(C)^2-sum_M w_M(C)^2. (3)

This partitions all OFF-DIAGONAL projected energy at C, including asynchronous pairs. It is an algebraic allocation to first connectivity, NOT a claim every cross-child pair actually shared the merger horizon J. All pairs in the cohort actually share the final C. The arity lemma remains true because same-label active visitors' predecessors occur in the original prefix histories of both retained leaves.

There is a second, physical version: process actual (t,J) instead of J, keeping exact time. If two cohort roots meet physically, they remain on the same suffix through C since both reach C. Therefore each component arriving at a physical merger is an actual physical predecessor group (root singleton allowed), and the merging event is the true first physical meeting for its cross pairs. Final components at C are exactly the distinct arrival times. Thus (3) with U(C)^2 replaced by the sum of squared same-time masses is an exact allocation of only the SAME-STATE energy at C. Projected and physical partitions are different ledgers, and their small-term energies must not be added as disjoint pieces.

## 5. NEW fractional truncated formation potential

At any fixed cohort use f_m(x)=x^2 for 0<=x<=m, and 2mx-m^2 for x>=m. This convex nonnegative function is superadditive (derivative nondecreasing, f_m(0)=0), with derivative <=2m. For each merger,

    D_v=f_m(a)-sum_i f_m(a_i)>=0.

Exact telescoping, allowing several physical final components A, gives

    sum D_v=sum_final A f_m(a_A)-sum_leaves f_m(w)
           <= 2m U(C).                                 (4)

No cutoff expiry correction is necessary because leaf weights are fixed at the evaluation horizon and every included history actually reaches C. Whenever a<=m, D_v equals the entire ordered cross-child product. Multiplying by r(C) and summing over all C yields

    E_cohort,small-total <= 2m R.                       (5)

This controls actual fractional occupations, not count masses, and holds for arbitrary sector/incidence masks, including where natural wait intervals of physically synchronized tags intersect the relative slab by different fractions. No use of the full-wait equality e=2min(tails), which would be invalid for fractional slab clipping. In particular at m_h=u^(11/4) it is o(XB u^3) with no lower remaining-tail cutoff or restriction on the incoming label.

Physical hierarchy: group the child weights by incoming selected label p, b_p=sum_{i:label p} a_i, with p=0 for the root group. Then

    D_v=[f_m(a)-sum_p f_m(b_p)]
          +sum_p[f_m(b_p)-sum_{i:label p} f_m(a_i)].

Every bracket is nonnegative. At a>m, the inner bracket for b_p<=m equals the ordered same-label cross product, even when the other labels have huge masses. Therefore the physical small-total term plus the small-label internal products at larger mergers together satisfy the SAME 2m R bound (5), rather than requiring a second budget. This extends the parallel prime-root natural-tail result to arbitrary fractional short-slab masks.

For projected cohorts, also classify ALL light/light cross-child products with a_i,a_j<m, including a>=m. The proof of (1) applies to nonnegative weighted leaves: disjoint maximal light subtrees cost <=m U(C) in ordered weights; light child weight at heavy crossing summed over all such mergers <=U(C); arity <=Dmax. Consequently

    E_cohort,LL <= (1+Dmax) m R.                       (6)

Here one must not use the rare-degree count over J from section 3 unaltered, because a given J can recur in many final C cohorts. Using Dmax=O(u/ell), (6) at m=u^2 gives O(XB u^3/ell)=o(XB u^3). One can use this threshold for the extra light/light terms, and the larger m_h=u^(11/4) in (5), taking the union with disjoint priority. These bounds do not require small total mass at the final C. Weighted heavy births and heavy-branch excess are each <=U(C)/m in a cohort; light attaching weight <=U(C). After summation with r(C), the bounds become R/m and R, respectively (weighted counts, not distinct global vertices). No saving on arbitrary cross products with large groups is implied.

## 6. NEW combination with the polynomially relaxed MED condition

Choose a different primorial from bc057ca's widest one: z largest prime cutoff with L_z<=B^(1/16) (eventually z=Theta(log B)), T=ceil(B^(1/4)). The natural MED sector z<p<=T then has sufficient target

    E_m=o(X B^(13/8) u^3),                             (7)

since 2-2/16-1/4=13/8. The HIGH sector p>T retains the cubic-log target E_h,J=o(XB u^3) with o(XB) HIGH linear deletion. The lower cutoff z still has order log B, but the chosen primorial is narrower than the previous B^(1/3)/f; this is an explicit choice trading the cutoff constant for a polynomial margin.

In the MED sector use m_M=floor(B^(5/8)). The elementary first bound in (1)-(2) proves for raw historical light/light pairs

    E_m,LL=O(X B^(13/8) u)=o(X B^(13/8) u^3).
    
The weighted cohort (6) gives the same upper bound, even with all arbitrary later masks; for (7) we use NATURAL MED weights to avoid amplified loss of LOW transfers. The MED diagonal O(XB) is negligible. Thus **both** raw-forest light/light and weighted-cohort light/light terms are independently negligible at the required MED scale. They may overlap; use union or disjoint priority, not raw subtraction of two ledgers. The remaining MED energy must involve at least one heavy child at both classifications (if the pair/incidence survives both). In the destination cohort this means an actual final occupation-weight sum >=B^(5/8) in one incoming historical component. In particular the final projected weight U_m(C)>=B^(5/8). This gives a polynomial threshold for the unresolved medium obstruction, with no need to evaluate LOW energy independently.

For HIGH use the m_h choice in (2),(5), and m=u^2 in (6). All removed energy terms and diagonal are o(XB u^3). One can additionally remove the physically synchronized small-total/label terms using (5), counting each actual pair incidence once. Earlier HIGH-only linear marks may be imposed on the weights before building each weighted cohort (all original prefix histories preserved). If the two residuals satisfy (7) and the HIGH cubic-log bound on the same unbounded windows, the wide primorial transfer forces twins. The residual is not bounded here. Specifically, both the raw and weighted approaches allow repeated light-to-heavy attachments; the number of heavy-heavy mergers alone does not control them.

## 7. Actual verification

Two standalone ECMAScript audits, both exact remote readback:
- research/min_clock_projected_union_forest_audit.mjs, commit 46f001070715f824c8c08c22bb5152ef1863952d, blob b41870c4642050f85a75cda7d5463f614206e9dc.
- research/min_clock_cohort_fusion_audit.mjs, commit d96eae01c0aa1dd4c38a0fecca4e595d7dad94f7, blob b4a838b8c29e2fe023264e9b6dc3da50f9cbd45e.

Run either with Node and arguments 1024 4096 16384 65536. Each audit function actually executed in the available ECMAScript runtime, four windows x three modes (12 successful runs each). All odd roots, no prior pruning, not a cumulative prior residual. Independent literal parity-GCD comparisons at X1024. Full actual prefix including final vertex. Raw audit verifies block cover, distinct incoming label witnesses, forest LCA of every directly contacting pair, pair energy identity, exact integer counts/potential/threshold-crossing/arity bounds. Weighted audit independently replays every positive occupation cohort's original prefix through C with projected and physical keys; verifies exact fractional energy and same-time oracle, potential and label hierarchy, weighted heavy thresholds and arity. Floating tolerances used. Counts of sector contacting pairs in raw output include zero-energy contacts; do not interpret as positive-energy counts.

At X65536,B678,N32768,794415 selected events, total R402074, E18998125.55. Raw partitions have 25945 and 25955 merger vertices, max arity5 despite arithmetic degree cap9. 2603741 distinct directly contacting pairs, of which 1619371 (62.19%) have first historical connectivity STRICTLY before first direct projected contact. Such pairs carry ordered energy11207349.22. 70044 pairs assigned shifted partition. These numbers illustrate why projected connectivity and actual first contact are not interchangeable.

Analytic cutoffs here z2,L2,T6,mH173,mM58; these finite parameters do not reach the logarithmic primorial asymptotics. Standard diagnostics z3,L6,T27,mH8,mM12,D0=4; wide mH16,mM24 (same natural sectors). D0 diagnostic is intentionally small, not the analytic rare-set estimate. Analytic no exceptional vertices. Standard first partition at mH8 heavy births454, branch excess406, light-attachment mass28033; total all connected pairs45514841, of which many never directly meet. Max raw arity5; weighted physical arity9. Heavy-light formation dominates the raw tree cross products, so the larger indirect forest is not automatically an efficient energy classifier.

Largest analytic HIGH natural E17307768.70, diag214766.48, raw light/light energy860419.42. Destination cohort high weighted small-total16881676.60, extra light/light12847.36, light/heavy198478.26, heavy/heavy0 (all offdiagonal). One high occupied horizon has U>=173. This is largely a finite mass-cap effect, not asymptotic evidence. For comparison use wide diagnostic (mH16,mM24) with nontrivial residuals:

| sector | total E | diag | raw light/light | cohort small total | cohort extra light/light | cohort light/heavy | cohort heavy/heavy |
|---|---:|---:|---:|---:|---:|---:|---:|
| MED |2733359.93|41523.52|134490.25|789307.64|241031.27|1501988.58|159508.92|
| HIGH |15313316.11|183442.18|541406.89|2525690.87|828721.75|9421604.22|2353857.09|

The projected cohort columns after diag partition the actual off-diagonal energy; the raw light/light column is a DIFFERENT classification, not another part of that partition. In wide, high 192 occupied horizon cohorts, 7287 positive tag incidences, max weight186.52, 51 cohorts above/equal16; medium 435 cohorts,16650 tag incidences, max weight130.91, 116 above/equal24. The physical HIGH cohort off-diagonal ledger (wide) yields 14949632.64, of which small-total2579655.49, extra small-label hierarchy57116.46, counted disjointly for (5). The physical and projected light terms overlap and the audit does not calculate their cumulative union. The cohort audit's finite upper bounds use measured Dmax; asymptotic factor u/ell and exceptional estimates are paper deductions. No numerical conclusion of little-o.

## 8. Next step

The medium obstruction has a polynomial occupancy threshold, and the projected and physical energy can now be assigned to formation events using final weights rather than raw ancestors or equal-relative-age tails. The outstanding terms are large-component attachments and heavy-heavy products. The observed light-heavy dominance makes controlling repeated attachments, rather than merely counting heavy-heavy births, a concrete next task. A useful direction is to exploit the actual visiting witness subset at each attachment and its time separation from the heavy child's prior visitors; historical component size alone is too coarse. No complete MED or HIGH estimate, no Lean compilation, main untouched.
