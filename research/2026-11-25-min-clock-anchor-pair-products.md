# Physical last-high anchor pairs: CRT counts, weighted tail products and time-refined thin groups

2026-11-25 JST. Continues fa2d2d214de5c446c546913b66cdc851028a8e53 (all-source projected first contact), f83cb64cd8d883e3fdbb0dcfff3b9773f552e3ac (degree pruning) and 25473614cf384cff0d8af534e34404cd774ae053 (short-clock slab). This is an unconditional whole-pair energy deletion for close physical high anchors with bounded ACTUAL group tail product, even when their later histories are arbitrarily long and both groups are thick. It also refines the previous thin-key lemma by physical clock time. It does not bound every thick-group product. Paper proof, not Lean-compiled.

## 1. Setup and pair conventions

Dyadic X, N=X/2 odd original M in [X,2X), B=ceil(sqrt(7X)), canonical root (s,C0)=(M+2,2M-2), original K=floor((7M-1)/4). H=4B,a=2B; assume H+2B<=min_M(K(M)-s), eventually. Use the actual original MIN prefix through the first vertex at or beyond relative age H, or twin terminal. Full horizon lists V_M include root and final vertex. Strictly increasing C and t, invariant C<=2t, waiting length <=2r(C), r<=selected p<=3(p-1)/2. The total gain including the possible final crossing event is <=2H+B+6. All post-event vertices satisfy

    0<=2t-C<=2(H+2B)+6=12B+6.

The even horizons lie in [2X,7X), the times in an interval of length O(X). For each source, w_M(C) is the clipped occupation of relative slab [a,H) divided by 2r(C), zero at terminal or unoccupied. Define R_M(J)=sum_{C>=J} r(C)w_M(C), R_M<=B, R=sum R_M, E=sum_C r(C)(sum_M w_M(C))^2. The short-clock target is E=o(XB log^2 B) (on unbounded dyadic windows). For any distinct unordered contacting pair, J*=min(V_M intersect V_M'), its ORDERED whole energy e(M,M')=2 sum_C r w_M w_M' satisfies e<=2min(R_M(J*),R_M'(J*))<=2B. This includes every later separation and projected recontact, not merely the physically synchronized suffix. All arguments apply to any retained original-root family. If o(X) roots removed, hypothetical no-twin R=(N-o(X))B; the energy target for that retained family is still sufficient.

Use P=ceil(B/log^(1/8) B), A=max(1,floor(log^(1/8) B)). Call p>=P high. For a visited horizon C after at least one completed high event, define its LAST-HIGH PHYSICAL ANCHOR

    alpha=(u,J,p),

where u,J are actual time and post-event horizon of its latest high selection p. This anchor is defined even if its history is no longer RECENT in the previous note. There is NO restriction on number, sizes, regularity or gains of the intervening non-high selections. In particular it covers arbitrarily deep paths. No anchor for a history with no high selections.

## 2. NEW uniqueness of first projected contact per physical anchor pair

Suppose a pair of original roots has first projected contact C*, and both last-high anchors alpha=(u,J,p), beta=(v,J',q) exist by that contact. They have distinct projected keys (J,p)! If both keys equal and J<C*, both roots visited J earlier. If J=C*, both visited the same predecessor J-p+1 earlier. Either contradicts firstness.

For fixed physical anchor pair alpha,beta, there is AT MOST ONE horizon C* that can be the first projected contact of any such pair after both anchors. Proof: from a fixed physical vertex (u,J), the actual MIN forward choices are deterministic until the source's cutoff or twin. All prefix continuations from it are prefixes of the same forward sequence; different root-dependent cutoffs only truncate it. Likewise for beta. If both sequences reach some shared C*, the first common horizon of the two continuations up to C* is uniquely defined. Since both anchors are included in the original lists, a first original contact at/after them must be this first continuation intersection. If some roots have earlier prefix contact, they are excluded from this first-contact class and can only reduce its mass. Thus if two different original pairs qualify for the same anchor pair, their contact C* agrees. This argument does not assert that the continuations agree at or after C*; arrival times can differ and paths can split. It uses the exact physical time to define the deterministic continuations, not a projected-horizon-only dynamics. No upper bound on the suffix length from alpha or beta is necessary.

This allows one to count anchor PAIRS once, rather than possible contact horizons or suffix offsets. There can be large numbers of original pairs per anchor pair; that weight is accounted for below.

## 3. NEW close-anchor arithmetic count for distinct high labels

Say alpha,beta are close if either |J-J'|<=A OR |u-v|<=A. It is a union, not simultaneous closeness. The arithmetic of actual post-events is

    even u: u=0 mod 2p, J=0 mod p;
    odd u:  u=p+2 mod 2p, J=-2 mod p.

Analogously for beta. In addition both deficits belong to [0,12B+6].

First assume p!=q. For horizon-close anchors, fix an integer e=J'-J with |e|<=A and the two parity sides. Then J has a specified residue modulo p and a specified residue modulo q. CRT gives O(1+X/(pq))=O(X/(pq)) possible J in the full window, since pq<=B^2=O(X). For each fixed J and side, u is in an interval of length O(B) by the deficit strip and one class modulo 2p, giving O(1+B/p)=O(B/p) possible u. Similarly beta has O(B/q) times. Thus the count for fixed p,q is O((A+1) X B^2/(p^2 q^2)).

For time-close anchors fix v-u and the two parity sides. Now u has two specified residues modulo p,q, giving O(X/(pq)) possible u. For each fixed u the even J in the deficit strip satisfying its side congruence has O(B/p) possibilities, likewise J' has O(B/q). This gives the same bound. Both counts are arithmetic upper envelopes for all possible physical anchors, independent of which are actual.

Elementary prime counting plus dyadic summation gives sum_{p>=P} 1/p^2 = O(1/(P log P)). Consequently the number K_dist of unordered pairs of different-label high physical anchors in the union of these two close classes is

    K_dist = O((A+1) X B^2/(P^2 log^2 P))
           = O(X (log B)^(-13/8)).                    (1)

Here A=O(log^(1/8) B), B/P=O(log^(1/8) B). By section 2 each such pair can support at most one first projected contact. This CRT count has no factor for the length of later continuation, nor a factor counting possible C*.

## 4. NEW close same-label anchor count and geometry

If p=q and the projected keys are distinct, assume A<p-2 (true eventually). If the two horizons are close, then they cannot be on the same side: their difference would be a nonzero even multiple of p, of magnitude >=2p. Opposite sides imply |J-J'|=2, since these horizons are even and their residues differ by 2 modulo p. Their absolute clock times then differ by at least p-2, by the even/odd clock classes modulo 2p. Thus

    |J-J'|<=A  => |J-J'|=2 and |u-v|>=p-2.

If the times are close, then the clock residues force equal parity and u=v. Distinct projected keys now imply |J-J'|>=2p. In particular they cannot be close in both coordinates.

For the near-horizon case there are O(X/p) choices of J, O(1) choices of J' and sides, and O((B/p)^2) choices of times. For near-time there are O(X/p) choices of u, v=u, and O((B/p)^2) horizon choices. The same-prime count does not carry an A factor. Using sum_{p>=P} p^-3=O(1/(P^2 log P)) gives

    K_same = O(X B^2/(P^2 log P))
           = O(X (log B)^(-3/4)).                     (2)

Only distinct projected keys are counted, as equal keys cannot produce first contact by section 2. For near-horizon same-prime anchors, at their first contact C*, the two arrival times satisfy

    |t-t'| >= max(0, |u-v|-3 max(C*-J,C*-J')).

Indeed each elapsed time since its anchor is nonnegative and <=3 times the gain, so their elapsed-time difference in absolute value is at most the larger such upper bound. Any later physical synchronization at horizon D requires D-C* >= |t-t'|/3 (the earlier-time path must advance at least the lag before reaching the synchronized state). These inequalities exhibit a genuine asynchronous obstruction, but are not themselves a bound on all later asynchronous pair energy.

## 5. NEW actual weighted group products, not uniform small-mass assumptions

At the unique first suffix intersection C* of a qualifying physical anchor pair define G_alpha to be all retained actual original tags visiting C* whose last-high anchor is alpha there. Similarly G_beta. These may include roots whose first mutual contact was earlier (an overcount is safe). Put

    n_alpha=|G_alpha|,   T_alpha=sum_{M in G_alpha} R_M(C*);
    n_beta=|G_beta|,     T_beta=sum_{M in G_beta} R_M(C*);
    W_alpha,beta = min(n_beta T_alpha,n_alpha T_beta)/B.

Every original pair in the first-contact class has distinct tags from these two disjoint groups, and e<=2 min(R_M(C*),R_M'(C*)). Summing over first-contact pairs and enlarging to the product of groups gives the actual WHOLE ordered energy bound

    E_alpha,beta <=2 min(n_beta T_alpha,n_alpha T_beta)
                 =2B W_alpha,beta.                    (3)

Also W<=n_alpha n_beta because each R_M<=B. The weight W can be much smaller than the raw group product; no uniformity of actual source masses or future tail costs assumed.

For close distinct-prime anchor pairs with W<=K_d=(log B)^(7/2), sum (3) over (1):

    E_close,distinct,cap
       <= O(B K_d K_dist)
       = O(XB (log B)^(15/8))
       = o(XB log^2 B).                               (4)

For close same-prime anchor pairs with W<=K_s=(log B)^(5/2), (2) gives

    E_close,same,cap
       <= O(B K_s K_same)
       = O(XB (log B)^(7/4))
       = o(XB log^2 B).                               (5)

Both are genuine bounds on actual original-pair energy, including arbitrary later overlap. Unlike the previous thin-group theorem, (4) admits, for example, two groups each of size <=(log B)^(7/4), even when both exceed the previous thin threshold (log B)^(3/2), simply by n_alpha n_beta<=K_d. The actual tail condition admits additional pairs with raw group product >K_d. The other side may have very large mass as long as the stated weighted product is bounded. The proof does NOT establish that all close-anchor pairs satisfy this cap, and says nothing about arbitrary far-anchor or anchorless pairs.

More generally P=B/log^beta B, A=log^delta B for fixed beta,delta>0, weighted cap log^gamma B, give E_dist=O(XB log^(gamma+delta+2beta-2) B) (negligible when gamma+delta+2beta<4) and E_same=O(XB log^(gamma+2beta-1) B) (negligible when gamma+2beta<3). These tradeoffs quantify how much larger the two incoming masses may be than a thin group. They use exact time even when only horizon proximity is assumed.

## 6. NEW physical-time refinement of the previous recent-thin class

Keep the previous note's parameters ell=loglog B, slowly growing even primorial L, T=ceil(20ell), g=max(2,TL), k=floor(ell/(8 log g)). A history RECENT has <=k subsequent non-LOW events since its last high; REGULAR if all those subsequent non-LOW post-horizons have reverse degree <=T. As proved there, there are at most O(Lg^k)=log^(1/8+o(1)) B projected regular keys (J,p) at C; total recent incidences V_rec=O(N(B/P)(k+1)L)=X log^(1/8+o(1)) B.

Now subdivide each regular projected key by actual high clock time u. For fixed J,p there are at most O(B/p)=O(log^(1/8) B) possible times (sum over two sides) by the deficit strip and clock period. Thus the total count of REGULAR PHYSICAL keys at any C is log^(1/4+o(1)) B. Each regular physical group consists only of actual retained regular recent tags having this full key. The old thin criterion n_projected<=tau implies the new one n_physical<=tau; converse need not hold. Let tau=log^(3/2) B. For both-RECENT first contact pairs with at least one REGULAR PHYSICAL group of mass <=tau, count from the other recent incidence, using the physical regular key cap and tau per thin group. Thus

    F_physical_thin <= V_rec * log^(1/4+o(1)) B * tau
                     = X log^(15/8+o(1)) B,
    E_physical_thin <=2B F_physical_thin
                     = o(XB log^2 B).                 (6)

The other side may be arbitrary recent, including an irregular suffix or large group. The whole ordered pair term (6) therefore extends the previous recent-thin deletion even if the previous projected group is thick. The cap is on actual regular source-tag mass per physical key, not the count of allowed clock residues. No time averaging or stochastic independence is assumed.

## 7. Combined reduction

Use degree-pruned original source family of fa2d2d2 (o(X) source tags removed analytically), optionally with other already valid root deletions. Use original full horizon lists to classify first contacts. The diagonal and previous near, short-tail, both-good, recent-good and recent-thin terms are o(XB log^2 B). Add (6), (4), (5) in priority order, subtracting overlapping classes only once. Equivalently use union upper bound. The additional classes genuinely remove whole-pair terms from the energy, not just a count of arithmetic vertices. The residual includes:
- both last-high physical anchors far in both coordinates, or close but their actual weighted product exceeds the cap;
- absence of one or both high anchors, or long histories not covered by previous pair classes.
There is not yet an estimate for the sum of those residual products. In particular the CRT rarity (1) is not used to multiply by a fictitious average group mass.

## 8. Actual finite verification

Standalone ECMAScript research/min_clock_anchor_pair_audit.mjs; exact remote readback at 5734d9e9b084866817b842984ea7c241beb33697, blob ed5e21749a331585dddf6a17ce9dd000efc65ffa. Run from repository root:

    node research/min_clock_anchor_pair_audit.mjs 1024 4096 16384 65536

Executed actual audit function in the available JS runtime for four windows x three modes (12 successful runs, repeated after adding independent relaxed arithmetic enumeration). Not a separate local Node run. Initial execution failed due to duplicate declaration of diag; corrected before successful runs/commit. 4658 literal parity-GCD checks at X1024 per mode. Full original root paths and per-root clipped occupation preserved; verifies physical anchor clock residues, deficit strip and deterministic continuation time at common C; regular physical key count, first-contact distinctness and uniqueness per close physical anchor pair; per-pair energy and aggregate group bound (3), whole energy decomposition by independent sum rW^2, arithmetic envelopes of (1),(2). Uses a source-local map of earlier root pairs; one global map for observed close anchor contacts. Integer counts exact; fractional weights tested with numerical tolerance.

The analytic mode uses A=floor(log^(1/8)B)=1 in all tested windows, k_g=k=0, and no close anchor first-contact pairs occur: the new CRT classes are vacuous in these finite analytic runs. Diagnostic P=ceil(B/4), A=max(2,floor(P/8)), T=6,k_g5,k3,tau=Z=12, K_d256,K_s144 (degree mode T4). The diagnostic thresholds are chosen to exercise classes, not to approximate asymptotic rates. At X1024 diagnostic independent enumeration of ALL relaxed arithmetic anchors (not actual paths) yields 5666 anchors, 78058 close distinct-prime pairs, 20201 near-horizon same-prime pairs and 37708 near-time same-prime pairs after excluding equal projected keys. It verifies the same-prime geometry and the arithmetic envelopes on both nonempty classes. Analytic relaxed enumeration also has 1491 near-time same-prime pairs despite no observed actual first contacts.

Largest X65536, B678 diagnostic, P170,A21: 944 original tags removed by shallow degree pruning, 31824 retained, E_kept=16529423.70, R_kept=373244.5. 1103 distinct actual physical last-high anchors, 2438629 first projected original pairs. 178 distinct-prime close physical anchor pairs supporting first projected contacts, one same-prime near-horizon pair (10 original pairs, zero slab pair energy), no actual same-prime near-time pair. Integer arithmetic upper envelopes 623637944 and 38260792, very loose finite overcounts. Maximum observed raw group product5699. Independent overlapping class counts:
- physical-thin 30872 first pairs, 4690 not old projected-thin;
- distinct-anchor weighted cap 44551 original first pairs, 21505 both physical masses >12, 21357 both histories deep, 9500 at least one side has more than k subsequent non-LOW selections (beyond RECENT window), 35616 raw group product>256 but actual weighted cap<=256.
- aggregate eligible distinct-anchor energy281043.22 <= actual summed group tail bound604319 (before priority partition). This is nonvacuous weighted product accounting, including thick and deep histories. Count of weighted-extra pairs includes zero energy contacts.

Disjoint new classes after previous priority at X65536 diagnostic:

| Class | First pairs | Ordered slab energy |
|---|--:|--:|
| physical-thin extra |110|31302.06|
| close distinct-anchor cap |481|187133.73|
| close same-anchor cap |0|0|
| remaining |56758|9664226.81|

Previous remaining 9882662.60, now reduced by 218435.79. New physical-thin energy is entirely asynchronous in this particular diagnostic (same physical state contribution 0); close distinct-anchor energy entirely same-state. Remaining ~58.47% of retained E. Degree diagnostic at X65536, 25172 root tags deleted, E_kept676873.87, new close distinct-anchor cap17 first pairs with energy12832.22, residual283113.85. These are finite classifications, not a claim of asymptotic proportion or negligible root removal at those sizes.

## 9. Remaining proof task

The new count uses proximity of the actual high anchors, not proximity of the final contact or short suffix gains. It handles arbitrary later depths and weighted thick pairs up to explicit caps. Need a genuinely new bound for the sum of products ABOVE those caps and for far/anchorless histories. The data show that the new close-anchor class is not the dominant residual. A useful next direction is to bound source-tag weights at physical anchors before their first contact (or to charge their weighted cross products to a bounded sequence of earlier ancestor interactions), while preserving relative cutoffs. Counting more rare anchor vertices alone cannot solve the heavy-product obstacle. Main unchanged; no Lean compilation or proof of twin-prime infinitude.
