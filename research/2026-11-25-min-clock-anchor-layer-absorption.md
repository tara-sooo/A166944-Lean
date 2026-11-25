# Dyadic tail layers and absorption of imbalanced physical anchor contacts

2026-11-25 JST. Continues 73d8d17df179b01c1787a8e25c48fc7a3152a267 and fa2d2d214de5c446c546913b66cdc851028a8e53 on the all-source short-clock slab. New thin-tail-layer estimate without a product cap, and an energy absorption inequality for sufficiently imbalanced large-tail layers, even if both groups are thick. This is a self-bounding estimate in terms of actual internal-pair energy, not a proof that all heavy groups are rare. Paper proof, no Lean compilation; twin infinitude OPEN.

## 1. Setup

Use dyadic X, N=X/2 odd original roots M in [X,2X), B=ceil(sqrt(7X)), root (s,C0)=(M+2,2M-2), original K(M)=floor((7M-1)/4), H=4B, a=2B and relative slab [a,H). Assume H+2B<=min_M(K(M)-s), eventually. Use actual full prefix including initial and final post-event vertex. At positive active r(C) the wait is <=2r(C), r<=selected p<=1.5(p-1), C<=2t and total gain including final crossing <=2H+B+6. At a twin stop. For each original tag, let w_M(C) be its clipped slab wait duration divided by 2r(C), zero outside occupation, and R_M(J)=sum_{C>=J} r(C)w_M(C) over its prefix. Then R_M<=B. Let E=sum_C r(C)(sum_M w_M(C))^2 for ANY retained family of original tags; ordered distinct-pair energy e(M,M')=2 sum_C r w_M w_M'. The target is E=o(XB log^2 B); under no twins, removing o(X) entire tags leaves R=(N-o(X))B. No removed-pair-energy assumption follows from root pruning.

At first projected contact C*=min(V_M intersect V_M'), e(M,M')<=2 min(R_M(C*),R_M'(C*)). If both tags have last-high physical anchors alpha=(u,J,p), beta=(v,J',q) with p,q>=P, the anchors are distinct, and a fixed anchor pair has at most one possible first projected contact after both anchors. These statements were proved in 73d8d17: physical deterministic continuation from each anchor implies the uniqueness even with root-specific truncation. All later overlaps are counted, even if paths split and recontact.

Take P=ceil(B/log^(1/8)B), A=max(1,floor(log^(1/8)B)). Call anchors close when |J-J'|<=A OR |u-v|<=A. The new estimates do not require bounded suffix depth or local regularity after the anchor, and include same or distinct high labels.

## 2. NEW local adjacency cap, rather than total rare-edge count

Form a graph on actual physical high anchors with an edge for closeness. It is harmless to enlarge to all arithmetic candidates. For fixed anchor and each even J' in the A-neighborhood of J, any high p' divides J' or J'+2. There are O(1) possible p'>=P, by the product of distinct prime factors and log P~log B. For each p' and side the time u' has one residue modulo 2p' and 0<=2u'-J'<=12B+6, giving O(B/P) possibilities. For each u' in the A-neighborhood of u, any high p' divides u' or u'-2; again O(1) labels and O(B/P) horizon choices. Thus MAXIMUM DEGREE, including same-label pairs, satisfies

    D = O((A+1) B/P) = O(log^(1/4) B).                (1)

Each original source has at most h=floor((2H+B+6)/(P-1)) high selections, since total gain is bounded and each high gain>=P-1. Thus h=O(log^(1/8)B) and the sum of original tag masses over all physical anchors is <=Nh. This degree estimate is independent of actual ancestry size. The earlier CRT total-edge count remains useful for bounded product classes; (1) is a different estimate.

## 3. Dyadic tail profiles and NEW thin-layer estimate

For every physical anchor alpha and 0<x<=1 define

    a_alpha(x) = #retained original tags visiting alpha as a selected high post-event,
                 with R_M(J_alpha)>=xB.

At a qualifying close anchor pair's unique first contact C*, let

    n_alpha(x) = #retained tags at C* with last-high anchor alpha and R_M(C*)>=xB,

and analogously beta. These are actual source-tag counts, not representative counts. Monotonicity of the remaining cost yields n_alpha(x)<=a_alpha(x). We have sum_alpha a_alpha(x)<=Nh at every x.

For each original unordered first-contact pair with positive min remaining cost choose its unique dyadic x=2^-j such that

    x B <= min(R_M(C*),R_M'(C*)) < 2 x B.

If the minimum equals B use x=1. Zero-tail pairs have zero energy. Half-integer slab costs imply only finitely many positive levels; the proof would also work by convergence. At that level there are at most n_alpha(x)n_beta(x) original first-contact pairs for a fixed anchor edge. Each has e<=4Bx. It is important to use the actual tails at C*, not to impose a uniform distribution on group members.

Call a level THIN if min(n_alpha(x),n_beta(x))<=tau, with tau=log^(3/2)B. At any level, summing the products over thin edges is <=tau D sum_alpha a_alpha(x), orienting each edge toward the larger contact group. Hence, summing the geometric x series,

    E_thin <= sum_x 4Bx tau D Nh
            <=8 B tau D Nh
            =O(XB log^(15/8)B)=o(XB log^2B).          (2)

This counts entire later original-pair energies, not merely their part in one waiting interval. It works for arbitrary deep histories, arbitrary raw mass product, and arbitrary irregular suffix; even the thinner contact group may be huge at lower tail levels. In particular, no cap on the OTHER group's mass is required, unlike the previous CRT product-cap class. The earlier physical-thin result required both histories RECENT; (2) has no recent-depth restriction, only close physical anchors.

## 4. NEW internal energy lower bound

Fix one physical anchor alpha=(u,J,p). Two distinct tags M,M' visiting this same anchor have an identical physical continuation until either truncated prefix ends. Suppose both have R_M(J),R_M'(J)>=xB and |M-M'|<=xB. From u onward their occupied absolute-time intervals are [max(u,M+2+a), min(M+2+H,twin arrival)] and the corresponding interval for M' (use infinity for no twin before the later endpoint). This is valid up to both root cutoffs by the prefix gate. The intervals have lengths 2R_M(J),2R_M'(J), at least 2xB, and their start times differ by at most |M-M'|<=xB. Hence their intersection has length >=xB. For every common waiting state let lambda(C) be the portion of this intersection at C. Then e(M,M') >= sum lambda(C)^2/(2r(C)). The sum of r over these distinct waiting states is <=1.5(2H+B+6)<=24B by the gain cap on either path. Cauchy gives

    e(M,M') >= x^2 B/48.                              (3)

Here e is the ACTUAL full slab pair energy, not the upper budget used for a cross-anchor pair. The internal pair's first physical meeting is no later than the anchor, and first projected contact is strictly earlier (both share J-p+1). Its energy may accrue later in time; the argument does not claim it was incurred before the new contact.

At each alpha partition its original roots with tail>=xB into source-value cells of width xB. They lie in an interval of length <=H+B/2+3=O(B) by the prefix gain cap, so at most 10/x cells suffice (half-open aligned cells; use the bound for sufficiently large B). If cell masses are m_c,

    a_alpha(x)^2 <= (10/x) sum_c m_c^2
                 = (10/x)(a_alpha(x)+2 sum_c binom(m_c,2)).

For each pair in a cell, (3) applies. A fixed original pair shares at most h physical high anchors, since each root has at most h high events. Summing over alpha and charging the internal pair energies with multiplicity <=h yields

    B x sum_alpha a_alpha(x)^2
       <= 10 B Nh + 960 h E/x^2.                       (4)

The use of E is legitimate because e includes both orders and E is the sum of e over unordered distinct pairs plus nonnegative diagonal. Formula (4) holds for the same retained family as E, not the pre-pruned family. This controls actual internal masses by energy, rather than assuming they are uniformly thin.

## 5. NEW imbalance absorption inequality

Choose z=log^(-1/8) B and K_imb=log B. At a close anchor edge's first contact and dyadic layer x>=z/2, call the layer IMBALANCED if min(n_alpha(x),n_beta(x))*K_imb<=max(n_alpha(x),n_beta(x)). One can exclude the THIN class first, or count overlaps by union. Orient each such edge toward the larger contact profile. Its product is <=a_large(x)^2/K_imb. Sum over edges, using maximum degree D, then over levels using (4):

    E_imb <= (4D/K_imb) sum_{x>=z/2} Bx sum_alpha a_alpha(x)^2
          <= O((Dh/K_imb) [XB(1+log(1/z)) + E/z^2]).

Indeed there are O(1+log(1/z)) dyadic levels and sum x^-2=O(z^-2). With the displayed choices,

    Dh/K_imb=O(log^(-5/8) B),
    Dh/(K_imb z^2)=O(log^(-3/8) B),

and therefore

    E_imb <= O(log^(-3/8) B) E
             + O(XB (1+loglog B)/log^(5/8) B).          (5)

This is an actual energy absorption result. It is NOT an independent little-o bound on E_imb when E itself is unknown or very large. If E_rest denotes all terms not covered by previous negligible classes, (2), and (5), using a disjoint partition (or union upper bound) yields

    E <= E_rest + o(XB log^2 B) + O(log^(-3/8)B) E,
    E <= (1+o(1)) E_rest + o(XB log^2 B).              (6)

Move the last E term to the left for sufficiently large B. Thus E_rest=o(XB log^2B) still suffices. This is a reduction using the internal energy of earlier-formed groups, not a theorem that all large products are negligible. It handles both-thick groups even when their raw and weighted product exceeds the previous caps, provided the relevant positive-tail layer is imbalanced and sufficiently large.

General parameters P=B/log^beta B, A=log^delta B, tau=log^gamma B, z=log^-eta B, K_imb=log^kappa B with fixed positive exponents: thin works if gamma+delta+2beta<2, absorption if kappa>delta+2beta+2eta. Constants in (5) are not asserted small on the tested finite scales. No claim for far anchors or absence of a high anchor.

## 6. Audit and limitations

Standalone research/min_clock_anchor_layer_audit.mjs, exact remote readback 72ba2dd95aa89f0cb592e64b5e0968d0f1b452fa, blob aa58231eac091c61987d61e833d63dc71d4b38d0. Run:

    node research/min_clock_anchor_layer_audit.mjs 1024 4096 16384 65536

Executed the actual JS audit function for four windows x four modes, 16 successful runs of final script in available JS runtime, not a separate local Node invocation. Uses exact original MIN prefixes, retained degree-pruned source family as in prior audit, independent W^2 energy oracle, physical anchor graph and measured D, profiles at each dyadic level, contact profile dominance, uniqueness per close anchor pair, per-layer budget and adjacency inequalities, internal cell Cauchy and aggregate lower bound (4). Through X16384 additionally enumerates each internal anchor pair with root separation<=largest dyadic xB below both tails; directly replays their common physical suffix, verifies overlap>=xB, sum r<=24B, and actual e>=x^2B/48. Counts exact integers, fractional energies checked with numerical tolerances.

Analytic modes (k_g=k=0,A=1) have no observed close anchor first contacts, so they do not test limiting absorption. Standard diagnostic P=B/4,A=P/8,T6,kg5,k3, thin=4, imbalance ratio2,z=1/16, previous caps256/144; degree mode T4. Wide diagnostic P=B/8,A=P/2, otherwise same. These fixed thresholds intentionally differ from asymptotic choices. The wide mode also changes the previous high-anchor cutoff and proximity region; compare priority partitions only within the same mode.

At X16384 wide, 30939 nonvacuous internal-pair direct suffix oracle checks (count includes repeated pairs at different anchors); smallest observed ratio of actual suffix energy to the lower bound is about 40.71. Standard diagnostic 17183 checks. These values do not imply an improved uniform constant.

Largest X65536,B678, standard diagnostic retained31824 after 944 degree-pruned roots, E=16529423.70, 1103 physical anchors, 675 adjacency edges, max degree6, 25348 actual high-tag incidences, theoretical high count h36. 44561 original first contacts at close anchors, 179 unique anchor pairs; 43410 zero-tail. Independent thin layer603 pairs with actual energy94856.44, imbalance357 pairs with energy109023.98; all are covered by previous priority classes in this diagnostic (no net additional deletion). Both raw group masses>12 for 224 imbalanced pairs (these particular pairs have zero energy). This is a limitation, not hidden by the aggregate counts.

Wide at X65536,P85,A42, same E=16529423.70: 2223 actual anchors,4518 adjacency edges,max degree13; 243539 close original first contacts,997 unique physical anchor pairs; independent thin layer2280 pairs, energy293729.83; imbalance4946 pairs, energy841379.56, 3265 with both raw group masses>12. Combined 2473 thin/imbalance first pairs not covered by previous weighted anchor cap. Disjoint priority after all previous classes in THIS wide mode: new thin0, new imbalance1921 pairs with actual energy263044.33, residual8142549.47. Prior residual in the same wide mode is8405593.80 (=new residual+new imbalance); standard diagnostic prior residual9664226.81 is not directly comparable to wide. The wide imbalance upper budget from individual dyadic brackets is2628521.25 (before priority), actual841379.56; theoretical graph/internal-energy envelope is much looser. No numerical contraction of the asymptotic O(log^-3/8 B) coefficient is established. The proof of absorption is (1)-(6), not finite extrapolation.

## 7. Remaining obstacle

After earlier negligible terms and the new absorption, heavy close-anchor contacts can be restricted to layers with both counts>tau, and either small remaining tail x<z/2 or comparable counts within factor K_imb. Far-anchor and anchorless histories remain as well. The new result uses earlier-formed actual internal pairs, but does not control their total energy independently. The next target is balanced high-tail cross products: need an independent saving (e.g. exploit first-contact disjointness of histories and quantitative restrictions on creation of large ancestor groups), not just a further upper bound proportional to E with a coefficient that fails to tend to zero. Main untouched, no Lean compilation or twin-prime proof.
