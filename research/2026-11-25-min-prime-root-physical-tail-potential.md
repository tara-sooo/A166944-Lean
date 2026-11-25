# Physical first-merger tail profiles and truncated quadratic potential

2026-11-25 JST. Continuation of 4e8c7dbabdf494326a8634580f566d74713b2ae5 on research/min-prime-root-repeat-energy-2026-11-25. A new absolute energy bound for physical first mergers at small tail-profile mass, without a depth, label, degree, or monotone actual mass hypothesis. The same potential separates same-incoming-label mergers within a large physical group. A separate CRT bound covers capped distinct-high-incoming-label formation. The remaining large physical merger profiles, asynchronous residual and medium moment are OPEN. Paper deductions and finite checks, no Lean compilation or novelty claim.

## 1. Exact synchronous energy at first physical meetings

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^(1/4)), N=Theta(X/u) prime roots M in [X,2X), original gain-stopped MIN prefixes including initial and terminal vertices. Each prefix gain<T+B, total r-cost<=1.5(T+B). Freeze the natural high incidence set I from b8fea48: actual p>=Q=ceil(B/u), r(C)>p/sqrt(log p). No root-specific accounting deletions in I. At a physical vertex v=(t,C) of root M let R_M(v) be its remaining I clock cost INCLUDING the outgoing hit at v if any. It is a nonnegative integer <=1.5H where H=T+B, nonincreasing along the original prefix.

All physical successors, whenever the prefix continues, are deterministic at a state. Two roots first meeting at v share an identical full physical suffix until one stops. The natural high hits of the shorter suffix form an initial segment of the longer suffix's natural high hits, so their ordered common physical high energy is EXACTLY 2 min(R_M(v),R_M'(v)). This equality uses natural I and original prefixes, not arbitrarily thinned retained lists.

At v partition its original tags into incoming predecessor-physical-state groups; a root starting at v has its own singleton arrival group. Tags in different groups have their first physical meeting at v, since any earlier physical meeting would imply the same immediate predecessor when both continue. Tags in the same group already met. Every unordered physically meeting pair belongs to exactly one cross-group product at its first physical vertex, including terminal meetings (zero future weight if either stops). No assumption that projected first meeting equals physical first meeting.

For a real x>0 count n_v(x)=#tags at v with R_M(v)>=x, and a_{v,i}(x) their counts in the incoming groups. Write
    b_v(x)=n_v(x)^2 - sum_i a_{v,i}(x)^2.
This counts ORDERED cross-group pairs. By the layer identity min(A,B)=integral_0^infty 1{x<=A,x<=B} dx and the first-meeting partition, the entire ordered synchronous off-diagonal high energy is exactly
    E_sync(I)=sum_v integral_0^(1.5H) b_v(x) dx.       (1)
No multiple charges of a pair at later synchronous hits.

For ANY retained subset J of I, the same natural profiles give upper bounds on its synchronous energy. More precisely at each first physical meeting v of a pair, parameterize the common natural high suffix by its cumulative r-cost measured from v. A natural hit of weight r contributes an interval of length r on this coordinate. The two tails contain identical successive intervals until one ends; retained-both hits contribute only their own intervals. Thus (1) bounds the energy on J, and any classification of the integrand into pair classes at v and x induces the same upper bounds on the corresponding part of J. This avoids claiming equality for the minimum of two arbitrarily thinned tails. In particular previous root and event deletions can only decrease the contribution.

## 2. A potential budget that accounts for expirations

For any m>=1 define the convex truncated quadratic
    f_m(n)= n² for 0<=n<=m,
             2mn-m² for n>=m.
It is superadditive on nonnegative arguments because f_m(0)=0 and the derivative is nondecreasing. Its slope never exceeds 2m. At a fixed layer x>0, keep the original root prefix of vertices with R_M(v)>=x. This is an initial segment, possibly empty. Each nonempty prefix has exactly one starting and one ending vertex, no re-entry. Let N_x<=N be the number of such roots. These are auxiliary prefixes for the proof, not reruns of MIN.

At v let e_v(x) count tags ending their auxiliary prefix there. Every other tag follows the unique physical successor. The mass flowing on that edge is n_v-e_v (zero if no successor), and equals one incoming group at its destination. In the following suppress x. Define the nonnegative potential increment
    D_v(m)= f_m(n_v) - sum_i f_m(a_{v,i}).
The sum over the finite graph, whose edges strictly increase C, telescopes exactly:
    sum_v D_v(m)
       = sum_v [f_m(n_v)-f_m(n_v-e_v)] - N_x f_m(1)
       <= (2m-1) N_x <= 2m N.                      (2)
Each singleton root is counted once as an incoming group, and each actual continuing edge once at both endpoints. The loss bound follows from slope<=2m and sum e_v=N_x. Thus expirations, unequal original cutoffs, and falling active group masses do not invalidate the estimate. One need not introduce ghost continuations of expired roots.

If n_v<=m then D_v=b_v. Consequently the total ordered first-meeting pair count at this layer from such vertices is <=2m N, even when a later common group becomes arbitrarily large. This conclusion holds for arbitrary actual histories, not merely first contacts while both roots satisfy a pre-existing GOOD prefix.

There are further useful exact bounds. Let h_v be the number of incoming physical groups with a_i>=m and s_v the sum of the other group masses. If h_v>=1 then n_v>=m and
    D_v=(h_v-1)m² + sum_{a_i<m}(2ma_i-a_i²)
       >= (h_v-1)m² + m s_v.                      (3)
If h_v=0 and n_v>=2m, then sum a_i²<=m n_v and
    D_v>=m n_v-m²>=m n_v/2.                        (4)
Therefore across each layer
    sum_{h>=1}(h_v-1)<=2N/m,
    sum_{h>=1}s_v<=2N,
    sum_{h=0,n>=2m}n_v<=4N.
The first two bounds also hold in their combined weighted form m² sum(h-1)+m sum s<=2mN. In particular the number of vertices with at least two heavy physical incoming groups is O(N/m), and the number with large total mass but all groups light (n>=2m) is also O(N/m). These bounds do not themselves limit the squared cross product at the few heavy mergers; one very large merge may still dominate. For example large-group attachments may accumulate many first pairs even when every joining group is small.

## 3. Tail-dependent mass cutoff, including same incoming label

Choose m0=floor(B u^(3/2)) and
    m(x)=max(1,floor(m0 sqrt(H/x))) for 0<x<=1.5H.
It grows as residual clock threshold falls. At each layer apply (2) with this choice of m. Since integral m(x) dx=O(m0 H),
    sum_v integral_{n_v(x)<=m(x)} b_v(x) dx
       <= 2N integral m(x) dx
       = O(N T B u^(3/2))
       = O(F/u^(1/4))=o(F),                         (5)
where F=T² B u, T=Theta(X/u^.25), N=Theta(X/u). This is an absolute WHOLE synchronous energy exclusion for low tail-profile mass, even if the unfiltered number of roots at the first meeting is large and even if later actual group sizes grow. The cutoff is chosen independently of whether the merger is same-label, mixed-label, root contact, cheap or expensive, synchronous age, or previous projected contacts. It can be replaced by any integrable nonnegative profile cutoff with N integral m=o(F). Since the smallest positive natural tail is an integer, an equivalent discrete layer sum is available.

Hierarchical refinement: partition incoming physical groups at a vertex by their actual incoming selected label p; use label 0 for a starting-root group. Let b_p(x)=sum of physical incoming group sizes with label p. Same-label incoming groups have a common predecessor horizon, possibly different predecessor times. The ordered first-meeting count within this label is
    c_{v,p}(x)=b_p²-sum_{i:label p} a_i².
The remaining first-meeting count, between distinct labels, is n_v²-sum_p b_p². The potential decomposes EXACTLY into nonnegative pieces:
    D_v = [f_m(n_v)-sum_p f_m(b_p)]
          + sum_p [f_m(b_p)-sum_{i:label p} f_m(a_i)].
For each b_p<=m the corresponding inner bracket equals c_{v,p}. Thus even when n_v>m, sum of c_{v,p} over labels with b_p<=m is bounded by D_v. Use disjoint priority: at n_v<=m charge the entire b_v to D_v, otherwise charge these small-label inner products. Combined total is bounded by the SAME right side of (5), not twice that bound. This is useful when a small same-label ancestor group meets a large group arriving with another label: the internal first-meeting pairs of the small label can be excluded even though the total physical mass is large. It does not remove all cross-label pairs involving that small label. Root group label 0 has no internal cross-pairs.

At each layer, the residual same-label first-meeting pairs necessarily have their actual incoming label's tail-qualified aggregate mass >m(x). The residual mixed-label pairs necessarily occur at total tail-qualified mass >m(x). These are conditions on actual groups and residual clocks at the first physical meeting, not current physical-group sizes at later hits.

## 4. Additional absolute bound for mixed high incoming labels

Let v=(t,J) have distinct incoming selected primes p,q>=Q (not necessarily relative-expensive at their previous horizons). For either incoming p, if t is even the preceding C satisfies p|(C-1), hence J=C+p-1=0 mod 2p and t=0 mod 2p. If t is odd, J=-2 mod 2p and t=p+2 mod 2p. With eps=0 for even t, eps=6 for odd t, both incoming labels therefore satisfy
    2pq | (2t-J-eps).
The gain-prefix time bound from 4e8c7db gives 0<=2t-J<=6+5H. For fixed distinct p,q and parity, there are O(1+T/(pq)) possible values of 2t-J in that strip. At fixed such value the two divisibility conditions on J leave one class modulo pq; hence O(X/(pq)) possibilities in the full horizon interval. The additive one is absorbed since pq<=B²=Theta(X). Given J and delta, t is determined; ignoring any parity restrictions only overcounts. The arithmetic envelope for ALL vertices with two distinct high incoming labels is therefore
    K_mix << X[(sum_{Q<=p<=B}1/p)² + T(sum_{Q<=p<=B}1/p²)²]
          << X/u^(1/4),                             (6)
using sum 1/p=O((1+ell)/u), sum 1/p²=O(1/B). This is not a count of source pairs; one vertex can carry enormous ancestry.

At layer x put
    C_v^hi(x)=(sum_{p>=Q} b_p(x))²-sum_{p>=Q} b_p(x)²,
the ordered cross-label high/high product at v, with same-label and root contacts excluded. Choose
    c0=floor(B u^(3/4)), c(x)=c0 sqrt(H/x).
All such cross-label terms with C_v^hi(x)<=c(x), whether n_v<=m or not, have combined energy <=K_mix integral c(x) dx. By (6) this is
    O(X T B u^(1/2)) = O(F/u^(1/4))=o(F).          (7)
Use only the portion not already covered by (5) for a disjoint ledger. This is a bound on entire subsequent synchronous energy slices, not only the cost at the merging event. No cap on every actual product is asserted. The cap is tail dependent and is on the sum of cross-label products at a vertex, not each individual label pair; same-label pairs do not enter it. Large mixed high groups failing the cap and mixed lower-label formation remain.

## 5. Combined sufficient residual

Let J be the final retained natural high subset of the existing gain-prefix hybrid. Use (5) and (7) to classify its already-physically-synchronous off-diagonal part in the phase ledger of 4e8c7db. With natural-tail coordinates as in section 1, the omitted synchronous parts are o(F), independently of subsequent accounting holes. For an alternative sufficient target one can simply use the full natural synchronous residual after these same layer exclusions as an upper bound, without classifying the subset J explicitly.

The remaining synchronous term E_phys,bad consists of:
- same-label first physical meetings with b_p(x)>m(x) at that layer;
- mixed-label meetings with n_v(x)>m(x), except the capped distinct-high/high products of (7).
This includes root contacts with an incoming group and all deep physical merger histories satisfying the residual conditions. Equations (3)-(4) identify O(N/m(x)) heavy branching events at each layer, but not a bound on their large cross products. Even if all previous exclusions are imposed, a large residual can arise by repeated small-to-large attachments or heavy-heavy merges. No assertion that the actual number of active roots in a group is monotone.

The unchanged asynchronous residual of 4e8c7db is balanced above-cap close exit groups or far output times, with earlier pair/young exclusions available. Write its actual energy E_async,bad. The relative imbalance term can still be moved to the left as before:
    E_J <= (1+O(1/u))(E_phys,bad+E_async,bad)+o(F).
This is a sufficient reduction, not a proof of small E_J. Joint OPEN conditions on the same unbounded dyadic windows:
    Z_m=O(N B u³),
    E_phys,bad+E_async,bad=o(F).
They would imply R=o(NT), hence the gain-prefix contradiction to twin-free windows. No improvement to medium moments is claimed here. The new potential is a deterministic bookkeeping inequality, not an argument for actual high-energy suppression without residual estimates.

## 6. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_physical_tail_potential_audit.mjs, exact remote readback at b5b94fab254878b9f08c8521257865731c3257a4, blob 1724dd6b01114ecbb41183610ef75ecc887d47f6. Run:
    node research/min_prime_root_physical_tail_potential_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node executable. 18 final runs, all passed. Exact canonical SPF paths, independent literal parity-GCD comparisons at X256/1024: short1183, wide1707, analytic1719. Physical vertex grouping including roots/terminal, predecessor classes, independent same-state horizon-by-horizon energy and first-meeting min-tail sum, exact integer layer integration at all actual tail breakpoints, disjoint priority small total / small same label / capped distinct-high labels / residual, and raw and sampled tail-layer potential telescoping identities and heavy/light bounds. Mixed-high actual incoming congruences checked independently at actual merger vertices. The finite integral uses threshold floors, cutpoints from m0²H/n² and c0²H/C²; all energy sums exact safe integers in tested windows. It tests the full natural I, not the cumulative previous marks or the arbitrary J restriction; the latter follows by subset argument in section 1. Does not numerically verify asymptotic CRT envelope constants.

Modes: analytic T=X/u^.25,Q=ceil(B/u) min5,r>p/sqrt(log p), m0=floor(Bu^1.5), c0=floor(Bu^.75); short T=B,Q=ceil(B/8) min5,r>p/2,m0=4,c0=16; wide T=4B,Q7,r>p/2,m0=8,c0=16. The diagnostic modes deliberately use small caps and can have many smaller selected labels than the analytic regime. The analytic total-mass cap covers all physical energy at tested sizes, not a nonvacuous finite residual test.

At largest X262144, B1355,N20390, wide T5420: 612685 actual events, 191361 distinct physical vertices, 12109 cross-group merger vertices, 126505 unordered first physical pairs including terminal. Natural high I224748 tags, r-cost14658404. Synchronous ordered offdiag E=174040038, exactly equal to both the min-tail pair sum and the full integrated profile. Full same-incoming-label component154819158; distinct incoming high/high component10594846. Raw m0=8 small-total mergers account for43163424. Tail-dependent small-total layer accounts for125179802, including82016378 at raw n>8; among these 1206376 have genuinely reduced tail-qualified mass n(x)<raw n. Additional small label internal layers326340, capped high/high cross layers64358, residual48469538. Total equality exact. 847 mixed-high merger vertices, 877 pair congruence checks. The mixed cap counts finite actual positive products, not every arithmetic candidate vertex.

Raw potential sum137690 = expiry loss158080 -20390 root starts, <=2m0N. Raw heavy branch excess59, total light arrivals into vertices with >=1 heavy predecessor3856, all-light large total201, maximum physical mass101. At layer x512, m29, N_x9081, potential104521, expiry113602, cross count110928 of which83426 at small total; light mass235. At x1024,m20,N_x5169,potential54669, cross63608, small37946. Profile integration11643 constant-tail intervals, max natural high tail6021.

| X | wide sync energy | small tail total | extra small same label | extra capped mixed high | residual |
|--:|--:|--:|--:|--:|--:|
|256|4768|4768|0|0|0|
|1024|12946|12946|0|0|0|
|4096|197588|197588|0|0|0|
|16384|1907350|1881654|0|0|25696|
|65536|19256438|16416932|36478|5252|2797776|
|262144|174040038|125179802|326340|64358|48469538|

Short largest E40953780, raw small8919182, profile small30009974, extra same183088, extra mixed15136, residual10745582. Analytic largest E120546712, m0=26241, max physical mass105, all classified small. This is not limiting evidence and not an incremental subtraction from the fully cumulative high residual. No Lean compilation, main and other branches unchanged.

## 7. Next target

The exact first-meeting tail profile isolates the actual formation of large synchronized ancestor groups. At each tail layer there is a finite potential budget and a sparse set of heavy-branch formations. To progress, bound the cross products at these sparse heavy meetings and light attachments using actual root arithmetic/local source dispersion, or establish a bound on tail-qualified same-label ancestor mass at the first physical meeting. No general such bound is currently proved.
