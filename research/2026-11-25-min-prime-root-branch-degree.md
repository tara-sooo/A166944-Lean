# Physical merger branch graphs and degree-free light-branch admission

2026-11-25 JST. Continuation of 0f74d826a528f527d56ac45c285ed00200fc964f on research/min-prime-root-repeat-energy-2026-11-25. Two new whole synchronous energy exclusions. First, reverse clock congruences bound the degree of a graph of incoming physical branches, and a matching decomposition pays thin/thin cross products even if other branches are enormous. Second, a degree-free light-branch admission lemma charges a bounded portion of the opposite side of an arbitrarily large merger; it works in both source orders, with expiry, in hierarchical labels and restricted source cells. No proof of residual high or medium moments, no Lean compilation, no novelty claim outside this project.

## 1. Setup and inherited potential

Use X dyadic, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts M in [X,2X), F=T² B u. Use all original gain-stopped MIN paths with their own original cutoff and final vertices. Freeze I of natural actual p>=Q=ceil(B/u), r(C)>p/sqrt(log p) selections. At a physical state v=(t,J) each source has remaining natural high clock tail R_M(v)<=1.5H. At layer x>0 keep its prefix where this tail is >=x. With n_v(x) active tags and a_i(x) their masses by immediate physical predecessor (starting root is its own singleton), the ordered cross-group count is b_v=n_v²-sum a_i². The full synchronous offdiag natural energy is exactly sum_v integral b_v(x) dx. Each pair counted at its first physical meeting only. For arbitrary retained J subset of I the natural suffix intervals upper bound corresponding retained-pair energy, not the minimum of separately thinned tails.

At fixed x define f_m(n)=n² for n<=m, 2mn-m² otherwise, D_v(m)=f_m(n_v)-sum_i f_m(a_i). Superadditivity gives nonnegative D_v. The expiry-inclusive telescoping budget from ae921f73 is sum_v D_v(m)<=2m N_x<=2mN, where N_x counts roots with nonempty layer prefix. Hierarchically group the incoming branches by actual incoming selected prime p, b_p=sum_{i:p_i=p} a_i. D_v is the sum of the outer increment f_m(n)-sum_p f_m(b_p) and all inner increments f_m(b_p)-sum_{i:p_i=p} f_m(a_i). This remains valid on a fixed restricted root ensemble (two source cells etc.). Integer layers x=1,...,floor(1.5H) are equivalent for natural integer costs when the classifier is evaluated at integer x; use these in the audit, continuous layers in estimates below. Both sum and integral versions have the same bounds.

## 2. General bounded-degree light/light lemma

For any partition into branch masses a_i and any undirected graph on those branches with maximum degree Delta, keep edges only if both endpoint masses <=m. Then
    2 sum_{kept edges {i,j}} a_i a_j <= 2 max(0,2Delta-1) D(m),       (1)
where D(m)=f_m(sum a_i)-sum f_m(a_i).
Indeed for a,b<=m,
    f_m(a+b)-f_m(a)-f_m(b)=2ab-(max(0,a+b-m))² >= ab
since a+b-m<=min(a,b) when positive. For a matching the sum of these increments is <=D(m) by superadditivity on disjoint pairs and leftover groups. Greedy edge coloring of a simple graph uses at most 2Delta-1 colors for Delta>=1. Sum over the matchings; Delta=0 is trivial. The same argument works with zero-mass vertices and any subgraph. This bound covers small/small interactions within a huge total group, not only cases where the total or all branches are small.

For different incoming labels, use the outer partition by b_p and its complete graph, of degree at most the number of distinct odd primes <=B dividing J(J+2), plus one for a root. Uniformly this number is O(u/(1+ell)): the product of k distinct primes is at least (k+1)!, while J(J+2)=O(X²), so k log(k+1)=O(u). This elementary bound needs no probabilistic divisor hypothesis. In fact no original prime root M can be a noninitial arrival at its own starting state (M+2,2M-2): t=M+2 is odd, and any incoming p would divide t-2=M while p<=B<M. Thus no root cross group exists here. The plus one bound is harmless.

Put m_mix(x)=floor(floor(B sqrt(u)) sqrt(H/x)) (min1 if needed). Sum (1) for distinct labels with both b_p,b_q<=m_mix. The outer increments are bounded by D_v and then by 2m_mix N. Integrating gives
    E_mix,light << (u/(1+ell)) N B sqrt(u) H
                 = O(F/(u^.25(1+ell)))=o(F).                     (2)
Unlike the earlier mixed-high CRT capped product, this treats ANY distinct incoming labels, including small primes, with no arithmetic product cap and no restriction on other label groups. It does require both indicated label masses small. No label-aggregate bound for all states is claimed.

## 3. Reverse clock graph for same incoming label

At fixed v=(t,J), two distinct physical predecessor branches arriving with the same selected p have common predecessor horizon D=J-p+1 and distinct times s in [t-2r(D),t-1]. The next event at each of those predecessor states is (t,p). Write r=r(D). This window length follows from the least eligible clock bound; all such predecessors have the same r. Let Z=max(1,floor(u^.25)). Define an original predecessor state (s,D) as regular if it is an original root, or at least ONE original tag at that state arriving into v has its own preceding selected q with q>=r/Z. This is a state-level sufficient condition, not a claim that all its tags have that incoming q. Freeze regularity on the full original histories before any layer restriction. If nonroot, the previous q arrival implies
    q | D or D+2,
    s=0 mod 2q if s even, s=q+2 mod 2q if s odd.
For a fixed odd q, only one of the divisibility sides is possible (q cannot divide 2); it fixes the clock progression. Consequently within the length-2r window, each q>=r/Z provides <=1+Z possible times. There is at most one original root state at horizon D. With the uniform divisor-count bound above, the number of regular predecessor states in this label group is at most
    1+(Z+1) # {odd q<=B:q|D(D+2)}
      = O(1+Zu/(1+ell)).                            (3)
This is an actual reverse two-step capacity, not a count of ancestors. The regular states are allowed to have arbitrarily large masses.

Connect two distinct physical predecessors within this same label if either their times differ by <=2Z OR both are regular. The first condition gives <=4Z neighbors of any integer time, and the second adds at most the number in (3). The graph degree is Delta_same=O(Zu/(1+ell)); if r<=Z all branches are mutually connected by the first condition. The bound is uniform even for huge r. It concerns two incoming physical states, not the high outgoing events later in their common suffix.

Take m_same(x)=floor(floor(B u^.25) sqrt(H/x)) (min1 if needed). Apply (1) to each label's inner increment, retaining edges with both physical predecessor masses <=m_same. Sum over labels without an additional factor for their number: the sum of inner increments <=D_v. Integrating the potential budget gives
    E_same,light << (Zu/(1+ell)) N B u^.25 H
                  = O(F/(u^.25(1+ell)))=o(F).       (4)
The remaining same-label first-meeting slices either have at least one physical predecessor mass >m_same(x), or have two different predecessor times separated by >2Z and at least one nonregular predecessor. In the latter case r>Z and that nonregular state is not a root and EVERY original incoming label q there is <r/Z (for the original branches arriving into this v). This is a genuine restriction on previous actual clock labels, including low r and moderate or large p; no universal bound on same-label merger multiplicity is asserted. The prior rank and label/cell caps may be unioned with (2)-(4). These are entire common suffix energy slices, not only the merger event's own r-weight.

## 4. Degree-free admission: a different and stronger partial-batch argument

Let an arbitrary partition of a layer mass n have branch sizes a_i. Mark a branch light when a_i<=m. For each tag in a light branch allow at most 2m other tags in DIFFERENT branches as its directed admission choices (an arbitrary rule, varying with v and x). Take the union of unordered edges selected by either endpoint; count each selected unordered pair with weight two. Write A_m for this ordered count. Then
    A_m <= D(2m)+8D(m).                             (5)
Proof: if n<=2m, all cross-branch ordered pairs are already D(2m). Otherwise let h count branches with a_i>m, and s be the total mass of light branches (including a_i=m). When h>=1,
    D(m)=(h-1)m²+sum_light(2ma_i-a_i²)>=m s.
When h=0 and n>2m, sum_i a_i²<=mn, hence D(m)=2mn-m²-sum_i a_i²>=mn-m²>mn/2=ms/2. In both cases A_m<=4ms<=8D(m), by the directed choice count. No assumption on branch arity, opposite masses, relative order of roots or actual persistence is needed. In particular the light branch can contain the LARGER endpoint and choose smaller partners, which could expire later. This does not require global cumulative ranks of those smaller partners.

Apply (5) to the flat physical predecessor partition. Independently it applies to the hierarchical partition: choose from other incoming LABELS if the tag's own label aggregate is light; choose within that same label but from other physical predecessor groups if its own physical group is light. Apply the lemma to the outer and all inner partitions separately, then sum their D increments. The resulting total is <=D_v(2m)+8D_v(m), without a label multiplicity factor. Union of the flat and hierarchical covers costs at most twice this bound. At fixed x across all v each of the two covers is <=20mN_x, by the expiry telescope. All these are first physical pair counts, not counts of arbitrary later synchronous contacts.

Concrete admission rule used for the audit: within each of the above partitions, sort candidate partner tags (other branches of that partition) by increasing source M. For a tag in a light branch allow the first m and last m candidates. Equivalently the pair can be selected from either endpoint if that endpoint's branch mass and the candidate's rank from at least one end are both <=m. At fixed x no more than 2m directed choices are used. Other choices, e.g. by source distance, can be substituted without changing the bound. The order is chosen for accounting; no dynamics altered. Ranks are LOCAL to this merger and its tail layer, not the persistent cumulative larger-partner ranks of 0f74d826. Smaller companions need not persist.

With m(x)=floor(floor(Bu^1.5) sqrt(H/x)), the global flat/hier union thus satisfies
    E_admit,global << N integral m(x) dx
                   = O(F/u^.25)=o(F).              (6)
This excludes portions of even arbitrarily large heavy/light and heavy aggregate formations, from either side. It does not remove all heavy/light products.

## 5. Restricted source-cell admission and joint residual

Fix a source-cell width d and restrict each auxiliary layer forest to the union of two fixed distinct cells whose index difference is <=K_d=ceil(H/(2d))+1. This restriction is on full original root histories, not on particular meeting states. Each root lies in at most 2K_d of the restricted ensembles. Apply (5) and the same flat/hier rule with branch masses and partner ranks computed within each restricted ensemble. Count only cross-cell selected pairs for the new cover; within-cell counts may safely be included in its upper bound. Thus
    E_admit,d << NK_d integral m_d(x) dx.
For d_j=B2^j<=B u^2.25, m_j(x)=floor(floor((d_j/B)u^1.75) sqrt(H/x)), each scale gives O(F/u^.25). The union of all O(1+ell) scales and the global cover is o(F). This works with arbitrary expiration and does not assert monotonicity of a light smaller-root group. Previous far pairs lie in distinct cells on every scale. Unlike the preceding rank criterion, both directions of admission can be used and the local incoming group may be small even if the endpoint's cell mass is large. It is essential that the light mass in the restricted test is the branch mass in the UNION of the two cells, not the branch mass in just one cell. No claim that this bounds arbitrary products with one light side.

On the final retained J subset of I, use natural first-merger suffix coordinates to remove (2),(4),(6) and the multiscale admission cover, as well as all previous absolute pair/slice exclusions. Their union has energy o(F). Call the remaining synchronous part E_phys,admitbad. The asynchronous absorption from 4e8c7db remains valid:
    E_J <= (1+O(1/u))(E_phys,admitbad+E_async,bad)+o(F).
Joint OPEN sufficient conditions on the same unbounded windows:
    Z_m=O(N B u³), E_phys,admitbad+E_async,bad=o(F).
The new residual excludes bounded-degree thin/thin mergers and local light-branch portions in both source orders at all scales; it can still contain thick/thick interactions, heavy/light products outside the admitted portion, and irregular long predecessor phase pairs. In particular there is no general bound on the arithmetic formation of huge predecessor groups. Medium and asynchronous estimates unchanged. No proof of twin prime infinitude.

## 6. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_branch_degree_audit.mjs, final exact remote readback at deb001d2d891dd4b0577caeb4e6bf8a6515ae7f1, blob 257a0694c66d9ee925a2515b7a74afac9b51e9ac (initial degree-only audit 99acd09014ea6306e39058213d4b19954357b0b6). Run:
    node research/min_prime_root_branch_degree_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node invocation. All 18 final runs, three modes x six windows, passed. Original SPF MIN, literal parity-GCD comparator on two smallest windows (short1183, wide1707, analytic1719). Checks prime-root singleton property, predecessor clock and divisibility, common p predecessor windows, regular-state and graph degree capacities. At sampled layers x1,128,512 independently verifies hierarchical matching bound and global expiry telescope for both thresholds. Integrates exact integer tail layers at constant-tail breakpoints, prior global/label/two-cell/rank covers, graph exclusions and new flat/hierarchical admission, global and two restricted widths. Local admission bound (5) checked on global/restricted masses at end of each relevant constant-tail interval, with the stated cap; exact integrated partitions checked independently of state-square synchronous energy. The restricted potential telescope itself is inherited from the earlier cell audit. Does not test every real x, asymptotic degree constants, growing scale ladder, arbitrary J masks, or the cumulative earlier near/CRT/other masks. Finite diagnostic caps chosen for nonvacuous checks; no extrapolation.

Short T=B,Q=max(5,ceil(B/8)), wide T=4B,Q7, relative r>p/2, Z2 or4 respectively, mixed/same/global base mass4 or8, cells d84,d336 at largest X with base caps2,4. Analytic T=X/u^.25,Q=ceil(B/u) min5, natural relative test, Z=floor(u^.25), mixed and same caps as above; global B u^1.5, cells B,4B. At tested analytic sizes all prior global-covered, so no residual tested there.

| X | wide previous rank residual | after degree exclusion | after admission |
|--:|--:|--:|--:|
|256|0|0|0|
|1024|0|0|0|
|4096|0|0|0|
|16384|0|0|0|
|65536|59196|59080|0|
|262144|1937248|1920030|50520|

At X262144 wide B1355,N20390,T5420: 612685 events,126505 first physical pairs,12109 merger states, full sync174040038. Previous total/label/two-cell/persistent rank union172102790 exactly matches prior audit. Reverse clock checks592636, prime-root singleton checks20390, actual same-label graph edges7780, of which6921 close,5467 regular,859 regular only (overlap allowed); max observed degree4, max regular states4, max observed divisor count9. Distinct label edges1962. Degree covers in isolation mixed15592196, same44170208, incremental mixed1720 and same15498. After degree residual1920030, of which same nonedge1513408, same above cap395662 (remaining mixed10960). At x512,m29, potential104521=113602 expiry loss−9081 starts, mixed cover10530, same28940. Admission local inequality checks46415; flat/hier union with two cells in isolation173899566 (not additive to prior covers). Additional global1790976 and cell78534, total1869510, final50520. Short largest previous336604, degree12222, admission300986, final23396. Analytic largest full sync120546712, all prior covered; no limiting inference. Main and other branches unchanged.

## 7. Next target

The admission bound makes the remaining physical formation requirement explicit at each first merger and tail layer: either both branches are thick or the pair lies beyond every admitted local partner segment of each light branch, even on the restricted source cells. A useful next step would be to bound those actual tail-qualified cross-branch rank distributions using reverse arithmetic, or obtain a new quantitative estimate for the medium moment rather than only refining the synchronous classification. The asynchronous residual remains independent.
