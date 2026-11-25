# Source-cell restricted physical merger potentials and ordered natural tails

2026-11-25 JST. Continuation of ae921f73330f8ef0cee2d6a97a81e1c143ca6577 on research/min-prime-root-repeat-energy-2026-11-25. A new unconditional multiscale bound for first physical merger energy, applying the previous truncated quadratic potential to the union of TWO source cells rather than to the entire physical ancestor group. It can cover large globally merged groups with small actual cell-local mass. Also gives exact ordered natural tail structure, due to the monotone root-specific stopping thresholds. The residual large restricted products and asynchronous and medium terms remain OPEN. Paper deductions and finite audit, no Lean compilation or novelty claim.

## 1. Natural first physical merger layers and monotone tails

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^(1/4)), H=T+B, N=Theta(X/u) prime roots M in [X,2X). Use the original canonical MIN prefixes, including initial and terminal vertices, stopped at first gain >=T or at original terminal/cutoff. Each gain <H. Let I be the frozen natural high incidences p>=Q=ceil(B/u), r(C)>p/sqrt(log p); no source-specific accounting marks are applied in I. At a physical vertex v=(t,C) let R_M(v) denote the remaining natural I clock cost of root M, including a natural high outgoing hit at v if present. It is nonnegative, <=1.5H, and nonincreasing along each root's path.

New order fact: if M<M' both visit v, then R_M(v)<=R_M'(v). Indeed the two original paths from v are the same deterministic physical path until a stopping rule intervenes. The gain stopping horizon 2M-2+T and the original time cutoff floor((7M-1)/4) are both nondecreasing with M. Absence of any next eligible event is state-dependent, not source-dependent. If the larger source stops at some vertex of their common path, the smaller source cannot continue beyond it (it either stopped earlier or must stop there as well). Therefore the smaller source's natural suffix is an initial segment of the larger's, and the natural high cost is monotone in M. This also applies when a source visits v as its terminal vertex; then its suffix has no outgoing hit. It does NOT imply monotonicity of arbitrarily thinned source-specific retained tails.

At layer x>0, the tail-qualified tags at any fixed physical vertex are thus an upper segment of the ordered visiting source set, not an arbitrary subset. For any source cell (or incoming group), restriction of that upper segment to the cell (group) is likewise an upper segment in the corresponding source ordering. This enables exact evaluation from one ordered list per state. It does not bound the actual visiting sources arithmetically or imply they form an interval of all primes.

Recall from ae921f73 that the exact entire ordered off-diagonal synchronous energy on I is
    E_sync(I)=sum_v integral_0^(1.5H) [n_v(x)^2-sum_i a_{v,i}(x)^2] dx,
where n counts tail-qualified tags and a_i are groups by immediate physical predecessor (root singletons). Each cross-group pair first meets physically at v. The integration is over the common natural suffix's cumulative clock coordinate, so any exclusion of slices at a first merger also upper bounds their contribution on ANY retained subset J of I; min of arbitrarily thinned tails is not an exact formula. Earlier pair exclusions can be unioned by a disjoint priority.

## 2. Restricted source-cell pair potential

Partition original source values into fixed aligned half-open intervals C_j=[X+jd,X+(j+1)d) for integer width d. Do not confuse the source cells C_j with current horizon C. If M,M' share any full vertex, 0<=C-(2M-2)<H for both, hence 2|M-M'|<H. Thus different cells at a first physical meeting must have |j-k|<=K_d=ceil(H/(2d))+1. For each unordered distinct cell pair {j,k} satisfying this distance bound, restrict the entire original root ensemble to sources in C_j union C_k. Empty cells can be included or omitted, and it is also valid to use only cell pairs observed at some first physical meeting; each such pair is fixed for the subsequent potential argument. At a fixed layer x>0 each restricted source's tail>=x vertices form an initial segment of its original path. They may expire before other sources, including within a physical group.

At a vertex v let n_{jk}(v,x) be the number of tail-qualified original roots from these two cells, and let a_{jk,i} be their counts by immediate physical predecessor. Let N_{jk,x} count restricted roots with nonempty layer prefix. For m>=1 use the previous convex superadditive truncated quadratic f_m(n)=n² up to m and 2mn-m² thereafter. The exact restricted potential increment
    D_{jk,v}(m,x)=f_m(n_{jk})-sum_i f_m(a_{jk,i})
is nonnegative. Telescoping along the restricted deterministic edges (including source singletons and expiry losses) gives
    sum_v D_{jk,v}(m,x) <= 2m N_{jk,x}.                (1)
This is the same proof as ae921f73 but with only the two specified source cells, not an arbitrary selection of current vertices. It is essential that the restriction is on original roots for the whole auxiliary path. Each source belongs to at most 2K_d restricted ensembles, so
    sum_{j<k} sum_v D_{jk,v}(m,x) <= 4m K_d N.         (2)
The double counting of within-cell pairs in the various potentials is allowed in this upper bound; only cross-cell first-meeting pairs are classified as new exclusions. There is no assumed independence of root cell, arrival label or physical time.

For a first physical meeting of roots from different cells j,k, its ordered cross-group count within this restriction is covered by D if n_{jk}<=m, since D then equals the complete restricted ordered first-meeting count. The full physical group at v can have arbitrarily many tags from OTHER cells; its global n need not satisfy any cap. In particular this is not the previous same-cell near-pair bound, nor a current-high-horizon source-cell thinning operation.

Hierarchical label refinement: let b_{jk,p} denote the total tail-qualified mass in the two cells with actual incoming selected prime p (root group label 0). The restricted increment splits into nonnegative label-between and label-internal brackets exactly as in ae921f73. If n_{jk}>m but both roots arrived using the same label p and b_{jk,p}<=m, the entire internal ordered cross-predecessor count for that label is paid by its corresponding bracket. Use priority small restricted total, then small restricted label. At each v the union of the covered cross-cell ordered pair counts is <=D_{jk,v}. No extra factor for the number of labels, and no double charge of the two cases. Cross-label interactions with only one small label are not covered by the internal bracket.

## 3. A growing family of simultaneous first-merger cell conditions

Choose d_j=B 2^j for j=0,...,floor(log_2(u^(9/4))), hence d_j=o(T). At each scale define
    m_j0=floor((d_j/B) u^(7/4)),
    m_j(x)=max(1,floor(m_j0 sqrt(H/x))).
All formulas apply for sufficiently large X (bounded X immaterial); integral_0^(1.5H) m_j(x) dx=O(m_j0 H), uniformly. The union of cross-cell slices satisfying either the small-total or the small-label condition of section 2 at this scale has energy
    E_cell,j <= 4 K_{d_j} N integral m_j(x) dx
              = O(N H² u^(7/4)/B)
              = O(F/u^(1/4)),                         (3)
where F=T² B u, N=Theta(X/u), X=Theta(B²), H~T. Thus all O(1+ell) scales together cost
    E_cell <= O(F(1+ell)/u^(1/4))=o(F).              (4)
This is an absolute whole-synchronous-energy exclusion of slices at first physical meetings, valid for arbitrary later retained natural incidences. No linear incidence deletion or negligible energy of such a deletion is claimed. One may also use any family of widths d=o(T) with integral cutoffs satisfying sum_j K_d integral m_j=o(F/N), without nesting; the stated dyadic ladder aligns with previous strengthened source-cell thinning.

In the existing hybrid all root pairs with separation <=d_near=floor(B u^(5/2)) have already been bounded by O(F/u^(1/4)), including their whole synchronous energy. Since every d_j<=B u^(9/4)<d_near eventually, every surviving far root pair lies in distinct cells at EVERY scale. Consequently the physical first-meeting residual can be restricted to layers with simultaneous conditions:
    n_{j(M),j(M')}(v,x)>m_j(x) at each scale;
    if their incoming label p agrees, also b_{j(M),j(M'),p}(v,x)>m_j(x).
Here the cell indices depend on the scale j, and both counts are at the original first physical merger v and tail coordinate x. At least one of the two cells must contain more than m_j(x)/2 tail-qualified roots (of that incoming label in the same-label case). This does NOT force both cells individually thick. The companions can be different at different scales, and some may not be retained after other accounting marks. The earlier current-event source-cell conditions and these first-merger conditions are distinct and coexist: no transport of thickness from a later event to its merger is assumed.

In particular one cannot justify the previous small-global-merger condition by inspecting the later synchronous horizon: a large group may have formed by many small first meetings. The restricted potential handles exactly those formation contributions even in the presence of unrelated large groups. For illustration at d=B the restricted mass threshold is order u^1.75 sqrt(H/x), at d~B u^2.25 it is order u^4 sqrt(H/x), matching the scale of the earlier cell-local clock-budget thresholds but now for an energy argument at a different physical vertex.

## 4. Combined residual and scope

Use the previous global tail mass and hierarchical same-label caps, capped high/high mixed-label merger terms, earlier near and other whole-pair exclusions, and now (4) by union or disjoint priority. Restrict the synchronous residual to those first merger layers that evade all these exclusions, in particular the simultaneous restricted-cell tests of section 3. Denote it E_phys,cellbad. It can be defined on the natural I layers as a sufficient upper bound, or on the intervals of the actual retained J subset as in ae921f73. With the previous asynchronous phase imbalance absorption of 4e8c7db,
    E_J <= (1+O(1/u))(E_phys,cellbad+E_async,bad)+o(F).
The unchanged joint OPEN sufficient conditions remain
    Z_m=O(N B u³), E_phys,cellbad+E_async,bad=o(F)
on the same unbounded dyadic windows. There is no independent bound here on the thick cell-local products, the number of distant cells participating in a single first merger, or the total synchronous residual. In particular mass and support conditions alone do not prove the twin prime conjecture. Next target: arithmetic control of actual thick restricted-cell ancestor masses at first physical meetings (using the monotone tail ordering and/or the sparse-heavy potential of ae921f73), especially the same-incoming-label class. No changes to medium moment or asynchronous phase proof.

## 5. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_cell_merger_audit.mjs, exact remote readback at d8b523e0008e5ed253e5ce64058e594298594692, blob 52fe961113a4d42fa53b3746355e8a24a7c0d79d. Run:
    node research/min_prime_root_cell_merger_audit.mjs 256 1024 4096 16384 65536 262144
Executed its function in the available ECMAScript runtime, not a separate Node invocation. All 18 runs (3 modes x 6 windows) passed. Exact original SPF MIN, literal parity-GCD comparison on the smallest two windows (short1183,wide1707,analytic1719); full physical vertex sweep checks ordered natural tails for adjacent sorted source tags, physical predecessor first-meeting groups and source locality. Independent synchronous energy from per-physical-state tag squares vs exact first-meeting tail integration with constant-tail breakpoints. For each source pair and layer interval, use the integer cap boundary x<=m_j0²H/(n_{jk}²) and the analogous label boundary. Union the two scales and global small-total/same-label conditions without overlap; record per-scale additional energy and same-label additions. Independently at sampled layers x=1,128,512 construct observed cross-cell merger adjacency; compute the sum of restricted potential and expiry contributions over all vertices of all corresponding restricted prefix forests, including vertices with only one participating cell present (degree weighting plus corrections when both are present). Exact potential telescope and restricted small-total/small-label cap checked. This does not test asymptotic constants, full growing ladder, prior near-pair/mixed-label cap or cumulative hybrid deletions; the arbitrary J restriction follows from the paper natural-tail interval argument.

Short T=B,Q=max(5,ceil(B/8)), wide T=4B,Q7, both r>p/2; diagnostic d0=max(4,floor(B/16)),d1=4d0, base m0(cell)=2,m1(cell)=4, global base mass 4 or8 respectively. Analytic T=X/u^.25,Q=ceil(B/u) min5,r>p/sqrt(log p), d0=B,d1=4B, base cell caps floor((d/B)u^1.75), global cap floor(Bu^1.5). At finite analytic settings global cap already covers all synchronous energy; it does not exercise a nonempty final residual. Finite diagnostic widths and thresholds are chosen to exercise the new conditions and do not estimate limiting removal fractions.

| X | wide sync energy | prior global total/same-label layers | extra two-cell union | remaining |
|--:|--:|--:|--:|--:|
|256|4768|4768|0|0|
|1024|12946|12946|0|0|
|4096|197588|197588|0|0|
|16384|1907350|1881654|13996|11700|
|65536|19256438|16453410|1018570|1784458|
|262144|174040038|125506142|13271582|35262314|

At X262144 wide B1355,N20390,T5420: 441714 adjacent-source ordered tail comparisons,12109 cross-group merger vertices,126505 unordered first physical pairs,11643 nonempty constant-tail intervals. Independent sync energy174040038. At d84:13446 observed cell-pair edges, max degree37, extra above global11535902 (of which25694 from the same-label cap beyond its restricted total cap), restricted coverage82992336. At d336:1797 edges,max degree13, extra6310174 (same-label incremental28752), restricted coverage56876704. The two-scale union extra13271582, not the sum of the two per-scale extras. At fine x512,m7, sum restricted potential279668=376316 expiry loss−96648 starts, covered cross count59630+140. At coarse x512,m14, potential270700=314938−44238, covered cross count37012+172. These starts count each root in multiple restricted ensembles, not distinct roots. Within-cell energy at fine28234392/coarse69153200 is reported but NOT removed in this independent diagnostic. Near-pair exclusions may overlap the new classes, and the previous mixed-high cap is not included here. Therefore the remaining35262314 is NOT the cumulative hybrid residual.

Short largest sync40953780, global30193062, extra2377470, remaining8383248. Analytic largest sync120546712,445110 ordered comparisons, all global-covered. No Lean compilation, main and other branches unchanged.
