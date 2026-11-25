# Normalized first-defect transport with a one-strand radical persistence envelope

2026-11-26 JST. Continues [cd83a9d1aba3](https://github.com/tara-sooo/A166944-Lean/blob/cd83a9d1aba37765b5a83e36aacc3214bc2d27f6/research/2026-11-26-min-unified-coarse-phase-return-obstructions.md), integrating the stable partner cleaning of f2a7cf2 and the exact translation lemma of the original prime-root branch 1a4005f2f336. Independent source heads at preflight unchanged: prime-root 1a4005f2f336ede61cca1a9656c158a559338b72 and stable-heavy e1ad9e2b434c652699e1bc9a0797887631e0ea6d. New: split the normalized phase energy into persistence and first-defect charges, bound the former using a radical computed from ONE actual strand, transport the latter to actual nonperiodic selected events with a linear per-tag capacity independent of the number of pairs or grids, and pay thin projected defect keys at a budget small enough to survive the factor ell in the clock inequality. No final upper contraction or Lean compilation.

## 1. Original ensemble and phase measure

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, all original completed gain-stopped MIN prime-root paths. Their per-tag gain is <H, wait <=3H, and d=2t-C lies in [0,6+5H]. Under finitely many twins all roots eventually reach T, so W_all>=N(T-6)/2. Each event has even prehorizon C, selected odd prime p<=B, gain g=p-1, wait w<=2r(C)<=3g, departure v. At fixed C,p all exits lie in one residue mod 2p; the original physical departure slot population is b_v, and n(C,p)=sum b_v.

Use M=Theta(u/ell) nested separated primorial grids P_j of bc6e3b7, P_min>=B^(1/8)/O(u), P_max<=B^.25. The coarse phase wheel L0 is the largest even primorial <=ell, with largest factor y0 and A=L0/2. At a crossing (K,C,q) one has q>largest factor of P>=y0 and gcd(q,L0)=1. Define class c=v mod L0, n_c=sum b_v within c; at most A classes. Retain the geometric, thin-class, rank, and partner-side class-stability local masks of cd83a9d. Thus each surviving focal event e has at least (1-epsilon)M good grids, epsilon=ell^(-1/2). On each good witness class n_c>H/(A q u ell²), the rank-unpaid slot has sum_(same class,b_v'<=b_v)b_v'>theta n_c, theta=1/ell, and unstable partner mass in its class is <=theta n_c/8. The original right/left directional clock cells have capacity <=9P per original tag-boundary atom. Use the longer original focal entropy window D=T/(u ell²), delta=1/ell, from fe87bc2; pay its original endpoint and entropy exceptions O(NT/ell). It ensures the good witness incidences of each retained e satisfy the shorter partner-stability condition of f2a7cf2 with D_s=floor(T/(u ell^6)), since D_s+2P_max+B<<D. The good witness b_v<=exp(delta)n_e<=2n_e eventually. This includes the individual focal tag's stability, not merely existence of a stable representative in its slot.

Define a_v as the number of original stable tag incidences at the departure slot v, stable with the short window D_s and endpoint margin D_s, using the definition of f2a7cf2. Do not recompute any b_v,n_c or rank after restrictions. Let E_P^o be the following restriction of the previous normalized phase-stable energy: require a stable focal tag as well as a stable partner tag, require focal class n_c>H/(A q u ell²), retain rank-unpaid v and near-mass condition
    (floor(R_P(q)/(Aq))+1)b_v <= theta n_c/2,
    R_P(q)=16 max(P,q).
Then
    E_P^o = sum_(K,C,q,c,v eligible) P a_v/n_c
                   * sum_(v' same class,b_v'<=b_v,|v'-v|>R_P(q)) a_v'.
The original denominator n_c, original smaller-or-equal slot-size condition b_v'<=b_v, and original rank all remain frozen. Additional optional source masks may be used if all good focal right-witness incidences are still included. Every stable eligible focal tag in v and stable qualifying partner tag in v' forms an ORDERED pair-incidence of charge P/n_c at each source atom K. At fixed projected source key each individual focal tag has total pair coefficient <=1 and each individual partner tag has total coefficient <=1, before multiplication by P. The latter follows by summing over focal tags in the same class, even after arbitrary pair restrictions. This is the row/column capacity, not a bound on unweighted pair count. In particular E_P^o<=N(H+P).

Let n_phase_cut(e)=H/[256 max(P_max,L0 p_e)u ell³] as in cd83a9d. For retained n_e<=n_phase_cut, the good right witness class meets the near-mass condition, and its stable far partner mass >3theta n_c/8. The focal tag itself is stable at that witness by the longer entropy window above. Therefore one-direction capacity gives
    W_mod_phase <= [24/(theta(1-epsilon))] mean_j E_(P_j)^o.       (1)
The massive clock includes residual n_e>n_phase_cut. This is the same clock bound as before but only needs the restricted source energy E^o; no assertion that discarded focal classes were small in the earlier energy (they are paid by the proved raw-clock masks). The partner-side cleaning and geometric masks are all on original incidence populations.

## 2. One-strand radical envelope for persistent pairs

Choose a common integer forward gain distance Lambda, P_max<=Lambda<=D_s/4, for all sufficiently large X. For example Lambda=floor(D_s/4); shorter choices are also allowed. Every stable original source tag has enough actual future gain after its departure J=C+q-1 to complete a prefix crossing gain Lambda, because its endpoint is at least D_s from C and q<=B<<D_s. Stable tags in one physical slot have identical true continuation from (v,J) until that prefix completes, by deterministic MIN and the endpoint margin. Thus its selected word p_1,...,p_k is uniquely defined by the physical slot, independent of representative tag. End on first completed gain crossing Lambda, overshoot <=B.

Set
    L_v(Lambda)=lcm(L0,2q,2p_1,...,2p_k).
This may be computed capped at 4H+1, with a special flag for exceeding 4H; do not treat the capped number as the actual divisor in divisibility tests. It is even and divisible by every prefix label. The general even-modulus strict crossing barrier from f2a7cf2 applies: an even horizon C with p|(C+-1) cannot cross a multiple of an even modulus divisible by p in [C,C+p-1), since the required even offset in [0,p-2] would have to be 1 or p-1 mod p. Hence the full contiguous prefix gain interval cannot contain any multiple of L_v, and L_v>Lambda. This holds for the true uncapped L_v and for the flag convention because Lambda<4H.

For each ordered source pair, compare the actual continuations at their common posthorizon J, initial lag Delta=v'-v, nonzero, divisible by L0 and 2q, |Delta|<=4H from the deficit slab. If all compared edges are translated (same projected edge, unchanged lag) until the focal prefix reaches Lambda, call the pair persistent. Otherwise stop at the first ACTUAL defect before the prefix completes. Both partners have sufficient completed future gain, so termination before a comparison cannot occur: at each common prehorizon before J+Lambda both have a next completed edge. For persistent pairs, every selected p_i has 2p_i|Delta by the exact exit congruence. Therefore L_v|Delta. The number of possible distinct NONZERO lags of size <=4H is at most 2 floor(4H/L_v), zero if the flag exceeds 4H. Each qualifying slot at the source has original population b_v'<=b_v by rank. Thus the persistent partner fraction at the focal slot is at most
    min(1, 2 floor(4H/L_v) b_v/n_c).
The restriction to stable partners and far distance only decreases this count. This is a one-strand upper envelope even for lag-restoring defects: it counts only entire unchanged translated prefixes, not pairs with equal endpoint lags but intermediate changes. In particular define
    Pi_P(Lambda)=sum_(eligible sources K,C,q,c,v)
             P a_v min(1,2 floor(4H/L_v) b_v/n_c).
Then the exact persistent energy I_P satisfies 0<=I_P<=Pi_P. This relaxation needs no partner path reconstruction. When L_v>4H there is NO persistence for any source partner, regardless of cohort size. When L_v is small it may give only the trivial bound.

Further, on source slots for which
    b_v <= L_v/(16 A q u ell^4)
(with the true L_v; flag>4H already zero), the fraction is <=1/(2ell²), by n_c>H/(A q u ell²). Thus their entire persistent energy over one grid is O(NT/ell²), using the original raw boundary budget. This costs o(NT) even after multiplying by ell in (1), and does not pay defect energy at those same slots. A simpler conservative cutoff uses L_v>Lambda in place of the actual radical. At all good witnesses of a focal e, q<=Q_e=max(P_max/a,p_e), a=u^.25, and b_v<=2n_e. Hence for n_e<=min(n_phase_cut(e),Lambda/[32 A Q_e u ell^4]) the persistent partner portion at every witness is uniformly <=n_c/(2ell²); stable far lower mass at each remains >3 n_c/(8ell)-n_c/(2ell²) in defect-bearing partners. This is a further optional focal subdivision; it does not replace n_phase_cut for other events. For Lambda=floor(D_s/4) the simpler cutoff is typically smaller than the old n_phase_cut, and is not claimed to cover all of that sector. The actual radical often improves on the conservative cutoff, but no asymptotic claim about its distribution is made.

## 3. Direct first-defect transport with row/column capacity

For every nonpersistent ordered pair-incidence, at its first defect both actual paths have the same prehorizon E, arrival lag Delta unchanged from the source, but either their selected labels differ or their common edge's exit lag changes. By exact two-way MIN comparison (1a4005f2f336), if both selected periods divided Delta then the labels and waits would agree. At least one selected label p therefore has 2p not dividing Delta. Since L0|Delta, necessarily p>y0. Choose that actual event as destination; if both labels qualify choose the focal side. This is a deterministic rule and no charge is sent to a merely projected or hypothetical path. It also handles same-edge lag change as a defect; subsequent rejoin or restored lag is irrelevant to the first-defect choice.

Route the entire original pair-incidence charge P/n_c to the selected side's original tagged event. Source boundary K satisfies
    E-Lambda-B <= K <= E,
because J-K is at most source gain <=B and E-J<Lambda. For a fixed original tag and its fixed destination event E, all routed charges in which that tag is the focal member come from source grid boundaries in this interval. At each such K the tag crosses it at most once; the row coefficient sum over all partners <=1. Thus the total in this role is at most P times the number of multiples of P in an interval of length Lambda+B, <=Lambda+B+P. The same argument using the column coefficient bound holds when that tag is the partner member. Both roles together give capacity
    D_P(tag,event) <= 2(Lambda+B+P).                     (2)
This is a single linear bound on the sum over ALL original ordered pairs. It does not multiply by number of other strands, number of departures sharing a projected horizon, or number of translation defects after the first. A tag may occur in both roles, hence the explicit factor 2. The source and destination are on the same actual original tag on the chosen side; the source boundary is shared by the two members, so the interval argument applies in either role. No mass-independence argument or common partner assumption across scales is used.

Define D_P(C,p) to be the sum routed to the chosen original tagged events at that projected key. Exact conservation
    E_P^o = I_P + sum_(C,p) D_P(C,p).
In particular E_P^o<=Pi_P+sum D_P, and all destination labels exceed y0. Use one common Lambda across the grids, and let Dbar(C,p)=mean_j D_(P_j)(C,p), with missing keys zero. By (2) and averaging on the same original tag-event incidences,
    Dbar(C,p) <= 2(Lambda+B+P_max) n(C,p).
Thus the effective transported defect mass
    m_eff(C,p)=Dbar(C,p)/[2(Lambda+B+P_max)]
is at most the distinct original tag population there. No claim it equals the physical synchronous mass. The sum of these averaged charges is exactly the averaged nonpersistent energy. This avoids summing a separate upper bound over each individual pair or grid. It is not a transfer of raw boundary weights at unit coefficient to actual waits: capacity (2) is in gain-length units, not in w or g.

## 4. Thin projected first-defect payment at the correct energy budget

For fixed selected p, candidate prehorizons satisfying p|(C+-1) have support O(X/p). More generally by the two-form support argument in 12292f36, the number at p with r(C)>=R is O(X/[p log²(2+R)]) uniformly for 3<=R<=p. The summable graded weight
    h(r)=log²(2+r)/(1+log log(2+r))²
therefore has total O(X/p) over those prehorizons, by the tail integration of 5b56248. Define Lcap=Lambda+B+P_max, and pay all averaged defect charge at a key when
    m_eff(C,p) <= m_def(C,p)= H h(r(C))/(Lcap u ell³).
The total energy paid is at most
    O(XH/(u ell³) sum_(y0<p<=B)1/p) = O(NT/ell²).        (3)
This is smaller by an extra factor ell than a typical clock-mask budget, because the energy appears multiplied by ell in (1). On p>=sqrt(P_min), the same calculation using the O(1) reciprocal sum over this range permits ell² instead of ell³ in this cap with the SAME O(NT/ell²) energy budget. On rough keys r>=(p-1)/log(2+p) use log²(2+p) instead of h(r) by the stronger rough support bound of 12292f36, with the same budgets; union only a fixed number of caps. These are caps on effective averaged transported defect populations, NOT on the old projected event masses or actual wait mass. In particular a small old clock mask does not automatically pay the full new defect transport, since its per-tag capacity is O(Lcap), not O(w). For the long choice Lambda~D_s the plain cap H/(Lcap u ell³)=Theta(ell³); the graded/rough caps may be much larger. For shorter Lambda the defect cap is larger, at the expense of a weaker radical persistence envelope. No selection of Lambda is claimed optimal.

## 5. Resulting alternative sufficient route

Let Pi_rem be the averaged persistence upper envelope restricted to slots NOT covered by the zero-radical flag or the persistent fraction payment in section 2. Let D_rem be the averaged routed defect charge after (3) and its applicable refinements. The exact energy partition, one-strand bound and payments give
    mean E_P^o <= Pi_rem + D_rem + O(NT/ell²).
Combining (1) with original clock masks and the deficit lower bound under finitely many twins, an alternative sufficient condition is
    liminf_(dyadic X) [ W_massive_phase +
                 24 ell (Pi_rem+D_rem)/(1-epsilon) ]/(NT) < 1/2.  (4)
Here all quantities use the SAME original ensemble and chosen common Lambda per X. The exact remaining persistent energy could replace Pi_rem and would be a no-larger objective. The radical envelope is an upper bound, not an assertion that every divisor-compatible lag is realized. If Pi_rem=o(NT/ell), the remaining task in (4) is the massive physical clock and the new projected first-defect residual. This is an alternative route, not a claim that (4) is logically weaker than the preceding exact-energy condition; the envelope may be loose. The substantive reduction is actual bounded-congestion transport, with a rigorously small paid energy sector and an arithmetic persistence test. No proof of either remaining upper contraction, no general claim that most original paths have radical>4H, no external novelty claim, and no Lean verification. Main and independent source branches unchanged.

## 6. Reproducible diagnostics

[Final audit](https://github.com/tara-sooo/A166944-Lean/blob/1033d1330bd585ec8038913ee89984ec669a0ccd/research/min_unified_first_defect_transport_audit.mjs), exact remote readback at 1033d1330bd585ec8038913ee89984ec669a0ccd. Seven original diagnostic runs and one added short-distance run passed in available ECMAScript runtime. The final update adds short mode without changing earlier default parameters. Reproduce:
    node research/min_unified_first_defect_transport_audit.mjs 1024 4096 16384 65536
Finite T=min(8B,floor(X/2)) ordinary or floor(B/2) focus, P=[6,30,210], L0=6, theta=.5, R=q, Lambda=max(8,floor(B/8)) or 2 in added short run. These are diagnostic substitutes, in particular Lambda need not exceed P_max. Uses actual future room >=Lambda after source exit in place of stable entropy/endpoint mask, original phase-rank and smaller-or-equal slot size, no analytic class-thin/near-cutoff/focal mass restrictions. Counts ready tag incidences per slot and computes the capped radical of a representative's original continuation. For each qualifying ordered slot pair, compares actual continuations until Lambda or first defect. Routes aggregated product weight P n_cross a_v a_v'/n_c uniformly to the chosen side's individual original tag events. Checks actual destination agreement, nonperiodic label, barrier and divisibility for persistent pairs, per-slot persistent upper envelope, exact total conservation, and per-tag capacity 2(Lambda+B+P) independently for each diagnostic grid. Finite illustrative projected thin payment per grid (effective mass <=.2 ordinary, <=.02 focus); does not test the analytic averaged graded cap or (4). All long-distance finite runs have zero persistent pair charge; added short run exercises positive persistence. No cumulative historical masks, literal gcd oracle, or formal Lean check. One script-update attempt had a syntax error in the tool wrapper before execution; corrected and saved final source.

| X/mode | ready slots | radical >4H | P=6 source energy | P=6 persistent | P=6 first defect |
|---:|---:|---:|---:|---:|---:|
|1024|468|86|38.400000|0|38.400000|
|4096|2444|867|1221.486268|0|1221.486268|
|16384|8823|5104|7046.927514|0|7046.927514|
|65536|33364|27167|29228.942332|0|29228.942332|
|4096 focus|1695|1288|57.500000|0|57.500000|
|16384 focus|6784|5821|490.033333|0|490.033333|
|65536 focus|28165|26141|5174.367155|0|5174.367155|
|65536 short|42292|442|40018.787704|18546.250181|21472.537523|

Largest ordinary: 5709 roots,140255 events, no reaches of diagnostic T,43927 slots. Across the three grids first-defect ordered slot-pair incidences 2265 (703 split,1562 same-edge lag change), individual routed destination checks15906. Grid P=6/30/210 energy respectively29228.942332/30005.475238/26708.122747; per-tag maximum loads55.609756/55.609756/194.634146, all within the finite capacity. Diagnostic thin paid26326.256978/27607.316147/11592.744280. Largest focus:2886 reaches,75256 events, all diagnostic paired charges routed. Added Lambda=2 ordinary: across P=6/30/210 persistent energy18546.250181/14761.504061/18006.150333, first-defect energy21472.537523/26355.702079/20025.517457; 1489 persistent slot-pair radical divisibility checks, all passed. These are finite normalized charge measurements, not a proof of an asymptotic upper estimate or of the final sufficient inequality.
