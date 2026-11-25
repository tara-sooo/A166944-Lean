# Original upward-birth keys and bilateral GAP source-cut cores

2026-11-25 JST. Continues 19aeea8d92459a926a8a2dc68fca9dd4f6b238b5. New paper results: original stop order on shared suffixes follows source order; a GAP first hit has an exact source-coordinate cut determined by the recorded predecessor time; every old terminal pair-level charge has a unique actual stationary upward-birth key; at that key the matched first hit (and its source cut) is deterministic. Splitting by these keys gives an unconditional bilateral weighted-core payment, including at the previously uncontrolled GAP recipient side, and a new three-logarithm arithmetic support saving for matched AND surviving charge. No whole residual bound or Lean compilation. Twin infinitude OPEN.

## 1. Original setup and stop geometry

Use X dyadic, N=X/2 odd original roots M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2, initial C=2M-2, H=4B, a=2B, u=log B, K(M)=floor((7M-1)/4). Original actual recorded prefix stops at the first recorded event at/beyond s_M+H or a twin terminal if earlier. Write e_M for that recorded endpoint. All original delayed masks and weights from 629f56a remain unchanged. Full completed original waits include the crossing event; e_M<=s_M+H+2B and d(e_M)<=12B+6. Reference continuation (common-cell as in 63fb14c or pair-local) is inside each original K and stops at a twin, never extends original charged occupation.

If two actual original completed waits share a slot (C,v0), both have recorded the departure event v0, and after it follow the same deterministic physical recorded suffix. Their original stops on that suffix follow the order of the nominal thresholds s_M+H: a larger threshold cannot yield an earlier first event at/beyond the threshold, and a common twin can only make stops equal. In particular
    M<M' implies e_M<=e_M'
for every originally charged same-slot pair. This does NOT hold for arbitrary unrelated trajectories before they meet. Equal stops at different M are allowed.

For a positive old terminal level lambda let the first observed post-state below lambda after e_-=min(e_M,e_M') be at t, with actual immediately preceding recorded state at b, selected p and post-horizon J. Both paths share this edge in the reference. The original charged slot departure satisfies v0<=e_-<=b<t. Since there is no intervening twin, the exact condition for a tag of the pair is
    e_M<t iff s_M+H<=b iff M<=c,
    c=b-H-2.                                           (1)
If its nominal threshold was already passed at v0, the stop is v0; otherwise it is the first later common recorded event at/beyond that threshold. This proves both directions, including equality at b. If the threshold is >b, the original stop is at t or later. Thus GAP (e_-<t<=e_+) has one root on each side of c, oriented from the smaller original source to the larger one. AFTER-BOTH (t>e_+) has both roots <=c. This cut is determined by the actual recorded predecessor, NOT by the selected event time t alone. At a fixed labeled post-key different incoming predecessor times may exist; do not assume c is a function of (t,J,p) alone.

## 2. Actual upward-birth keys for old terminal energy

Recall 629f56a: at a retained focal tick t0 in a rough slot (C,v0), orient pair toward the later *actual wait arrival* (not necessarily the larger source). Shift by ell=max(1,floor(eta*r(C))) and split its tick contribution equally over the two upward integer levels at true stationary tick z=t0-ell. Each pair-level charge <=1/2 and is an actual common stationary upcross before the recorded departure v0. It was classified old terminal precisely because the level remains occupied until the earlier original recorded stop. By alternation of up/down crossings, this is the UNIQUE last upward crossing of lambda on the common true path through e_-. In particular, for the old terminal positive charge define its origin key
    A=(C,v0,lambda),  z=ceil((C+lambda)/2).            (2)
The tick z is determined by this key. Both original tags actually occupy C at z-1,z, and both complete its outgoing event v0. Each charge has exactly one such A (same original pair and level cannot be charged at two different origins).

For a fixed A every path that contributes has the SAME physical state (z,C). Its continuation up to any common permitted time is deterministic. There is no downcross of lambda before the respective earlier original endpoint, by the old terminal classification. If any pair at A has an observed first hit after its earlier original endpoint, this is the first downcross after z along that physical path, uniquely determined by A. All matched pairs at A have the same post-key (t,J,p), the same actual preceding b, and the SAME source cut c in (1). This statement allows different cells or local reference cutoffs: a shorter reference can omit the first hit but cannot change it. A can support GAP and AFTER-BOTH simultaneously, or matched and other statuses for different pair-local endpoints. In a full common-cell continuation through the hit, its fate is shared; no identification of pair-local survivor endpoints across pairs is made.

Distinct A may hit the same future key. There is no injectivity in that direction; the arithmetic first-hit quotas of 19aeea8 remain global at the destination.

## 3. Bilateral birth-key graph peeling (including GAP recipients)

At each A form separate simple weighted graphs of actual positive old pair-level charges, by type GAP, AFTER-BOTH, active SURVIVOR (and optional twin class, irrelevant under no-large-twins). Each edge has weight <=1/2. GAP is bipartite with the actual cut c from section1; its two sides consist of earlier/later source roots. Unlike the previous directed peeling of 19aeea8, we may now iteratively pay low weighted degree at EITHER side. For AFTER-BOTH and survivor use the same undirected rule. The graph is an energy ledger, no changes to original occupation or its masks.

Let m=u^(11/4). For each such graph repeatedly remove a vertex with current incident weighted degree <=m, paying its remaining edges once. Each vertex costs <=m in its particular A/type graph. Although a source may be a GAP recipient at MANY different first hits or origins for a fixed lambda, it cannot create an unbounded budget: every membership is witnessed by its own ORIGINAL stationary tick z in a completed original wait at C. Every such stationary tick crosses only two upward levels and determines a unique next event time v0 for that tag. The sum of source membership counts over ALL A (without splitting types) is at most 2 sum_M (e_M-s_M)=O(XB). A tag can belong to at most three non-twin type graphs at a particular A. Thus total payment over all graphs is bounded by
    P_birth-core <= 6m sum_M(e_M-s_M)
                  =O(XB u^(11/4))=o(XB u^3).          (3)
This is an absolute quadratic estimate independent of W, even for pair-local continuations. It applies after arbitrary earlier payments by using the remaining fractional edge weights. No vertex from a new pair formed only in the reference is included.

Each remaining vertex has current weighted degree >m. Each retained GAP vertex therefore has >2m distinct charged partners on the OPPOSITE side of the SAME source cut at the SAME origin-level key. A nonempty GAP core needs >2m vertices on BOTH sides and total weight >2m^2; a nonempty undirected AFTER-BOTH or survivor core needs >2m+1 vertices and weight >m^2. This is stricter than earlier one-sided GAP degree. It removes a key with a huge number of earlier stoppers but few later partners, or the reverse, without assuming the total physical ancestry is small.

Optional paper-only near-cut refinement (not separately audited): set h=m or any h=o(u^3). For each GAP key pay all edges with at least one root within h of c. At most O(h+1) odd roots can lie in either side strip. Charge edges incident to the earlier strip to their later endpoint and those remaining incident to later strip to their earlier endpoint. By edge cap and the same original membership bound, payment is O(XB(h+1)), independently of W. The retained GAP edges after this priority satisfy i<=c-h and j>=c+h (up to endpoint rounding) and hence |i-j|>=2h; the nominal cutoffs straddle b by h. This is a constraint on nominal cutoffs, NOT a lower bound of h on the separation of actual rounded event endpoints. Peeling may follow. This is another optional absolute payment, not an unconditional bound for the remaining GAP graph.

## 4. Arithmetic support at the original upward origin

The outgoing-slot sieve in 629f56a gives, for rough r(C)>=D/4 with D=floor(B/u^2),
    S_slot = sum_(distinct actual rough slots (C,v0)) r(C)
           = O(XB log u/u^3).
Recall the reasons: actual outgoing p>=r>=cB/u^2, C+2s-1=0 mod p; O(B/p) allowed departure phases, O(X/(p u^2)) rough horizons per p/side by uniform two-form sieve; r<=p and sum_{p>=cB/u²}1/p=O(log u/u). This uses actual original slots in O(X) range, not future slots or twin terminal r=0.

For each fixed slot all actual original arrivals occur within 2r of v0. All possible upward-birth ticks z lie in [v0-2r+1,v0-1]; at most 4r integer levels are crossed by these stationary ticks. The delayed masks only reduce this support. Hence the number of distinct possible origin-level keys A, including all types together, is
    S_birth <= 4 S_slot = O(XB log u/u^3).             (4)
This is a three-logarithm saving compared with the trivial source/time key strip scale XB, up to log u. It holds for OLD terminal pairs that eventually descend AND for pairs still surviving at the extended reference endpoint. It is independent of the outgoing p at the future first hit, the last incoming q at the original rough state, and W.

After any graph payments, sum the ACTUAL remaining non-twin charge at each A over its types, call it V_A. With
    c_birth = u^(23/4)
pay min(V_A,c_birth), e.g. proportionally to the remaining edge weights at the key. By (4),
    P_birth-quota <= c_birth S_birth
                   =O(XB u^(11/4) log u)=o(XB u^3).  (5)
This is an absolute bound on actual allocated energy, not a linear occupation mask. All positive residual origin keys must have had V_A>c_birth before that quota. In particular their pre-quota union graph had >2 sqrt(c_birth) distinct vertices up to harmless rounding, because total weight <=n(n-1)/4. This is a union condition across types, not a separate claim about each type. The exponent of the permitted origin cap is u^5.75, substantially above the destination caps u^4.75,u^3.75,u^2.75. It can also be used on the survivor graph, which has no matched destination. 

The origin quota and destination quota are compatible in series: apply one, then compute the actual remaining weights before applying the other. Both total budgets hold separately, hence their sum is still o(XB u^3). The same for source-level/endpoint/low-level payments. Fractional quota subtraction may destroy minimum degree; repeat the bilateral peeling on the actual remainder at cost (3). Do not automatically infer that a core degree constraint survives proportional reduction. The numerical audit compares the NEW ledger with the previous ledger on the same original charges; it does not cumulatively measure both quota systems.

## 5. Residual sufficient condition and next step

Under the no-large-twins hypothesis, for sufficiently large X the twin terminal type is empty. With the above disjoint payments, including the destination quotas of 19aeea8 if desired,
    T_old <= G_birth,GAP + G_birth,AFTER + G_birth,SURV
             + O(XB u^(11/4)(1+log u)).
Here the terms are actual residual pair-level weights grouped by original rough birth, with bilateral core property if the final peel is reapplied. GAP is now tied to an explicit source cut and a deterministic first future hit. Matched types can additionally be required to survive destination-key quotas. No estimate o(XB u^3) for these dense remaining graphs is supplied. The restriction that many sources on both sides of a single cut share one original upward tick and one first future hit may allow a more direct weighted reverse-reachability/interval argument, and for survivor the origin grouping can be combined with the previous long-reference energy transport. The earlier immediate/later and CROSS/low-r/MED residuals remain; the project has not proved twin infinitude.

## 6. Reproducible verification

Standalone research/min_clock_terminal_birth_key_audit.mjs, initial source commit 29b8a91567f3d6e671e0abdfb90f2d023eb25fcb, final source commit 687f4703610acd5b0b5d2f353d9315b3c6a319f6, exact final readback blob 5020686595bfc39302d871b76926ac91da8ef236. Retains the corrected literal parity-gcd original replay, independent future progression stepping, level interval sweep and previous graph assertions. New checks: source-monotone original stops, exact root cut per matched edge, actual shared stationary tick for every compressed origin/level incidence, uniqueness of matched destination AND predecessor cut at each A, per-source original stationary membership upper bound aggregated by type, weighted peeling on both sides of the GAP cut, core lower size/mass, actual distinct origin-key support <=4 sum actual r, quota accounting. Floating-point sums use tolerance. The initial common-cell runs reach twins for all sources, so nonvacuous survivor graph data use pair-local continuations as in 19aeea8. Optional near-cut payment in section3 is paper only; cumulative destination+origin priority is paper only.

Run:
    node research/min_clock_terminal_birth_key_audit.mjs 4096 16384
The function was actually executed in the available JS runtime, not separate Node invocation. Ten stress occupation combinations: X4096,16384 at (W=floor(B/8), graph threshold2, origin cap32) and (W=B, threshold8, cap128), plus X16384 at (W=floor(B/8), threshold0.25, cap4), two occupations each. Earlier original delayed masks unchanged (D=floor(B/4), L30,y5, thin cap12, etc.). The graph threshold/cap and local W are diagnostic, not asymptotic; no analytic-mode numerical runs claimed.

Largest X16384, B339, local W42, old GAP52.4483/69.9310 late/full positive and AFTER-BOTH1.9138/4.0345. Previous directed threshold2 left all GAP charge; new bilateral threshold2 pays ALL these GAP and AFTER-BOTH charges (no dense core). This is nonvacuous improvement in the same actual data, not an asymptotic estimate. At threshold0.25 both GAP cores are nonempty, with six keys each, minimum side cardinalities 3/26 late and4/26 full positive. Actual origin cap4 paid24 late GAP, leaving28.4483; positive paid22.6909 GAP and1.3091 AFTER, leaving47.2401 and2.7254. The positive AFTER graph also nonempty. At W42, all old terminal origin key counts including twin=3862 late/19726 positive, matched keys6 each, max destination fan-in1 in these runs, some origin keys support multiple types (1178/2060 keys), actual sum r=92665. Memberships per type for positive (GAP180, AFTER24, SURV119502) vs original total clock1875194. No inference from fan-in1 to general injectivity.

New independent surviving graph ledger:
| X | occupation | W | threshold | origin cap | raw survivor | core payment | origin payment | residual |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
|4096|late|21|2|32|98556.46|502.26|11392|86662.20|
|4096|full positive|21|2|32|189454.43|0.67|16768|172685.76|
|16384|late|42|2|32|471678.47|4577.02|58880.60|408220.85|
|16384|full positive|42|2|32|952926.92|0.59|99919.61|853006.71|
|16384|late|339|8|128|74960.75|67360.75|5888|1712|
|16384|full positive|339|8|128|151624.77|54990.00|57856|38778.76|

All assertions passed, including nonempty bilateral cores in the fractional-threshold run. The W339 and W42 comparison varies graph thresholds and origin caps as well as reference duration, so is not an isolated estimate of W dependence. Finite candidate counts and retained energy are not evidence of a limiting little-o for the residual. Main/other branches unchanged, no Lean compilation.
