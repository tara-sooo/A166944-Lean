# Canonical renewal map, even-reset bridge, and thin departure gain

2026-11-25 JST. Continues eaf6c527e1d978c28d4fb5ec568b954f141fd765 (reset-cohort energy transfer), 842e743d7219abf6ad143288fe22ea3f321f36e4 (monotone crossing peeling), and e15eb81dd0e0e1fe2b98086421b9c5023fd2f313 (uniform rough sieve). New: every even reset reaches an odd canonical start after at most seven clock units (unless stopped), exact first-return renewal map with virtual starts inside waits, sliding ancestor convolution reconstructing the whole natural occupation energy, bounded inverse degree for elementary large-prime returns, and a sieve bound on actual thin departure gains near canonical states. No complete bound on renewal basins or inter-arc energy; twin infinitude and Lean compilation open.

## 1. Definitions and virtual canonical points

Use original all-odd MIN roots M in [X,2X), X dyadic,N=X/2, B=ceil(sqrt(7X)),H=4B,a=2B,G=2H+B+6. Original root state (t,C)=(M+2,2M-2), K=floor((7M-1)/4). Assume H+2B<=min(K-(M+2)) eventually. Original canonical paths include first post-state crossing the relative clock H or twin terminal. Selected q<=B; waiting time w<=2r(C)<=2q<=3(q-1). All horizons in [2X,7X); gain<=G, deficit delta=2t-C in [0,12B+6]. C increases strictly at each event, and is constant during the wait. Use integer times in half-open wait [t,v), i.e. the next selected event has not yet occurred. If a twin terminal or original cutoff is reached, the finite path stops. All statements about continuation are within the common fixed B and range gate; they are not an extrapolation of a root-dependent finite K beyond its allowed range.

A CANONICAL POINT is an actual state at an integer time (t,C)=(m+2,2m-2) for odd m. Thus C=0 mod4, t=C/2+3. This includes an odd reset POST-state but also a virtual point inside a wait: if the current post-state has time t0<=C/2+3<next event time, then the state at time C/2+3 is canonical, even if no event occurred then. Include a canonical point at the actual terminal post-state if it satisfies the definition and is within the original clock cutoff, but do not invent further waits at a twin terminal. Restrict point times to <=M+2+H. At most one canonical point per horizon, and future MIN continuation from that point equals the original continuation (strict next-event search starts after that time). Cutoffs can shorten, not change this common suffix. The canonical index m need not be an original root in the fixed dyadic family; allow it in the enlarged O(B)-boundary interval, or safely in [X,7X/2+1].

## 2. NEW even reset bridge

At an even reset with J=0 mod4 and t=J/2 even, the only possible odd prime selected at t+1 is 3: for odd arrival the divisors of J+1 and t-1 divide 3. It occurs iff J=2 mod3. The post-state then has horizon J+2,time t+1, deficit 0, and at t+2 the even rule selects 3 again (the same prime divides J+1 and t+2, and no other odd prime can divide both). The resulting state is (t+2,J+4), another even reset. If J!=2 mod3, the next possible event at t+2 is 5, since any prime dividing J-1 and t+2 divides 5, occurring iff J=1 mod5. This also produces (t+2,J+4). If neither condition holds, no event occurs at t+1 or t+2, nor at t+3 (the odd condition at t+3 would require a prime dividing 1). Therefore (t+3,J) is a virtual canonical point.

In the first two cases repeat with J replaced by J+4. The trigger residues modulo 15 are 1,2,5,6,8,11,14. Adding 4 modulo15 can stay in that set for at most two consecutive starting residues (1->5,2->6); the next is outside. Hence at most k=2 increments J->J+4, each either two 3 events or one 5 event, followed by a quiet 3-time segment. The canonical index reached is
    m=J/2+1+2k,   time=t+2k+3,   0<=k<=2.
The added horizon gain is <=8, number of actual events<=4, added clock<=7. This is an exact bridge, not a density assertion. It applies when the requisite prefix exists; a cutoff or a twin terminal can truncate it. A reset state with odd arrival is already canonical. The odd intermediate state of the two-3 bridge has deficit zero, NOT the usual odd reset deficit 6, and is not mislabeled as an odd reset.

## 3. NEW renewal graph and sliding ancestor measure

Let f(m) be the first strictly later canonical index reached from canonical m, whenever it exists within a realized prefix. It is a partial map, strictly increasing on odd integers. Its value is independent of the original source tag whenever the next canonical point is reached. In a union of observed original prefixes, retain one copy of each observed edge m->f(m). The observed graph is a directed forest (outdegree<=1, increasing labels, no cycles). If m'=f(m), then the elapsed clock time between the two points is EXACTLY m'-m and horizon gain exactly 2(m'-m), so the sum of selected p-1 along the segment is 2(m'-m), even if one or both endpoints are virtual points inside waits. This is not true for arbitrary physical post-states; it is a special feature of canonical indices.

For an original family S (odd roots in [X,2X) or any retained subset), define A(m) to be its ancestor set in this observed graph INCLUDING m itself if an original root, with zero or more forward edges to m. Then actual roots reaching m within their original short prefix are EXACTLY
    A_H(m) = A(m) intersect [m-H,m].                 (1)
Proof: one direction is obvious by following recorded returns and comparing time m+2 to original M+2+H. Conversely, a path in the observed graph from M to m with m<=M+H can be followed by this original tag, because every edge is a realized deterministic segment and the tag's cutoff is no earlier than the edge endpoint. The range gate ensures its K does not interfere; a terminal twin cannot precede a realized return on the common suffix. The graph uses only edges that some original tag reached; it suffices for reconstructing the same reference family, not unseen ancestors of arbitrary other roots. A canonical start at the exact cutoff can appear as a vertex but contributes no later occupation.

A RENEWAL ARC at m is the deterministic path segment from time m+2 through, but not including, the next canonical point, or the longest actual truncated continuation in the reference family if no next return was observed. At each horizon C its segment is one interval [l_m(C),h_m(C)); strict horizon growth ensures uniqueness. Clip its right endpoint to the maximum actual cutoff among tags that reach it, or the twin/return if earlier. All tags of A_H(m) follow this arc until their own cutoff; shorter ones have only a prefix. At a virtual canonical point a single original wait splits into two arc segments, preserving its total duration.

For a given arc, define interval counting function
    N_m(x)=# { M in A_H(m): x-H-2 < M <= x-a-2 }.
Endpoint convention at integer boundaries can be reversed without affecting integrals. The EXACT natural fractional occupation of arc m at C in the late slab [a,H) of each original root is
    U_m(C) = (1/(2r(C))) integral_{l_m(C)}^{h_m(C)} N_m(x) dx
           = (1/(2r(C))) sum_{M in A_H(m)}
                | [l_m(C),h_m(C)) intersect [M+2+a,M+2+H) |.      (2)
If no arc segment at C, set U_m(C)=0; no occupation at a twin terminal. Formula uses an ordinary length, not count of visited states. Tags with cutoff before this arc segment contribute zero automatically. It also works in a different relative slab, or on a retained original root family. For selected-prime sectors, assign each split segment the label of its original event; the deterministic next event from a virtual canonical point is the same. More general arbitrary incidence masks require corresponding weighted ancestor counts; (2) is the exact NATURAL ledger.

At each C,
    U(C)=sum_m U_m(C),
    R=sum_m sum_C r(C) U_m(C),
    E=sum_C r(C)(sum_m U_m(C))²
     =sum_m sum_C r(C) U_m(C)²
       +2 sum_{m<n} sum_C r(C) U_m(C) U_n(C).          (3)
This reconstructs all projected overlap, including asynchronous overlaps, not merely pairs meeting at canonical states. The cross-arc terms may include different portions of the SAME original wait at a virtual split, so they are not all distinct-root pairs; (3) is exact for the original E including its diagonal. The formula replaces repeated ancestry walks by a one-dimensional return graph, shared deterministic arcs, and interval sums over original source indices. It is not itself a proof that basin sizes or cross-arc energy are small.

## 4. NEW inverse bound for elementary large returns

Call an edge elementary if its first selected prime p>=Y>=7 after canonical m immediately enters an odd or even reset, and the next canonical point is that odd reset or the even bridge of section 2. The first event may follow a virtual start. For the odd case with destination n=f(m), J=2n-2 and p|J+2, hence p|n, and m=n-(p-1)/2. For the even case J=2n-2-4k, 0<=k<=2, p|J, hence p|n-1-2k, and m=n-2k-(p-1)/2. Thus every incoming elementary edge is indexed by a prime factor of one of
    n, n-1, n-3, n-5,
plus the indicated case. Each such p/case fixes m. For n in the ambient range, the inverse degree of elementary edges with p>=Y is O(log B/log Y), hence O(1) for Y=B^delta, fixed delta>0. Extra parity, exact first return, and MIN constraints only reduce the degree. This does not bound the incoming degree of general renewal edges with long nonreset excursions. Nor does constant elementary degree alone bound an arbitrary-depth basin.

## 5. NEW sieve bound on gain of canonical departures

For a canonical point m, consider the FIRST selected event after it, including if it lies within an original wait. If its next time is t=m+2+w and label p, the clock congruence gives
    p | 2w+7  if arrival even,
    p | 2w+1  if arrival odd.
In either case w>0 and w<=2r(D) for D=2m-2. For p>=17, w>=(p-7)/2>=p/4, and r(D)>=p/8. Therefore large departures from a canonical point are necessarily rough on their predecessor horizon.

Extend this to a later event with pre-horizon D at gain e=D-(2m-2)<=L after the latest canonical point m, where L>=0. Its pre-event deficit is <=6+5e because elapsed<=3e, using a shortened first wait if m was virtual. For p>=max(17,10e+16) the post-event deficit>=0 and the drift equation imply
    2w >= p-1-(6+5e) >= p/2.
Thus r(D)>=p/8 also here. No condition on intermediate labels except the gain bound; a short LOW-only prefix is one application.

Use u=log B,Y=max(17,ceil(B^1/8)), L=floor(u^1/8), Q=max(Y,10L+16). We treat two disjoint event types per original tag:
  direct: first event after its latest canonical point (e=0), any p;
  near: e in (0,L], p>=Q.
Only count an event once in the chosen type. A virtual point in the current wait is included in the latest-point rule; the whole original selected gain p-1 may be charged for that event, despite the shortened clock from the canonical point. For a fixed canonical m there is at most one direct departure and at most one near event, since the first near event has p-1>L and takes the gain beyond L. Some original tags starting at m can stop before it or encounter a newer canonical point and be assigned elsewhere; no new trajectories are generated by deleting tags.

For fixed p>=Y and sign, D+-1 are p j and p j+-2 for odd j. Rough r(D)>=p/8 means that j and p j+-2 avoid all odd primes up to Z=floor(B^1/64) eventually. The uniform dimension-two Selberg sieve from e15eb81 applies in j=2n+1 (two distinct forbidden residues at each odd prime <=Z, p>Z), gives O(X/(p u²)+Z^6)=O(X/(p u²)) possible D per p/sign. Summing the selected gain p-1 over these pairs (D,p), p>=Y, costs
    O(X/u² * pi(B)) = O(XB/u³).
The direct canonical m is uniquely determined by D, and the small direct p<Y have at most O(X) distinct canonical keys and gain <Y each. For a near event at fixed D,p there are O(L+1) possible canonical indices m (since e<=L). Thus over all DISTINCT possible departure keys (type,m), counted at most once per type with its deterministic selected label p,
    S_direct = O(XB/u³ + XY) = O(XB/u³),
    S_near   = O((L+1) XB/u³).                          (4)
Here the sums S are gain-weighted (sum p-1), not counts of original root tags. The bound holds in the larger ambient range and includes possible starts not observed in the dyadic root family. The same sieve with weight1 gives O(X/u²) candidate direct keys with p>=Y and O((L+1)X/u²) candidate near keys (since sum_{Y<=p<=B}1/p=O(1)). In particular only o(X) original canonical starts themselves have a direct large departure, though later inherited tags can accumulate there.

Let n_g be actual count of original tags assigned to a departure group g=(type,m), with its unique selected p. Each tag contributes at most once to that group. For m0=floor(u^11/4), call groups with n_g<=m0 thin. Then total ACTUAL selected gain of thin groups of both types is bounded unconditionally by
    G_thin <= m0 (S_direct+S_near)
           = O(XB/u^1/8)=o(XB).                       (5)
Direct-only bound is O(XB/u^1/4). The corresponding natural clipped clock cost is <=1.5 G_thin (in fact full half-wait<=p<=1.5(p-1)). This is a genuine linear deletion, not a bound on the quadratic energy discarded. For the previous MED/HIGH criterion one may use such a mask only with the existing LOW destination accounting; (5) itself does not license arbitrary MED loss in that transfer argument.

## 6. Monotone peeling and actual retained masses

Use the frozen departure group membership of section 5 on any reference family. Iteratively delete an original root if its total selected gain in CURRENT thin departure groups is >=eps B, eps=u^-1/16. Charge those groups at deletion, decrement all its memberships. Once a group is charged for the first time its remaining membership is <=m0, and each charged tag is immediately deleted. Its lifetime charged gain <=m0(p-1), irrespective of subsequent threshold crossings of other groups. Consequently
    #deleted <= G_lifetime/(eps B)
              = O(X/u^1/16)=o(X).
Each deleted root loses at most B of late slab linear occupation, so this costs o(XB). At the fixed point every retained root has <eps B selected gain at its remaining thin canonical departures. All other qualifying departures have >m0 actual retained tags in their group. Total remaining thin gain <=eps BN=o(XB), even if the initially thin groups are no longer the same after deletion. The thick groups consist of actual tags sharing a canonical point and the departure event; not necessarily all tags in its full ancestor basin. No claim that a positive fraction of overall gain is in these departure types, and no bound on unrestricted later events of a long arc. This theorem gives a different, gain-weighted reduction from the earlier cutset-level peeling of 842e743.

## 7. Verification

Standalone research/min_clock_canonical_renewal_audit.mjs, final remote readback b409bf7f382d199860016aa06f2b91088bd343f9, blob 83db238cfd09ab9305f58ac8470ee8bb2749974f. Run:
    node research/min_clock_canonical_renewal_audit.mjs 1024 4096 16384 65536
Final JS executed in available runtime, 12 runs (four windows x3 modes). Original canonical MIN simulator and literal parity-GCD check at X1024; independent even-reset bridge checks using exact next-event search at every J divisible4 in ambient range; actual bridge and virtual point checks with cutoffs; deterministic return edge and exact displacement/gain identities; elementary inverse prime divisors and degree; actual direct/near departure congruences, roughness and unique group; independent deterministic replay of all ambient canonical starts for finite gain envelope; lifetime peeling and retained fixed point. Added exact return map composition with cutoff, full ancestor list reconstruction, and per-arc interval occupation oracle (2)-(3), reran all 12. Floating tolerance for weights, no finite inference of sieve asymptotics. Terminal bridge counter called bridgeTwin also covers any recorded prefix ending before the bridge; it is NOT a count of distinct twin primes. Audit computes all-label natural E in (3), not sector decomposition or cumulative prior masks. Unused chargedClock placeholder is not a measured loss. Finite analytic L=1 (near branch empty because gains even), Y17, m0=floor(u^2.75), eps=u^-1/16; diagnostic L4,Y17,Q56,m0=2,eps.1; wide L12,Y7,Q136,m0=8,eps.05, finite stress choices only.

Largest X65536,B678,N32768,794415 selected events:
- Independent bridge checks81915, max k2; actual even reset bridges47265, truncated before bridge1058. Actual canonical incidences128470, including37290 virtual,32775 distinct indices; renewal edge incidences95702,24605 distinct directed edges. Exact map composition128470 point checks,32775 basin lists,227328 arc interval-convolution checks. Max actual sliding basin226,325 arcs with positive late occupation. Reconstructed R402074 and E18998125.5468697, within-arc quadratic part7961910.5228300 (41.9%); remaining cross-arc term11036215.0240397 (58.1%). All modes same natural ledger. These are not a diagonal/offdiagonal pair partition because waits may split.
- For Y17 elementary returns10813 tag-edge incidences,2030 distinct edges, max observed inverse degree3; Y7 gives16704/3920/max3. Original roots' own first selected total gain340420,3157 roots first p>=17 (finite Y).
- Actual direct departure incidences125618,32184 groups,max226, selected gain1692836, natural late clock535. Independent ambient direct support80520 keys, gain895044. Diagnostic near9654 incidences,1770 groups,max141, actual gain1767530, late clock0, ambient near support5389 keys/gain1027278. Wide near7351 incidences,1719 groups,max145, gain2049072, late clock137, ambient6044 keys/gain1756806. Thus these departure types occur primarily BEFORE late slab at this finite scale, as in previous reset-energy-transfer findings.
- Analytic thin direct gain1666462 (late clock466), near empty, 131 roots removed at eps=.88943 in one pass, charged gain88394, remaining thin1578068, remaining thick26374. Diagnostic thin direct287920/near246644 (both late clock0), 2034 roots peeled, charged392348, final thin147008 (138868 direct+8140 near), thick2767824. Wide thin direct629448/near722672 (late clock0),6419 roots removed in two passes,charged1283086, final thin170394 direct only, thick1828518. These are selected-gain ledgers, not cumulative reductions of previous residual energy. Finite analytic eps is large and L1, so no numerical demonstration of the limiting small loss. Independent arithmetic bridge and return map tests are nonvacuous.

## 8. Remaining direction

Use (1)-(3) to analyze actual interval-localized ancestor counts of renewal graph, with elementary inverse degree and thin departure gain bounds as tools. The majority of finite late energy crosses arcs, and large basin masses and non-elementary long excursions remain. A key next issue is whether long renewal edges with many ancestors can be controlled by the local occupation/first-contact bounds, or by stronger inverse estimates on non-elementary returns. The new representation and gain reduction do not supply either complete MED/HIGH upper bound or the twin-prime proof. Main unchanged; no Lean compilation.
