# Compressed inverse stationary intervals and primorial block-entry cores

2026-11-25 JST. Continues 5cc7609c15c06e27f9d2942d2f410454bd66c83b. New paper results: exact inverse enumeration for actual completed rough waits by compressing stationary clock intervals, safe source-set upper certificates at any finite horizon cut, and an actual primorial block-entry cohort decomposition (not the last nonLOW event). Refined simultaneous partner quotas inside each origin-level graph give an unconditional absolute payment O(XB log^(11/4) B); remaining cross-entry edges require many actual charged partners through a specific earlier entry key, not only a large total ancestor count. No general bound on heavy same-entry or cross-entry graphs, no Lean compilation, twin infinitude OPEN.

## 1. Setup and scope

Keep the original dyadic family: X dyadic, N=X/2 odd M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2, initial C0=2M-2, H=4B,a=2B,u=log B,K(M)=floor((7M-1)/4). Assume original gate H+2B<=K-s_M for every source. Original actual completed waits include the crossing event at/beyond relative H; stop at first such event or twin terminal. Recorded end e_M<=s_M+H+2B. MIN uses the smallest odd prime <=B dividing gcd(t-2s,C+2s-1) at tick t, s=t mod2. If none, stationary. C<=2t, each jump increases C by p-1, each full wait <=2r(C)<=2p<=3(p-1). Every nonterminal query below lies within the original horizon range. No extrapolation past twin terminals.

The old terminal charge of 5cc7609 is an unordered original pair and integer level lambda, weight at most 1/2, arising at a true stationary tick z=ceil((C+lambda)/2) in a rough completed slot (C,v), z<v. Both tags are present at z-1 and z and complete v. A=(C,v,lambda) is the actual upward origin key. The total distinct source memberships over all A is <=2 sum_M(e_M-s_M)=O(XB). GAP, AFTER-BOTH and survivor graphs may be treated separately at constant-factor cost. All prior actual masks and charges can be retained. This note works at the original birth, before reference extension, and does not introduce new future pairs.

## 2. Exact interval-compressed inverse enumeration

Fix a nonterminal even horizon J and a true clock state (t,J), state AFTER tick t. Define the last potential event at fixed J up to t, respecting nonnegative deficit:
    a(J,t)=max(ceil(J/2), max_{s in {0,1}, p|J+2s-1, odd p<=B}
                 [rho(p,s)+2p floor((t-rho(p,s))/(2p))]),
    rho(p,0)=0, rho(p,1)=p+2.
The inner maximum may be ignored if its indexing set is empty. For every query here r(J)>0. The actual potential event times at J are exactly the union of these progressions, irrespective of which eligible prime is least at a tie. Thus [a,t] is the complete possible stationary entry interval for a history arriving at J and still at J at t: an entry earlier than a would have had to leave J at a; any entry in [a,t] has no possible outgoing event in (entry,t]. Entry at a itself is permitted: a jump can arrive from a DIFFERENT horizon at that tick, or a root can start there. The artificial lower bound ceil(J/2) just enforces C<=2t and need not be a potential event. Since at least one progression has modulus 2r(J), t-a+1<=2r(J).

The exact backward recursion from (t,J) is now compressed:
* A canonical root M=J/2+1, M odd, is admissible if its start s_M lies in [a,t] and in the source range.
* For every side s and odd prime q<=B dividing J+2s, enumerate b in [a,t] on the progression rho(q,s) mod 2q. The candidate jump predecessor is (b-1,D), D=J-q+1. Keep it iff D>=2, D<=2(b-1), and the actual MIN test at tick b from horizon D selects q exactly. Recursively recover canonical ancestors of this predecessor. D is strictly smaller than J, so this terminates in the finite root-horizon range. A predecessor with selected q is nonterminal.

Necessity follows by taking the actual arrival event into J (or its root start) and substituting D=J-q+1 in the MIN divisibility condition. Sufficiency follows by forward replay of that event and the stationary interval. This avoids scanning every stationary inverse tick as a separate state, and differs from merely enumerating possible incoming labels without the MIN check. At finite nonreset exceptions (including odd q=3,d=0) direct congruence and MIN are used; no incorrect k>=0 assumption.

To obtain EXACT source tags of an ORIGINAL completed slot at a birth A, query (z-1,C), not just an arbitrary unrestricted state. A candidate top arrival b is allowed only for M with b<s_M+H, equivalent to M>=b-H-1 for integer M; pass this lower bound down that reverse branch. A top root at its own start automatically satisfies this. All earlier path states occur before b and hence before that source's nominal cutoff. The next event v is deterministic and the crossing event is included in the original prefix. Thus the resulting exact set consists of all original tags present at z-1 in completed slot (C,v), not necessarily all charged graph vertices (masks and terminal tests restrict them further). Every source lies in [X+1,2X-1], odd, and M>=v-2r(C)-H-1 from b>=v-2r(C). This top lower bound can be imposed before recursion. Additional monotonicity range bounds at any queried (t,J) are
    max(inherited lower bound, X+1, t-H-2B-2) <= M
          <= min(2X-1,J/2+1,t-2).                    (1)
They use t<=e_M and nondecreasing horizon. They do NOT replace the top entry condition. Exact search memoizes (t,J,inherited effective lower bound); distinct lower bounds may not be conflated.

## 3. Certified partial reverse supports and exact source cut bounds

Stop the reverse recursion whenever a non-top query reaches J<=K0, where K0 is any chosen backward horizon cut (not the original time gate K(M)). At each stopped query keep the odd source interval (1). Take the UNION of these intervals together with every exact root recovered above the cut. This is a rigorously valid superset S_A(K0) of all actual slot ancestors. Counting interval unions, not their sum, avoids duplication. A deeper cut replaces a frontier interval by exact roots and smaller intervals contained in it (inherited lower bound does not decrease; clock and horizon decrease). Hence the upper set is nested nonincreasing under deeper exploration. When no unresolved queries remain, the set is exact. The shallow upper envelopes can be very loose; no bound O(polylog B) is claimed for their sizes or for search complexity.

For matched A in 5cc7609, the first future crossing predecessor time b* yields the exact source cut c=b*-H-2. Let n_-,n_+ be counts of odd sources in any certified superset S_A on <=c and >c. Let n=n_-+n_+. Then for arbitrary actual old charge weights, without reconstructing all graph edges,
    V_GAP(A) <= n_- n_+/2,
    V_AFTER(A) <= n_-(n_--1)/4,
    V_SURV(A) <= n(n-1)/4.                           (2)
The first two use the deterministic matched cut; the third does not require any observed first hit. For total charge across all types at one A, n(n-1)/4 is a valid upper cap because each pair-level is unique even across types. The same caps hold with exact reverse sets. If the union cap is <=u^(23/4), the entire non-twin origin energy is covered by the birth quota of 5cc7609; if a bilateral core requires >2m vertices per side, a certificate of n_-<=2m or n_+<=2m excludes that GAP core. More generally every subset of actual origins satisfying such certified caps has absolute cost O(XB u^(11/4) log u) by the previous arithmetic origin support. No claim that all actual origins satisfy these caps.

A useful arithmetic reverse local degree: for an incoming label q>=Q at a query J, q divides either J or J+2; the number of distinct such prime factors is O(log X/log Q). In the stationary interval at most O(1+r(J)/Q) phase times are available per factor. Hence the number of large-label candidate inverse jumps in a query is O((1+r(J)/Q) log X/log Q), before the exact MIN test. This does not bound the number of small-label candidates or the root count across many reverse layers.

## 4. First entry into the final primorial block

Choose an even primorial L=product_{p<=y}p <=u^(1/16), largest possible (eventually L>=2), and f=u^(1/16). Let A be a rough origin C with r(C)>=cB/u^2, so eventually r(C)>L+1. Define the even block boundary
    K0=L floor((C-1)/L),   K0<C<=K0+L.
Use the strict interval (K0,K0+L], including the right endpoint. Every source reaching C either has its root horizon already in (K0,C], or it has a unique ACTUAL first event crossing from D<=K0 into J>K0. Denote the labeled entry key g=(J,t,q), J<=C, t<=z-1. LOW primes q<=y cannot make this crossing: if even D<=K0 and D+q-1>K0, then K0-D is even in [0,q-2]; eligibility modulo q requires K0-D congruent to +1 or -1 mod q, impossible in that interval. Thus q>y at all non-root entries. All intermediate event gains after the entry through arrival at C sum to C-J<L, and full wait times total <=3(C-J). Including the last incomplete stationary age at the charged tick gives
    K0<J<=C,    z-2r(C)-3L <= t <= z-1.               (3)
This argument allows other nonLOW events inside the block. The entry is not in general the last nonLOW anchor used in c8999c2.

There are at most O(L) root-inside vertices per origin A (root horizon injective in M). Pay all actual graph edges incident to these vertices, charging at most O(L) per other vertex by the edge weight cap. Edges with both endpoints inside can be charged once by any fixed orientation. Across all origin graphs the original source membership bound gives O(XB L)=o(XB u^3). This is an absolute quadratic payment, not deletion of a source trajectory or its later occupations.

For each remaining actual source assign its unique block-entry key g. The graph now has actual entry cohorts; two sources in the same cohort share the deterministic suffix from the crossing post-state onward. For different entry cohorts they cannot share a true state before their first crossing of K0, because then deterministic continuation would make the crossing event identical. Thus this is a real reverse-history split, not a partition by source-coordinate proximity alone. Different cohorts may merge later in the block.

Call q comparable if q>=r(C)/f. For fixed J and side, q is a prime factor of J+2s, and t is on its phase progression; all comparable q>=cB/u^(2+1/16). There are O(1) such factors per side, and (3) contains O(1+(r+L)/q)=O(f) eligible phase times. Summing across O(L) even J gives
    k_comp(A)=#distinct actual comparable entry keys <= O(L f).    (4)
This is a local arithmetic upper bound on the number of entry keys, not their multiplicities. Small-q group counts are not bounded by (4); use actual k_small or a larger arithmetic envelope.

A useful additional uniqueness: because a rough outgoing p>=r(C)>L+1, its jump leaves the block. A fixed labeled entry key g has a unique deterministic suffix, and can support at most ONE rough slot within its entry block across all original tags using g (an earlier source cutoff can omit it). This is a block-entry analogue of the previous last-nonLOW target uniqueness, now permitting intervening nonLOW events of small total gain. Paper consequence, not separately audited: same-entry comparable terminal energy summed over origins in the block is <= f sum_g q n_g^2, where n_g is actual original source mass entering g; every pair in a group has total charge at that one slot <=2r, so the group costs <=r n_g². All comparable-comparable groups in a slot can be bounded by O(L f²) times this selected-gain moment without an extra repeated-origin factor, by Cauchy and the actual one-slot-per-entry property. No bound for that quadratic gain moment is inferred from its linear counterpart.

## 5. Actual opposite-entry weighted cores

After any preceding payments, freeze actual remaining weights of the origin/type graph; remove root-inside edges as above. Let V be its current vertices with their true entry keys. Let k_comp,k_small count the occupied distinct comparable/small entry keys among those vertices. For a vertex v and entry cohort g, define current incident weighted degree toward that cohort. Use the following simultaneous constraints:
    cap(v,g) = m if g is v's own entry cohort,
               m/max(1,k_comp) if g is a different comparable cohort,
               m/max(1,k_small) if g is a different small cohort,
    m=u^(11/4).
At most one own-cohort constraint and at most k_comp+k_small other cohort constraints exist at v. Their caps sum to <=3m, even if many groups are empty or numerous. Repeatedly pay all currently remaining edges of any constraint whose degree is <=its cap. Each constraint is charged at most once (degrees only decrease, and all its edges are gone afterward). The total actual energy paid is <=3m |V|. Adding all original A and bounded types, and the root-inside payment,
    P_entry <= O(XB(m+L))=o(XB u^3).                 (5)
This is independent of reference duration W and can be used after any previous fractional quotas. It is not a bound on raw quadratic energy of reference ancestors. If desired add the previous global degree constraint per vertex at cost another m membership. If earlier paid amounts are frozen, there is no double count. Iterating constraints in any order leaves the greatest support satisfying the strict lower-degree constraints (any admissible subgraph cannot lose its first edge during peeling); this elementary statement refers to fixed residual weights, not reoptimizing earlier allocations.

For each remaining edge, both endpoint constraints towards the other's entry cohort have current degree ABOVE cap. In particular:
* Same-entry surviving edges have >2m actual charged partners in that entry cohort at each endpoint.
* Cross-entry edges whose opposite cohort is comparable require >2m/k_comp >= c u^(21/8) distinct actual charged partners through that SPECIFIC comparable entry key, by (4) and L f<=u^1/8.
* For opposite small cohorts the threshold is 2m/k_small, which can be small. No uniform diverging threshold is proved there.
All surviving cross-entry endpoints have genuine separated pre-crossing histories as proved in section4. This differs from merely requiring >2m partners anywhere in the full origin graph. The new residual is constrained by entry labels, reverse reachability and per-entry actual charged mass. It does not yet yield a little-o upper bound for either dense same-entry or cross-entry energies. Combine with previous bilateral GAP cut and destination quotas by disjoint priorities, then reapply cores if degree restrictions are needed.

## 6. Reproducible finite verification

Standalone research/min_clock_reverse_block_entry_audit.mjs, source commit 55e8ce273054fbf685580a38a7fe575af1f54ba9, exact remote blob 633536f9995467cb9799112c92cca36e6513aabb. Run:
    node research/min_clock_reverse_block_entry_audit.mjs 4096 16384 65536
Actual functions executed in available JS runtime, twice (second run summarizes the exact committed code). Forward literal parity-gcd smallest factor for ALL odd sources in each window. Select 12 rough slots per window by six largest tag masses and six evenly spaced ranks, sample z=min(v-1,latest arrival+1); check actual stationary predecessors. This is a diagnostic sample of origins, NOT exhaustive all birth keys or full terminal ledger. For each target compare exact compressed inverse original source set to the independent full forward source list, independently scan literal last eligible tick and incoming arithmetic candidates at up to64 inverse queries, check nested partial reverse union supports at cuts K0,K0-4L,K0-16L. Compare original actual first entry key and congruence/time window to relaxed comparable envelope; exact entry cohorts and weights. For each sample use the old delayed stress masks at the single level lambda=2z-C, late HIGH and full positive, with the same terminal test through earlier original end. No future extension/type split in this audit: use the union old terminal graph. The paper proofs allow separate matched/survivor graphs and the source cut caps (2); these numerical runs do not independently test the future source cut cap or block-entry gain transfer. Stress L30,y5,D=floor(B/4), f4, delay r/8, original thin cap12, NEW opposite-entry threshold m4. These differ from asymptotic parameters. No analytic mode numbers claimed.

| X | exact targets | maximum actual roots among samples | compressed queries | total stationary interval ticks represented |
|---:|---:|---:|---:|---:|
|4096|12|46|13580|69154|
|16384|12|133|25501|129482|
|65536|12|238|131285|681017|

All 36 exact source sets match, all nested upper certificates contain the actual set. The counts of compressed queries and sum of interval lengths are not a measured runtime speedup; the latter can include overlap across query keys. Maximum upper set sizes across the three partial depths respectively: X4096 342/329/193, X16384 680/662/630, X65536 1356/1354/1326. They remain loose. Largest sample actual 238 at C250980,z125941,r419; partial upper 1352->1324->1217, full inverse35512 queries gives exactly238. Another 238-root sample C251568 has all roots in one small-q entry cohort. At X65536 max actual entry groups8, max comparable groups3, max relaxed comparable envelope73 (across samples). Thus limited actual comparable groups do not imply small mass.

Nonzero sampled old terminal energy (only one level per selected slot):
| X | mode | raw | root-inside paid | cohort paid | remaining |
|---:|---|---:|---:|---:|---:|
|4096|late HIGH|682.3904|0|2.2744|680.1160|
|4096|full positive|1195.8690|0|90.2220|1105.6471|
|16384|late HIGH|0|0|0|0|
|16384|full positive|99.7943|25.4404|37.8586|36.4954|
|65536|late HIGH|0|0|0|0|
|65536|full positive|28022.4705|0|0|28022.4705|

Largest X65536 C203040,z101863,r277, 235 exact roots, two entry cohorts of sizes143/92, one comparable. Positive sampled level energy10920.4928, same-entry5434.8682, cross5485.6245, no cohort payment at m4. All27495 unordered edges retained; surviving comparable opposite partners143. C165690,z83023,r67, all215 roots in one small-q entry cohort, positive level energy10129.0672 all retained. Thus this finite test exposes genuine dense small-entry and cross-entry examples, rather than showing numerical contraction. At X4096 C14940 two actual comparable groups with positive charge84.8284 paid fully; some nontrivial peel checks at X16384. Many sampled origins have zero old terminal charge under the chosen masks, especially late HIGH at larger X. No extrapolation to all energy or asymptotic saving. The new unconditional absolute payment is mathematical; the heavy residual remains open.

## 7. Next target

Use the inverse block-entry decomposition to trace dense cohorts to earlier primorial block crossings or the true canonical renewal roots. For a surviving same-entry small-q cohort, large actual root mass was already present at an earlier nonLOW event; need control its repeated amplification across blocks, not a candidate-count bound on the last anchor. For cross-entry edges use genuinely different pre-crossing trajectories and the specific opposite-cohort partner lower bounds, possibly applying actual weighted cutset methods at several reverse scales. The independent prime-root multigrid work has a related precontact direction but concerns a different source ensemble and energy scale; no result imported without transfer proof. Keep previous immediate/later, distinct-slot, low-r and MED/full-positive residuals. Main and other branches unchanged. No Lean compilation.
