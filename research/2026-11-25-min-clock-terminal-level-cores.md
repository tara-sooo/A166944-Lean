# Original terminal-level graphs, directed gap peeling and arithmetic first-hit quotas

2026-11-25 JST. Continues 63fb14cd7b9c0fac7d069d8ddf0821d3cc0473a8. New paper deductions: compress the old terminal occupation into a simple weighted graph at each integer deficit level, independent of future reference length; distinguish first downcrosses before the later original stop from those after BOTH stops; directed gap peeling and iterative weighted-core peeling pay O(XB log^(11/4)B) of actual pair-level charge; three arithmetic first-hit support envelopes pay adaptive weighted key quotas independently of W. These are absolute quadratic payments, not linear masks and not an upper estimate for all future collision energy. Heavy gap groups, dense post-stop first-hit cores and persistent cores remain. No Lean compilation; twin infinitude OPEN.

## 1. Original charge, reference and unique level edges

Keep the setup of 63fb14c: X dyadic, N=X/2 odd original sources M, B=ceil(sqrt(7X)), s=M+2, H=4B, a=2B, u=log B, original K(M)=floor((7M-1)/4). All original charged masks and weights unchanged. The original actual recorded stop e_M is the first crossing post-state at/beyond relative H or an earlier twin terminal. It satisfies e_M<=s+H+2B and 0<=d(e_M)<=12B+6=:Dmax. Extend only the reference inside the original K, not the charged original occupation. Either the common-cell extension from 63fb14c or a fixed pair-local W from the earlier stop is allowed. In the latter case require e+W<=min(K(M),K(M')) for every queried pair. For common-cell, preserve the two shifted 10B cell cover, pair assignment and common absolute cutoff.

For an unordered original charged pair (M,M'), e=min(e_M,e_M'), let c_(M,M',lambda) be the old terminal level charge from all its original retained rough slots, at lambda in [1,Dmax]. The shifted stationary level allocation of 629f56a implies
    0<=c_(M,M',lambda)<=1/2.                          (1)
Indeed at a fixed level the upward/downward indicator alternates; at most one upward crossing can still be unmatched at the original common recorded stop. Within one slot each shifted focal tick contributes to distinct integer levels, and no crossing is charged more than 1/2. Thus the level graph is SIMPLE (no duplicated pair edge), even if the same pair had many original shared slots. Its weight is the actual allocated energy, not the raw count of pairs in an ancestor group. Every supported pair has source separation <=H+3. Zero weight edges may be omitted.

For each lambda extend the pair exactly as in 63fb14c. If it first reaches d<lambda after e, assign c to the first such recorded post-state v=(t,J) and actual selected incoming prime p. This is a net recorded descent. Otherwise assign c to either twin terminal or active survivor, as before. The entire old terminal charge is the sum over these graph weights. No new pair formed only in the extension can enter the graph. Reference duration W does not increase the number Dmax of charged levels.

## 2. NEW asymmetric gap versus after-both first-hit keys

Write e_-=min(e_M,e_M'), e_+=max(e_M,e_M'). For every matched positive pair-level weight let t be the first downcross of lambda after e_-.

* GAP: e_-<t<=e_+. Orient its edge from the earlier-stopping tag to the later one. Ties e_M=e_M' cannot be GAP. For any fixed earlier tag M and lambda ALL its outgoing GAP edges have the SAME actual first-hit key (t,J,p), since their reference continuation starts from its own fixed actual endpoint e_M, and any retained crossing is the first below lambda after that endpoint. The later tag can belong to multiple different GAP keys as a recipient: do not assume it has one first hit from its own stop.
* AFTER-BOTH: t>e_+. Both original endpoints have already occurred, and neither tag can have crossed below lambda between its own stop and t. Thus for either vertex M the crossing is the first below lambda after its OWN original endpoint e_M. All its incident AFTER-BOTH edges at a given lambda must have the same (t,J,p). In particular the graph decomposes into vertex-disjoint labeled first-hit key groups at that level.

This uniqueness does not require the same original endpoint for both tags. It holds even when different pairs are assigned different shifted common cells or different local absolute end clocks: these may omit a crossing but cannot alter the first crossing that exists. The two tags' recorded paths coincide from their original common slot departure onward, including through unequal endpoint times. If the first earlier-stop crossing occurs exactly at the later recorded endpoint, it is GAP by definition. If a local reference ends before the later original endpoint, only observed crossings or actual local terminal status are used; no artificial future downcross is inferred.

For an active survivor in a common-cell reference, every edge joins two vertices in a single physical endpoint group at T. If desired, split the survivor graph into assigned cell/partition graphs before peeling. Each tag belongs to one cell per partition, so this adds at most factor 2 to the budget. In the pair-local reference, endpoints may depend on the pair's earlier stop; the global survivor graph still satisfies (1), but no common-endpoint partition is claimed.

## 3. NEW weighted source-level peeling independent of W

Let m=u^(11/4).

GAP: at each lambda calculate the total outgoing weighted degree of every earlier-stopping vertex in the actual GAP graph. Pay all edges from vertices with outgoing weight <=m. Each such vertex's entire charge is <=m; for all levels total payment <=mNDmax=O(XB m)=o(XB u^3). All unpaid earlier stoppers have outgoing weight >m at that particular level and first-hit key. By (1) this requires >2m distinct actual original partners. This is stronger than a large reference ancestor mass: all these partners actually carry an old charge at the given level.

AFTER-BOTH: at each lambda, iteratively delete any vertex whose CURRENT total incident weighted degree is <=m, paying every remaining incident edge once at deletion. Total payment <=mN per level, because each vertex is deleted at most once. This is a weighted graph core (not a count of all physical ancestors). It works for any finite graph and arbitrary fractional weights satisfying (1). On termination every retained vertex has weighted degree >m, hence >2m distinct charged partners. By section 2 each connected component lies in one first-hit key; the active key groups are vertex-disjoint. In particular any nonempty retained key group has >2m+1 vertices and weighted mass >m^2, and there are O(N/m) such keys per level. Across all levels there are O(XB/m) nonempty retained AFTER-BOTH key-level groups. These are count and density restrictions, not a bound for their aggregate weight.

SURVIVOR: the identical iterative weighted-core payment works on the actual surviving pair-level graph. It can be applied globally, or separately to cell endpoint groups in the common-cell construction (constant-factor cost). This strictly refines a test based only on total endpoint mass: even a huge endpoint group can have a sparse weighted graph of actual charged pairs at a given level. A component of the retained graph needs >2m original charged neighbors at EACH surviving vertex at that level. Since source separation is O(B), these dense graphs are local in original source coordinates. No claim that a large endpoint cohort must supply such a graph.

Adding the three payments gives at most 3mNDmax (or 4mNDmax with the optional two-partition survivor peeling), i.e. o(XB u^3), independent of W. All are absolute contributions of the actual original energy, not changes to the occupation weights. Low-level and thin-endpoint payments from 63fb14c can be applied first by restricting the graph; (1) and all bounds remain true. If a fractional key quota is applied AFTER weighted-core peeling, some remaining weighted degrees may fall below m; a further peeling pass costs the same O(XB m) and restores the core property. Do not claim it automatically persists after weight subtraction.

## 4. NEW arithmetic support for first-hit keys in a bounded level strip

The arithmetic negative-cutset proof in 3bd47c5 counts labeled post-keys per level. Here apply it to FIRST hits of ORIGINAL unmatched levels only, even in a much longer reference. At a crossing of lambda<=Dmax with incoming p>=5, pre/post deficits d_pre>=lambda>d', and completed wait w>=1, we have
    lambda-p+3 <= d' <= lambda-1,
    d'=6s+2p k,  J+2s=0 mod p,  s=t mod 2.           (2)
The first inequality uses net drop p-1-2w<=p-3. For fixed lambda,p,s there is at most one integer phase k (the interval has length <2p); even if d'=6s is a reset it is counted. For each such phase, J in the original O(X) horizon range satisfying its congruence has O(X/p) possible values (p<=B), and t=(J+d')/2 is fixed. Thus key-level support is bounded independently of W and even of the possibly much larger reference maximum deficit. All charged crossing labels are actual MIN selected labels; relaxed arithmetic candidates can only enlarge the support.

Split distinct keys (lambda,t,J,p) into disjoint types, in this priority:
  R: rough predecessor r(C)>=Y=ceil(B^1/8), C=J-p+1;
  H: remaining keys with p>=Ptop=ceil(B/u^2);
  A: all other keys.
R includes only p>=Y. For R use the uniform two-form upper sieve on C-1,C+1, exactly as in earlier rough cutsets: for each fixed p, side and phase, the congruence on C modulo p leaves O(X/(p u^2)) candidates after excluding odd prime factors <=B^1/64. The sieve interval length O(X/p)>=cB absorbs the established error. Since p>=Y eventually exceeds sieve cutoff, the two distinct forbidden residues are valid. The elementary reciprocal sum from Y to B is O(1) by Chebyshev and dyadic summation, so R has O(XB/u^2) possible key-levels. H has O(XB log u/u) by the near-top reciprocal sum. A has O(XB log u) by the all-prime reciprocal sum. Explicitly,
    S_R=O(XB/u^2), S_H=O(XB log u/u), S_A=O(XB log u).  (3)
The bound includes resets and arbitrarily short waits; roughness is an extra assumption only in R. It counts distinct crossing post-keys with label and level, not all incoming physical edges, not original root pairs, and not newly formed reference pairs. For a pair assigned to either partition the physical crossing key is global, so aggregate both partitions at the same key; no double-count issue. For a fixed key-level, GAP and AFTER-BOTH residual weights can likewise be combined.

## 5. Absolute adaptive first-hit quotas, residual and significance

After source-level/core peeling, let A_K be the ACTUAL remaining weighted charge at a key-level K, combining GAP and AFTER-BOTH. Pay min(A_K,c_type) using any deterministic fractional allocation on edges at that key, e.g. uniform proportional reduction. Choose
    c_R=u^(19/4), c_H=u^(15/4), c_A=u^(11/4).
By (3), total paid is at most
    c_R S_R+c_H S_H+c_A S_A
      =O(XB u^(11/4)(1+log u))=o(XB u^3).           (4)
This pays real energy, not merely candidate count. All actual charges at a key below its cap are paid, and at a larger key the cap is a partial payment. The estimate improves the plain all-label key cap by one logarithmic power for the near-top labels and two for rough predecessors. It applies regardless of how long the first-hit time is delayed, how large n_edge becomes after new merges, or how many total downcrosses occur at that level in the long reference. Only original terminal level charges enter it. Unlike 63fb14c equation (2), no factor proportional to W occurs in (4).

Under the no-large-twins hypothesis the twin term is zero. With disjoint priorities and optional second core pass, the old terminal term satisfies the new reduction
    T_old <= G_gap,res + G_after-both,res + G_survivor,core
             + O(XB u^(11/4)(1+log u)).
G_gap,res and G_after-both,res denote remaining portions of actual newly matched old terminal charge after source and arithmetic payments, not full selected-gain energy. G_survivor,core is actual surviving high weighted-degree original charge. It can still be transported to longer future occupation by 63fb14c (4). The three residuals are not known to be o(XB u^3). The new matched reduction is independent of bounding the full extended net-descent envelope, but does not close the matched part. It is useful because the heavy residual is expressed using actual simultaneously charged source-level partners, not an assumed uniform bound on ancestor mass. For AFTER-BOTH the vertex-disjoint first-hit key constraint and the O(XB/m) key-level core count may permit a stronger source-support bound; for GAP only outgoing uniqueness is available.

Possible next improvement: use the local source order and endpoint differences in GAP to restrict which later tags can supply many charged partners at the same first hit. For AFTER-BOTH and SURVIVOR, use the level-specific heavy graph to count actual sources surviving above lambda, exploiting backward tick reachability or aggregate source separation. Do not assume a large reference endpoint group implies many charged edges, or use a future pair created after the original stop to increase the original graph. Original immediate/later intra-wait and recorded matching, low-r thick anchors, distinct-slot energy and MED transfer remain unresolved.

## 6. Reproducible finite diagnostics

Standalone research/min_clock_terminal_level_core_audit.mjs, source commit 925ac5c11fd84414d5ecc012b482949087732da0, exact readback blob 27338bfb384dde20a64f6fe149ee2c842fd8a994. Reuses corrected literal MIN original histories, masks, pair expansion and independent arithmetic future stepping from 63fb14c local control. The new compressed interval allocation splits each old charge at successive future record-low deficits, then sweeps integer levels. Checks each actual crossing is a net descent with correct phase and (2), one positive edge per unordered pair and level, unique earlier GAP key and both AFTER-BOTH endpoint keys, exact source/core payments and nonnegative weighted degree on retained vertices, independent relaxed arithmetic support count by enumerating eligible C,p and allowed phase d' (including resets), key quota bounds and all aggregate charge identities. Earlier first attempted run failed because an audit counter was const; corrected before the final runs, no invalid code committed in this turn. All final assertions pass. Floating point weighted sums use tolerances.

Run from repo root:
    node research/min_clock_terminal_level_core_audit.mjs 4096 16384
Actual function executed in available JS runtime (not separate Node invocation). X4096,16384; local W=floor(B/8),B; stress threshold m=2,8; both original occupations=16 occupation combinations. Original delayed masks remain stress from earlier code (D=floor(B/4), L30, y5, q comparison4, original thin cap12, delay r/8); the NEW graph threshold is independently varied, not the original thin cap. Arithmetic diagnostic caps [4,3,2] for [R,H,A] and finite Y=max(5,ceil B^.125), Ptop=ceil(B/u²); these are not asymptotic numerical estimates. Common-cell extension still reaches twins for all original tags in these finite windows, so the graphs used for nonvacuous survivor diagnostics are the pair-local ones. The code can also run its analytic branch by calling audit with stress=false; no analytic runs claimed in this checkpoint.

Largest X16384, B339, W42, old late HIGH terminal692872.40, full-positive3865898.97. Actual newly matched charge split GAP52.4483/69.9310 and AFTER-BOTH1.9138/4.0345. All six realized crossing key-levels were H in this finite classification. Relaxed arithmetic key-level envelopes R25978996,H42971204,A8992466, far larger than realized support. At new graph threshold2, GAP remained in both occupations; AFTER-BOTH was entirely paid. Arithmetic H cap paid18 in each occupation; residual GAP34.4483/51.9310. At threshold8 the GAP also paid in full, so no additional arithmetic payment. This is nonvacuous evidence for the directed-versus-both distinction and the cap accounting, not for the asymptotic bound's tightness.

Surviving local graph:
| original occupation | local W | weighted threshold | raw survivor | peeled | residual core |
|---|---:|---:|---:|---:|---:|
| late HIGH |42|2|471678.47|4577.02|467101.46|
| late HIGH |42|8|471678.47|104375.86|367302.61|
| full positive |42|2|952926.92|0.59|952926.33|
| full positive |42|8|952926.92|80270.99|872655.92|
| late HIGH |339|2|74960.75|1163.89|73796.85|
| late HIGH |339|8|74960.75|67360.75|7600.00|
| full positive |339|2|151624.77|0|151624.77|
| full positive |339|8|151624.77|54990.00|96634.76|

Largest full-positive compressed input119452 intervals, 11026812 pair-level incidences across1390 nonempty levels. At X4096,W21 survivor charges98556.46/189454.43, W170 none; no matched charges in those cases. These graphs are of original pair energy, not all ancestors of the future state. The largest graph retains substantial core energy even at diagnostic threshold8. No evidence of asymptotic o-bound for heavy residuals. Main and other branches unchanged, no Lean compilation.
