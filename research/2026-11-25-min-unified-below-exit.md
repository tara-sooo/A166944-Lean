# Below-level provenance: wide-prefix recent-exit absolute payment

2026-11-25 JST. Companion to [unified wide-boundary / first-record Hall tail](https://github.com/tara-sooo/A166944-Lean/blob/9a60c91099af12eb6f46037d52c4f41a01ccf58b/research/2026-11-25-min-unified-record-hall-tail.md). During this investigation the stable-heavy branch advanced from 80e7125e523d to [a0093d61d846](https://github.com/tara-sooo/A166944-Lean/commit/a0093d61d84632e88d9f06c069626956464c5729) (23:16:26 JST), adding [below-excursion audit source](https://github.com/tara-sooo/A166944-Lean/blob/a0093d61d84632e88d9f06c069626956464c5729/research/min_clock_record_below_excursion_audit.mjs), lines 72-156. Its actual short-prefix classification is adapted below, not its sampled results or short-prefix budgets. New paper result: an absolute small-o payment of all sufficiently deep-band global-first-record pieces having an endpoint's last below-level exit within an adaptive gain distance BEFORE or AT the pair's common recorded birth. In particular the same-exit class is paid in this deep sector. This is a genuine unconditional pair-mass bound, not a transport to another unbounded moment. No Lean compilation, no cumulative MIN audit of this new bound, no general linear-tail estimate.

## 1. Set-up and exact prior-exit partition

Use precisely the long prime-root ensemble and notation of the unified note: H=T+B, u=log B, W=ceil(Bu^2), F=T^2Bu, N=Theta(X/u), L=B u^(3/2). Paths and their actual completed events are unchanged. The new first-record split uses independent uniform lambda in (D/2,D) for each dyadic deficit band d_target in [2D,4D). For one pair all parts of a given band together have level density <=6H/D, even after arbitrary earlier disjoint masks and after summing all grid and old residence coordinates.

Consider only GLOBAL first-record nonbirth parts. The common recorded birth state v_* has d_*<lambda and the first common recorded upcrossing has pre-deficit <lambda and post-deficit >=lambda. For either source, if there was a recorded state >=lambda on its earlier own path, it has a unique last recorded downward exit e^- before the global first common upcross: the edge with d_pre>=lambda>d_post after the last earlier recorded state >=lambda. If there was no such state, the source is virgin at that level. We use only lambda>6 so all original initial deficits are below lambda. The actual shared recorded suffix is strictly below lambda from birth until the first common recorded upcross. Hence any such exit occurs no later than the common recorded birth; there cannot be a downward exit in the intervening strictly-below common suffix. This is true for recorded states, not for transient waiting ticks.

Classify a nonbirth part by the two exits: both virgin; one recycled; both recycled with different exit post states; or both recycled with the SAME exit post state. In the last case the common post state must equal v_* (otherwise the pair already had a common recorded state earlier), and the two exit predecessors are different recorded states. This is exactly the provenance geometry inspected in the new stable-heavy audit, now stated for the long ensemble.

## 2. New adaptive near-birth absolute bound

Restrict to bands D>=H/u^2; asymptotically these have D/2>6, D>>B. Define V_D = D W/H. A nonbirth part is RECENT-EXIT if at least one endpoint's last downward exit e^- has post-horizon J^- satisfying
    0 <= C_* - J^- <= V_D,
where C_* is the common recorded birth horizon. This is a gain distance BEFORE the common birth, not the shared age of the final hit, so it is a distinct test from the fixed short-shared-age payment. It includes downward exits arriving at birth.

Since each completed edge's net deficit decrease is at most its gain, which is <=B, the exit post-deficit satisfies
    d_post(e^-) >= lambda - B.
Along the endpoint's actual path from J^- to C_*, total negative variation is at most the total gain C_*-J^- (because each edge's negative part is <= its gain). Therefore
    lambda > d_* >= lambda - B - V_D,
or
    d_* < lambda <= d_* + B + V_D.                 (1)
This does not assume that the other source had any prior exit, or that the pair shares the earlier exit edge.

For D>=H/u^2, B<=V_D and B+V_D<=2D W/H. Since W/H=o(1), eventually this is <=D/4. Combining (1) with D/2<lambda<D gives D/4<=d_*<D. For fixed pair d_* is fixed. Hence qualifying dyadic bands D lie in (d_*,4d_*], at most three (indeed at most two away from endpoints). For each such band, its total qualifying pair mass, even after combining both endpoints' RECENT-EXIT tests by union, is at most
    (6H/D) (B+V_D) <=12W.
The interval (1) is common to both endpoint tests, so no doubling is needed. Summed across all bands a pair pays at most 36W, and across all original pairs
    E_recent-exit,deep <=36 choose(N,2) W
                      = O(F/sqrt u)=o(F).          (2)
All grid choices, original layer origins, visits, and distinct hit locations are already accounted for in the per-pair level density. No arithmetic independence or estimate of cohort multiplicity is used. This is an upper bound on actual weighted PARTS, not a deletion of whole pairs, high incidences, or physical paths. If incorporated after other pair payments, pay only the remaining qualifying parts.

The SAME-exit class in the deep bands is a subset of (2), since its common exit post state is birth. The one-recycled and distinct-exit cases are also covered whenever at least one exit is sufficiently close before birth. This result does NOT pay same-exit in shallower bands; it does not pay all recycled histories or all high birth-stock parts. For the remaining deep nonbirth pieces, every recycled endpoint has an actual last exit strictly farther than V_D in gain before pair birth. V_D ranges from about B at the lowest included band to order W at deficit scale H. The pair must share a subsequent below-level recorded history up to its common first record as before. The virgin cases are retained.

## 3. Additional integrated downcross keys for remaining recycled pieces

For each original source M, actual completed negative-drift edge e, and band j set
    A^-_j(e) = length((D_j/2,D_j) intersect (d_post(e),d_pre(e))).
Attach a separate eligible key (down,M,e,j) of capacity 3L A^-_j(e) to each remaining nonbirth piece whenever that endpoint's actual last exit is e. There may be one or two such keys. Only use actual last exits; no assumption that the other endpoint visited e. For a fixed pair and level, its global first-record edge and each endpoint's last preceding exit are unique. Its density over all targets and coordinates in the band is <=6H/D_j. Thus its total weight eligible at this downcross key is <=6H A^-_j(e)/D_j, without a return-count factor.

The strips are disjoint, and total negative variation on a source is <=H, so the total new capacity <=3NHL=o(F). In the same minimum-cardinality maximizing Hall obstruction as all previous key families, an included downcross key with positive A^- requires distinct actual internal partners > L D_j/(2H). Both endpoint exit keys, when present, must be included simultaneously. All previous narrow/wide crossing and first-record constraints continue to hold. No claim that the new keys suffice by themselves to bound the residual.

Use the exact joint demand ledger after adding the recent-exit absolute payment (2), i.e. increase Q_X in the unified note's linear tail certificate by at most (2) and count these added capacities once in C_tot. The finite bound and its constant-threshold asymptotic sufficient condition remain unchanged at their respective error scales. For work on the deep recycled sector, the remaining last exit is before common birth by > V_D, and the endpoint below-level interval lasts at least this gain distance before birth. This is a new actual history constraint, not an assumption about stationary tick excursions. For the remaining virgin sector both relevant roots can be tested for first individual attainment (or one virgin when mixed), but no general upper bound follows here.

## 4. Status

Pinned stable-heavy input was 80e7125e at the beginning of the integration; the later a0093d61 audit source was fetched and inspected before deriving this extension. The original branch's short all-odd ensemble, samples and numerical statements have not been run or merged here. The adaptive deep recent-exit estimate is elementary on the long prime-root ensemble; no external novelty or completion of the twin-prime proof is claimed. Next estimate the linear clock of the large effective Hall partner-count tail using the remaining deep recycled long prebirth intervals and virgin cases, along with shallow/low-deficit and asynchronous sectors. The actual MED/other clock condition also remains to be established or combined with the constant threshold. Both input branches and main are untouched.
