# Canonical-gap normalized gain-target certificate with bounded tick load

2026-11-26 JST. A change of sufficient-condition design, following [d14a0685402](https://github.com/tara-sooo/A166944-Lean/blob/d14a0685402be89ca0f9873aa21a9c63af31e9f0/research/2026-11-26-min-unified-word-phase-halos.md). Integrates the stable-heavy [canonical renewal identity](https://github.com/tara-sooo/A166944-Lean/blob/e1ad9e2b434c652699e1bc9a0797887631e0ea6d/research/2026-11-25-min-clock-canonical-renewal.md), the prime-root [primorial boundary method](https://github.com/tara-sooo/A166944-Lean/blob/1ccfb6af1957dcada4ee3286d01206288664e135/research/2026-11-25-min-prime-root-boundary-hall.md), and all previous unified LINEAR original-clock masks. Both independent heads checked unchanged (1a4005f2f336 and e1ad9e2b434c). The new normalized objective ignores completed canonical prefixes for each target, and focuses on the last half of sufficiently long canonical gain gaps. A deterministic primorial exposure lower bound under the no-twin hypothesis permits transfer of old absolute little-o payments, even when the new target count is o(NT). Also a relative-cost terminal-strip deletion, applicable regardless of mass. This is an alternative sufficient condition, not a proof of its required inequality or of twin-prime infinitude. No Lean compilation.

## 1. Original paths and an exact single-target neutral cancellation

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime roots M in [X,2X), T=floor(X/u^.25), H=T+B. All ORIGINAL gain-stopped MIN prefixes, first completed gain crossing T or original cutoff/twin stop, are unchanged. Each actual completed event gains g=p-1<=B, waits 1<=w<=2r<=3g. Original deficit d=2t-C>=0, starts at 6. Total gain <H and elapsed <=3H. Under no twins in the original large horizon domain, all tags reach gain T for sufficiently large X, by the original clock-cutoff argument (3T+2B is smaller than the original remaining cutoff interval). If there are only finitely many twins, all sufficiently large dyadic X satisfy this hypothesis.

For each original tag write its relative gain as C-C_origin. A canonical point is an actual physical state with C=0 mod4, t=C/2+3, including virtual points inside completed waits and actual canonical terminal snapshots. The root is canonical. At most one canonical point per horizon; successive canonical gains are strictly increasing. For two actual canonical points the elapsed time between them is EXACTLY half their horizon difference, including virtual endpoints. No point is extrapolated after original stop.

For each INTEGER target x in [1,T], use the original prefix through the first completed event whose postgain is >=x, or the whole original completed path if x is not reached. Let its end gain and time be G_x,t_x. Let c_x be the last actual canonical point of relative gain STRICTLY below x, with gain g_c and time t_c. It exists (the root), and is contained in the target prefix: if the target is reached then every later state has gain >=x, and if not reached the target prefix is the whole original path. Strict inequality matters, including canonical points at a terminal or virtual points inside waits. Put
    R_x=x-g_c>0,      W_x=t_x-t_c>=0.
Then the original target-prefix elapsed clock is exactly g_c/2+W_x. On a reached target,
    2 W_x = G_x-g_c+d_x-6 >= R_x-6.                       (1)
No requirement of large deficit, and no aggregate bound on RESET clock.

For fixed x=T, let R_tot=sum_M R_T and W_tail=sum_M W_T. Exact identity
    W_all = (NT-R_tot)/2 + W_tail.                        (2)
So a sufficient condition is 2 W_tail+6N<R_tot along infinitely many dyadic X. An asymptotic ratio version is liminf W_tail/R_tot<1/2 and N/R_tot->0 on the same witnessing sequence. This is the same actual-clock inequality after exact neutral cancellation, with an adaptive margin; do not claim an independent bound on W_tail merely by renaming it. It can use a smaller-than-NT budget, so a constant-fraction NT improvement is no longer demanded. Old o(NT) payments need not be o(R_tot) if R_tot is small; the next construction resolves that scaling issue for a many-target objective.

## 2. Canonical gain partition and selected latter-half targets

For each original tag, list all actual canonical gains strictly below T, starting with 0. Append T as the artificial partition endpoint even if T is an actual canonical gain. Consecutive partition endpoints g_i,g_{i+1} define a gap of positive integer length L_i=g_{i+1}-g_i. The trailing gap may include unreached gains when the original path stops early; do not delete those targets or pretend the trailing endpoint is canonical. All gaps partition the full integer target set (0,T]. For x in (g_i,g_{i+1}], c_x is exactly the actual canonical point at g_i. This includes x at the next actual canonical gain because we used strictly below x.

Choose an integer a>=13, possibly slowly growing with X. In each gap of length L>=a, select its latter half of integer targets:
    g_i+floor(L/2)<x<=g_{i+1}.
The number selected in that gap is ceil(L/2); each R_x=x-g_i>L/2>=a/2. Exclude all targets in shorter gaps. Let I_a be the selected (original tag,target) set and
    J_a=|I_a|,
    B_a=sum_(I_a) (1/2-3/R_x),
    V_a=sum_(I_a) W_x/R_x.
Here B_a denotes the normalized lower-bound budget, unrelated to the prime cutoff B. Thus (1) implies, if all targets are reached,
    V_a >= B_a >= (1/2-6/a) J_a.                         (3)
In particular B_a is positive if J_a>0 and a>12. Targets are selected using actual canonical gaps plus the artificial endpoint, not conditioned on actually reaching x. Otherwise the criterion could be impossible even on a path that stops at a twin.

## 3. Transpose to one bounded load per actual tick

For each original completed event, let its pre-gain be g and occupied integer ticks j in [t,v). For a specific such tick j let h be the gain of the next actual canonical point STRICTLY AFTER j in physical time, or +infinity if there is none on the original completed path including terminal snapshot. Define the tick load
    omega_M(j)=sum_(x: (M,x) in I_a, g<x<=h) 1/R_x.       (4)
The two inequalities are exact: the completed event belongs to the target prefix iff x>g (even if x is unreached), and the tick is at/after the target's last canonical point iff there is no later canonical point with gain <x. Any canonical point at the current tick is included as the tail start, whereas a future virtual point at the same horizon makes h=g and the tick contributes zero. If the next canonical point is at x exactly, it does not cancel that tick because c_x is strictly below x.

All nonzero terms of (4) are in ONE canonical gain gap. Indeed if the latest actual canonical at/before j has gain b<=g, then no canonical lies strictly between b and h; if h is above T or nonexistent use the artificial endpoint T. If g>=T the sum is empty. Thus the load is bounded by the full selected latter-half harmonic sum of one gap,
    0<=omega_M(j)<=sum_(floor(L/2)<r<=L) 1/r <=1.         (5)
The last inequality follows by counting ceil(L/2) terms each <=1/(floor(L/2)+1). No probabilistic or stationarity assumption. In particular an arbitrarily long actual RESET cluster does not acquire a factor equal to the number of gain targets. Finite Fubini now gives the exact original-clock transpose
    V_a=sum_(original completed tag ticks) omega_M(j).   (6)
The original tick states, not projected visits or artificial selected labels, are used.

Let D_paid be ANY union of previous linear actual-clock masks, including partial ticks, with cost W_paid<=beta_X NT, beta_X->0. Pair-energy payments are not linear masks. Use the original target gaps and loads, do not recompute them after deleting events. Then V_paid<=W_paid by (5), and V_rem=V_a-V_paid is the sum of loads on the remaining actual ticks. It can be split into HIGH and other labels exactly as in the original ledger. This is a loss-free transfer at the NT scale, unlike weighting all targets by 1/R_x without restricting the half-gap: the latter harmonic sum can grow with T.

## 4. Unconditional lower exposure under the no-twin hypothesis

Let P=P(a) be the even primorial product of primes <=a+1. It may be fixed or grow slowly, with P+B=o(T). An actual strict crossing of a multiple K of P, i.e. C<=K<C+p-1, must use a selected p not dividing P. Proof: if p|P, then p|C+sigma implies K-C=+/-1 mod p; since K-C is even and nonnegative, the smallest possible such even difference is >=p-1, contradicting strict crossing. The case K=C is impossible by p|C+sigma. Consequently p>a+1 and each crossing jump has gain g=p-1>=a.

If an original tag reaches T, count all multiples of P in [C_origin,C_origin+T-B). There are at least (T-B)/P-1. Each is strictly crossed by some completed event whose entire gain interval is inside [0,T] in relative gain units, since each gain <=B. A single such jump of gain g can cross at most g/P+1 <=g(1/P+1/a) multiples, including the case g>P. Sum over distinct crossing jumps, not multiple boundary incidences. Their total disjoint gain is at least
    (T-B-P) a/(P+a).                                    (7)
Each such jump is wholly contained in a single canonical gain gap of length >=a: no actual canonical horizon can occur strictly between its pre and posthorizon (even virtual points are at visited horizons). Canonical points at either endpoint are allowed. Therefore the total length of long gaps on the tag is at least (7). At least half of their targets are selected. Under the no-twin hypothesis, all tags reach T, so
    J_a >= N (T-B-P) a/[2(P+a)].                         (8)
For all sufficiently large X, J_a>=NT a/[4(P+a)]. This uses only deterministic primorial barriers and the original no-twin reachability, not any positive-density assumption on HIGH events or canonical gaps. A useful independent bound is J_a>=1/2 of the total original gain of completed jumps with gain>=a whose entire interval is in [0,T], even on paths not reaching T.

For a fixed a>12, (8) gives a positive constant fraction of NT under no twins; old W_paid=o(NT) is then o(J_a) under that hypothesis. For a growing a=a_X->infinity require
    P(a)+B=o(T),        beta_X (P(a)+a)/a ->0.            (9)
Such a choice exists for any given beta_X->0 by choosing a slowly enough (diagonal choice), also using T/B->infinity. If the combined verified linear budget has beta_X=O(1/ell), use the elementary Chebyshev bound log P(a)<=C a for large a and any sufficiently small positive fixed c with a=floor(c log ell) eventually >12; then P<=ell^(1/2), and (9) holds. This explicit example is conditional on the stated budget rate. Do not assume that every historical quadratic or unverified mask has that rate; one can use a finite set of verified linear masks, or a slower a adapted to their established bound.

Under (9) and no twins, V_paid=o(J_a), B_a=(1/2+o(1))J_a. Hence a NEW sufficient condition for infinitely many twin primes is, along an unbounded dyadic sequence,
    liminf V_rem/J_a < 1/2,                              (10)
where J_a>0 on the witnessing subsequence, or J_a=0 on infinitely many scales (which itself contradicts (8) if twins are finite). For fixed a>12 the sufficient threshold is 1/2-6/a, or the exact budget ratio liminf V_rem/B_a<1. The proof is contradiction with (3),(8),(9). No claim that (10) is already verified. In contrast with the old absolute condition, no constant fraction of NT must be saved on the original total clock; only the normalized tail clock on selected gain targets must have the stated gap. The old sufficient route remains available independently, and their disjunction is a weaker requirement than insisting on the old route. No strict implication comparison between the two conditions on actual MIN paths has been proved.

## 5. Extra relative strip deletion (no absolute NT payment needed)

The load formula also provides a genuinely relative budget even if J_a=o(NT). Fix 0<eta<1/4, possibly tending to zero. For each selected long canonical gain gap [b,h] of length L=h-b, on each original tag mark all completed events with their FULL gain interval contained in its last strip [h-eta L,h]. Ignore uncompleted events and do not rerun any trajectory. Their total disjoint gain is <=eta L, so their original waits total <=3eta L. At every occupied tick of any such event with nonzero load, the next canonical gain (clipped at T) is h and the pre-gain g>=h-eta L. Thus (4), R_x>L/2, and the at most h-g eligible integer targets give
    omega <= 2(h-g)/L <=2 eta.
(If a virtual canonical at the prehorizon is still in the future then the load is zero, which is harmless.) The normalized clock cost of the union within this gap is <=6 eta² L. Since sum of selected gap lengths <=2 J_a,
    V_end-strip <=12 eta² J_a.                            (11)
Likewise an initial-strip mask using fully contained intervals in [b,b+eta L] costs <=6 eta J_a from omega<=1 and gain packing. These are relative linear payments in the normalized objective; their unweighted W need not be o(NT). They are not legal absolute deletions in the old objective without an independent budget. Mark by priority and use original loads.

In particular a high RESET-ending event has a next actual canonical point at horizon within eight gain of its posthorizon, or is the last high RESET on that tag before a truncated bridge (stable-heavy bridge lemma). If this next point exists, and the full event interval is within [0,T], its gain interval lies in a single gap. Let L be the length of that gap clipped at T. Whenever L>=a and p+8<=eta L, the event is contained in the last strip and is paid by (11). This includes a virtual next canonical point at the following horizon. A final crossing event not fully within [0,T] or a last high RESET whose bridge is truncated can be handled separately at <=4NB actual wait, hence <=4NB normalized cost by (5). This is o(J_a) under no twins if (9) is supplemented by B(P+a)/(T a)->0, automatic for the above slow choice and any fixed a. For all eta->0 the residual relative payment is o(J_a). Unlike the earlier absolute canonical-age mask, this controls the terminal high RESET waits by the length of the target gap and counts their reduced weight; it is valid at arbitrary original cohort mass. It does not assert that all high RESET endpoints are in the terminal strip, or that remaining long-gap clock is small. The strip theorem is a paper deduction, not implemented in the numerical audit below.

## 6. What this changes and what it does not

For a selected target, all earlier completed canonical arcs have disappeared exactly from both sides of (1). The normalized sum does not discard a completed arc from EVERY target: it may still contribute to targets in its OWN gap. Short canonical gaps are excluded entirely, except for any zero-weight issues at virtual boundaries already resolved by (4). Large neutral-clock contributions from short returns therefore need not be bounded in (10); long gaps must still satisfy a normalized tail estimate. This is a real change of the sufficient estimate, not a proof that giant cohorts have small total original waiting time. A toy abstract clock ledger can have almost all gain in short neutral canonical arcs, a final unreached gap of length o(T) much larger than a, and W_all/(NT)->1/2 while the selected tail ratio is small. That explains the potential benefit of a non-constant margin; it is not claimed to be an actual MIN realization or to establish strictness under its full arithmetic constraints.

Do NOT try to require the actual total signed deficit drift to be a negative constant times NT: nonnegative deficit implies that this drift is always >=-6N even when twins occur. The fixed targets and unreached trailing gaps in (1)-(10) retain the necessary information about premature termination. No path is extended after a terminal or changed by a mask. All original linear estimates remain reusable by (5),(9), but the final bound (10), including the unmarked HIGH and nonHIGH tails, remains open. No bound on the global canonical basin, no external novelty claim, no Lean verification. Main and independent branches unchanged.

## 7. Reproducible finite audits

Two standalone sources, exact remote readback verified:
- [min_unified_canonical_target_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/f3e6e94ff7f3cc6a37227637785ec57a23cbb0dd/research/min_unified_canonical_target_audit.mjs), commit f3e6e94ff7f3cc6a37227637785ec57a23cbb0dd.
- [min_unified_canonical_exposure_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/c33b97abbe87cefaa7a88ccbf9891e5c4d439ab9/research/min_unified_canonical_exposure_audit.mjs), commit c33b97abbe87cefaa7a88ccbf9891e5c4d439ab9.

Both audit functions executed in available ECMAScript tool runtime, not a separate Node process. Reproduce:
    node research/min_unified_canonical_target_audit.mjs 256 1024 4096 16384 65536
    node research/min_unified_canonical_exposure_audit.mjs 256 1024 4096 16384 65536

Finite T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), HIGH r>3 and 2r>p. Target audit: a=max(4,ceil(B/2)), stress a=max(4,ceil(B/8)); diagnostic mark union w<=.2(p-1) OR high RESET with age>2p. These are diagnostic substitutes, NOT the full historical ledger or analytic choice (9). Check literal gcd on X256/1024 (431/1239), actual virtual canonical points, exact neutral interval identity, full target partition, strict last-canonical and target prefix, every reached target lower bound (1), direct weighted sum and independent tick transpose for all selected targets, exact paid/high/RESET subledgers and load<=1 for all completed ticks. Six successful runs. Most finite original paths terminate before T, so the small raw ratios at larger X are NOT evidence of the no-twin asymptotic estimate. The test does not distinguish each early stop reason and does not test the optional relative strip mask. For finite a<=12 in any other use the positive lower bound (3) must not be inferred; the target audit uses a>=22 except stress a=85.

| X/mode | selected targets | reached selected | V_a/J_a | V_rem/J_a | max tick load |
|---:|---:|---:|---:|---:|---:|
|256|2560|862|.527890|.512493|.689256|
|1024|33780|1612|.123707|.122201|.692172|
|4096|305844|10908|.128862|.125934|.692780|
|16384|2131516|64324|.107015|.104791|.692963|
|65536|15078958|336572|.091301|.089757|.693055|
|65536 stress|15340138|597752|.101244|.099361|.693055|

Largest normal: N5709,140255 completed events,2395330 raw clock,1380549 HIGH,257778 high RESET. 22781 canonical points including6544 virtual,17072 exact neutral arc identities. 6827 long partition gaps, total length30157916; short length807700. All 5709 paths stop before T in this diagnostic. 15078958 selected target checks, of which14742386 unreached; 2395330 direct occupied tick-load checks and exact transpose. V_a=1376729.084627, weighted HIGH853781.768475 and RESET81515.856485; old-example paid raw50211, weighted paid23279.597447 (46.36% of raw), V_rem=1353449.487179. Stress direct15340138 target checks, weighted paid28875.125248. Raw RESET clock is not deleted wholesale.

Exposure audit: 15 runs, three fixed pairs (P,a)=(6,3),(30,5),(210,7) at each X. These thresholds have the required strict-crossing implication; small a is for geometry only, not the positive certificate threshold. Independent literal enumeration of crossed multiples, distinct crossing jump packing, full contained gain intervals inside long canonical gaps, target-count lower bound and reached-path (7),(8). At X256 nine roots reach T; total selected exposures on those roots576,568,568 respectively, versus lower bounds118.5,35.357143,0. At all larger finite X no original tag reaches T; the reached-T inequality there is vacuous, but the actual crossing and containment checks are nonvacuous. At X65536, P=6,30,210: strict crossings512919,102172,14560; total crossing gain2978986,2670576,1891656; all 140255 completed event packing checks per run. Actual gain total3088970. No numerical assertion about growing primorial rates, no cumulative historical masks, no asymptotic conclusion.
