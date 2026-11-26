# Hypothetical infinite MIN worlds VI: repeated shallow-entry capacity and signed recovery cost

2026-11-26 JST. Independent continuation of [6ba4e70](https://github.com/tara-sooo/A166944-Lean/commit/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052). Sources: [III clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), [IV low relays](https://github.com/tara-sooo/A166944-Lean/blob/73a01303cbc6c0bc73fa053a1e4e3a6e3525f21a/research/infinite-orbit/low_relay.md), [V frozen entry](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md). Sibling preflight direct [3214564 multiband weighted deficit sieve](https://github.com/tara-sooo/A166944-Lean/blob/3214564a96ec7bab6234d37f253dcb0636b7c229/research/2026-11-26-min-direct-multiband-weighted-deficit-sieve.md), unified [6dda1b5 all-scale shell sieve](https://github.com/tara-sooo/A166944-Lean/blob/6dda1b5a3ff98944b47f42eafee1ce90e63e05f3/research/2026-11-26-min-unified-all-scale-deficit-shell.md). These are new paper deductions and finite arithmetic diagnostics, not a Lean proof or external novelty claim.

## 1. Classification and exact low supply

Work on any actual contiguous adaptive MIN event block of pre-horizons in [X,lambda X], with nonnegative ordinary deficit d=2t-H throughout (in particular on canonical rays). Let B=floor sqrt(lambda X+1); selected primes p<=B. Put g=p-1, d'-d=2w-g. Fix a low bound R with H+1>=R², and let M_R be the exact maximum low-only gain from IV's finite transducer. Thus every contiguous low-only run has gain <=M_R<K_R, where K_R=2 prod_(3<=q<=R prime) q. Let r_R be the least odd prime >R. Choose T>R, T>=11, and a fixed positive drift rate delta>0. Classify ALL physical events, not only selected ones:
- low: p<=R;
- good: p>=T and d'-d>=delta g;
- medium: R<p<T;
- bad high: p>=T and d'-d<delta g.
The last two classes together are called interruptions. Let F,U_m,U_h,L be the respective good, medium, bad-high and low gains. Define
    alpha = delta - M_R/(T-1) > 0.
The main application is the previous long condition w>=p-2. Such good events satisfy d'-d>=g-2>=(1-2/(T-1))g. For that application use the long condition ITSELF to classify good, use delta=1-2/(T-1) as a uniform lower bound on their drift, and classify all other p>=T as bad high. The arguments require only the lower drift on good; a bad-high event need not actually have negative drift. For this long version alpha=1-(M_R+2)/(T-1). For fixed R it tends to 1. More generally R may grow provided the displayed hypotheses hold.

At a good event define the adjusted positive multiplier h=(d'-6s)/(2p), s=t' mod2, by the exact event congruence. For the long version p>=11, d'>=p-3>6 so h>=1. In the general delta version the same is true eventually for delta(T-1)>6. We will use absolute post-deficit caps directly, without needing positivity for small labels.

## 2. Uniform capacity of shallow portions of mixed runs

A mixed run consists of good events separated only by low events. Its span begins at the first good and ends at the last good. It is maximal inside the chosen block unless specified otherwise. In any prefix ending at its j-th good event, let F_j be total good gain and L_j intervening low gain. Then
    L_j <= M_R(j-1), j <= F_j/(T-1),
    d'_j - d_start >= delta F_j - L_j >= alpha F_j.      (1)
Here the lower bound -g on each low deficit increment is exact; no independence or finite-twin assumption is used. In fact successive good post-deficits increase strictly:
    d'_(i+1) - d'_i >= delta g_(i+1)-M_R > 0.           (2)
For long good events the sharper pointwise form is >=p_(i+1)-3-M_R.

For ANY absolute cap D>=0, take the LAST good event with d'<=D in this run, if there is one. All good gain up to and including it is <=(D-d_start)/alpha<=D/alpha. Every good event satisfying the cap is in that prefix, even if events with large multiplier were interspersed. Thus the total capped good gain per mixed run is <=D/alpha, and the count is <=D/(alpha(T-1)). Low gain between these good events is <=M_R times their count. In particular if every good event in a run satisfies h<=k, then D=2kB+6 and its FULL span is bounded by
    L_R,k <= (2kB+6)/alpha * (1+M_R/(T-1)).             (3)
For fixed R,k and T=Theta(sqrt X), this is O(sqrt X), uniformly in actual time phase, start deficit and all intervening low labels. This proves the earlier desired run-length estimate in the bounded-multiplier subclass, not for uncapped arbitrary mixed runs. For k growing slowly the explicit dependence is linear in k. Neither a prime cofactor nor safe endpoint condition is needed, so imposing them only reduces the class.

More strongly, a run with unbounded multipliers may still be counted once: its total gain in h<=k events is <=(2kB+6)/alpha, not multiplied by the number of deep events. If a run has m good events, at its j-th such event
    h_j >= (alpha j(T-1)-6)/(2B)
whenever adjusted coordinates are defined (d_start>=0). At square-root scale the multiplier grows at least linearly in j up to constants in T/B. Thus an uninterrupted macro gain of order X forces multiplier of order sqrt X late in the run. This is a dynamical, not sieve, constraint.

## 3. Exact upward price of an apparent shallow return

The absolute deficit in (2) is increasing, but a relative multiplier h=d_adjusted/(2p) may decrease when p rises. For two successive good events in the same mixed run with first multiplier h_1 and second h_2<=k, use (2):
    (2k-delta) p_2 >= 2 h_1 p_1 - M_R - delta - 6.     (4)
This follows by substituting d'_i=2h_i p_i+6s_i and taking the worst side difference. In the long version the exact pointwise gain p_2-3 gives
    (2k-1) p_2 >= 2 h_1 p_1 - M_R - 9.                (5)
If h_1>=k+1 and k fixed, M_R=o(T), p_i>=T->infinity, then
    p_2/p_1 >= 2(k+1)/(2k-1) - o(1).
For k=1 this is 4-o(1), for k=2 it is 2-o(1), for k=4 it is 10/7-o(1). In a band [T,2T) with fixed R, k=1 such a deep-to-unit transition is impossible inside a mixed run for large T. At k=2 the limiting ratio is 2; without a fixed gap below 2 the small error prevents asserting impossibility on the whole half-open band. For k>=2, a sufficiently narrow fixed-ratio band also forbids the corresponding transition. If a unit event follows a deep one by several good events, take the last adjacent deep-to-unit transition. Thus bounded low relays cannot repeatedly restore a unit multiplier in a fixed narrow band. There must instead be an interruption or an upward change. This connects to the unified upward escape without counting a deep predecessor as a new interruption. (5) is for w>=p-2, not all of unified's positive 4w-g events, which may have negative ordinary drift.

## 4. Signed recovery budget across arbitrary interruptions

The main improvement over a run-count bound is to charge actual gain and negative variation, with ONLY ONE terminal cap per physical block. Suppose at least one good event has d'<=D. Stop the block immediately after the LAST such event, and restrict all quantities in this section to this prefix. Write d_a,d_b for actual endpoint deficits. Sum the signed increments over good events and let P^-_m,P^-_h,P^-_low be actual total negative variations of the other classes. Then
    P^-_m+P^-_h+P^-_low >= delta F - d_b + d_a.       (6)
No good event is negative and any positive increments of other classes only strengthen this. Each negative increment has magnitude <=g. Every low run in this entire prefix is bounded by M_R. If n_g,n_m,n_h are counts of nonlow events,
    L <= M_R(1+n_g+n_m+n_h)
      <= M_R[1+F/(T-1)+U_m/(r_R-1)+U_h/(T-1)].
Therefore retaining the actual bad negative variation gives
    P^-_m+P^-_h >= alpha F - d_b + d_a
          - M_R[1+U_m/(r_R-1)+U_h/(T-1)].             (7)
Using P^-_m<=U_m and P^-_h<=U_h:
    alpha F <= d_b-d_a + M_R
        +(1+M_R/(r_R-1)) U_m
        +(1+M_R/(T-1)) U_h.                          (8)
All gain from capped good events of the FULL block occurs in this prefix, so with F_cap their full gain and U_m,U_h now enlarged to the full block, d_a>=0, we get
    alpha F_cap <= D+M_R
        +(1+M_R/(r_R-1)) U_m
        +(1+M_R/(T-1)) U_h.                          (9)
If no capped good event, (9) is trivially true; (6)-(8) apply only when the prefix exists. Importantly F in (8) includes ALL good gain before the last cap, not just the capped population. A deep good event does not provide negative recovery. There is no repeated initial-deficit term, no bound assumed on number of runs, and no assumption that all interruptions reduce deficit.

At fixed R, T=Theta(sqrt X), D=2kB+6=o(X) for k=o(sqrt X), and alpha->1 in the long version. If capped good gain is Omega(X), (9) forces U_m+U_h=Omega(X), not merely Omega(sqrt X) interruption count as in IV's conditional run-length bound. For example R=3 has M_R=4,r_R=5, so for this long version
    (1-6/(T-1)) F_cap <= D+4+2 U_m+(1+4/(T-1)) U_h.
At fixed R, if U_m+U_h=o(X), not only does F_cap=o(X) for every D=o(X), but (8) applied through ANY good event gives
    d' >= d_a+alpha F_prefix-M_R
              -(1+M_R/(r_R-1))U_m
              -(1+M_R/(T-1))U_h.
Thus once cumulative good gain exceeds rho X for any fixed rho>0, all subsequent good events have d'=Omega(X) and h=Omega(sqrt X). More quantitatively the prefix ending at the last capped event contains only o(X) total good gain. This excludes a macro shallow/recurrent-reset good supply with submacro interruptions, even if arbitrarily many deep good events are allowed. It does not exclude an all-deep, strongly positive-drift survivor or a macro medium/bad-high supply. For growing R the coefficients must be retained; a macro lower bound on U_m+U_h with constants independent of R does not follow.

## 5. Tagged transfer with actual endpoint boundaries

For arbitrary nonnegative weights on actual contiguous blocks, (9) can be summed directly. If the blocks are the full lifetimes of N original distinct source tags with common cap D, the bound is
    alpha F_cap,tag <= N(D+M_R)
        + c_m U_m,tag + c_h U_h,tag
where c_m=1+M_R/(r_R-1), c_h=1+M_R/(T-1). Select the last capped prefix ONCE for each original tag, keeping the entire actual path up to it. Then the more precise (8) also sums with the actual signed endpoint terms. Shared physical events are counted once for EACH tag that traverses them, exactly as in unified. No assumption of independent trajectories, disjoint physical supports or bounded source multiplicity is required. This is an original-lifetime resource inequality; it cannot be read as a core-only or missing-measure bound.

For the short-lifetime scaling of unified, where the physical lifetime gain scale is X/(log X)^a with fixed a>0, T=Theta(sqrt X), B=O(sqrt X), fixed R and k polylogarithmic, N(D+M_R)=o(N X/(log X)^a). Consequently a macro tagged capped good gain requires macro tagged medium or bad-high gain on the full lifetimes. The proof does not imply that such capped gain is forced by unified's high excess branch: its threshold 4w>=g is weaker than positive ordinary drift. The arbitrary common-core weighted version has boundary penalty (D+M_R) sum_Q b_Q, not N(D+M_R), unless one uses full lifetimes. A core-level conclusion requires this actual penalty to be small relative to total core gain, or additional information on shared endpoints. The new relation complements the all-scale shell sieve, whose small weighted relay and variation hypotheses are different; neither estimate forces the other's hypotheses.

## 6. Reproducible finite diagnostics

Final source [1fc2f70](https://github.com/tara-sooo/A166944-Lean/blob/1fc2f7006036c3e653e59baf927e28a0d1fdeede/research/infinite-orbit/recovery_budget_audit.mjs), blob4c5fbf755f7efa3d7357f7fcfaa854a568b03777. Run node research/infinite-orbit/recovery_budget_audit.mjs. Exact ECMAScript executed in the available runtime, not separate Node; final assertions all pass. The first draft incorrectly required nonnegative adjusted h on every small event. For arbitrary intermediate states even a p=3 odd-side event can have d'=0, adjusted h=-1; the final audit explicitly allows exactly this case (2556 incidences). No formula for large good events requires nonnegative h at small events.

Windows X=4096,16384,65536, pre-horizon X<=H<16X, T=ceil(sqrt X/2), B=floor sqrt(16X+1), use all p>=T (not the narrower prior band). R=3,5,7 with exact M_R=4,14,34; k=1,2,4. Skip R7 at X4096 since alpha<=0. 24 configurations in total. Canonical source scans and sampled arbitrary intermediate states; add exact prescribed post-arrival strata h=1,2,4,8 at actual long first clock w=p-2. These targeted states satisfy the canonical envelope but not established ancestry. Start incidences 20,480 canonical, 13,440 generic intermediate, 27,366 targeted; 61,286 total, 61,216 finite stops and 70 upper exits, zero event cap unresolved. Repeated starts/configurations are allowed, not claimed unique source count. 1,402,869 actual MIN event incidences. Check (1)-(2), (5)-(9) and nonnegative deficit, exact multiplier congruence, low relay gain, and independently retain signed deficit at the true last capped endpoint.
- 517617 good-prefix growth checks; 198797 capped good incidences, 495516 mixed-run capacity controls.
- 22101 successive-good strict post-deficit increase checks; 512 adjacent deep-to-shallow checks of (5).
- 37720 consecutive capped-event recovery intervals, 8809 with positive deficit recovery demand; 4078 shallow-after-deep incidences over the full path (may contain interruptions), 515 within a mixed run. Counts overlap across thresholds and sources.
- 161077 last-capped prefix resource checks including exact endpoint version (8) and separated medium/high cost; 1098 have positive exact endpoint cost alpha F > d_b-d_a+M_R. The weaker coarse D-only positive-demand test had ZERO instances alpha F>D+M_R (the audit's stricter diagnostic F>D also has zero instances). Thus finite data exercise the stronger exact ledger, but do not exhibit the asymptotic macro regime of (9). 24 weighted aggregate checks with deterministic positive integer weights, not a computation of actual unified common-core assignments.
Representative actual deep-to-shallow transition in one mixed run: pre-H=24888, p=41, h=4, post d=328; next good pre-H=24930, p=107, h=2, post d=434. The multiplier halves but ordinary deficit rises by 106. This is an example of upward transition, not negative recovery.

For R=3 the observed maxima of good gain in a run (all multiplier values) and capped subset gain are:
| X | max good gain | k=1 capped gain | k=2 | k=4 |
|---:|---:|---:|---:|---:|
|4096|418|240|404|404|
|16384|982|588|832|982|
|65536|1664|1220|1562|1636|
These are observed on the sampled/targeted trajectories, NOT exhaustive maxima or an asymptotic estimate. The uniform capped-run bound (3) is analytic and independent of these values. The finite tests contain actual twin stops, so no inference of finite twins from the sample.

## 7. Next obstruction

We have closed the uniform run-bound question only for bounded multiplier (or capped absolute deficit) mixed runs, and obtained a stronger unconditional signed recovery cost for arbitrary interruptions. A hypothetical infinite ray with macroscopic long high supply must pay at least one of macroscopic medium/bad-high gain or escape to large ordinary deficit and high multipliers; the latter is compatible with the earlier coarse scalar survivor. For unified, the gap between positive 4w-g and positive 2w-g remains important. Next: investigate the actual high-deficit, variable-multiplier regime, including negative-drift high clocks and whether their recovery supply can be repeated; couple exact phase constraints to high multiplier arithmetic and the newest multiband sieve. No all-constraint infinite model, Lean verification or finite-twin contradiction. 
