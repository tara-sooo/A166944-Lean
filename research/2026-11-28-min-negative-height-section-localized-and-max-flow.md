# First-height section: localized residuals, maximum-ancestor flow, and an asymptotically negligible top-band defect

2026-11-28 JST, Issue #10. The user adopted the strategy proposed in 6f5a9c7de0967fa3a02210c4e54ded6f8b041c0c: focus on actual first-height section H=floor(R^.4), >>R/L² distinct canonical first-hit states within age O(H), and a trial/true transport certificate rather than more fixed-length polyloglog increments. This checkpoint executes the first pilots, improves the residual certificate, and proves a new asymptotic **transfer** theorem for a different maximum-ancestor discount. It does NOT prove the required lower for the trial section and does NOT reach 4.85. Core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a (614 declarations) unchanged. No new external theorem, Lean compile, or independent specialist review. No .295 draft use.

## 1. Exact finite graph

Use H=floor(R^theta), fixed 0<theta<.5 (target theta=.4), L=log R. Vertices (x,h), x even in [R-4H,2R] (round lower endpoint to even), 0<=h<=H. Birth injection at x in [R,2R], x=0 mod6, h=3. Stop at the first height H, discard any edge leaving the rectangle. On a prestate the new absolute clock is n=h+1-x/2. If n even, eligible primes p divide x+1 and 2h+3; if n odd, eligible primes divide x-1 and 2h-3. This follows by doubling n and using p|x+1 or x-1. Conversely those divisibilities and the parity give n=0 mod2p or n=p+2 mod2p respectively. Take the smallest eligible odd prime; p=0 for idle. Edge is (x,h)->(x-p+1,h+1-(p-1)/2) when p>0, else (x,h+1). At most one outgoing edge and finite DAG: moving edges strictly decrease x, idle increases h. All labels <=2H+3; preheight zero and odd-clock cases handled using absolute factors of the nonzero odd integer 2h-3. Topological order x descending, h ascending. A trial cutoff z ignores every prime >z, with all remaining priority unchanged.

The gain of a root A at vertex x is G=A-x; age=h-3+G/2. At first-height H with G<=4H, age<=3H-3. Exact integer reachability can propagate the smallest ancestor coordinate A (min over incoming, include birth when applicable); no need to track all root histories. If the minimum ancestor lies outside the gain budget, all others do. To test paths restricted to qmin(x)<=K at EVERY visited site, delete vertices with qmin(x)>K and their edges, and use the same min recurrence. Do not confuse this with replacing the actual winning prime or testing the terminal qmin only.

## 2. Refined localized residual lemma (both sum-clipped and max versions)

Use weights w_uv=exp(-lambda log(L)(x_u-x_v)/H) with lambda>0 fixed. They telescope to L^(-lambda G/H), and <=1. Define true operator T at each vertex either by clipped sum min(1,b(v)+sum w_uv C(u)) as in 6f5a9c7, or by max(b(v), max_{u->v} w_uv C(u)); b in {0,1}, empty max zero. The latter is the maximum weight of an actual birth path (minimum gain), not total mass of all ancestors. Both are monotone and satisfy one-sided difference <=sum w_uv [F(u)-C(u)]_+. The max case follows from max_i a_i-max_i b_i<=max_i(a_i-b_i), then sum of positive differences. For any trial array F in [0,1], r(v)=[F(v)-(T F)(v)]_+, d(v)=[F(v)-C(v)]_+. Then
    d(v)<=r(v)+sum_{u->v}w_uv d(u).
Let sigma(v) be the terminal true height-H sink reachable from v, or empty if the outgoing path exits. Let W(v) be product of weights along that true suffix if sigma exists, zero otherwise. For each sink s, unrolling in the DAG and using unique outgoing path gives
    C(s) >= [F(s)-E_s]_+,
    E_s=sum_{v:sigma(v)=s} W(v) r(v).
Thus sum C(s)>=sum_s [F(s)-E_s]_+ >= [sum_s F(s)-sum_v W(v)r(v)]_+ >= [sum_s F(s)-sum_v r(v)]_+. The first bound is new localized residual certificate, retaining positive mass even when losses exceed F at some sinks. For k-step lookahead, W_k(v) is the product along the first k true steps, with early exit giving zero, height-H arrival treated as absorbing weight1. Then 1>=W_k>=W_(k+1)>=W; thus sum F(s)-sum W_k r is a valid intermediate lower requiring only bounded true lookahead from positive-defect vertices, not full true ancestry. Exact full routing uses true successor information; it is not a free analytic estimate.

If F is exact trial clipped sum/max flow, positive residual is bounded by lost incoming trial-edge contributions at changed sources. For max operator, removing any incoming terms loses at most the sum of those positive terms (adding others cannot hurt), so same raw bound:
    sum r <= sum_{v:changed outgoing trial edge} F(v).
The true and trial graphs can also be swapped. These estimates require no bound on ancestor multiplicity. A separate integer certificate is min-ancestor flow in the intersection graph where a changed outgoing edge is REMOVED, not replaced by either edge. Its reachable sinks are actual true sinks with an unchanged trial witness, and a max discount of such a witness gives another valid lower. For a cutoff z this equals the actual first-height reachability via paths whose firing labels are all <=z. No monotonicity of actual vs trial sink sets is asserted.

## 3. New analytic max-flow top-band transfer

Take z=floor(3H/2), lambda=3, maximum-ancestor operator. Let F_z be trial flow, C true flow. We prove
    |sum_{h=H} C - sum_{h=H} F_z| <<_theta R/L^(17/8) = o(R/L²).       (1)
This is a paper deduction with explicit exponent gap; unlike raw cap1 defect count, it is uniform in the entire actual/trial ancestry and is small relative to the user's target. It is for max-flow discount lambda=3, NOT the original clipped-sum lambda=1. We derive both directions, so the top band is asymptotically removable for this weighted objective.

Proof. A changed source v=(x,h) has actual winner p>z and trial idle. Thus h>=(p-3)/2>=3H/4-O(1). For any fixed p in [z,2H+3], and sign, x lies in a single even spatial class modulo 2p (O(R/p) centers). Given x, the eligible absolute clock is in a single class mod2p in an interval of length H, giving O(1) clocks. Elementary Chebyshev/dyadic prime count over this fixed relative band gives sum 1/p=O(1/L). Hence there are O(R/L) changed sources. This counts all candidates, not necessarily reachable.

For each changed source with F_z(v)>0, take its minimum-gain ancestor G (exists by finiteness). The previous universal mod2310 potential of c0e45b0 gives W<=17G/8+395/12 for completed waits. It also applies to the truncated rule when z>=11: every truncated event obeys w<=2p and the exact retained priority of 3,5,7,11, which are the only priority constraints in the certified relaxation. This is the same finite-state certified paper bound, not a newly Lean-proved statement. Age t=h-3+G/2. Terminal idle I=t-W therefore obeys
    I>=h-13G/8-3-395/12.
Split at G=h/2. In the low-gain case I>=3h/16-O(1)>=9H/64-O(1). Every odd prime r<=z dividing either x neighbor would fire within 2r ticks in the truncated rule; hence qmin(x)>min(z,I/2)>=H/20 for all sufficiently large R. At a changed source the true winner p>z gives x+s=p v0. Since theta<.5, v0~R/p>>H, and both v0 and p v0-2s are H/20-rough. Elementary dimension-two upper sieve in v0, with a small fixed polynomial cutoff less than H/20 and p and enough CRT room, gives O(R/(p L²)) possible centers for fixed p and sign, uniformly. There are O(1) clocks per center; sum p reciprocal O(1/L) gives O(R/L³) low-gain changed sources. This uses the same two-form upper as the earlier square-root rough frontier, but H=R^theta can be strictly below sqrt R: no claim of semiprime-only factorization required. Each low-gain flow weight <=1.

In the high-gain case G>h/2>=3H/8-O(1), so F_z(v)=L^(-3G/H)<=O(L^(-9/8)). Sum over all O(R/L) changed sources to obtain O(R/L^(17/8)). Combine both estimates:
    sum_changed F_z(v)<<R/L³+R/L^(17/8).
Apply section2 raw residual to get one direction of (1). For the reverse comparison use true maximum-ancestor C(v) at changed sources instead. The true minimum-gain ancestor obeys exactly the same W and I estimates, and absence of any eligible prime during I implies the same roughness. Same high-gain weighting. Swap graph roles in the max residual lemma. This gives the other direction. Sources whose actual edge exits the rectangle may be included in this count and cannot invalidate it.

More generally for cutoff floor(cH), fixed 0<c<2, split G<=a h where 0<a<8/13, and use any fixed lambda with lambda*a*c/2>1. The small-gain terminal idle is >=(1-13a/8)h-O(1) so qmin>>H with a constant depending on c,a; high-gain weight is O(L^(-lambda*a*c/2)). Thus transfer error O(R/L³+R/L^(1+lambda*a*c/2)). This does NOT allow taking c->0 with lambda fixed or iterating cutoff down to polylog labels at unchanged target weight. For (1), c=1.5,a=.5,lambda=3 gives exponent17/8. Weight lambda=3 suppresses long-gain paths more strongly than the previous lambda=1; this is a stronger sufficient weighted lower, not a logically equivalent unweighted target.

Consequent sufficient lower: if trial maximum-ancestor sum at H=.4 and z=1.5H is >>R/L², (1) implies the true sum is >>R/L². Each sink contributes <=1 and weight of a sink with no ancestor of G<=4H is <=L^-12; at most O(R) sinks, so after excluding those still >>R/L² distinct actual first-hit states by age<=3H. This is the exact desired milestone conditional on the remaining TRIAL lower. That lower has NOT been proved. Even a positive finite margin at all tested sizes does not prove it. The previous accepted .2855 prime-product lower supplies first-height states at a lower scale only; no unproved amplification to .4 is used.

## 4. Diagnose static-roughness and small-cutoff limitations

For ANY actual canonical path first hitting H, gain G, and terminal center x, the same W bound gives
    H <= 13G/8 + 3+395/12 + 2 qmin(x),
since the final idle is <2qmin. Thus first-height transport does not intrinsically REQUIRE qmin comparable H, unlike a subcritical gain/time witness, but if G/H is bounded strictly below 8/13, then it DOES force qmin>>H. In particular a path with terminal qmin<=K=o(H) must have G>=(8/13-o(1))H. If EVERY visited center has qmin<=K, each completed wait and final idle is <=2K, and age>=H-3; hence completed event count >=(H-3)/(2K)-1. At H=R^.4, K=R^.2855 this requires order R^.1145 actual events. This is a useful strengthened diagnostic to distinguish genuine dynamical growth from a single static rough phase, not a replacement user-adopted 4.85 criterion.

For intersection-graph witnesses with prime cutoff z and wheel Q_z=2 product_{3<=p<=z}p, the existing spatial wall theorem implies G<Q_z: no event with p|Q_z can cross a multiple of Q_z downward. Therefore if Q_z=o(H), every such actual unchanged witness forces qmin(x)>=(1-o(1))H/2 by the preceding height ledger. In particular fixed z or z=o(log R) for H=R^theta cannot circumvent the static roughness barrier with unchanged witnesses. This explains why high finite coverage of z=7 safe witnesses must not be extrapolated into an asymptotic dynamical proof. Full residual method includes redirections; it is not restricted to unchanged witnesses. Nevertheless no small-cutoff weighted defect upper has been obtained.

## 5. Executed pilot and finite results

Audit research/lean/negative_min_height_section_flow_audit.mjs @bbe98aaa9411358aef633de289c8ad33dc89e9d8 blob 2bef63bafb7c0a35b6940198db5a9855cde7c1a3. Executed ECMAScript, exact pinned readback. Graphs R12000,48000,192000, H42,74,129. Independent trial factorization of neighbor and literal minimum eligible clock on 2148+15631+107597=125376 sampled physical states agrees with height divisor transition. Exact integer min ancestor, safe witness, roughness-restricted reachability; double precision only for discounted masses and residual comparisons (tolerance1e-6, not interval-certified numerical bounds). All final finite assertions passed. Height-first stops, no future motion beyond first H. All full graph reachable sinks have an ancestor with G<=4H, by exact integer test.

Full graph:
 R       H    sinks    clipped mass lambda1   max mass lambda3   min gain<=H/2  terminal qmin<=H/2  terminal qmin<=H/10
 12000   42   391      342.143                322.217             343            48                  1
 48000   74   1114     1004.222               967.367             1009           96                  18
 192000  129  3391     3141.300               3066.254            3135           212                 24

Paths restricted at ALL visited sites:
 R       K=floor(R^.2855)  reachable sinks (gain<=4H)   K=floor(H/10) reachable sinks
 12000   14                 15                         4            0
 48000   21                 14                         7            0
 192000  32                 18                         12           0
For R192000 the intermediate K64 and K129 counts are165 and569. Thus some genuinely multi-phase, bounded-roughness first-height paths exist at these finite sizes; no claim of asymptotic density. Most full sinks have a small-gain witness; finite additive potential constants make the asymptotic roughness implication sometimes vacuous at these H.

For clipped sum lambda1 at R192000 H129:
 z   trial mass  raw margin   local residual+64 steps margin  exact routed total margin   localized per-sink lower   unchanged witness count
 7   13714       -45051.367   -17653.431                       -12874.287                  645.765                   3060
 32  5959.340    647.508      2018.062                         2588.634                    2704.963                  3177
 64  4461.088    2662.667     2969.357                         3024.220                    3030.380                  3320
 129 3656.121    3080.045     3129.454                         3130.628                    3130.810                  3390
 193 3339.041    3134.598     3139.956                         3139.995                    3139.995                  3391
 Full true mass3141.300. Exact routed lower uses actual outgoing suffix from each positive residual vertex, NOT the trial route. Unchanged witness bound (different method) can be stronger than the localized residual; at z7 it gives 3060 integer sinks, but section4's asymptotic obstruction applies for fixed z. No claim that local residual itself proves a lower at z7 without the extra routing information.

For max-flow lambda3 at z=floor(1.5H):
 R       trial mass   low-gain changed keys/weight   high-gain changed keys/weight   raw certified margin (numeric)   true max mass
 12000   345.241      23 / 23.000                    5 / .095                        322.146                         322.217
 48000   1028.595     63 / 62.176                    6 / .073                        966.345                         967.367
 192000  3262.355     204 / 200.285                  18 / .069                       3062.002                        3066.254
Finite counts and weights agree with the proposed split, but the asymptotic estimate (1) is a separate paper proof based on upper sieve and the finite-state wait potential. The audit checks the qmin lower with the actual additive potential constant (sometimes negative at small H), not a false asymptotic finite threshold. It verifies the max-flow raw lower on all tested z, not a formal interval arithmetic proof. Earlier pilot code commits 63d2674 and 2c2d458 are superseded by the exact final audit.

## 6. Next barrier

The new max-flow estimate removes the top-band error at the required asymptotic accuracy. It is a substantive transfer theorem, not a new canonical occupation lower at exponent .4. The remaining task is an independent lower for the z~H trial section, preferably with a decomposition of high-gain paths so it does not merely restate a stronger roughness existence theorem. The finite test favors studying minimum-gain ancestors and per-sink residual routing, but reveals that fixed-small-label unchanged witnesses are not an escape from roughness. Need a multiscale trial construction with rigorously positive height-section mass through polynomial scales, rather than declaring the finite pilot decisive. No 4.85, no .4 or square-root canonical lower, no .40 witness. No new external research/Lean/human review; main and siblings unchanged.
