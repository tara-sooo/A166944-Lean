# Integration VI: sliding future minimum of signed endpoint drift and pair-preserving deep witnesses

2026-11-26 JST. Parent [baf477b](https://github.com/tara-sooo/A166944-Lean/commit/baf477be7204bc27c93adaf6d188ef8adc7e751e). Direct head [319d42d](https://github.com/tara-sooo/A166944-Lean/blob/319d42d2ac9bf3dcdfc2cfd34ce8a4117f1cd611/research/2026-11-26-min-direct-last-exit-corridors-and-record-support.md) read; its record-only downward support concerns actual recovery corridors, not arbitrary upward records. Reuse the original future-witness support estimates and live-cohort variation. New paper reduction: a sliding future minimum replaces the signed endpoint drift at o(NT) cost, so the positive part has actual persistent left contact and admits a two-witness pair-preserving transport. Negative part remains a signed credit. This concerns the signed relaxed backward envelope, not the older target-normalized global record charge. No strict final contraction, Lean compilation or external novelty claim.

## 1. Frozen domain

Use actual endpoint U=U_end,3 of integration V (ideal version not needed), original dyadic X,B,u,ell,N,T,H, D=floor(eta H/log(2+N)), eta=ell^(-1/4), D_sh=floor(D/ell), b0, actual endpoint gate and denominator b_Q=max(b0,|Q|), single admissible ordered pair interval I=[a,b) in a slab [l,e). All original source masks preserved; this relaxed endpoint domain is an upper bound. The fixed birth age is >>B and lifetime strip h=eta H>>D. Interpolated nonnegative deficit d_i is continuous piecewise affine, derivative in [-1,5] (w>=1, w<=3g). Shared pairs have identical actual completed path on I and up to h-O(B) after I. In particular all points below are on actual completed lives, not hypothetical continuation. Let
    z=floor(D/ell²), epsilon=ell^(-1/4).
Then B u^A=o(z) for any fixed A, z=o(D_sh), z=o(D), z log N/epsilon=o(T). Use z constant over the ensemble. Define m_i(x)=min_{x<=t<=x+z} d_i(t), M_i(x)=(m_i(x)-D_sh)_+. On eligible domains future room holds. Since slope >=-1,
    0<=d_i(x)-m_i(x)<=z.
Clipping is 1-Lipschitz, so replacing each endpoint deep deficit by M_i changes its signed difference by at most 2z (indeed z suffices). Total endpoint error <=2z N(H/D+2)=o(NT), using sum pair weights <=|Q| per snapshot. This is a uniform quantitative error, not the assertion that every deep deficit is a global future record.

## 2. Positive sliding-minimum derivative is persistent left contact

The sliding minimum of a finite piecewise affine path is piecewise affine: partition by knots of d and their translates by -z; on each open cell it is minimum of the two affine endpoint values and constant interior knot values, with finitely many intersections. It is Lipschitz (slope range [-1,5]); clipping preserves this. Almost everywhere where M_i'(x)>0, the minimum is attained by the LEFT endpoint and
    M_i(x)=d_i(x)-D_sh>0,
    M_i'(x)=d_i'(x)>0,
    d_i(t)>=d_i(x)>D_sh for all t in [x,x+z].           (1)
Indeed an interior minimum persists locally as a constant, and a right endpoint with positive slope cannot minimize against points immediately to its left. At isolated ties or clipping breakpoints no derivative claim is needed. Conversely no blanket claim that every left contact gives a positive derivative. Almost everywhere negative derivative may be a right contact, and is retained rather than discarded. Put
    P_z=sum_(slab,Q,i,j) integral_I (M_i')_+/b_Q,
    L_z=sum_(slab,Q,i,j) integral_I (-M_i')_+/b_Q.
Integration V now gives
    W_B <= U/2 + (P_z-L_z)/2 + o(NT).                (2)
Both nonnegative; their difference differs from Xi_deep by o(NT). The finite smoothing horizon is essential: using a global minimum through terminal could reduce endpoints by order H, not the o(NT) proven here. This eliminates short positive excursions from P_z only insofar as they fail (1), not necessarily all excursions of length z by their complete rise/fall extent.

## 3. Unfreeze the positive density; retain exact signed credit

For positive source measure use original relaxed ordered pairs with density (M_i')_+/b_Q on I. Replace denominator by max(b0,b(x)), where b(x) is full original physical crossing slot of the pair at x (unique outside breakpoints). This changes total by o(NT): for source cohort b, n members surviving to actual slab endpoint Q of size q, numerator at most 5 n²; same absolute denominator error as ef0953b, <=5[n log(q/n)+(b-n)]. Integration over all slabs <=5DN(log N+2)=o(NT). With max(b0,.) on both sides the estimate remains valid even for b<b0, since denominators >=n. No new eligibility or endpoint gate; negative credit L_z stays on ORIGINAL frozen denominator. Now at each x, per tag per ordered role density <=5, per pair <=5/max(b0,b(x)). These are relaxed measure bounds, not exact original grid-clock masks. Positive source is actually in a selected event with 2w>g, hence r>g/4, but do not require every old raw-clock mask on this source.

## 4. Actual future suffix witnesses

For each positive source point x use complete events wholly inside [x,x+z], excluding partial event fringes. Total complete gain G>=z-2B. By (1) and slope bounds, start deficit <=d(x)+5B, end deficit >=d(x), so actual complete waits >=(G-5B)/2. Expensive events w>=g/4 then carry >=G/4-5B/2>=z/8 ticks for large X. Define tick witness set F_x as ALL actual occupied future ticks in these completed expensive events (pre event arrival t, ticks t+1..t+w). Each such event has least eligible r>=(p-1)/8. Define P largest even primorial<=B/u^4, K_x grid multiples of P in [x,x+z) (strict crossings). |K_x|>=z/(2P); each actual crossing label cannot divide P, by strict primorial barrier. Shared original pair executes the exact same complete future suffix, including all witness ticks and grid crossings. All witnesses have actual event/occupied deficits between d(x)-O(B) and d(x)+5z+O(B), hence deep and relatively narrow (1+O(z/D_sh)). No independence of witness sets required.

Split positive measure at x uniformly over the Cartesian product K_x times F_x, retaining both tag identities and their original first birth. This is a partition. For each tag in one role and fixed grid witness K, sources x lie within [K-z,K], density <=5, normalization >=z/(2P), so load <=10P. For fixed expensive tick in event with prehorizon C, x in [C-z,C], normalization >=z/8, so load <=40. Either-role bound twice these. No charge per pair per source multiple times; integration includes only the source's original slab interval. This already allows old future-witness projected and physical thin support cuts on this POSITIVE ENVELOPE at o(NT) cost. Unlike the old global record objective, no 1/R or target normalization.

## 5. Preserve physical pair denominator at both witnesses

Apply the original live exit cohort variation from 850c7de, including actual retirement. For each transported product fraction delete if variation from source crossing exit S_x to either witness exit exceeds epsilon. For fixed tagged edge all such source x lie within a backwards interval of length z+B (source slot fringe), and per-tag either-role density <=10. Markov and the total active variation <=N(log N+2) give cost O((z+B)N log N/epsilon)=o(NT) (sum two witness sectors, only union paid). The pair survives both by actual future room; this deletion can be tested on focal history since the pair shares the suffix. Hence b(x) and b_V at either witness are within exp(epsilon). For fixed ordered pair, the source density <=5 exp(epsilon)/max(b0,b_V) after this deletion, and source x again varies over length at most z. Marginal per ordered pair at boundary V <=10 exp(epsilon) P/max(b0,b_V), at tick V <=40 exp(epsilon)/max(b0,b_V). These bounds include all grids/slabs/positive sources simultaneously; no extra factor of number of source intervals. At each actual witness endpoint S_V use all original tags executing that event, not a recomputed effective population.

As in 1782fd3, impose induced root-tail and prefix ranks >=rho b_V at the pair's ORIGINAL first meeting, rho=ell^(-1/4), using actual witness endpoint members. At most 4rho b_V² ordered pairs fail per witness. Sum boundary load upper over all actual physical boundary witnesses: sum P b_V<=N(H+P). Sum tick population over all actual physical expensive ticks <=3NH. Thus pay either rank failure at O(rho NT)=o(NT). This is a new pair-preserving deep witness condition. No original source rank masks are removed; they were imposed at original endpoint slab. A tick key includes its actual selected p and physical tick j,C; its exit n is determined by j,C,p on an occupied episode, except j may be final firing tick (then n=j), so the physical pair cap is unambiguous. Boundary projected keys (K,C,p) may combine several true slots, retain true slot in pair census.

## 6. Thin payments on the new positive measure

Use earlier future-witness-transport support: possible projected crossing keys (K,C,p) O((X/P+1) pi(B)), uniform per-tag boundary marginal O(P). Let effective mass equal marginal load divided by a fixed absolute capacity constant times P. Pay mass<=H/(B ell) at cost O(NT/ell). At expensive physical tick keys (j,C,p) projected C support O(X/[p log²(2+p)]) via two-form upper sieve and r>=g/8; tick range O(H) per C because original deficit<=6+5H+4B. Effective mass defined using absolute per-tag tick cap, pay <=log²(2+p)/(u ell²), cost O(NT/ell) by sum 1/p=O(ell). For high p>=ceil(B/u) pay <=u²/ell², same O(NT/ell) by prime reciprocal sum O(ell/u). Payments on product fractions, union accounting. All sources may be processed simultaneously, no claim of independence or constant improvement from these o(NT) removals. Rank caps in Section5 apply physical keys while thin cap can use projected keys. Let P_z^heavy be residual exact POSITIVE relaxed envelope after replacement, stability, rank and thin witness deletions. Then
    P_z <= P_z^heavy + o(NT),
    NT/2-o(NT) <= U/2 + (P_z^heavy-L_z)/2 + c_a(D_l+D_h)
under finite twins. Sufficient strict liminf of [U+P_z^heavy-L_z+6(D_l+D_h)]/(NT)<1. This retains the negative credit, not a new positive source charge added to the whole old Xi_deep. No lower bound on L_z of constant size or upper bound on heavy term obtained. A further improvement would route negative right-contact derivatives to actual record decreases and compare supply by cut-level on the SAME pair population; direct 319d42d record barriers apply to true downward records, not arbitrary right-contact pieces without a matching argument.

## 7. Diagnostics

Run node research/min_unified_sliding_minimum_witness_audit.mjs 4096 16384 65536. Exact function executed in ECMAScript tool runtime (not separate Node process). Six actual prime-root finite controls; exact piecewise-affine lower envelope from shifted knots and line intersections, direct minimum checks, positive contact, signed integral and endpoint error. Actual endpoint samples up to 8 members per cohort with full denominator; first shared completed exit proxy, not cumulative rank/age masks; z and cut finite substitutes, b truncated to actual pair future room. Midpoint samples of positive pieces verify actual half-rate and expensive partial clock integral; when finite z permits enough complete ticks/grid points, check common physical pair and variation, report finite sampled witness load (not exact integrated product measure, no thin/rank cap numerical test). Synthetic exact affine spike control, not an actual MIN orbit. No asymptotic sieve or Lean verification. Results:
```json
{
  "results": [
    {
      "X": 4096,
      "focus": false,
      "B": 170,
      "T": 1360,
      "D": 340,
      "z": 42,
      "cut": 42,
      "N": 464,
      "events": 7448,
      "segments": 11396,
      "intervals": 363,
      "terminalPairs": 69,
      "variation": 509.48311289038037,
      "raw": 11230.671576890161,
      "smoothed": 10891.102814037335,
      "pos": 11863.724060651833,
      "neg": 972.6212466145055,
      "positiveSamples": 3125,
      "negativeSamples": 730,
      "sourceMass": 6756.614344882427,
      "witnessMass": 6132.972206454909,
      "unstableMass": 623.6421384275237,
      "maxPairTick": 23.515151515151516,
      "maxPairGrid": 4.479076479076479
    },
    {
      "X": 4096,
      "focus": true,
      "B": 170,
      "T": 85,
      "D": 21,
      "z": 4,
      "cut": 42,
      "N": 464,
      "events": 3292,
      "segments": 6189,
      "intervals": 610,
      "terminalPairs": 72,
      "variation": 405.1837365277168,
      "raw": 4346.071205075812,
      "smoothed": 4339.786345490963,
      "pos": 4725.824879264457,
      "neg": 386.0385337734911,
      "positiveSamples": 608,
      "negativeSamples": 158,
      "sourceMass": 159.32540792540445,
      "witnessMass": 139.32540792540442,
      "unstableMass": 20,
      "maxPairTick": 20,
      "maxPairGrid": 3.3333333333333335
    },
    {
      "X": 16384,
      "focus": false,
      "B": 339,
      "T": 2712,
      "D": 678,
      "z": 84,
      "cut": 84,
      "N": 1612,
      "events": 33736,
      "segments": 49206,
      "intervals": 1002,
      "terminalPairs": 233,
      "variation": 2164.41647985876,
      "raw": 44231.035115944505,
      "smoothed": 43228.62980183464,
      "pos": 47185.949602245746,
      "neg": 3957.3198004111755,
      "positiveSamples": 11032,
      "negativeSamples": 2141,
      "sourceMass": 26005.392734965382,
      "witnessMass": 24305.580437483266,
      "unstableMass": 1699.8122974818157,
      "maxPairTick": 17.36898395721925,
      "maxPairGrid": 4.549019607843138
    },
    {
      "X": 16384,
      "focus": true,
      "B": 339,
      "T": 169,
      "D": 42,
      "z": 5,
      "cut": 84,
      "N": 1612,
      "events": 15668,
      "segments": 32653,
      "intervals": 3443,
      "terminalPairs": 296,
      "variation": 1883.09735342764,
      "raw": 27057.181676809185,
      "smoothed": 26949.05955909075,
      "pos": 29169.406369504683,
      "neg": 2220.3468104139642,
      "positiveSamples": 4027,
      "negativeSamples": 949,
      "sourceMass": 2115.6175467408175,
      "witnessMass": 1767.014824523806,
      "unstableMass": 348.6027222170127,
      "maxPairTick": 33.333333333333336,
      "maxPairGrid": 5.555555555555556
    },
    {
      "X": 65536,
      "focus": false,
      "B": 678,
      "T": 5424,
      "D": 1356,
      "z": 169,
      "cut": 169,
      "N": 5709,
      "events": 142413,
      "segments": 207992,
      "intervals": 2891,
      "terminalPairs": 538,
      "variation": 9149.470840405398,
      "raw": 168384.5776766572,
      "smoothed": 161016.11539201022,
      "pos": 184531.5226149824,
      "neg": 23515.407222971266,
      "positiveSamples": 33616,
      "negativeSamples": 10113,
      "sourceMass": 94148.83291342345,
      "witnessMass": 84535.15064959895,
      "unstableMass": 9613.682263823795,
      "maxPairTick": 25.538416422289743,
      "maxPairGrid": 3.9444444444444446
    },
    {
      "X": 65536,
      "focus": true,
      "B": 678,
      "T": 339,
      "D": 84,
      "z": 10,
      "cut": 169,
      "N": 5709,
      "events": 75430,
      "segments": 147391,
      "intervals": 18067,
      "terminalPairs": 1084,
      "variation": 8128.293488425862,
      "raw": 179728.33932551826,
      "smoothed": 178964.5042341836,
      "pos": 195838.37267515372,
      "neg": 16873.868440968803,
      "positiveSamples": 17950,
      "negativeSamples": 4676,
      "sourceMass": 15280.62598021977,
      "witnessMass": 13694.480503288016,
      "unstableMass": 1586.145476931741,
      "maxPairTick": 25.6,
      "maxPairGrid": 7.466666666666668
    }
  ],
  "synthetic": {
    "first": 0,
    "later": 16
  }
}
```
