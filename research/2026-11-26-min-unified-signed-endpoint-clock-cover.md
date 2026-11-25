# Direct-arithmetic integration V: signed endpoint clock kernel, half-rate shallow census and overlapping radical covers

2026-11-26 JST. Parent [1782fd3](https://github.com/tara-sooo/A166944-Lean/commit/1782fd3b6f077b23c72c8adfa9dff630d1beda77). Independent direct head 6fa601556aa43af535e269c2f6879429c3d65ed2 read (overlapping recovery corridor controls are relaxed selected-clock paths, NOT actual MIN). Use [direct laminar leaves](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-laminar-support-and-leaf-packing.md), integration IV global small-leaf census, and the original endpoint denominator and birth-rank machinery. Two paper results: replace the flat backward endpoint coefficient c_a by actual signed clock integral, including half-rate shallow and A1 subpopulation envelopes; pay the union of arbitrary overlapping long, extremely band-dominated bounded-radical prefixes by disjoint-color cover and varying-support leaf packing. No strict final contraction, Lean verification or novelty claim.

## 1. Original endpoint kernel and clock interpolation

Keep X,B,u,ell,N,T,H, actual completed original prime-root MIN tags, actual terminal horizons, original grids and all valid exact masks through 1782fd3. c_a=3(1+2/u^.25), P_max<=B^.25, b0 and endpoint gates unchanged from 3f98290, D=max(1,floor(eta H/log(2+N))), eta=ell^(-1/4). Use the actual endpoint version of U_end,3 from b1e071f, or its ideal version under finite twins. For each slab [l,e), full original endpoint cohort Q (or ideal subset), mass r, retain original gate and denominator b_Q=max(b0,r). For each ordered distinct pair i,j in Q, let I_ij be its SINGLE permitted interval in this slab: intersection of the two original eligibility intervals, historical age tests, fixed uniform age, actual first-birth lower bound, with static actual-large branch test, induced root-rank tests and long-low birth exclusions as in U_end,3. Empty if static test fails. Omit other dynamic masks only for an upper envelope, as before. Half-integer endpoints, half-open convention. Denote U= sum |I_ij|/b_Q over these slabs and pairs (U_end,3 or U_rank,3). Full populations unchanged, no pair resampling beyond existing kernel.

For each actual completed event of tag i, pre/post horizon C,J=C+g and arrival/post deficit d,d'=d+2w-g, linearly interpolate d_i(x) from d to d' on [C,J]. This is continuous along each original gained horizon, since next predeficit is preceding postdeficit. On each open event interval define omega_i=w/g. Then
    omega_i(x)=(1+d_i'(x))/2,  0<omega_i<=3.
For a selected class of actual focal waits use omega_i^S=omega_i times its actual event indicator. In particular shallow means actual POSTdeficit <=D_sh (choose D_sh=D/ell rounded down), A1 means actual p>=Y=B^.5, pre d+3<=p/5, adjusted post 2p. Since D_sh/B->infinity all A1 marks are shallow eventually. No extrapolation outside original life. Two endpoint members in an admitted pair already met before I_ij by the old fixed birth age >>B+P_max. Therefore their actual path, including arrival phase, is identical in I_ij and its event fringes; the integrands coincide. This also implies both actual pair members have same A1 status at any original residual backward A1 source even if the full exit cohort mixes arrivals (integration IV remains needed for dominance and forward charges).

## 2. A general interval bound for original assigned focal clocks

In the original common kernel, backward pair at source atom K of crossing event U has exact clock <= assigned focal atom clock w_i(K)/b (since a_omega/n_c<=1). On a fixed grid the right-witness assignment distributes each actual focal wait over the witness crossing's strict atoms without reuse; nonself focal events lie in its preceding noncrossing cell, of gain <=P, and self focal wait is at that crossing. This property is from the original joint kernel, not an assumed new clock allocation. The exact old masks only reduce such contributions. If K lies in a fixed interval I=[a,b), all actual focal events whose allocated fractions enter I have gain intervals in [a-B-P-O(1),b+B+O(1)]. Indeed source witness prehorizon >=K-B and post <=K+B; preceding cell adds <=P. The same holds for any chosen subset of actual focal waits, not just self. Sum each actual wait at most once on this grid. Since omega_i<=3, the sum of assigned clock of class S into I is <=
    integral_I omega_i^S(x) dx + O(B+P+1).              (1)
Bound only the intersection of the enlarged interval with the actual completed life; no fictional extension. If I contains only part of a witness gain, the O(B+P) error absorbs all its possible excess; one does not pay an error per internal event. This proves (1) for arbitrary original grids without a quadrature of a rapidly oscillating clock density.

Freeze the original backward pair denominator from b to b_Q using precisely the earlier entropy/retirement proof of ef0953b: actual weighted numerator per atom <=c_a P times the same pair count, so its positive freezing error is bounded by c_a times the earlier error (D+P_max) N(log N+1+1/xi), and ideal endpoint replacement uses the old strip. Apply once to a partition of the actual focal clock, not separately to two full copies. No change to old normalized populations. Then sum (1) over admissible ordered pairs/endpoint denominator. Total error
    O((B+P_max+1) N(H/D+2))=o(NT),                    (2)
since per endpoint sum 1/b_Q over all ordered pairs <=r, total snapshot membership <=N(H/D+2). Average over original grids. It follows for ANY actual focal-wait subpopulation of exact remaining backward charges, on the same original relaxed endpoint domains,
    W_B^S <= V_S+o(NT),   V_S=sum_(slabs,Q,i,j) integral_(I_ij) omega_i^S / b_Q. (3)
In particular this is not an equality for the original backward clock; all omitted masks only loosen the upper envelope. Since original per-atom clock is already split by its assigned actual focal waits, use the actual row components when defining S, not the source witness label for a nonself event.

## 3. Signed full-clock endpoint objective and half-rate shallow envelope

For full backward clock, (3) yields the explicit identity for the new upper scalar
    V_clock = U/2 + (1/2) sum_(I=[a,b)) [d_i(b)-d_i(a)]/b_Q.       (4)
Each pair interval is in original actual life; use zero for empty. Same branch census as 3f98290/long-low birth refinement: in each slab group by actual original birth branches, count eligible pairs via sorted root prefix counts. The weighted integral can be evaluated by additionally splitting at actual gain events of the eligible shared slot and applying omega of that slot; alternatively integrate pair intervals via prefix-clock interpolation using (4). No new time-averaging or independence. V_clock<=3U, and is nonnegative even though the drift term is signed. This is a genuine different sufficient objective, with all backward clock units already included (do not multiply by c_a again).

For shallow focal waits, consider any pair interval I. The marked actual events meeting I (or whose assigned atoms meet I on a grid) are contained in the fringe in Section 2. If nonempty, take the contiguous block from first such event to LAST shallow event, even if other deep events intervene. Its actual total wait equals (block gain + last postdeficit - first predeficit)/2 <= (|I|+2B+P+O(1)+D_sh)/2. All selected shallow waits are a subset. Hence
    W_B^shallow <= U/2 + O(N(H/D+2)(D_sh+B+P_max+1))
                     + old freezing error
                 <= U/2+o(NT).                              (5)
This uses bounded LAST postdeficit, not a uniform deficit bound throughout the interval. Can use actual V_shallow in (3), and it too satisfies V_shallow<=U/2+o(NT). All A1 backward source clock belongs to this class, since p>=Y>>aP_max implies a large self witness, and last A1 postdeficit<=2B+6. In fact (5) for the A1 subpopulation has error O(NB(H/D+2)) before freezing. This gives an independent bound W_A1,B<=U/2+o(NT), to take the minimum with (15/8+o(1))E_A1 from integration IV. It bounds that same subpopulation on a different envelope, not a factor-six estimate of the entire residual. Equation (5) extends the half-rate bound to shallow non-A1 focal waits, which the A1 recovery transport did not cover.

A useful signed refinement for full backward clock: let d_hi(x)=max(d_i(x)-D_sh,0), d_lo=min(d_i,D_sh). Sum the endpoint differences of d_lo with error <=D_sh N(H/D+2)=o(NT). Therefore
    W_B <= U/2 + (1/2) sum_(I=[a,b)) [d_hi(b)-d_hi(a)]/b_Q + o(NT). (6)
The high-deficit contribution is SIGNED, not absolute or positive-only; negative returns cancel inside each pair interval. Both signs are necessary. We do not establish that it is o(NT) over the actual ensemble. No claim of a constant contraction from mere clipping. For an independent bound on the remaining deep backward clock use V_deep of (3), or old exact deep masks. Avoid counting shallow clock twice. Since A1 is large self, V_nonA1 obtained by excluding actual A1 focal waits is valid for the original complementary non-A1 BACKWARD source clock: A1 focal waits cannot be assigned to a different nonself crossing on good grids, and actual admitted pair already shares its arrival. Thus one may combine V_nonA1 with the corrected A1 supply census. In particular a new sufficient upper on exact backward clock is the minimum of
    c_a U, V_clock, U/2+W_B^deep, V_nonA1+min(U/2,(15/8)E_A1)
up to o(NT). W_B^deep denotes exact remaining deep focal clock (or a valid bound). All expressions use the same old source eligibility; E_A1 remains the corrected supply-endpoint envelope with its own valid masks. For finite twins the usual lower bound NT/2-o(NT) is <= this backward upper + c_a(D_l+D_h). Forward unchanged here. Strict inequality with threshold 1/2 in CLOCK units suffices; previous full and independent boundary criteria remain. This is a coefficient improvement for a broad class, but not a proof of the strict margin: U can be of order NT, and deep/forward clocks remain.

## 4. Arbitrarily overlapping intervals admit a two-color cover

For a fixed original tag and fixed label band, consider ANY finite family of contiguous actual completed event blocks (half-open in event indices and gained horizon). Sort by left endpoint ascending/right endpoint descending and remove contained intervals. Remaining left/right endpoints strictly increase. If three consecutive intervals share a point (or first reaches start of third), middle interval is contained in union of first and third; delete it. A stack implementation removes its middle when the next interval arrives, repeating as needed. The union is unchanged. No point is in more than two selected interiors. Greedy two-color assignment gives disjoint blocks in each color; selected total gain <=2H per tag. This does NOT require originally disjoint recovery corridors; the new direct relaxed overlapping controls underscore why the original family cannot simply be summed as disjoint. All selected blocks are original candidates, not concatenations with enlarged radical.

## 5. New general mask for long extremely band-dominated bounded-radical blocks

Retain integration IV band parameters: fixed k=24, bands [Z,2Z) covering p>=B^.1 (start >=B^.1/2), U0=floor(ell), even outside gain threshold, actual radical product<=4H. On each original tag and band consider the family of ALL contiguous completed event blocks satisfying:
    (a) product of DISTINCT selected primes in the entire block <=4H;
    (b) gained length G_block >= Z u^3;
    (c) outside-band gain E_block <= (U0/(Z u²)) G_block.
A translated common prefix with nonzero lag |Delta|<=4H satisfies (a) automatically, since every selected period divides lag. A block with all labels in the band also satisfies (c) trivially. Conditions (b),(c) are real restrictions, not implied by finite twins or arbitrary translated prefixes. No requirement on actual wait or deficit.

Select a two-color cover by Section 4. Each chosen block has <=k distinguished labels in band for large X. Apply direct laminar theorem (13) separately to its two disjoint-color families. For each band there are at most 2H/(Z u^3) selected blocks, total outside gain <=2H U0/(Z u²). Small leaves (actual outside gain <=U0) start at distinct prehorizons within each color; their actual used label product <=4H. Integration IV global arithmetic count (including its improved close-prime-pair upper sieve for two-label leaves) is
    A(Z) << X/(Z u^(2-o(1)))
uniformly over these bands, using fixed k and global O(X) horizon domain. For l>=3 CRT counting suffices; l=1 impossible. No statistical sampling. The direct combinatorial inequality, or just count and charge its disjoint large leaves, yields
    K_band <= (2^k-1) [2H/(Z u^3) + 2 A(Z) + 2H U0/(Z u² U0^+)],
where K_band counts distinguished events over selected blocks including color multiplicity and U0^+=2(floor(U0/2)+1)>U0. Multiplying by 2Z bounds distinguished gain. Adding actual outside gain and summing O(u) bands, the total length of the UNION of all original candidate blocks on one tag is
    <<_k H/u + X/u^(1-o(1)) = o(T).                     (7)
This is uniform PER TAG. It pays every original focal event whose entire gain lies in this union of actual event blocks, by w<=3g; total actual clock o(NT), including non-A1. It pays all exact focal-row fractions attached to those waits (uniform original good-grid normalization); no arbitrary partner-column or transported destination mask is implied. Raw/discounted boundary events can be paid on their own routes by their actual atom cap if also control grid fringe: for Z>=B^.25 the selected union interval count <=2H/(Z u³) makes P overhead o(T) after all bands; for smaller bands only focal waits are asserted here. This is a genuine extension of small-leaf local halos to WHOLE long almost single-band blocks, with arbitrarily overlapping actual candidate blocks and changing supports. The outside gain term is essential: typical prefixes with substantial other-band gain need not meet (c). The high pursuit length B ell may be shorter than (b) for the largest bands. No assertion the residual is covered. Can use variable thresholds L_Z and epsilon_Z with same proof if sum of Z H/L_Z and Z H epsilon_Z/U0 and H epsilon_Z is o(T). A further restriction to actual source/defect intervals only reduces the family.

## 6. Diagnostics and scope

Run node research/min_unified_signed_endpoint_clock_cover_audit.mjs 4096 16384 65536. Exact function ran in ECMAScript tool runtime, not separate Node. Six actual prime-root controls, ordinary target and focus floor(B/2). Actual endpoint cohorts with deterministic sample of <=16 members per cohort but FULL denominator; pair eligibility uses first common completed exit posthorizon and actual endpoints, not full cumulative rank/age/maturity masks. Signed clock interpolation, shared suffix, local shallow and A1 clock bounds, clipped drift identity/upper, finite surrogate right-cell assigned clock on P=6,30,210 capped per atom (not full original kernel), compare assigned sums to integral fringe. Finite shallow threshold floor(B/2), not asymptotic D/ell. Independent actual bounded-radical band-block controls with relaxed finite G>=2Z and outside<=G/4, max32 events, not analytic thresholds; exact union preservation, two-color disjointness, distinct small leaf starts per color and laminar count, outside budgets. Exhaustive interval families on five cells plus dense overlap control. No numerical upper-sieve test, no formal Lean compilation. Results:
```json
{
  "results": [
    {
      "X": 4096,
      "focus": false,
      "B": 170,
      "T": 1360,
      "D": 340,
      "K0": 85,
      "N": 464,
      "events": 7448,
      "reaches": 0,
      "snapshots": 42,
      "pairs": 470,
      "gridChecks": 1410,
      "signedChecks": 470,
      "shallowChecks": 470,
      "cutoffChecks": 470,
      "weightedLen": 17799.574125874136,
      "weightedClock": 15513.590879450641,
      "weightedShallow": 3706.953559656926,
      "weightedA1": 500.0641446433645,
      "weightedSigned": 6613.803816513571,
      "weightedDeepSigned": 5272.687298673309,
      "weightedShallowUpper": 35933.32872960374,
      "weightedA1Upper": 52535.10372960378,
      "weightedGrid": 14537.69941633526,
      "weightError": 161819.59999999998,
      "deepPositive": 252,
      "families": 449,
      "candidates": 1946,
      "selected": 791,
      "overlap": 204,
      "coveredGain": 27588,
      "selectedGain": 36478,
      "outside": 6068,
      "distinguished": 1042,
      "leafChecks": 4,
      "small": 3,
      "large": 1,
      "coveredEvents": 2381
    },
    {
      "X": 4096,
      "focus": true,
      "B": 170,
      "T": 85,
      "D": 21,
      "K0": 85,
      "N": 464,
      "events": 3292,
      "reaches": 276,
      "snapshots": 427,
      "pairs": 612,
      "gridChecks": 1836,
      "signedChecks": 612,
      "shallowChecks": 612,
      "cutoffChecks": 612,
      "weightedLen": 6851.7999999999865,
      "weightedClock": 6040.073870225077,
      "weightedShallow": 3077.220244752076,
      "weightedA1": 638.4973189498767,
      "weightedSigned": 2614.173870225073,
      "weightedDeepSigned": 1251.2987379400702,
      "weightedShallowUpper": 88822.56666666661,
      "weightedA1Upper": 141266.16666666663,
      "weightedGrid": 4682.677979482378,
      "weightError": 511174.39999999956,
      "deepPositive": 122,
      "families": 223,
      "candidates": 480,
      "selected": 292,
      "overlap": 56,
      "coveredGain": 8528,
      "selectedGain": 10228,
      "outside": 1616,
      "distinguished": 354,
      "leafChecks": 1,
      "small": 1,
      "large": 0,
      "coveredEvents": 771
    },
    {
      "X": 16384,
      "focus": false,
      "B": 339,
      "T": 2712,
      "D": 678,
      "K0": 169,
      "N": 1612,
      "events": 33736,
      "reaches": 0,
      "snapshots": 119,
      "pairs": 1697,
      "gridChecks": 5091,
      "signedChecks": 1697,
      "shallowChecks": 1697,
      "cutoffChecks": 1697,
      "weightedLen": 89766.78021661824,
      "weightedClock": 80590.07738455158,
      "weightedShallow": 18736.778212964222,
      "weightedA1": 5184.5930634730685,
      "weightedSigned": 35706.687276243036,
      "weightedDeepSigned": 28133.951832702234,
      "weightedShallowUpper": 208465.61716237097,
      "weightedA1Upper": 307928.2463628902,
      "weightedGrid": 78984.53518691065,
      "weightError": 882996.3897179984,
      "deepPositive": 875,
      "families": 1875,
      "candidates": 10337,
      "selected": 3455,
      "overlap": 834,
      "coveredGain": 137936,
      "selectedGain": 179088,
      "outside": 31914,
      "distinguished": 4872,
      "leafChecks": 42,
      "small": 22,
      "large": 20,
      "coveredEvents": 11448
    },
    {
      "X": 16384,
      "focus": true,
      "B": 339,
      "T": 169,
      "D": 42,
      "K0": 169,
      "N": 1612,
      "events": 15668,
      "reaches": 841,
      "snapshots": 1245,
      "pairs": 3474,
      "gridChecks": 10422,
      "signedChecks": 3474,
      "shallowChecks": 3474,
      "cutoffChecks": 3474,
      "weightedLen": 55262.364430014815,
      "weightedClock": 48400.80781764203,
      "weightedShallow": 29160.29600112406,
      "weightedA1": 6762.416199468248,
      "weightedSigned": 20769.625602634947,
      "weightedDeepSigned": 7069.1057416023705,
      "weightedShallowUpper": 730161.368326113,
      "weightedA1Upper": 1157319.6278860162,
      "weightedGrid": 40773.28030175803,
      "weightError": 3792170.0246753776,
      "deepPositive": 629,
      "families": 967,
      "candidates": 2540,
      "selected": 1359,
      "overlap": 296,
      "coveredGain": 42018,
      "selectedGain": 52602,
      "outside": 8522,
      "distinguished": 1693,
      "leafChecks": 8,
      "small": 8,
      "large": 0,
      "coveredEvents": 3702
    },
    {
      "X": 65536,
      "focus": false,
      "B": 678,
      "T": 5424,
      "D": 1356,
      "K0": 339,
      "N": 5709,
      "events": 142413,
      "reaches": 0,
      "snapshots": 315,
      "pairs": 5546,
      "gridChecks": 16638,
      "signedChecks": 5546,
      "shallowChecks": 5546,
      "cutoffChecks": 5546,
      "weightedLen": 448074.478384774,
      "weightedClock": 381709.69662189885,
      "weightedShallow": 113054.65858458166,
      "weightedA1": 49165.62704992156,
      "weightedSigned": 157672.45742950923,
      "weightedDeepSigned": 104458.67338896329,
      "weightedShallowUpper": 1156364.1820088911,
      "weightedA1Upper": 1719060.620062786,
      "weightedGrid": 374435.35193283285,
      "weightError": 4752392.204091234,
      "deepPositive": 2991,
      "families": 7672,
      "candidates": 46572,
      "selected": 14923,
      "overlap": 3315,
      "coveredGain": 717088,
      "selectedGain": 913168,
      "outside": 160672,
      "distinguished": 21189,
      "leafChecks": 402,
      "small": 184,
      "large": 218,
      "coveredEvents": 51571
    },
    {
      "X": 65536,
      "focus": true,
      "B": 678,
      "T": 339,
      "D": 84,
      "K0": 339,
      "N": 5709,
      "events": 75430,
      "reaches": 2870,
      "snapshots": 3826,
      "pairs": 19882,
      "gridChecks": 59646,
      "signedChecks": 19882,
      "shallowChecks": 19882,
      "cutoffChecks": 19882,
      "weightedLen": 470588.14310131234,
      "weightedClock": 382645.86606884183,
      "weightedShallow": 227888.97466361494,
      "weightedA1": 71318.26556188872,
      "weightedSigned": 147351.79451816814,
      "weightedDeepSigned": 48906.50709341751,
      "weightedShallowUpper": 6381991.9873014195,
      "weightedA1Upper": 10091768.959462833,
      "weightedGrid": 367308.7905897266,
      "weightError": 31331840.703295104,
      "deepPositive": 2735,
      "families": 4425,
      "candidates": 14957,
      "selected": 6735,
      "overlap": 1608,
      "coveredGain": 226572,
      "selectedGain": 289412,
      "outside": 47226,
      "distinguished": 8820,
      "leafChecks": 84,
      "small": 70,
      "large": 14,
      "coveredEvents": 19434
    }
  ],
  "exhaustive": 32768,
  "dense": {
    "c": [
      {
        "l": 0,
        "r": 4
      },
      {
        "l": 3,
        "r": 7
      },
      {
        "l": 5,
        "r": 9
      },
      {
        "l": 8,
        "r": 10
      }
    ],
    "color": [
      0,
      1,
      0,
      1
    ]
  }
}
```

Next: bound SIGNED deep endpoint differences in (6) using actual deficit records and pair lifetimes, rather than discarding negative drift. For forward complements, seek a forcing cover or outside-gain supply bound beyond the extremely band-dominated class; in particular the direct corridor overlap controls prohibit simply summing all candidate blocks. Main and sibling branches unchanged.
