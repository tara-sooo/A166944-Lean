# Direct-arithmetic integration III: live cohort turnover, unique cut ancestry and physical supply census

2026-11-26 JST. Parent [c8cdf7e](https://github.com/tara-sooo/A166944-Lean/commit/c8cdf7eab35652703530a98294fd7baa3ef841aa); direct head [8ad273f](https://github.com/tara-sooo/A166944-Lean/blob/8ad273f39d01c792926c9cfeabcfe9f2e481fc5c/research/2026-11-26-min-direct-event-discovery-and-log-scale-recovery.md) read, including its log-scale two-label recovery obstruction. Import [fixed cut clock supply](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-cut-clock-supply.md) and factor phases. New paper deductions: retirement-aware total live-cohort log variation O(N log N), all-mass deletion of unstable short A1 transport, unique dominant marked ancestor at every retained physical supply slot and deficit level, transport of exact backward pairs (not just scalar clock) with the provider's physical denominator, phase-specific cut census with strengthened long-wait mass thresholds. No strict final contraction, Lean verification or novelty claim.

## 1. Frozen setup and completed physical slots

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), original prime roots, original completed MIN histories stopped at gain T or twin. No extrapolation. Keep old grids and common average, c_a=3(1+2/u^.25), original joint row/column clock cap c_a P, original A1 transport and every old mask. A1 marks p>=Y=ceil(B^.5) with pre x=d+3<=p/5 and adjusted post D=2p. Exact mark clock q_i(P)<=kappa p, density lambda_i(P)=5q_i/(4p)<=Lambda. Each cut level y in (p/5,p] goes to first actual later downward event; c8cdf7e leaves direct high providers or short-low-run relay precursors and age a<C_mark_post+p u² (in distance notation C_destination-J_mark<p u²). Retain old thin projected cuts. All destinations below are these actual events on the same original tag.

A physical exit slot V=(C,p,n) is a completed event including true winning tick n and selected p. Let S_V be ALL original tags executing that slot, b_V=|S_V|. After V the next completed exit is unique for every member that continues (determinism of post state); those members stopping at V are retired forever. The successor may also receive members from other earlier slots or injected roots. Define for an edge V->W, r=|S_V intersect S_W|>0. This intersection is exactly the continuing members of V, since any member at V which continues must have this next completed exit. No tag is counted as continuing if retired. Thus r<=b_V,b_W. Distinct predecessor exit slots have disjoint continuing sets at W. A root with first exit W belongs to a new singleton entering W; roots with no exit do not enter. All claims refer to the original completed paths, not histories extended after terminal.

## 2. Total variation of live populations, including retirements

For each continuing tag across V->W assign
    v(V,W)=log(b_V/r)+log(b_W/r) >=0.
The first term records retirements, second mergers/injections. For each root tag at its first exit W record positive entry log b_W. Across each nonterminal V the total negative contribution is r log(b_V/r)<=b_V-r. Its right side is exactly number retiring at V; a slot with no successor contributes zero negative variation. Sum over distinct V, <=N. For every tag, signed sum of log ratios plus entry log b_first telescopes to log b_last<=log N. Hence over all active original tags:
    V_neg<=N, V_pos<=N log N+N, V_tot<=N(log N+2).       (1)
This does not require historical mass or artificially keeping retired members alive. It is stronger than controlling net log population change: equal starting and ending mass can hide substantial replacement. No factor number of other members or incoming edges.

For a contiguous chain on a tag from marked slot U to destination V, let v_i be sum of v along chain (not entry). Each elementary removal or addition of size a-b costs log(a/b), and all intermediate sizes are <=b_U exp(v_i) and <=b_V exp(v_i). Since a-b<=max(a,b)|log(a/b)|, sum of symmetric differences bounds the endpoint difference:
    |S_U symmetric_difference S_V|
       <= exp(v_i) v_i min(b_U,b_V).                  (2)
Also exp(-v_i)<=b_U/b_V<=exp(v_i). This proof uses the intermediate survivor set on every edge, not a presumed monotone active mass.

## 3. Relative-age transport yields stable live ancestry at o(NT) cost

Fix epsilon=u^(-1/2), or any epsilon->0 with B u³/epsilon=o(T). Pay each remaining original A1 fraction whose assigned physical destination V has v_i(U,V)>epsilon, measured on its own original tag. The mark-to-destination prehorizon distance <=p_i(1+u²)<=B(1+u²). For any fixed edge variation on that tag, all source marks whose interval uses that edge start within a backwards gain interval of length L=B(1+u²)+O(B). Their disjoint mark gain intervals fit in the interval enlarged by at most B. Since q_i<=kappa p_i<=1.5 kappa g_i, sum of q_i over such marks <=1.5 kappa(L+B). This bound holds even if a mark routes fractions to many different providers: integrate only the total exact mark charge, never multiply by number of cut levels. Charging variation by epsilon^{-1}, (1) gives
    W_unstable <= O(kappa (B u²+B) N(log N+2)/epsilon)
               = O(N B u³/epsilon)=o(NT).             (3)
Uniform on original grids, average unchanged. More precisely this applies to the union of direct and relay charges already partitioned in c8cdf7e, not two independent full source clocks. Source/endpoint retirement masks remain. For retained fractions let delta=epsilon exp(epsilon). Then |S_U intersect S_V|>=(1-delta) max(b_U,b_V), and both masses comparable within exp(epsilon). This is a statement about live ORIGINAL exit members, not historical components. Does not imply every individual path has stable mass at all times, only that unstable routed weight costs little.

## 4. Unique dominant marked ancestor at a physical supply slot and level

For fixed real y (endpoints measure zero) and physical direct provider V, each retained mark U has y pending just before V and first downward crossing at V. Every member of S_U intersect S_V shares the actual post-U continuation through V, so y has that same mark as its pending ancestor on that tag (unweighted assignment includes all eligible marks, independent of grid or source weights). For a relay precursor V the level is still pending immediately AFTER V and is paid within the ensuing short low run; all members in the intersection share the path at least through V, even if some retire before the later low event. Thus any two distinct possible U for the same V,y have disjoint intersections with S_V: a tag cannot have two pending marks at the same level. Direct and relay are incompatible at the same V,y on a shared member since direct crosses it down and relay leaves it pending. Each retained intersection has size >(1/2)b_V for large X by (2). Consequently there is at most ONE such U for the physical V,y, even across both ledgers and all grids. This is not uniqueness of the mark for the whole drop interval; the ancestor may change with y. It is an actual causal constraint even when two different high-mass marks coalesce at the same provider.

## 5. Preserve backward pair structure under transport

For backward source atoms the two original tags occupy the same physical source exit slot U, and old per ordered pair bound c_a P/b_U holds (including all masks). A1 mark is shared; fixed focal priority assigns charge. Sum its per-pair source atoms, divide uniformly over the 4p/5 interval. At each level original ordered pair density <=5c_a(p-1+P)/(4p b_U). For retained stable mark->V transport, pay any fraction whose partner does not execute V. Per focal tag there are at most delta b_U such partners for each y by (2); thus density paid <=(5c_a/4)(1+o(1))delta, integrated over its mark interval, then summed over original mark gains <=O(NT). Total O(delta NT)=o(NT). This is valid even if V varies with y, and partner may be retired; no independent per-provider re-normalization.

The surviving backward fractions now carry both original tags to the SAME actual physical direct provider or relay precursor, preserving their original true first meeting and ordered pair. At each physical V,y only one U by Section4, with b_U>=exp(-epsilon)b_V. Therefore per pair density <= (5c_a/4)(1+o(1)) exp(epsilon)/b_V, with the original grid denominator (same bound averaged). Direct pair clock can be integrated over the actual drop interval, length <=p_V-3. Relay pair clock over y lies in (x_V-4l,x_V] up to endpoints, length <=4l. For each provider one may now apply a true-birth rank census on the actual shared endpoint S_V to upper bound these backward A1 pair fractions; no assertion that all pairs in S_V are eligible. The source-age and root-order masks remain at the original source. Forward differing-slot pair charges are NOT asserted to share a provider; retain scalar role transport for them. This is a new exact pair-preserving reduction, not a claimed endpoint census contraction.

## 6. Fixed-cut physical-slot support and effective mass

At real y in (Y/5,B], put b=2 ceil((y-3)/2), the even ordinary-deficit cut. Ignore measure-zero endpoints if needed. For direct provider selected s>=5, side I, post adjusted d'-6I=2sh (h>=0 including reset), a downward crossing d'<b<=d forces
    h=floor((b-6I-1)/(2s)), r=b-6I-2sh in {2,4,...,s-3},
    1<=w<=(s-1-r)/2,
    C=1-2I+s(2I-2h-1) mod 4s,
    n=(C+s-1+2sh+6I)/2.
So for each C,s,I,y at most ONE physical slot n (regardless of different arrival ticks). The formulas in the direct fixed-cut note extend to h=0 by exactly the same divisibility and range proof. Negative h impossible at s>=5. For a relay precursor q>R the post x lies in [y,y+4l); the same horizon phase formula with its actual h holds, and at most 1+2l/q (or its integer ceiling) possible h, up to an absolute constant. Thus for each y the total support per s is O(X/s) direct slots; for q O((X/q)(1+l/q)) relay slots. This includes the full O(X) horizon domain, no product of independent phases.

For any candidate slot with minimum actual wait W, rival prime f!=s on side J, if C=1-2J mod f, its lag from n is the unique residue in [0,2f) satisfying
    lag = I-J mod2, 2 lag = (2h+1)s+6(I-J) mod f.
No lag 0 with f<s, nor 0<lag<W, is permitted. Applies to precursor itself even if it is not decreasing; for that case use actual h and W, not fixed-cut maximum wait. Actual original tags in the same exit may arrive at different ticks; split the load into wait>=W and wait<W using EACH receiving tag's actual wait. If W=B^xi with fixed 0<xi<1 (floor, e.g. xi=1/8), all odd primes <=W/2 are excluded from both C neighbors since eligible and smaller than selected label (w<=2s, use primes strictly <W/2). Uniform dimension-two upper sieve on the fixed progression of step4s gives
    O(X/(s u²)) direct long-wait slots per s at fixed y,
    O((X/(q u²))(1+l/q)) relay long-wait slots per q.
Proof: select z=floor(min(W/4,(X/s)^(1/40))) excluding 2,s (s>=W/2); log z >>u and parameter interval length O(X/s)>=constant B. Standard two-form sieve used in unified discounted-boundary support, slopes 4s invertible mod f, distinct roots; O((X/s)/log² z+z^8), latter absorbed. For each h relay progression same argument. This does not apply to short/unit waits; the direct source gives abstract saturation and actual finite canonical high-multiplier unit-wait controls. For polynomial W the prime reciprocal sum over s>=W/2..B is O_xi(1); unrestricted sum O(ell).

At a fixed y and V the exact averaged routed scalar load density divided by Lambda is an effective physical mass a(y,V)<=b_V: each original tag has at most one pending mark per level, and assigned density<=Lambda. For relay this remains true because all matching providers in the short run concern disjoint pending levels on that tag. For forward/backward combined use the exact original joint partition. Split long (actual wait>=W) and short independently, still bounded by b_V. Thin payments using the following thresholds are valid:
    direct short: a <= H/(u² ell² y);
    direct long:  a <= H/(ell y);
    relay short:  a <= H/(u² ell² y (1+l/q));
    relay long:   a <= H/(ell y (1+l/q)).
For short, sum support times threshold at fixed y over all labels <= O(XH/(u² ell y)); long same using sieve and reciprocal O(1), O(XH/(u² ell y)). Integrate y over [Y/5,B], log(5B/Y)=O(u): total O(XH/(u ell))=o(NT). Apply measurable cuts to exact level fractions after grid averaging, no denominator changed. Distinct slots, not projected cohorts; long-wait direct with s comparable y obtains an extra factor order u ell in threshold relative to earlier projected H/(u ell² s), but these are different masses (density per cut vs total per projected key), so no pointwise comparison or claim of covering all old keys. The new thresholds and old projected cuts may be intersected by successive payments. For the relay the factor 1+l/q accounts for all possible multipliers, not an assumed unique phase. Every retained slot-level has large live physical population AND its unique dominant mark has comparable population by (2). This is a same-population coupling between source and actual supply, not just a local prime-pair count.

## 7. Remaining objective and limitation

With all new payments the old sufficient inequality persists:
    NT/2-o(NT) <= W_other + W_A1,heavy,new.
Here W_other is unchanged exact complement of marked A1 source and W_A1,heavy,new is the exact remaining supply ledger, now with stable live cohorts, dominant mark at each physical cut, physical mass gates, and backward pairs preserved. One can intersect the backward A1 part with a true-birth census at each actual provider; this requires keeping the original source pair eligibility and weight, not adding the whole previous endpoint envelope again. This work does not show W_other small or prove any strict constant margin. Local unit-wait saturation and the direct log-scale two-label recovery family are reasons the long-wait sieve must not be applied to all suppliers. Next target: exploit dominant mark for local ancestor/descendant mass matching and bound the backward A1 birth pair census with root ranks at the physical supply endpoint; for direct/relay short waits exploit actual competing-clock word constraints or derive complementary non-A1 charge estimate. No main or sibling merge.

## 8. Finite diagnostics

Run node research/min_unified_a1_cohort_cut_audit.mjs 4096 16384 65536. Exact audit function executed in ECMAScript tool runtime, not separate Node process. Original finite prime-root trajectories and completed physical slots; distinct successor, actual intersection, total retirement-aware log variation; fixed-cut multiplier/residue for all decreasing events including reset, exact actual competitor lag check; level-weighted age and cohort variation partition, symmetric difference, dominant ancestor at fivefold integer levels when epsilon exp(epsilon)<1/2, partner-loss cap. Surrogate finite unweighted level allocation, not full cumulative joint ledger. Three finite parameter controls; combined late field includes low-run exclusions not just age. Abstract deterministic turnover example shows equal endpoint size with 50% replacement; abstract unit-wait saturation arithmetic checks (not canonical ancestry). No numerical sieve test, no actual full backward pair kernel rerun, no Lean compilation. Finite results:
```json
{
  "results": [
    {
      "X": 4096,
      "N": 464,
      "events": 7448,
      "slots": 3136,
      "negative": 0,
      "positive": 580.0587775602995,
      "fixed": 8836,
      "rivals": 2063,
      "unit": 407,
      "reset": 464,
      "controls": [
        {
          "cfg": {
            "Y": 47,
            "A": 4,
            "eps": 0.2,
            "R": 7,
            "l": 2
          },
          "dem": 15696,
          "pending": 15696,
          "matched": 0,
          "late": 0,
          "unstable": 0,
          "stable": 0,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 0,
          "cohortTests": 0,
          "changes": 0
        },
        {
          "cfg": {
            "Y": 67,
            "A": 16,
            "eps": 0.05,
            "R": 7,
            "l": 2
          },
          "dem": 11188,
          "pending": 11188,
          "matched": 0,
          "late": 0,
          "unstable": 0,
          "stable": 0,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 0,
          "cohortTests": 0,
          "changes": 0
        },
        {
          "cfg": {
            "Y": 47,
            "A": 16,
            "eps": 1,
            "R": 7,
            "l": 2
          },
          "dem": 15696,
          "pending": 15696,
          "matched": 0,
          "late": 0,
          "unstable": 0,
          "stable": 0,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 0,
          "cohortTests": 0,
          "changes": 0
        }
      ]
    },
    {
      "X": 16384,
      "N": 1612,
      "events": 33736,
      "slots": 11571,
      "negative": 0,
      "positive": 2419.121030950549,
      "fixed": 52335,
      "rivals": 10662,
      "unit": 1810,
      "reset": 1855,
      "controls": [
        {
          "cfg": {
            "Y": 47,
            "A": 4,
            "eps": 0.2,
            "R": 7,
            "l": 2
          },
          "dem": 119700,
          "pending": 113156,
          "matched": 6544,
          "late": 0,
          "unstable": 0,
          "stable": 6544,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 1872,
          "cohortTests": 22,
          "changes": 13
        },
        {
          "cfg": {
            "Y": 67,
            "A": 16,
            "eps": 0.05,
            "R": 7,
            "l": 2
          },
          "dem": 106756,
          "pending": 101060,
          "matched": 5696,
          "late": 0,
          "unstable": 2336,
          "stable": 3360,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 1368,
          "cohortTests": 18,
          "changes": 13
        },
        {
          "cfg": {
            "Y": 47,
            "A": 16,
            "eps": 1,
            "R": 7,
            "l": 2
          },
          "dem": 119700,
          "pending": 113156,
          "matched": 6544,
          "late": 0,
          "unstable": 0,
          "stable": 6544,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 0,
          "cohortTests": 22,
          "changes": 13
        }
      ]
    },
    {
      "X": 65536,
      "N": 5709,
      "events": 142413,
      "slots": 45090,
      "negative": 0,
      "positive": 10013.948674502686,
      "fixed": 309000,
      "rivals": 50249,
      "unit": 7930,
      "reset": 8727,
      "controls": [
        {
          "cfg": {
            "Y": 47,
            "A": 4,
            "eps": 0.2,
            "R": 7,
            "l": 2
          },
          "dem": 1113072,
          "pending": 1066468,
          "matched": 46604,
          "late": 1496,
          "unstable": 16264,
          "stable": 28844,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 14028,
          "cohortTests": 135,
          "changes": 62
        },
        {
          "cfg": {
            "Y": 67,
            "A": 16,
            "eps": 0.05,
            "R": 7,
            "l": 2
          },
          "dem": 1077216,
          "pending": 1039012,
          "matched": 38204,
          "late": 0,
          "unstable": 17676,
          "stable": 20528,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 9728,
          "cohortTests": 101,
          "changes": 45
        },
        {
          "cfg": {
            "Y": 47,
            "A": 16,
            "eps": 1,
            "R": 7,
            "l": 2
          },
          "dem": 1113072,
          "pending": 1066468,
          "matched": 46604,
          "late": 0,
          "unstable": 7124,
          "stable": 39480,
          "relays": 0,
          "partnerLoss": 0,
          "dominant": 0,
          "cohortTests": 141,
          "changes": 68
        }
      ]
    }
  ],
  "turnover": [
    {
      "a": 4,
      "b": 2,
      "r": 2,
      "v": 0.6931471805599453
    },
    {
      "a": 2,
      "b": 4,
      "r": 2,
      "v": 1.3862943611198906
    },
    {
      "a": 4,
      "b": 6,
      "r": 4,
      "v": 1.791759469228055
    },
    {
      "a": 6,
      "b": 5,
      "r": 5,
      "v": 1.9740810260220096
    }
  ],
  "abstract": 5071
}
```
