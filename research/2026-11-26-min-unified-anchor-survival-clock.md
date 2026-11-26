# Integration XII: whole-birth monotone survival ledger and terminal deficit credit

2026-11-26 JST. Parent [75d4251](https://github.com/tara-sooo/A166944-Lean/commit/75d4251d7759d5eafa486348ad65e22397829c8c); independent direct head 789c806704496fc394ac04ee0efbd886d247943a (new repeated-cofactor/near-flat audit, no new paper theorem imported; latest paper 074993c). New paper result: an alternative whole-continuation upper envelope for selected true birth sectors, with a monotone survival denominator and exact signed integration by parts across all previous endpoint slabs; keep actual terminal deficit on the left of the global clock inequality. This is an alternative bound on FULL backward clock of a static birth sector, not a deletion of its positive envelope while retaining its negative credit. No strict final contraction or Lean verification.

## 1. Actual total clock, not its weakened lower bound

Keep original prime-root ensemble, original finite stopping rules, original joint assigned-clock partition and all proved o(NT) payments. X,B,u,ell,N,T,H,c_a,b0 as before. Let F_i be actual terminal horizon, G_i=F_i-C0_i and d_i(F_i) actual ordinary terminal deficit. Set G_all=sum G_i, Z_all=sum d_i(F_i). Exact clock balance
    2 W_all=G_all+Z_all-6N.
The old joint kernel (joint-kernel-wait-episode, signed-endpoint-clock-cover) partitions the ACTUAL clock except for the already bounded discarded parts; its lower bound NT/2-o(NT) merely used G_all>=NT and Z_all>=0 under finite twins. Retain W_all itself, hence under finite twins the stronger necessary inequality
    NT+Z_all-o(NT) <= U+P_giant-L_*+2c_a(D_l+D_h).
Thus liminf [U+P_giant-L_*+6(D_l+D_h)-Z_all]/(NT)<1 suffices. Z_all>=0, bounded O(NH) by actual deficit envelope. No claim Z_all is asymptotically positive fraction or that the new criterion holds. This change is available also on all older full-clock upper routes; it is not available on a route that only decomposes a different normalized target charge. Use actual terminal values, not hypothetical extension after stopping.

## 2. Select a static birth sector, unfreeze the entire nonnegative clock

Let S be any set of original true birth vertices and allowed ordered pairs of their actual incoming branches (e.g. both historical masses >=a0 from XI, or exactly one). Membership in S is independent of slab, source and transported witness. Classify every original admissible backward pair by its true first meeting and branches, and split the full endpoint envelope into S and complement. Use integration V: W_B^S<= sum_(slabs,Q,i,j in S) integral_(I_ij) omega_i(x)/b_Q + o(NT). Unfreeze the entire NONNEGATIVE integral to actual max(b0,b(x)) denominator by integration VI's absolute turnover estimate (omega<=3). Cost O(DN(log N+2))=o(NT); same proof with density 3 rather than 5. Do not unfreeze only the positive drift and then subtract a differently normalized negative part. Use one common error budget across the partition.

Drop slab-dependent gates and induced endpoint ranks within S only for this alternative upper envelope. Retain all static age, true birth, branch and individual E_i eligibility bounds that are interval constraints. If a predicate is not an interval constraint, omit it as an upper relaxation. For each pair from S the union of original intervals is then contained in one interval [a_ij,b_ij) within the actual common life: a=max of individual lower limits, fixed birth age and any static rank-age limits, b=min of individual upper limits, including actual terminal strips F_i-h,F_j-h. Empty if static test fails or b<=a. Fixed age >>B ensures shared completed event path, including clock interpolation, throughout it. No extra copies of a pair when crossing slab boundaries. This enlarges support, but yields whole-life cancellation. This alternative can be computed using only birth branch lists, original tag histories and actual terminal horizons.

## 3. Monotone denominator by an actual anchor

At a true birth V=(t,J) all members that continue have a common deterministic trajectory after their meeting, even if the meeting is inside a wait. Let A_V be a fixed actual completed departure anchor on this trajectory, before the earliest permitted a_ij in this birth sector, at/after first common completed departure. One may choose first completed exit crossing J+a_min/2, where a_min>>B is a common old lower birth-age bound; if not reached by any members no eligible pairs. Use FULL original physical exit cohort at anchor, including later joiners up to this anchor. For x in a permitted interval define
    s_V(x)=# {i in full anchor cohort: F_i>x},
    f_V(x)=1/max(b0,s_V(x)).
For every x beyond anchor, every such surviving tag is actually in the physical crossing slot at x. Conversely new entrants after anchor need not belong to anchor cohort. So s_V(x)<=b(x) and f_V(x)>=1/max(b0,b(x)), with f_V nondecreasing right-continuous step function. Denominator does not use retired histories. Using only full members at birth that survive to x is another valid but generally weaker denominator; anchor choice can improve because it includes actual early arrivals after birth. If desired use lower guaranteed F_i>=C0_i+T under finite twins for a root-only lower survival count (a weaker upper envelope); unconditional actual F_i stronger. No interpolation of the discrete mass needed.

Define
    V_S^anchor=sum_(V,i,j in S) integral_[a,b) omega_V(x) f_V(x) dx.
Then W_B^S<= V_S^anchor+o(NT). All contributing pairs share same actual interpolated deficit d_V(x) on the permitted intervals. This is a sum over static first-birth keys; even when different birth anchors have overlapping histories, each original pair counted once. The envelope can nevertheless overestimate the full clock when denominators at several births omit different later entrants. It is not claimed smaller than earlier frozen envelope; take the minimum.

## 4. Exact signed integration by parts across slabs

For an eligible pair I=[a,b), set
    U_I=integral_I f_V(x) dx,
    E_I=f_V(b-) d_V(b), A_I=f_V(a) d_V(a),
    R_I=sum_(a<x<b at anchor retirements) d_V(x) [f_V(x)-f_V(x-)].
All three E_I,A_I,R_I nonnegative. Endpoints use right limit at a and left limit at b; no extra jump at boundaries. Since d continuous piecewise affine and omega=(1+d')/2, exact Stieltjes identity
    2 integral_I omega_V f_V = U_I+E_I-A_I-R_I.            (1)
This telescopes across ALL old endpoint slabs for that pair; neither an independent positive part on each slab nor the absolute variation of d is needed. Retirements increase reciprocal weights, so their term is a NEGATIVE credit. No assumption that deficit returns to 0 or is globally monotone. In particular 2V_S^anchor<=sum(U_I+E_I-A_I) and even stronger with R retained. A uniform estimate replacing d at retirement by zero is unnecessary. One may compute U_I by a prefix integral of f_V, and R_I by prefix sums over ordered actual anchor retirement horizons; endpoint d from common trajectory. Hence after one ray and one retirement sequence per birth, a pair evaluation uses endpoint lookups, not separate future paths for every slab. This is an exact formula for the new relaxed envelope, not equality for original W_B. Can further use pairwise clipped deficit with explicit boundary low term, but ordinary deficit gives exact identity and avoids summing a fresh per-pair clipping error.

Let U_S^a,E_S^a,A_S^a,R_S^a be sums. Conditional on finite twins, if b=min(F_i,F_j)-h as in original eligibility interval (otherwise retain actual b), d(b)<=d_i(F_i)+h for earlier terminating member by d'>=-1. This bounds the terminal endpoint contribution without reconstructing late trajectory, but no claim E_S^a<=Z_all: ordered pairs and varying anchor denominators prohibit that simple inference. Initial deficit A and retirement R are genuine additional deductions relative to dropping them in THIS anchor bound, not necessarily a strict improvement over every previous signed bound.

## 5. Sparse giant merger and attachment census

Use XI a0=X^(1-o(1)) and full retirement-preserving historical forest. Let S_g be all true birth branch pairs with both incoming historical sizes>=a0, not only the subset receiving concentrated positive witnesses. Then at most N/a0=X^o(1) actual vertices in S_g. The entire S_g upper bound uses at most this many common continuations, each length <=H up to B fringe (not the number of pairs or slabs). They may overlap, but actual pair partition and full denominators remain fixed. One can bound the integrand numerator exactly by sum over eligible distinct original branch groups: for group j at x, n_j(x)=count of original members with own static interval containing x; if static pair-specific rank test is not separable omit it; include only giant groups. Ordered count = (sum n_j)^2-sum n_j². Thus V_S^anchor=integral omega f_V times this count if chosen relaxed static constraints factorize (otherwise this is an upper bound). Sweep all individual interval starts/ends and anchor retirements, plus actual gain knots, with this formula. No pair enumeration necessary for factorized relaxation.

For one giant history and one small history, small member has unique such first attachment in full historical forest. At fixed x after birth, use its actual individual eligibility and the eligible giant branch union size n_g(x), divided by max(b0,s_V(x)). Both orientations give bound 2 times that share (<=2 because giant branch members reaching x belong to anchor cohort). The anchor weight does not introduce ghost histories. Aggregate unique attached tags, or evaluate all birth pair integrals with (1). This route offers separate explicit upper bounds for sparse giant merger and attachment sectors. A0 alone is not a bound on total load of their continuing rays. In particular even if count of giant merger vertices is subpolynomial, sum over them may still carry macroscopic mass.

## 6. Combined criterion, valid signed accounting

For any fixed S as above, keep old signed endpoint/positive transport upper on complement only. Denote U_bar, P_bar, L_bar the complementary baseline, surviving positive and original net negative. All previously proved positive deletions/normalized transport can be restricted to complement; auxiliary coupling may still sample all units of original bin, its marginal is dominated, so costs do not increase. Negative credit in S is NOT subtracted again when using V_S^anchor. Then
    NT+Z_all-o(NT)
       <= U_bar+P_bar-L_bar + U_S^a+E_S^a-A_S^a-R_S^a
                                +2c_a(D_l+D_h).
Strict normalized liminf of RHS minus Z_all (with 2c_a replaced by 6) below 1 suffices. One can take minimum of old signed S and whole-anchor S bound, since both upper the SAME full backward subclock. This provides an actual alternative scalar inequality, not a new necessary witness alone. S may be chosen as static sparse giant birth sector, or any static union of birth keys. Cannot classify S using only transported positive witnesses and use whole-clock negative credit; that would mix two different measures.

No upper estimate achieving the strict final margin has been obtained. Direct latest audit checks higher-dimensional cofactor clusters and near-flat same-stratum return spacing, but no new asymptotic result from those checks used here. Next: evaluate the new signed criterion with full original source masks, especially whether anchor initial/retirement credits and terminal deficit are comparable with old positive residual; use actual repeated cofactor arithmetic for certified common rays.

## 7. Diagnostics

Run node research/min_unified_anchor_survival_clock_audit.mjs 4096 16384 65536. Exact ECMAScript execution. Six actual prime-root finite controls. True births reconstructed by all actual time-plateau arrivals and wait overlap, distinct branch groups, unique pair keys globally. Finite age/terminal strip and full anchor chosen before eligible pair interval, not cumulative masks. All birth-member survival and later-anchor denominators integrated on actual event/retirement breakpoints; compare to full physical denominator, verify monotone reciprocal, exact Stieltjes balance, retirement debit, and conservation across finite slabs. Finite physical group threshold3 diagnostics not full retired historical forest or asymptotic a0. Exact terminal deficit balance. No full original grid ledger or Lean verification. Results:
```json
[
  {
    "X": 4096,
    "focus": false,
    "N": 464,
    "events": 7448,
    "allGain": 86486,
    "allWait": 76866,
    "terminal": 70030,
    "births": 270,
    "pairs": 924,
    "eligible": 748,
    "anchors": 748,
    "anchorGains": 100,
    "retireSteps": 0,
    "strictCredit": 0,
    "actualClock": 35093.035134361955,
    "birthClock": 56284.90377625098,
    "anchorClock": 53064.160351504586,
    "horizon": 60540.190997891135,
    "startDebit": 21278.10225888704,
    "endCredit": 66866.2319640048,
    "retirementDebit": 0,
    "sparseBirths": 122,
    "sparseClock": 1992.4398001998013,
    "attachClock": 21977.313468151926,
    "maxBirth": 15,
    "slabChecks": 7283
  },
  {
    "X": 4096,
    "focus": true,
    "N": 464,
    "events": 3292,
    "allGain": 36420,
    "allWait": 32624,
    "terminal": 31612,
    "births": 236,
    "pairs": 418,
    "eligible": 197,
    "anchors": 197,
    "anchorGains": 15,
    "retireSteps": 21,
    "strictCredit": 19,
    "actualClock": 4551.556906426476,
    "birthClock": 5901.893958379588,
    "anchorClock": 5812.784841570472,
    "horizon": 6793.266666666667,
    "startDebit": 5547.68340010831,
    "endCredit": 10654.453083249246,
    "retirementDebit": 274.4666666666667,
    "sparseBirths": 0,
    "sparseClock": 0,
    "attachClock": 561.4859266685615,
    "maxBirth": 6,
    "slabChecks": 572
  },
  {
    "X": 16384,
    "focus": false,
    "N": 1612,
    "events": 33736,
    "allGain": 491744,
    "allWait": 421120,
    "terminal": 360168,
    "births": 1020,
    "pairs": 5133,
    "eligible": 4028,
    "anchors": 4028,
    "anchorGains": 980,
    "retireSteps": 0,
    "strictCredit": 0,
    "actualClock": 196888.70580024619,
    "birthClock": 351724.60627785476,
    "anchorClock": 320215.87712634885,
    "horizon": 390763.10933332774,
    "startDebit": 132919.64198903344,
    "endCredit": 382588.2869084033,
    "retirementDebit": 0,
    "sparseBirths": 1422,
    "sparseClock": 37419.88232363702,
    "attachClock": 138535.12785885358,
    "maxBirth": 28,
    "slabChecks": 34262
  },
  {
    "X": 16384,
    "focus": true,
    "N": 1612,
    "events": 15668,
    "allGain": 225120,
    "allWait": 198237,
    "terminal": 181026,
    "births": 940,
    "pairs": 2344,
    "eligible": 1103,
    "anchors": 1103,
    "anchorGains": 199,
    "retireSteps": 246,
    "strictCredit": 178,
    "actualClock": 35225.55129188747,
    "birthClock": 54870.94236943185,
    "anchorClock": 51533.182310047836,
    "horizon": 59151.88571428576,
    "startDebit": 33519.43362351594,
    "endCredit": 81750.11252932558,
    "retirementDebit": 4316.200000000003,
    "sparseBirths": 37,
    "sparseClock": 279.92557950716525,
    "attachClock": 14291.548683608728,
    "maxBirth": 11,
    "slabChecks": 3357
  },
  {
    "X": 65536,
    "focus": false,
    "N": 5709,
    "events": 142413,
    "allGain": 3032084,
    "allWait": 2576721,
    "terminal": 2155612,
    "births": 3904,
    "pairs": 25399,
    "eligible": 18388,
    "anchors": 18388,
    "anchorGains": 5585,
    "retireSteps": 0,
    "strictCredit": 0,
    "actualClock": 1242523.383616775,
    "birthClock": 2514325.2469298984,
    "anchorClock": 2256181.2101758444,
    "horizon": 2662974.6957512633,
    "startDebit": 788478.4408067011,
    "endCredit": 2637866.165407276,
    "retirementDebit": 0,
    "sparseBirths": 8019,
    "sparseClock": 443105.2249763278,
    "attachClock": 955292.9100837145,
    "maxBirth": 42,
    "slabChecks": 143731
  },
  {
    "X": 65536,
    "focus": true,
    "N": 5709,
    "events": 75430,
    "allGain": 1535468,
    "allWait": 1300986,
    "terminal": 1100758,
    "births": 3678,
    "pairs": 12490,
    "eligible": 5842,
    "anchors": 5842,
    "anchorGains": 1470,
    "retireSteps": 1889,
    "strictCredit": 1168,
    "actualClock": 287720.20358455746,
    "birthClock": 500933.15130038455,
    "anchorClock": 455025.1937681086,
    "horizon": 555126.5829059798,
    "startDebit": 232699.22336143805,
    "endCredit": 616516.7233962727,
    "retirementDebit": 28893.695404595466,
    "sparseBirths": 645,
    "sparseClock": 17346.132864247196,
    "attachClock": 159070.60847140042,
    "maxBirth": 20,
    "slabChecks": 17695
  }
]
```
Main/direct unchanged.
