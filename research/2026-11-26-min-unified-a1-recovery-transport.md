# Direct-arithmetic integration II: A1 recovery age, weighted transport and precursor compression

2026-11-26 JST. Parent [b1e071f](https://github.com/tara-sooo/A166944-Lean/commit/b1e071f5043baa2f47595d8eabe4e58fd4dffe6d). Independent direct head read at 45ecde8c329833dc2b33f16ab4af3694c99a51c6; use [precursor exclusion](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-precursor-exclusion.md), [deficit barriers](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-deficit-barriers.md), and earlier mean-square horizon smoothing. New paper deductions: exact transport of original joint A1 source charge to actual lower-level recovery providers, scale-relative age payment (no assumption of completed whole recoveries), exclusion of RESET precursors for marked lower levels, compression of short low-label supply to high-multiplier far-B precursors, effective-mass payments on projected provider keys. All other source charges and old masks unchanged. No strict constant contraction, Lean compilation, or novelty claim.

## 1. Original charge on an A1 event

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime-root original completed adaptive MIN tags. Pre/post horizon C,J=C+p-1, wait w, ordinary deficit d=2t-C, post d'=d+2w-(p-1), side I, adjusted D=d'-6I. Total gain per tag <H. Original grids P<=P_max<=B^.25 and common averaging denominator, clock-unit joint row/column cap c_a P at each original source atom, c_a=3(1+2/u^.25). Retain all masks through b1e071f. Let Y=ceil(B^.5); only marks p>=Y, p>=47, pre x=d+3<=p/5 and adjusted post D=2p (A1). For large X every such event crosses each grid since p-1>P_max.

For remaining exact joint source fractions with at least one original source member executing such an A1 crossing, assign each fraction to one qualifying original tag/mark by fixed priority (focal first). This is a partition. Since the mark atoms are in [C,J) and joint row/column caps hold, charge q_i(P)<=2 c_a(p-1+P)<=4 c_a p. This covers A1 focal waits since their own crossing is their right witness, but not every charge at an A1 crossing is its own wait. No such per-p bound is assumed for arbitrary first-defect DESTINATIONS. More generally use any nonnegative mark charge q_i<=kappa p_i with bounded constant kappa (e.g. 4c_a). For separate raw/discounted boundary routes their original atom caps and their own masks suffice. No transport between tags.

## 2. Exact demand assignment and scale-relative age bound

For every marked event i of label p_i place continuous lower interval (p_i/5,p_i] in x=d+3 space on its own tag at post-horizon J_i. Assign each level y to the FIRST later actual completed downward event with x'<y<=x, or leave pending at actual endpoint. Endpoints of measure zero immaterial. Assignment independent of q_i, including zero-weight marks. At fixed y at most one pending mark, since a new A1 crossing at y requires x<=p_i/5<y and old pending level has already crossed downward. Every pending level <=current x, total pending length <=B; length assigned to one downward provider f <=Delta_f=(d-d')_+.

Give mark interval uniform density lambda_i(P)=5 q_i(P)/(4p_i)<=Lambda=5 kappa/4. Split EACH original charge fraction in proportions of lengths of its assigned levels. Exact partition including endpoint-pending fractions. Per actual tagged provider, load <=Lambda Delta_f, irrespective of pairs, grids or overlapping recovery intervals. Pending cost <=Lambda NB=o(NT).

Age of completed assignment a=C_f-J_i>=0 (provider PRE-horizon minus mark POST-horizon). Integrate pending occupation of each level over [J_i,C_f), dividing by p_i. At fixed horizon z pending intervals have disjoint interiors, y<=p_i implies 1/p_i<=1/y, and Y/5<=y<=B. Hence
    sum_i integral_(pending i at z) lambda_i/p_i dy <= Lambda log(5B/Y).
Integrate over gained horizon length <H:
    sum_(completed assignments) integral lambda_i (C_f-J_i)/p_i dy
         <= Lambda H log(5B/Y).                       (1)
Pending ages through actual terminal can also be included. Integration in gained horizon coordinate, not wall clock; plateaus have zero measure, no fictitious continuation. For A>=1, total completed charge with a>=A p_i satisfies
    W_age <= Lambda N H log(5B/Y)/A.                   (2)
Take A=u², giving O(NT/u)=o(NT). This pays arbitrary long or overlapping recovery LEVEL assignments, not a uniform bound on the whole first return to x<=p. Every remaining assignment lies within p_i u² of its mark. Since K is a strict source boundary of that mark, C_f-K<=p_i(1+u²). Any replacement by an earlier actual precursor inherits this upper bound. Unconditional on finite twins.

## 3. Arithmetic restrictions on actual providers

Nonreset decreasing label s>=5 has x'=2hs+6I+3 for integer h>=1, and x/x'<3/2 (direct deficit-barrier geometry). If it pays y in (p_i/5,p_i], then x'<y<=x and
    2p_i/15 < x' < p_i,  s < p_i/2,
    hs > p_i/15 - 9/2.                                (3)
Provider cannot be near in direct fixed square-band sense: later near label >=(1-eta)p_i with eta<=1/4 eventually, so nonreset post-x>=1.5p_i+3. RESET provider has x'<=9, x>=y>p_i/5 and drop <=s-3, thus s>p_i/5-9. Label3 never decreases x. A reset provider therefore has comparable or larger label.

## 4. Long low runs and short-run precursor compression

Take Q largest odd primorial <=Y, R largest factor, k=pi(R), c0=log(pi/2), l=floor(Q exp(-c0 k/2)). As b1e071f, V_R/Q=exp(-(2c0+o(1))k), V_R/l=o(1), Q=O(Y), and u^K l/Y->0 for fixed K. In particular R<Y/5-9, 4l<Y/5, u l=o(Y). Per tag maximal low runs (labels <=R), long if gain >=4l. Total long gain <=16(H/2+Q)V_R/l. All direct assignments to long runs cost <=Lambda times total long gain, thus o(NT). No halo factor: exact mark weight already partitioned into bounded-density provider loads. Low RESET providers impossible by Section 3.

Short paying low run of gain L<4l has preceding high event f, label q, post-x x0. It exists and occurs at or after original mark (initial run cannot pay mark p_i>R). f is NOT reset: paying level y>Y/5>9 still pending after f, whereas reset post-x<=9. If f is the mark it is A1 and not RESET. Earlier precursor exclusion rules out f A1 or near nonreset because run would need gain >p_i/5 or >p_i/2 respectively. Thus f is far high nonreset B, q>R. For each indirectly paid level,
    y <= x0 < y+L < y+4l,
    q < (p_i+4l)/2,  h_f q > p_i/10-9/2.              (4)
First inequality uses pending level at run start and maximum decrease <=L; strict upper bound follows from x'<y. Adjusted D gives others. This removes the high-reset alternative entirely. Charge remaining low-run matched weight to f, unique precursor per run, capacity <=Lambda L<4Lambda l. If q>=u l, per-precursor load <=4Lambda q/u; all such precursors distinct on tag and sum q<=1.5H, so O(NT/u). Remaining short-run supply goes only to
    R < q < u l,  h_f > (Y/10-9/2)/(u l) -> infinity. (5)
Actual precursor strictly after mark (A1 exclusion) and at or before provider; inherits age bound. No bounded-multiplier claim for all low runs.

## 5. Projected thin supply payments

Average over unchanged grids AFTER partitions. Group remaining direct high providers by actual projected (C,s) and compressed remaining low relay loads by (C,q), disjoint charge sectors (an event can receive both distinct charges). Let n(C,s) be full original tag count executing event. Direct load A_dir(C,s)<=Lambda s n(C,s); relay A_rel(C,q)<=4Lambda l n(C,q). Effective masses a_dir=A_dir/(Lambda s), a_rel=A_rel/(4Lambda l) <=full original population. For fixed odd prime s possible C in O(X) range satisfy s|(C+-1), giving O(X/s) keys; no roughness assumed for a negative-drift provider.

Pay direct key if a_dir<=H/(u ell² s), relay key if a_rel<=H/(u ell² l). Fractional effective mass, not physical synchronous population. Each sector total payment
    O(sum_(odd prime s<=B) (X/s) H/(u ell²))
      = O(XH/(u ell))=o(NT),                          (6)
by prime reciprocal sum O(ell). Pull payments back through exact partition (only paid FRACTIONS of each mark removed); no renormalization. Old exact masks stay frozen.

Remaining exact A1 source clock conserved as sum of two supply ledgers:
(i) actual high decreasing provider s>R, reset or nonreset satisfying Section 3, effective mass >H/(u ell² s);
(ii) far high B precursor R<q<u l with growing multiplier (5), effective mass >H/(u ell² l), actual short low-run recovery. All levels within relative gain age p_i u². Combined discarded amount o(NT) including pending, age, long low runs, large precursors and thin keys. Same-population necessary supply condition, not a bound on remaining heavy supply or claim positive proportion of all residual originates at A1.

## 6. Updated sufficient objective and missing step

Let B_old,D_l,D_h be current exact residuals after b1e071f, split each into A1 source and complement by fixed priority, forward units c_a D. Let W_A1,heavy be combined weighted supply ledgers, W_other exact complementary joint source clock. Under finitely many twins the inherited lower bound and partition give
    NT/2-o(NT) <= W_other + W_A1,heavy.                 (7)
Thus liminf normalized sum <1/2 suffices; dividing by c_a gives threshold 1/6. This replaces A1 portion, not an additional term atop whole old backward endpoint envelope. To combine with endpoint census remove relevant source fractions first or give separate valid upper bound on complement. All earlier sufficient criteria remain. No strict asymptotic improvement established. Next: exploit (3)-(5) and mass cuts by true time/deficit rank at providers and fixed-cut competing-clock exclusions; establish positive share of A1 sources or estimate complementary non-A1. Upper bound for A1-heavy alone does not control full residual.

## 7. Reproducible finite audit

Source min_unified_a1_recovery_transport_audit.mjs. Run node research/min_unified_a1_recovery_transport_audit.mjs 4096 16384 65536. Exact function executed in ECMAScript tool runtime (not separate Node process). Actual prime-root gain-stopped MIN, literal gcd oracle at X4096. Fivefold integer deficit-level intervals and integer densities 1,2,3 (scaled units; arbitrary bounded mark weights, not full cumulative joint kernel). Tests disjoint pending intervals, exact weighted partition, normalized occupation area, age inequality, reset/nonreset scale, precursor type and gain caps, per-provider/per-run capacities, individual thin-load proxies. Finite substitute cutoffs/ratios, no asymptotic Fourier or projected-key sieve test. Known canonical four-event CRT witness from direct precursor audit reconstructed, actual BigInt GCD replay; not new root nor asserted prime root. Relative horizon coordinates preserve ages, near evaluated on true BigInt horizon. R=7000 witness control exceeds no-low-reset bound but all its paying providers nonreset. First run's coverage assertion failed because the large-precursor control used an age threshold that paid its charge earlier; increased that control's age allowance and reran; positive long-low, short-relay, large-precursor and late sectors all exercised. No Lean compilation. Results:
```json
{
  "runs": [
    {
      "X": 4096,
      "B": 170,
      "T": 1360,
      "N": 464,
      "events": 7448,
      "reaches": 0,
      "literal": 76866,
      "outputs": [
        {
          "config": {
            "R": 3,
            "Y": 67,
            "l": 2,
            "A": 1,
            "M": 4
          },
          "marks": 31,
          "total": 25532,
          "paid": 0,
          "pending": 25532,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 0,
          "nonreset": 0,
          "thinDirect": 0,
          "thinRelay": 0,
          "longGain": 0,
          "area": 27792,
          "matches": 0
        },
        {
          "config": {
            "R": 5,
            "Y": 77,
            "l": 3,
            "A": 2,
            "M": 16
          },
          "marks": 24,
          "total": 21100,
          "paid": 0,
          "pending": 21100,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 0,
          "nonreset": 0,
          "thinDirect": 0,
          "thinRelay": 0,
          "longGain": 894,
          "area": 13368,
          "matches": 0
        },
        {
          "config": {
            "R": 7,
            "Y": 87,
            "l": 4,
            "A": 4,
            "M": 4
          },
          "marks": 17,
          "total": 15948,
          "paid": 0,
          "pending": 15948,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 0,
          "nonreset": 0,
          "thinDirect": 0,
          "thinRelay": 0,
          "longGain": 4616,
          "area": 8184,
          "matches": 0
        }
      ]
    },
    {
      "X": 16384,
      "B": 339,
      "T": 2712,
      "N": 1612,
      "events": 33736,
      "reaches": 0,
      "literal": 0,
      "outputs": [
        {
          "config": {
            "R": 3,
            "Y": 67,
            "l": 2,
            "A": 1,
            "M": 4
          },
          "marks": 203,
          "total": 275640,
          "paid": 14048,
          "pending": 261592,
          "late": 10236,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 3812,
          "nonreset": 0,
          "thinDirect": 824,
          "thinRelay": 0,
          "longGain": 0,
          "area": 648256,
          "matches": 18
        },
        {
          "config": {
            "R": 5,
            "Y": 77,
            "l": 3,
            "A": 2,
            "M": 16
          },
          "marks": 167,
          "total": 253076,
          "paid": 8792,
          "pending": 244284,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 8792,
          "nonreset": 0,
          "thinDirect": 824,
          "thinRelay": 0,
          "longGain": 3170,
          "area": 531024,
          "matches": 9
        },
        {
          "config": {
            "R": 7,
            "Y": 87,
            "l": 4,
            "A": 4,
            "M": 4
          },
          "marks": 145,
          "total": 235168,
          "paid": 824,
          "pending": 234344,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 824,
          "nonreset": 0,
          "thinDirect": 824,
          "thinRelay": 0,
          "longGain": 24208,
          "area": 467544,
          "matches": 1
        }
      ]
    },
    {
      "X": 65536,
      "B": 678,
      "T": 5424,
      "N": 5709,
      "events": 142413,
      "reaches": 0,
      "literal": 0,
      "outputs": [
        {
          "config": {
            "R": 3,
            "Y": 67,
            "l": 2,
            "A": 1,
            "M": 4
          },
          "marks": 1226,
          "total": 2663816,
          "paid": 95956,
          "pending": 2567860,
          "late": 27240,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 68716,
          "nonreset": 0,
          "thinDirect": 50056,
          "thinRelay": 0,
          "longGain": 0,
          "area": 6014520,
          "matches": 101
        },
        {
          "config": {
            "R": 5,
            "Y": 77,
            "l": 3,
            "A": 2,
            "M": 16
          },
          "marks": 1139,
          "total": 2607308,
          "paid": 75460,
          "pending": 2531848,
          "late": 11776,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 63684,
          "nonreset": 0,
          "thinDirect": 50136,
          "thinRelay": 0,
          "longGain": 13518,
          "area": 5640696,
          "matches": 72
        },
        {
          "config": {
            "R": 7,
            "Y": 87,
            "l": 4,
            "A": 4,
            "M": 4
          },
          "marks": 1065,
          "total": 2549620,
          "paid": 49508,
          "pending": 2500112,
          "late": 0,
          "long": 0,
          "largeRelay": 0,
          "shortRelay": 0,
          "reset": 49508,
          "nonreset": 0,
          "thinDirect": 40152,
          "thinRelay": 0,
          "longGain": 99944,
          "area": 5406032,
          "matches": 39
        }
      ]
    }
  ],
  "witness": [
    {
      "config": {
        "R": 7,
        "Y": 10000,
        "l": 400,
        "A": 4,
        "M": 4
      },
      "marks": 1,
      "total": 80312,
      "paid": 10140,
      "pending": 70172,
      "late": 0,
      "long": 0,
      "largeRelay": 40,
      "shortRelay": 0,
      "reset": 0,
      "nonreset": 10100,
      "thinDirect": 10100,
      "thinRelay": 0,
      "longGain": 0,
      "area": 89801.96354218548,
      "matches": 2
    },
    {
      "config": {
        "R": 7,
        "Y": 10000,
        "l": 400,
        "A": 4,
        "M": 16
      },
      "marks": 1,
      "total": 80312,
      "paid": 10140,
      "pending": 70172,
      "late": 0,
      "long": 0,
      "largeRelay": 0,
      "shortRelay": 40,
      "reset": 0,
      "nonreset": 10100,
      "thinDirect": 10100,
      "thinRelay": 40,
      "longGain": 0,
      "area": 89801.96354218548,
      "matches": 2
    },
    {
      "config": {
        "R": 7000,
        "Y": 10000,
        "l": 400,
        "A": 4,
        "M": 16
      },
      "marks": 1,
      "total": 80312,
      "paid": 10140,
      "pending": 70172,
      "late": 0,
      "long": 10140,
      "largeRelay": 0,
      "shortRelay": 0,
      "reset": 0,
      "nonreset": 0,
      "thinDirect": 0,
      "thinRelay": 0,
      "longGain": 11226,
      "area": 89801.96354218548,
      "matches": 2
    },
    {
      "config": {
        "R": 7,
        "Y": 10000,
        "l": 400,
        "A": 0.1,
        "M": 16
      },
      "marks": 1,
      "total": 80312,
      "paid": 10140,
      "pending": 70172,
      "late": 10140,
      "long": 0,
      "largeRelay": 0,
      "shortRelay": 0,
      "reset": 0,
      "nonreset": 0,
      "thinDirect": 0,
      "thinRelay": 0,
      "longGain": 0,
      "area": 89801.96354218548,
      "matches": 2
    }
  ],
  "rootDigits": 12979,
  "ticks": 15140,
  "crt": 13028,
  "word": [
    10039,
    6709,
    4513,
    7
  ],
  "deficits": [
    20078,
    13418,
    9026,
    9022
  ]
}
```
