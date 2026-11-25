# Direct-arithmetic integration I: rare physical states and smoothed low-run transport halos

2026-11-26 JST. User requested continuation of the unified branch with independent direct-arithmetic results. Parent [3f982907](https://github.com/tara-sooo/A166944-Lean/blob/3f982907a4e6d875e48fcdd28dcb0897a8e593da/research/2026-11-26-min-unified-bidirectional-rank-age-survivor-cut.md). Independent source head [8798cf0d](https://github.com/tara-sooo/A166944-Lean/tree/8798cf0def95997805cc5e91a4a30cba6c84b68e), unchanged. Import the paper deductions in [discovery-only packing](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-discovery-word-packing.md), [mean-square smoothing](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-mean-square-barrier-smoothing.md) and [long low runs](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-low-run-tail.md). New paper deductions: all-mass rare-source and high-defect payments, plus smoothed low-run halo payments for BOTH forward pursuits and the backward birth tree; a static memberwise refinement of the current endpoint census. No change to original tags, source weights, masks or denominator. No proof of twin-prime infinitude or A166944; no Lean verification or novelty claim.

## 1. Frozen model and joint source capacity

Retain the parent dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, prime roots M in [X,2X), actual original completed adaptive MIN paths stopped at gain T or terminal. The horizon C is even, t is actual plateau arrival tick, d=2t-C>=0, root (2M-2,M+2), gains g=p-1<=B, waits w<=3g, total gain <H. No extrapolation past actual stopping. For rare states below use actual finite prefixes only. In the direct papers H denotes the current horizon, not the unified gain cap H.

Keep original grids P_j, P_max<=B^.25 and common averaging denominator, c_a=3(1+2/u^.25). In the joint kernel of [0bc6ab1](https://github.com/tara-sooo/A166944-Lean/blob/0bc6ab1b60f8f98ecfb11724e4d89be21acb04b0/research/2026-11-26-min-unified-joint-kernel-wait-episode.md) all forward energy is converted to clock units c_a D. The sum of exact retained ordered charges at one grid boundary K with a given original tag in either fixed role is <=c_a P. A tag crosses K at most once. Every subsequent exact mask only decreases these row/column sums. This property, rather than distinct projected cohort counts, is the sole transport assumption below. A charge eligible via either role is paid ONCE and assigned a qualifying role by a fixed rule. For any interval of possible source boundaries of length A, a given tag/role can receive at most c_a(A+P), because P times the count of grid multiples in a half-open interval is <=A+P. For a union of m intervals one may sum these capacities (overlaps only enlarge the bound). In all statements below add the two roles, not the two ledgers independently. All bounds survive averaging over the original grids.

## 2. Rare physical states: exact source and high-pursuit destination masks

Let D0=O(log^C X) for fixed C>0, L=floor(log^beta X), 1<beta<2, S=floor(a log X), 0<a<1, j=ceil(theta log X/log(S+1)), 0<theta<=1-a. Let A_X be the set of physical states (t,C) of original tags with 0<=d<=D0 and an actual subsequent prefix of at most L ticks discovering j distinct selected primes >S. Include roots, actual post-event states or actual pre-event arrivals as needed, never simulated continuation past a tag's stop. The state is specified uniquely by (C,d). Every possible tick defect F=d+3-6I has |F|<=D0+2L+3<=sqrt(C+1) eventually, so the adaptive cutoff in the direct theorem is automatic. The initial horizon spans an interval of length O(X). In the notation of the direct paper b=floor(log(D0+2L+3)/log(S+1))=O(1), P_S=product of odd primes <=S. Encode initial d, parity, small-prime residues, first discovery ticks and selected primes. The direct finite count is
    |A_X| <= (D0+2) binom(L,j) b^j [P_S+O(X)/(4(S+1)^j)].
A prime discovered at a specified tick fixes a residue of C modulo that prime. At all other ticks the least known firing prime must win or the tick must be quiet; unknown nonwinning primes need not be encoded. A word with an unrecorded winning prime is not a realization, so counting necessary CRT cylinders is an upper bound. PNT gives P_S=X^(a+o(1)), and hence
    |A_X| <= X^(1-(2-beta)theta+o(1)).                 (1)
It is legitimate for the set to be defined as a union over original recorded histories: distinct tags may contribute the same state, counted only once. No primality density of original tags is used in (1).

At a source crossing with original prehorizon C, gain <=B and post-state (v,J), pay the exact remaining joint charge whenever either original source member has a rare post-state. For each fixed rare state and fixed tag, its source event is unique if it exists. Its source boundaries lie in [J-B,J), so the joint charge is <=2 c_a (B+P) per rare state per tag (both roles). In total
    B_rare,source + c_a D_rare,source
       <= 2 c_a N |A_X| (B+P_max).                     (2)
This includes backward and both forward pursuits; no new denominator or multiplicity estimate is needed. A member may be classified using a prefix it actually completes even if other members with the same source state retire earlier. The mask only removes original charges.

For the original high forward pursuit L_h=ceil(B exp(1/tau)), tau>=1/log ell, the actual first-defect prehorizon E is before J+L_h. Its actual tagged arrival state (t,E), or its post-state (v,E+p-1), is an allowed destination key. Pay remaining high charge whose chosen actual destination is rare at either state. For each fixed rare destination and tag, the source K is in an interval of length L_h+2B ending at its horizon; a post-state can be a pre-state of the next event but the union of the two possible source intervals is contained in the same halo. By the role cap,
    c_a D_h,rare,dest <= 2 c_a N |A_X| (L_h+2B+P_max).  (3)
The high pursuit is B X^o(1); the low pursuit can be much longer and (3) is NOT asserted for it. Also (3) applies to a rare focal destination instead of the chosen side if the focal member is used for the payment. For a=.05, beta=1.1, theta=.8, exponent in (1) is .28. Thus (2) and (3) are O(NT X^(-.22+o(1))) and o(NT). These are full original mass payments even for huge merging populations.

The same source mask on the independent raw boundary-only route costs <=N |A_X|(B+P), since each original boundary atom weighs P; on the discounted boundary objective of [discounted boundary support](https://github.com/tara-sooo/A166944-Lean/blob/3f982907a4e6d875e48fcdd28dcb0897a8e593da/research/2026-11-26-min-unified-discounted-boundary-support.md) each atom weighs <=5P/4. Apply only to those exact atoms that remain under that route's own frozen masks.

## 3. Rapid A1 recovery as an actual source of rare states

For any completed recovery after an A1 event p>=47 (pre d+3<=p/5, adjusted post d-6I=2p), let the first return to d+3<=p occur within L ticks and use only labels <=R_rec. Restrict p=O(log^C X) and p>R_rec. Its initial poststate has d=2p+6I, within D0 after increasing its constant. Its recovery gain is >=p+3. The direct per-prime clock bound m_s<=1+floor((L+1)/s) and (s-1)m_s<L+s gives the following exact sufficient discovery condition:
    p+3 > C_S(L)+(j-1)(L+R_rec),
    C_S(L)=sum_(odd primes s<=S)(s-1)(1+floor((L+1)/s)).
Then the recovery post-A1 state is in A_X. For the above a,beta,theta take R_rec~.95 log X and p>=.86 L log X/loglog X, with p<=log^C X and C>beta+1. This satisfies the inequality for large X by PNT and lies below the total allowed clock capacity; no assertion of nonempty asymptotic population. The entire recovery has gain <=2L+D0 by nonnegative deficit, and actual clock <=L. Therefore all such completed recovery intervals, even overlapping on a tag, occupy at most N|A_X|L total clock. Their originating A1 waits cost <=2p each and have the same rare-state count. One may pay actual focal waits in these intervals directly using original source-cell assignment (unit row clock); no inference that all high/low residual pairs are such recoveries. Long, high-label, or unfinished recoveries are not covered. The original direct example 0.68 exponent at balanced cutoff .5 is not enough for the B-sized destination halo; this is why a larger cutoff and theta were chosen.

## 4. Smoothed low-run halos, including actual forward defects and backward births

Use the direct horizon-barrier period Q=product of odd primes <=R (not a unified grid P). In even horizon coordinate z=C/2 the allowed barrier residues are z mod p in {0,...,(p-3)/2} for every odd prime p<=R. No p<=R event strictly crosses a barrier. Let f be its normalized indicator, f_l its l-point moving average, V_R the direct Fourier mean-square parameter:
    sigma_l^2=mean_Q (f_l-1)^2 <=4 V_R/l,   1<=l<=Q,
    V_R/Q=exp(-(2c0+o(1))pi(R)), c0=log(pi/2).
Here pi(R) denotes prime count. On each original tag, take maximal consecutive runs with selected labels <=R (include truncated runs at original endpoints), and keep those of gain >=4l. Their half-open gain intervals are disjoint and contain no barrier. The direct zero-window count gives for any original tag of total gain G:
    G_long <=4(G/2+Q) sigma_l^2 <=16(H/2+Q)V_R/l,
    m_long <= G_long/(4l).                             (4)
Thus the actual original waits on these runs cost <=3 G_long. The imported bound is per tag, not a claim about statistically independent trajectories.

A new use of (4) is to control charges transported TO these runs, not merely the waits in them. Suppose a chosen destination lies in a long-run interval [C_1,C_2), and on the same original tag the source grid K lies at distance <=A on its earlier side (or later side, for backward transport). Its possible sources lie in the one-sided halo [C_1-A,C_2) (or [C_1,C_2+A)). Pay all exact charges with such destination, assigning qualifying tag/role once. By Section 1,
    W_halo <= 2 c_a sum_tags [G_long+(A+P_max)m_long]
           <= 32 c_a N(H/2+Q)(V_R/l)
                         (1+(A+P_max)/(4l)).          (5)
This is a union-of-intervals capacity, not the per-destination cap times every event; arbitrary overlap of halos is harmless. The same bound covers a source atom lying inside the run by A=0. For a forward first defect use actual prehorizon E in the run on the chosen original tag and A=L_sector+B+O(1). It is immaterial whether the source or destination label exceeds R. The low pursuit of 0bc6ab1 is O(H) uniformly; the high pursuit is O(B ell). For backward charge use the original actual first-meeting horizon C_V, on either participating original tag, and A=H+O(1): the original later source K is on that tag, K>=C_V and its total gain is <H. The point C_V need not itself be a nonunit event on the waiting member. Apply (5) to low and high with their own cutoffs, and to backward, with overlaps paid once.

Explicit nontrivial scales: for the high sector let Q be the largest odd primorial <=B; for the low and backward sectors let Q be the largest odd primorial <=H. Write Z=B or H respectively, R the largest factor of Q, k=pi(R) and l=floor(Q exp(-c0 k/2)). By PNT and the next-prime bound Q>=Z/O(log Z), R=Theta(log Z), k=Theta(log Z/loglog Z). Then l->infinity, l<=Q, l=o(Z); V_R/l=exp(-(3c0/2+o(1))k); and A+P_max=O(Z ell+Z), so
    (V_R/l)(1+(A+P_max)/(4l))
       <= exp(-(c0+o(1))k) times a fixed polylog(Z)
       =o(1).
In (5) H/2+Q=O(T). Consequently all these halo payments cost o(NT). In the high sector, the run threshold is SUB-B (B exp(-Omega(u/ell)) up to polynomial factors), although the pursuit length exceeds B. In the low/backward sector, threshold is sub-H. This improvement follows from squared denominator l^2 in the halo term, not an assumption that A<=l. No claim that short low runs or all low-label defects can be deleted. The boundary-only and discounted objectives also permit paying raw atoms in long runs at A=0 by the corresponding atom cap, with their own masks.

## 5. Exact endpoint rank census refinement

Take the parent endpoint-survivor sets Q_r, original induced tree, actual first birth V, original incoming groups, and all original ages and ranks unchanged. For each individual member i at that birth, determine from its OWN original trajectory whether C_V lies in a long low run using the backward choice of R,l above. If so set its birth eligibility interval I_i(V) empty. Otherwise keep the old interval. A pair with either such member was payable in the exact backward clock by (5), before endpoint freezing. The mark is static for a tag/birth, independent of K, slab or partner. Thus the parent's sorted-branch census (equations 6 and 7) applies verbatim with these smaller intervals; denominator, actual endpoint members, historical ranks and actual incoming branch masses are NOT changed. The old freezing error applies to the remaining exact measure (all old upper bounds still apply). Let U_end,3 and U_rank,3 be the resulting relaxed envelopes, no larger than U_end,2 and U_rank,2 on their original domains. The exact backward mask, not an assumed small change in the relaxed integral, justifies this refinement. On the other two backward envelopes retain their old upper bounds, or intersect them with corresponding valid static restrictions.

Let D_l', D_h' denote the exact remaining forward energies after the above new applicable masks; preserve the original sector normalization. Under finitely many twins the previous sufficient inequality now reads
    NT/2-o(NT) <= c_a min(U_ind,U_cont,U_end,3,U_rank,3)
                       +(3+o(1))(D_l'+D_h').
Hence liminf of the bracketed normalized sum <1/6 suffices as before. This is a genuine integration of the direct arithmetic deductions into the same source measure; it proves no strict constant contraction. The separate boundary-only threshold 1/6 and discounted threshold 1/4 remain valid with the additional appropriate exact boundary masks, not with arbitrary transported clock deletions.

## 6. Finite audit and limitations

Standalone source min_unified_direct_arithmetic_transport_audit.mjs, execute with Node: node research/min_unified_direct_arithmetic_transport_audit.mjs 1024 4096 16384. In this session its exact function ran in the ECMAScript tool runtime (not a separate Node process). Actual prime-root adaptive completed MIN trajectories, literal parity GCD check at X1024, actual short continuation prefixes and CRT-code reconstruction, per-prime clock caps, actual long barrier-free run intervals and zero-window variance, original projected source cohorts at P=6,30,210. Finite unit-cap joint ordered pair kernel P/n over original projected groups; same physical slot pairs use actual first meeting of occupied intervals, different slots compare actual first defects (including lag changes) and choose a nonperiodic side. Source roles checked jointly, every qualifying defect/birth halo checked and all paid amounts compared against finite cap. Finite R/l=(5,2),(7,4),(11,8), D0=10,S=3,L=8,j=2; finite pursuit and high sector substitutes. Not the analytic asymptotic parameter choices, not the full original cumulative exact kernel/masks, not an endpoint integral implementation. No test of the asymptotic sieve constants or strict final contraction. The finite gain-stop target and prime-root population differ in scale from the analytic one. Actual finite tests include nonzero rare and low-run masks where present. Full run results follow as JSON for reproducibility.

```json
[
  {
    "X": 1024,
    "focus": false,
    "N": 137,
    "T": 512,
    "B": 85,
    "evCount": 1118,
    "reaches": 0,
    "literal": 8272,
    "rare": 26,
    "rareBound": 59619,
    "codes": 15,
    "discChecks": 244,
    "spacing": 11,
    "clockChecks": 727,
    "summaries": [
      {
        "R": 5,
        "l": 2,
        "Q": 15,
        "sigma": 2.750000000000001,
        "zeros": 11,
        "longCount": 71,
        "longGain": 626,
        "barrierChecks": 878,
        "runChecks": 242,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 1414,
            "pairChecks": 4574,
            "defects": 1106,
            "births": 3382,
            "rareSource": 0,
            "rareDef": 16,
            "lowHigh": 26,
            "lowLow": 62.88636363636364,
            "lowBirth": 526.8813852813862
          },
          {
            "P": 30,
            "sourceAtoms": 274,
            "pairChecks": 922,
            "defects": 254,
            "births": 668,
            "rareSource": 0,
            "rareDef": 20,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 488.16666666666646
          },
          {
            "P": 210,
            "sourceAtoms": 46,
            "pairChecks": 176,
            "defects": 54,
            "births": 122,
            "rareSource": 0,
            "rareDef": 140,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 229.83333333333331
          }
        ]
      },
      {
        "R": 7,
        "l": 4,
        "Q": 105,
        "sigma": 3.374999999999999,
        "zeros": 81,
        "longCount": 41,
        "longGain": 842,
        "barrierChecks": 1280,
        "runChecks": 298,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 1414,
            "pairChecks": 4574,
            "defects": 1106,
            "births": 3382,
            "rareSource": 0,
            "rareDef": 16,
            "lowHigh": 26,
            "lowLow": 189.30714285714208,
            "lowBirth": 585.6528138528157
          },
          {
            "P": 30,
            "sourceAtoms": 274,
            "pairChecks": 922,
            "defects": 254,
            "births": 668,
            "rareSource": 0,
            "rareDef": 20,
            "lowHigh": 0,
            "lowLow": 337.2857142857143,
            "lowBirth": 621.6666666666661
          },
          {
            "P": 210,
            "sourceAtoms": 46,
            "pairChecks": 176,
            "defects": 54,
            "births": 122,
            "rareSource": 0,
            "rareDef": 140,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 285.83333333333337
          }
        ]
      },
      {
        "R": 11,
        "l": 8,
        "Q": 1155,
        "sigma": 3.8125000000000355,
        "zeros": 915,
        "longCount": 11,
        "longGain": 466,
        "barrierChecks": 1630,
        "runChecks": 156,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 1414,
            "pairChecks": 4574,
            "defects": 1106,
            "births": 3382,
            "rareSource": 0,
            "rareDef": 16,
            "lowHigh": 36,
            "lowLow": 48.00714285714285,
            "lowBirth": 200.77142857142843
          },
          {
            "P": 30,
            "sourceAtoms": 274,
            "pairChecks": 922,
            "defects": 254,
            "births": 668,
            "rareSource": 0,
            "rareDef": 20,
            "lowHigh": 30,
            "lowLow": 90.28571428571428,
            "lowBirth": 203.8571428571428
          },
          {
            "P": 210,
            "sourceAtoms": 46,
            "pairChecks": 176,
            "defects": 54,
            "births": 122,
            "rareSource": 0,
            "rareDef": 140,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 0
          }
        ]
      }
    ]
  },
  {
    "X": 4096,
    "focus": false,
    "N": 464,
    "T": 1360,
    "B": 170,
    "evCount": 7448,
    "reaches": 0,
    "literal": 0,
    "rare": 77,
    "rareBound": 208236,
    "codes": 25,
    "discChecks": 1124,
    "spacing": 52,
    "clockChecks": 3780,
    "summaries": [
      {
        "R": 5,
        "l": 2,
        "Q": 15,
        "sigma": 2.750000000000001,
        "zeros": 11,
        "longCount": 523,
        "longGain": 4786,
        "barrierChecks": 5706,
        "runChecks": 1870,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 14257,
            "pairChecks": 102784,
            "defects": 37814,
            "births": 61618,
            "rareSource": 874.857142857117,
            "rareDef": 151.02857142857235,
            "lowHigh": 2595.3980685980596,
            "lowLow": 1158.5381595991792,
            "lowBirth": 4496.735033475498
          },
          {
            "P": 30,
            "sourceAtoms": 2834,
            "pairChecks": 20724,
            "defects": 7458,
            "births": 12534,
            "rareSource": 1161.4285714285702,
            "rareDef": 241.71428571428567,
            "lowHigh": 2871.101481851497,
            "lowLow": 164.28571428571425,
            "lowBirth": 4204.895320365907
          },
          {
            "P": 210,
            "sourceAtoms": 404,
            "pairChecks": 3250,
            "defects": 1100,
            "births": 1930,
            "rareSource": 0,
            "rareDef": 0,
            "lowHigh": 540,
            "lowLow": 0,
            "lowBirth": 3739.727272727273
          }
        ]
      },
      {
        "R": 7,
        "l": 4,
        "Q": 105,
        "sigma": 3.374999999999999,
        "zeros": 81,
        "longCount": 215,
        "longGain": 4616,
        "barrierChecks": 8346,
        "runChecks": 1663,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 14257,
            "pairChecks": 102784,
            "defects": 37814,
            "births": 61618,
            "rareSource": 874.857142857117,
            "rareDef": 151.02857142857235,
            "lowHigh": 677.0861471861388,
            "lowLow": 1503.363756986006,
            "lowBirth": 5927.2571219981855
          },
          {
            "P": 30,
            "sourceAtoms": 2834,
            "pairChecks": 20724,
            "defects": 7458,
            "births": 12534,
            "rareSource": 1161.4285714285702,
            "rareDef": 241.71428571428567,
            "lowHigh": 525.2467532467543,
            "lowLow": 1982.6785714285843,
            "lowBirth": 6195.551615051584
          },
          {
            "P": 210,
            "sourceAtoms": 404,
            "pairChecks": 3250,
            "defects": 1100,
            "births": 1930,
            "rareSource": 0,
            "rareDef": 0,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 5206.954545454544
          }
        ]
      },
      {
        "R": 11,
        "l": 8,
        "Q": 1155,
        "sigma": 3.8125000000000355,
        "zeros": 915,
        "longCount": 117,
        "longGain": 4822,
        "barrierChecks": 10651,
        "runChecks": 1592,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 14257,
            "pairChecks": 102784,
            "defects": 37814,
            "births": 61618,
            "rareSource": 874.857142857117,
            "rareDef": 151.02857142857235,
            "lowHigh": 469.61428571428814,
            "lowLow": 1329.9306019058051,
            "lowBirth": 4241.086113630677
          },
          {
            "P": 30,
            "sourceAtoms": 2834,
            "pairChecks": 20724,
            "defects": 7458,
            "births": 12534,
            "rareSource": 1161.4285714285702,
            "rareDef": 241.71428571428567,
            "lowHigh": 450.42857142857144,
            "lowLow": 1184.9783549783556,
            "lowBirth": 4284.2733932734145
          },
          {
            "P": 210,
            "sourceAtoms": 404,
            "pairChecks": 3250,
            "defects": 1100,
            "births": 1930,
            "rareSource": 0,
            "rareDef": 0,
            "lowHigh": 0,
            "lowLow": 735,
            "lowBirth": 4211.81818181818
          }
        ]
      }
    ]
  },
  {
    "X": 16384,
    "focus": true,
    "N": 1612,
    "T": 169,
    "B": 339,
    "evCount": 15668,
    "reaches": 841,
    "literal": 0,
    "rare": 292,
    "rareBound": 702870,
    "codes": 29,
    "discChecks": 3539,
    "spacing": 263,
    "clockChecks": 10913,
    "summaries": [
      {
        "R": 5,
        "l": 2,
        "Q": 15,
        "sigma": 2.750000000000001,
        "zeros": 11,
        "longCount": 936,
        "longGain": 8598,
        "barrierChecks": 11825,
        "runChecks": 3363,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 37144,
            "pairChecks": 107080,
            "defects": 12288,
            "births": 88448,
            "rareSource": 2085.6000000000163,
            "rareDef": 101.20000000000005,
            "lowHigh": 618.4571428571417,
            "lowLow": 1701.5642857142943,
            "lowBirth": 8703.128571428748
          },
          {
            "P": 30,
            "sourceAtoms": 7412,
            "pairChecks": 22066,
            "defects": 2676,
            "births": 18028,
            "rareSource": 2151.999999999997,
            "rareDef": 134,
            "lowHigh": 720.7857142857144,
            "lowLow": 568,
            "lowBirth": 8140.07142857144
          },
          {
            "P": 210,
            "sourceAtoms": 1019,
            "pairChecks": 2934,
            "defects": 214,
            "births": 2566,
            "rareSource": 2576,
            "rareDef": 105,
            "lowHigh": 453,
            "lowLow": 210,
            "lowBirth": 7264.166666666662
          }
        ]
      },
      {
        "R": 7,
        "l": 4,
        "Q": 105,
        "sigma": 3.374999999999999,
        "zeros": 81,
        "longCount": 520,
        "longGain": 10782,
        "barrierChecks": 17315,
        "runChecks": 3831,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 37144,
            "pairChecks": 107080,
            "defects": 12288,
            "births": 88448,
            "rareSource": 2085.6000000000163,
            "rareDef": 101.20000000000005,
            "lowHigh": 278.00000000000017,
            "lowLow": 2394.4523809523835,
            "lowBirth": 12010.182683983287
          },
          {
            "P": 30,
            "sourceAtoms": 7412,
            "pairChecks": 22066,
            "defects": 2676,
            "births": 18028,
            "rareSource": 2151.999999999997,
            "rareDef": 134,
            "lowHigh": 298.3333333333333,
            "lowLow": 3622.785714285709,
            "lowBirth": 12487.515151515134
          },
          {
            "P": 210,
            "sourceAtoms": 1019,
            "pairChecks": 2934,
            "defects": 214,
            "births": 2566,
            "rareSource": 2576,
            "rareDef": 105,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 9693.30303030303
          }
        ]
      },
      {
        "R": 11,
        "l": 8,
        "Q": 1155,
        "sigma": 3.8125000000000355,
        "zeros": 915,
        "longCount": 154,
        "longGain": 6554,
        "barrierChecks": 21270,
        "runChecks": 2199,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 37144,
            "pairChecks": 107080,
            "defects": 12288,
            "births": 88448,
            "rareSource": 2085.6000000000163,
            "rareDef": 101.20000000000005,
            "lowHigh": 78,
            "lowLow": 1106.8666666666722,
            "lowBirth": 5270.028571428415
          },
          {
            "P": 30,
            "sourceAtoms": 7412,
            "pairChecks": 22066,
            "defects": 2676,
            "births": 18028,
            "rareSource": 2151.999999999997,
            "rareDef": 134,
            "lowHigh": 87.5,
            "lowLow": 1239.3809523809537,
            "lowBirth": 5421.904761904775
          },
          {
            "P": 210,
            "sourceAtoms": 1019,
            "pairChecks": 2934,
            "defects": 214,
            "births": 2566,
            "rareSource": 2576,
            "rareDef": 105,
            "lowHigh": 0,
            "lowLow": 0,
            "lowBirth": 4691.666666666666
          }
        ]
      }
    ]
  },
  {
    "X": 16384,
    "focus": false,
    "N": 1612,
    "T": 2712,
    "B": 339,
    "evCount": 33736,
    "reaches": 0,
    "literal": 0,
    "rare": 304,
    "rareBound": 756273,
    "codes": 29,
    "discChecks": 5163,
    "spacing": 275,
    "clockChecks": 15519,
    "summaries": [
      {
        "R": 5,
        "l": 2,
        "Q": 15,
        "sigma": 2.750000000000001,
        "zeros": 11,
        "longCount": 2174,
        "longGain": 19362,
        "barrierChecks": 25142,
        "runChecks": 7507,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 81420,
            "pairChecks": 839644,
            "defects": 232810,
            "births": 596324,
            "rareSource": 8205.891575089146,
            "rareDef": 1281.9369408369137,
            "lowHigh": 6854.221832612055,
            "lowLow": 4757.883663015358,
            "lowBirth": 18063.99058268466
          },
          {
            "P": 30,
            "sourceAtoms": 16265,
            "pairChecks": 172998,
            "defects": 49940,
            "births": 120264,
            "rareSource": 8285.76923076868,
            "rareDef": 1344.7088744588666,
            "lowHigh": 7360.656890331962,
            "lowLow": 1799.5357209287001,
            "lowBirth": 17470.40233528712
          },
          {
            "P": 210,
            "sourceAtoms": 2229,
            "pairChecks": 22494,
            "defects": 5320,
            "births": 16456,
            "rareSource": 10378.33333333341,
            "rareDef": 1376.6388888888898,
            "lowHigh": 6641.625,
            "lowLow": 1109.2941176470558,
            "lowBirth": 15746.735528462934
          }
        ]
      },
      {
        "R": 7,
        "l": 4,
        "Q": 105,
        "sigma": 3.374999999999999,
        "zeros": 81,
        "longCount": 1145,
        "longGain": 24208,
        "barrierChecks": 37082,
        "runChecks": 8669,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 81420,
            "pairChecks": 839644,
            "defects": 232810,
            "births": 596324,
            "rareSource": 8205.891575089146,
            "rareDef": 1281.9369408369137,
            "lowHigh": 5064.493502249967,
            "lowLow": 8012.770057562549,
            "lowBirth": 29244.47728500785
          },
          {
            "P": 30,
            "sourceAtoms": 16265,
            "pairChecks": 172998,
            "defects": 49940,
            "births": 120264,
            "rareSource": 8285.76923076868,
            "rareDef": 1344.7088744588666,
            "lowHigh": 4994.751697949041,
            "lowLow": 10940.974334737717,
            "lowBirth": 29313.873249296004
          },
          {
            "P": 210,
            "sourceAtoms": 2229,
            "pairChecks": 22494,
            "defects": 5320,
            "births": 16456,
            "rareSource": 10378.33333333341,
            "rareDef": 1376.6388888888898,
            "lowHigh": 2975.0730994152227,
            "lowLow": 0,
            "lowBirth": 25191.99523049527
          }
        ]
      },
      {
        "R": 11,
        "l": 8,
        "Q": 1155,
        "sigma": 3.8125000000000355,
        "zeros": 915,
        "longCount": 360,
        "longGain": 15438,
        "barrierChecks": 46717,
        "runChecks": 5199,
        "rows": [
          {
            "P": 6,
            "sourceAtoms": 81420,
            "pairChecks": 839644,
            "defects": 232810,
            "births": 596324,
            "rareSource": 8205.891575089146,
            "rareDef": 1281.9369408369137,
            "lowHigh": 2259.590219243169,
            "lowLow": 4092.1202678071454,
            "lowBirth": 17215.817028476908
          },
          {
            "P": 30,
            "sourceAtoms": 16265,
            "pairChecks": 172998,
            "defects": 49940,
            "births": 120264,
            "rareSource": 8285.76923076868,
            "rareDef": 1344.7088744588666,
            "lowHigh": 2345.77394218687,
            "lowLow": 4447.631124473077,
            "lowBirth": 17049.371790316705
          },
          {
            "P": 210,
            "sourceAtoms": 2229,
            "pairChecks": 22494,
            "defects": 5320,
            "births": 16456,
            "rareSource": 10378.33333333341,
            "rareDef": 1376.6388888888898,
            "lowHigh": 962.1818181818179,
            "lowLow": 0,
            "lowBirth": 14627.273919078456
          }
        ]
      }
    ]
  }
]
```

## 7. Next step

Find a forcing implication for the remaining exact high/low defects or backward pairs into one of the rare/halo populations, or a complementary quantitative recovery category. In particular split actual A1 demands by the first downward crossing of their level intervals, retain direct precursor-exclusion and long-run capacities, and transport to actual recovery providers under the same joint row/column budget. Need handle all high-label relays and unfinished intervals and quantify a positive constant share (or a direct supply contradiction). Neither the rarity of fast completed recoveries nor smallness of long low runs alone forces the sufficient constant inequality. Do not combine unweighted single-ray lower counts with weighted aggregate upper counts without a proved same-population transfer. Main and direct branch unchanged; no Lean files changed.
