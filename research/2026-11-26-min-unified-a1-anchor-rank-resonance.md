# Direct-arithmetic integration IV: A1 arrival-anchor repair, half-density birth census and global resonance halos

2026-11-26 JST. Parent [850c7de](https://github.com/tara-sooo/A166944-Lean/commit/850c7de68dd312299b4e5827fe93ea0c8f86123f); latest independent direct head [5ca09ca](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-laminar-support-and-leaf-packing.md). Corrects a genuine logical gap in 850c7de Sections 4–5 (A1 depends on ARRIVAL even at the same exit). Repairs the claimed asymptotic uniqueness and pair-preserving transport at o(NT) cost, obtains a new factor-two improvement of the backward A1 pair-density coefficient and actual supply-endpoint induced rank census. Independently imports bounded-support minimal-return CRT packing for a new all-tag global small-resonance source halo deletion. No strict final contraction or Lean verification.

## 1. Correction: an A1 mark is not determined by an exit slot

Keep the original ensemble and notation X,B,u,ell,N,T,H and all valid previous masks. The physical exit U=(C,p,n) fixes post deficit and adjusted multiplier h, but the pre deficit d=2t-C varies with arrival t. Therefore the statement in 850c7de that all members of S_U intersect S_V share the same pending A1 mark is false as written. The premise h=1 does not imply d+3<=p/5. Finite prime-root counterexamples are recorded below, including C=8850,p=53,n=4507 where an arrival with d=30 is not A1 although the other five arrivals with d=6 are. This affects the dominant mark uniqueness, pair-preserving argument and conclusions requiring uniqueness, NOT the scalar weighted first-downcross partition, relative-age payment, provider geometry, projected thin cuts, fixed-cut arithmetic or the original exit-cohort variation inequality. Replace the affected arguments by Sections 2–4 of this note. No previously excluded charge is reinstated as a new population; retain the old valid deletions, and impose the additional exact payment below before using dominance. In particular the earlier exit-chain stability deletion is valid by itself and can remain frozen.

## 2. Expand the live exit DAG by genuine early-arrival nodes

For each physical slot U of label p>=Y=ceil(B^.5), p>=47, adjusted post h=1 and with at least one actual A1 member, define A_U subset S_U to consist of the actual A1 tags (arrival t<=floor((C+p/5-3)/2)). Let a_U=|A_U|, b_U=|S_U|. Introduce an auxiliary node with member set A_U immediately before the exit node S_U; an A1 tag traverses A_U then S_U, a non-A1 tag traverses S_U only. The node is an actual early waiting cohort among the ORIGINAL completed exits, not all abstract plateau starts. All A_U members share the same physical waiting state at the threshold tick. The auxiliary graph is acyclic (order by horizon and then anchor before exit), and every nonterminal node has a unique successor for its continuing tags. For an exit the next completed event and its arrival state are determined by the common poststate, so all continuing members either pass the next anchor or all bypass it. For an anchor all members pass its exit; no loss on that auxiliary edge. Distinct incoming continuing sets and new roots are disjoint; retired tags are not resurrected.

The exact old log-variation proof thus applies verbatim to the EXPANDED DAG. For each edge with member sizes b,c and continuing intersection r>0 give each continuing tag variation log(b/r)+log(c/r); entry log of first node's size. Sum of negative variation <=N because r log(b/r)<=b-r and each tag retires once. Signed sum telescopes to <=N log N; total variation <=N(log N+2). Anchor->exit term log(b_U/a_U) is now explicitly counted. For any chain from A_U to V with accumulated variation v,
    |A_U symmetric_difference S_V| <= exp(v) v min(a_U,b_V),
    exp(-v)<=a_U/b_V<=exp(v).
Also |S_U symmetric_difference S_V| obeys same bound for the subchain, and b_U/a_U<=exp(v). For v<=epsilon, delta=epsilon exp(epsilon), |A_U intersect S_V|>=(1-delta) max(a_U,b_V); relative to b_U the omitted fraction is <=1-(1-delta) exp(-epsilon)=O(epsilon).

Use exact mark weights and prior relative age (C_destination-J_mark<p u²). Delete transported fractions for which EXPANDED variation exceeds epsilon=u^(-1/2). Every edge used by a mark lies at gain distance at most O(Bu²) from that mark, including its anchor edge at the mark horizon. As before per tagged edge the disjoint original mark gain intervals and q_i<=kappa p bound the sum of all such mark charges by O(kappa B u²); no multiplicity over levels. Hence total extra payment
    O(N B u³/epsilon)=o(NT).
This covers the possible large expansion even in a single mark wait. After deletion all statements requiring an actual A1 majority are valid for the early cohort. No assumption that all exit arrivals satisfy A1.

## 3. Partial bijection at each level and sharp backward density

At fixed real level y and surviving direct or relay destination V, any surviving mark U has actual early intersection A_U intersect S_V of size >b_V/2. The path from U to V is deterministic; for every member of this intersection U is a REAL mark, with y pending until the same first downward crossing (or still pending at relay precursor). Distinct marked ancestors at that level have disjoint intersections. Thus U is unique at fixed (V,y). Conversely a fixed (U,y) has at most one retained actual provider V: the first later downward event in the deterministic suffix is fixed whenever completed, and if it is low-label, the preceding high precursor is fixed. Some members may retire or be removed by long-run masks, but cannot acquire a different retained destination. This holds across grids, direct and relay ledgers, after old masks; endpoints of measure zero ignored. We have a partial bijection between retained physical mark and supply keys at fixed y. In particular
    integral sum_(retained V at y) b_V dy
       <= exp(epsilon) sum_U (4p_U/5) a_U
       = O(NH).                                      (1)
No counting of the same U,y for multiple providers; no assumption every member supplies charge.

For backward pair fractions, original source exit U is shared, but either member may have been the actual A1 mark. Pay pairs whose other member is not in A_U intersect S_V using the old per-pair upper bound (5c_a/4)(1+o(1))/b_U per level: missing partner fraction O(epsilon), integrating over mark gains costs O(epsilon NT) even across both original roles. Both remaining tags are actual A1 and execute V, with original true birth preserved. Crucially the large-self witness q=p>=Y>>a P_max (a=u^.25) has no assigned nonself waits, by the old good-grid source rules. The original backward kernel coefficient is a_omega/(n_c b_U)<=1/b_U per pair. At this source all assigned focal clock at most its own actual wait w_i, even if an original focal tag was not A1 but used the same h=1 exit. The exact deficit identity gives
    w_i=(3p-1+6I-d_i)/2 <= (3p+5)/2.
Divide sum of original source atoms by the level interval length 4p/5. With c_a already in CLOCK units, the sharper density is
    per ordered pair <=5(3p+5)/(8p b_U)
                    <= (15/8+o(1))/b_V.             (2)
Use b_U/b_V within exp(epsilon), p>=Y->infinity. The prior bound was (5c_a/4)(1+o(1))/b_V=(15/4+o(1))/b_V. This is a genuine factor-two coefficient improvement for the A1 backward supply census, not a factor-two claim for all clock. The forward differing-slot transport remains scalar. No source renormalization, and no duplication over grids.

## 4. Actual supply-endpoint induced birth rank cut and census

At each retained (V,y), use all original S_V, including members with no remaining weight. In their actual induced true history tree, for older origin i<j (C0_i<C0_j) meeting first at node D require
    tail_i(D;S_V)>=rho b_V,   pre_j(D;S_V)>=rho b_V,
rho=ell^(-1/4). Counts include i or j, and use the ORIGINAL actual presence at the birth, not historical retired members. Along each fixed endpoint member its induced component grows monotonically through V (all members persist to V), including wait-jump births. Thus for each i the union of younger partners at births failing its tail condition has size <=rho b_V, by nested sets, and likewise for each j's older partners. At most 4 rho b_V² ordered pairs fail, including both orientations. By (1),(2) the exact pair fractions removed cost O(rho NT)=o(NT). This direct integration avoids any multiplication by the number of supply keys; even for short-run relay precursors where 4l may exceed q, (1) is valid. Origin interval prime sieve as in 3f98290 yields older root age at birth >=c rho b_V log(2+rho b_V), and younger origin >=C_V-H+c rho b_V log(2+rho b_V), when rho b_V tends to infinity (otherwise use the exact rank counts). Both inequalities use only actual endpoint lifetimes (<H), not the finite-twin ideal endpoint. Existing birth age, large original branch test and old pair eligibility stay at original mark/source atoms.

For each retained V,y, choose its unique mark U, intersect S_V with A_U, keep original actual incoming groups at each true birth D in induced tree. Define per-member eligibility from the OLD source-age and maturity intervals, at original source K in [C_U,J_U); can either retain K and sum exact original grid bounds or relax using existence of a K in the interval satisfying its own constraints, omitting unfactorized pair masks only for an upper envelope. Count ordered distinct pairs in different actual incoming groups, with at least one ORIGINAL large group as in 3f98290 and the induced tail/pre tests. Denote this relaxed count C(V,y). It may be evaluated by sorted origin prefix counts: for each older member passing tail, count strictly younger members passing prefix in other groups with the large-group condition, multiply by 2. Include every actual birth once. Define
    E_A1 = integral sum_(retained V at y) C(V,y)/b_V dy.
Then the exact new backward A1 clock is <=(15/8+o(1)) E_A1; same relaxed census with old density had coefficient 15/4+o(1). The marked gain ceiling from direct A1 gain-share (1924deb continuation) gives sum_U a_U p_U <= (5/14+o(1))NT, by truncating each tag after its last A1, including O(NB) endpoint and label-count correction (p>=Y). Thus E_A1 <= (2/7+o(1))NT, a crude bound; its coefficient alone gives 15/28>1/2, not a final strict margin. An independent exact row-clock upper bound <=NH/2+O(NB) follows from all actual A1 waits lying before the last mark, telescoping d at that endpoint. Do not add the entire old backward envelope to the new A1 census. Under finite twins:
    NT/2-o(NT) <= W_other + W_A1,forward + (15/8+o(1)) E_A1,
where other and forward are remaining exact original charge complements. The prior full sufficient criteria remain; no strict global contraction established.

## 5. Independent global small-leaf resonance halo deletion (both A1 and non-A1)

Import the laminar visible-repeat theorem from direct 5ca09ca. Fix k=24, Y0=B^.1, dyadic label bands [Z,2Z) covering [Y0,B] (first band may start at Y0/2), U0=floor(ell), and halo factor h0=u^.25. Consider every possible minimal visible-repeat leaf on a distinguished subset of primes in one band, at most k labels, with product of ACTUALLY USED distinct labels <=4H. Allow any outside labels with total gain E<=U0, no time or deficit restriction. This includes leaves from the old bounded-radical translated suffix (restrict distinguished labels to that band), regardless of which actual subset is chosen by each tag. Count a GLOBAL union of candidate start horizons with interval length O_k(h0 Z) covering the whole leaf and that additional halo on either side. Leaf includes first anchor and excludes second repeat, length <=2^k*2Z+U0. The global union is a relaxed arithmetic set, not a choice of overlapping blocks assumed disjoint.

For l>=3 actually used distinct labels, direct formula (10)/(11) gives number of candidate starts in O(X) horizon range
    <<_k (U0+1)^(2^(l-1)) [ (Z/log Z)^(l-1) + X/(Z (log Z)^(l-1)) ].
If such a leaf exists Z^l<=4H=O(X), hence this is <=X/(Z u^(l-1-o(1))) uniformly across bands. For l=2 the anchor p is larger than the single interior q, and direct delta_2=p-q, hence 0<p-q<=U0. The two-form upper sieve already proved in prime-root small-phase diamond (1a4005f2) bounds close prime pairs for fixed difference d<=U0 by O(Z log²(2+U0)/log² Z), uniformly. There are <=U0 gaps, O((U0+1)^2) outside gain vectors, constant signs and one CRT class modulo 2pq; candidate horizons O(1+X/Z²). So l=2 count <=X/(Z u^(2-o(1))) using Z²<=4H. l=1 impossible for E<=U0<Z-1 because consecutive same anchor needs E>=p-1. These bounds use only fixed k, so all powers of ell are u^o(1); k is fixed before the limit. The stronger two-label sieve is necessary for summing over O(u) bands, rather than the original l=2 single omitted-prime count.

For each band the total length of all candidate halos is <=X h0/u^(2-o(1)). Sum across O(u) bands, giving total length <=X/u^(.75-o(1))=o(T). A grid count of a halo interval adds at most P_max, absorbed by O(h0 Z) only for Z>=P_max; for smaller bands use the following actual-source event argument or restrict the joint grid mask to Z>=B^.25. Specifically for all bands the union can mark actual completed events whose gain intervals are wholly contained in a halo; waits <=3g, total marked gain on each tag <=union length, so all focal assigned waits of those events cost o(NT) even for nonself witnesses. For joint source atom masks with Z>=B^.25, grid overhead absorbed, per-tag per-role capacity c_a P gives total o(NT) for ALL pair charges whose original K lies inside a candidate halo (no requirement actual leaf visited). For smaller bands this unconditional atom-mask extension is NOT claimed; raw event clock deletion applies to actual contained focal events only. Raw/discounted boundary source atoms likewise have cap O(P) and can use the large-band grid mask. This is a universal arithmetic support deletion, not an independence or actual path sampling hypothesis. It pays the whole small-leaf actual gain interval and nearby events fully contained, not arbitrary long future defect/birth charges with destinations there. To pay a transported destination require its original K is inside the halo by a separate distance implication. Large outside-gain leaves still consume >U0 per disjoint leaf as in the direct theorem; no cover by bounded supports or strong enough outside-gain budget for all residual established. The two branches' new laminar and cohort methods thus give additional exact masks for general original source charge, including non-A1, without replacing the existing first-defect rule.

## 6. Finite diagnostics and status

Run node research/min_unified_a1_anchor_rank_resonance_audit.mjs 4096 16384 65536. Exact audit function executed in ECMAScript runtime, not a separate Node process. Six actual prime-root controls, standard finite targets and reach-focused target floor(B/2); actual early vs late membership, expanded unique successor and signed variation including retirement, actual first downward level assignments in fivefold integer units, early-anchor dominance and partial bijection, slot-level mass bound, partner loss, sampled true endpoint rank census using actual occupied intervals and poststates, actual comparable-support leaves in disjoint 24-event blocks (finite k<=5, E<=2, product<=4H). The level allocations here use actual direct downward destinations, not compressed relay or full cumulative joint masks. No numerical verification of the asymptotic sieve, no Lean compilation. The earlier exploratory run showed the concrete 5/6 mixed example at C8850,p53,n4507 and 3/21 example at C131670,p353,n66364; the final code records the most imbalanced example per run. All final controls passed. Results:
```json
[
  {
    "X": 4096,
    "focus": false,
    "T": 1360,
    "N": 464,
    "events": 7448,
    "reaches": 0,
    "slots": 3136,
    "early": 28,
    "mixed": 15,
    "mixedTags": 27,
    "mixedExample": {
      "C": 14940,
      "p": 67,
      "n": 7573,
      "early": 1,
      "full": 8,
      "arr": [
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 38,
          "d": 130,
          "a1": false
        },
        {
          "w": 100,
          "d": 6,
          "a1": true
        },
        {
          "w": 91,
          "d": 24,
          "a1": false
        }
      ]
    },
    "waitChecks": 111,
    "rawPairs": 256,
    "neg": 0,
    "pos": 580.0587775602985,
    "retired": 0,
    "controls": [
      {
        "eps": 0.1,
        "matched": 0,
        "unstable": 0,
        "stable": 0,
        "checks": 0,
        "dominant": 0,
        "partnerLoss": 0,
        "slotLevelMass": 0,
        "markLevelMass": 0,
        "rankCount": 0,
        "rankCut": 0
      },
      {
        "eps": 0.25,
        "matched": 0,
        "unstable": 0,
        "stable": 0,
        "checks": 0,
        "dominant": 0,
        "partnerLoss": 0,
        "slotLevelMass": 0,
        "markLevelMass": 0,
        "rankCount": 0,
        "rankCut": 0
      }
    ],
    "leafChecks": 164,
    "smallLeaves": 2,
    "twoLeaves": 2,
    "smallLeafExamples": [
      {
        "Z": 8,
        "C": 9348,
        "end": 9372,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 8,
        "C": 12936,
        "end": 12960,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      }
    ]
  },
  {
    "X": 4096,
    "focus": true,
    "T": 85,
    "N": 464,
    "events": 3292,
    "reaches": 276,
    "slots": 2278,
    "early": 27,
    "mixed": 12,
    "mixedTags": 17,
    "mixedExample": {
      "C": 10560,
      "p": 59,
      "n": 5371,
      "early": 1,
      "full": 4,
      "arr": [
        {
          "w": 73,
          "d": 36,
          "a1": false
        },
        {
          "w": 73,
          "d": 36,
          "a1": false
        },
        {
          "w": 85,
          "d": 12,
          "a1": false
        },
        {
          "w": 88,
          "d": 6,
          "a1": true
        }
      ]
    },
    "waitChecks": 60,
    "rawPairs": 109,
    "neg": 76.03692625960774,
    "pos": 386.74369328910194,
    "retired": 110,
    "controls": [
      {
        "eps": 0.1,
        "matched": 0,
        "unstable": 0,
        "stable": 0,
        "checks": 0,
        "dominant": 0,
        "partnerLoss": 0,
        "slotLevelMass": 0,
        "markLevelMass": 0,
        "rankCount": 0,
        "rankCut": 0
      },
      {
        "eps": 0.25,
        "matched": 0,
        "unstable": 0,
        "stable": 0,
        "checks": 0,
        "dominant": 0,
        "partnerLoss": 0,
        "slotLevelMass": 0,
        "markLevelMass": 0,
        "rankCount": 0,
        "rankCut": 0
      }
    ],
    "leafChecks": 19,
    "smallLeaves": 2,
    "twoLeaves": 2,
    "smallLeafExamples": [
      {
        "Z": 8,
        "C": 12936,
        "end": 12960,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 16,
        "C": 12990,
        "end": 13050,
        "E": 2,
        "labels": [
          31,
          29
        ],
        "w": [
          31,
          29,
          31
        ]
      }
    ]
  },
  {
    "X": 16384,
    "focus": false,
    "T": 2712,
    "N": 1612,
    "events": 33736,
    "reaches": 0,
    "slots": 11571,
    "early": 127,
    "mixed": 73,
    "mixedTags": 160,
    "mixedExample": {
      "C": 64218,
      "p": 149,
      "n": 32335,
      "early": 1,
      "full": 22,
      "arr": [
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        },
        {
          "w": 90,
          "d": 272,
          "a1": false
        }
      ]
    },
    "waitChecks": 565,
    "rawPairs": 1753,
    "neg": 0,
    "pos": 2419.1210309505564,
    "retired": 0,
    "controls": [
      {
        "eps": 0.1,
        "matched": 6544,
        "unstable": 4992,
        "stable": 1552,
        "checks": 6,
        "dominant": 916,
        "partnerLoss": 0,
        "slotLevelMass": 1552,
        "markLevelMass": 1552,
        "rankCount": 6,
        "rankCut": 0
      },
      {
        "eps": 0.25,
        "matched": 6544,
        "unstable": 2656,
        "stable": 3888,
        "checks": 14,
        "dominant": 1208,
        "partnerLoss": 0,
        "slotLevelMass": 4180,
        "markLevelMass": 3888,
        "rankCount": 42,
        "rankCut": 14
      }
    ],
    "leafChecks": 769,
    "smallLeaves": 15,
    "twoLeaves": 15,
    "smallLeafExamples": [
      {
        "Z": 16,
        "C": 39882,
        "end": 39918,
        "E": 2,
        "labels": [
          19,
          17
        ],
        "w": [
          19,
          17,
          19
        ]
      },
      {
        "Z": 16,
        "C": 39882,
        "end": 39918,
        "E": 2,
        "labels": [
          19,
          17
        ],
        "w": [
          19,
          17,
          19
        ]
      },
      {
        "Z": 16,
        "C": 39882,
        "end": 39918,
        "E": 2,
        "labels": [
          19,
          17
        ],
        "w": [
          19,
          17,
          19
        ]
      }
    ]
  },
  {
    "X": 16384,
    "focus": true,
    "T": 169,
    "N": 1612,
    "events": 15668,
    "reaches": 841,
    "slots": 9313,
    "early": 125,
    "mixed": 71,
    "mixedTags": 123,
    "mixedExample": {
      "C": 48282,
      "p": 53,
      "n": 24223,
      "early": 1,
      "full": 11,
      "arr": [
        {
          "w": 79,
          "d": 6,
          "a1": true
        },
        {
          "w": 17,
          "d": 130,
          "a1": false
        },
        {
          "w": 17,
          "d": 130,
          "a1": false
        },
        {
          "w": 17,
          "d": 130,
          "a1": false
        },
        {
          "w": 17,
          "d": 130,
          "a1": false
        },
        {
          "w": 17,
          "d": 130,
          "a1": false
        },
        {
          "w": 69,
          "d": 26,
          "a1": false
        },
        {
          "w": 69,
          "d": 26,
          "a1": false
        },
        {
          "w": 69,
          "d": 26,
          "a1": false
        },
        {
          "w": 69,
          "d": 26,
          "a1": false
        }
      ]
    },
    "waitChecks": 398,
    "rawPairs": 846,
    "neg": 296.02663168851484,
    "pos": 1813.251997389671,
    "retired": 409,
    "controls": [
      {
        "eps": 0.1,
        "matched": 1408,
        "unstable": 996,
        "stable": 412,
        "checks": 1,
        "dominant": 412,
        "partnerLoss": 0,
        "slotLevelMass": 412,
        "markLevelMass": 412,
        "rankCount": 0,
        "rankCut": 0
      },
      {
        "eps": 0.25,
        "matched": 1408,
        "unstable": 996,
        "stable": 412,
        "checks": 1,
        "dominant": 412,
        "partnerLoss": 0,
        "slotLevelMass": 412,
        "markLevelMass": 412,
        "rankCount": 0,
        "rankCut": 0
      }
    ],
    "leafChecks": 182,
    "smallLeaves": 8,
    "twoLeaves": 8,
    "smallLeafExamples": [
      {
        "Z": 8,
        "C": 47256,
        "end": 47280,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 8,
        "C": 54120,
        "end": 54144,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 8,
        "C": 54120,
        "end": 54144,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      }
    ]
  },
  {
    "X": 65536,
    "focus": false,
    "T": 5424,
    "N": 5709,
    "events": 142413,
    "reaches": 0,
    "slots": 45090,
    "early": 551,
    "mixed": 276,
    "mixedTags": 767,
    "mixedExample": {
      "C": 165480,
      "p": 127,
      "n": 82933,
      "early": 1,
      "full": 38,
      "arr": [
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        },
        {
          "w": 139,
          "d": 108,
          "a1": false
        }
      ]
    },
    "waitChecks": 2677,
    "rawPairs": 12342,
    "neg": 0,
    "pos": 10013.948674502672,
    "retired": 0,
    "controls": [
      {
        "eps": 0.1,
        "matched": 46604,
        "unstable": 36924,
        "stable": 9680,
        "checks": 28,
        "dominant": 5376,
        "partnerLoss": 0,
        "slotLevelMass": 9680,
        "markLevelMass": 9680,
        "rankCount": 51,
        "rankCut": 14
      },
      {
        "eps": 0.25,
        "matched": 46604,
        "unstable": 33448,
        "stable": 13156,
        "checks": 41,
        "dominant": 5880,
        "partnerLoss": 432.3999999999999,
        "slotLevelMass": 13660,
        "markLevelMass": 13156,
        "rankCount": 106,
        "rankCut": 34
      }
    ],
    "leafChecks": 3340,
    "smallLeaves": 132,
    "twoLeaves": 132,
    "smallLeafExamples": [
      {
        "Z": 8,
        "C": 133758,
        "end": 133782,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 8,
        "C": 142338,
        "end": 142362,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 16,
        "C": 142254,
        "end": 142290,
        "E": 2,
        "labels": [
          19,
          17
        ],
        "w": [
          19,
          17,
          19
        ]
      }
    ]
  },
  {
    "X": 65536,
    "focus": true,
    "T": 339,
    "N": 5709,
    "events": 75430,
    "reaches": 2870,
    "slots": 38730,
    "early": 540,
    "mixed": 257,
    "mixedTags": 529,
    "mixedExample": {
      "C": 183048,
      "p": 163,
      "n": 91771,
      "early": 1,
      "full": 14,
      "arr": [
        {
          "w": 132,
          "d": 230,
          "a1": false
        },
        {
          "w": 132,
          "d": 230,
          "a1": false
        },
        {
          "w": 132,
          "d": 230,
          "a1": false
        },
        {
          "w": 132,
          "d": 230,
          "a1": false
        },
        {
          "w": 211,
          "d": 72,
          "a1": false
        },
        {
          "w": 211,
          "d": 72,
          "a1": false
        },
        {
          "w": 211,
          "d": 72,
          "a1": false
        },
        {
          "w": 211,
          "d": 72,
          "a1": false
        },
        {
          "w": 132,
          "d": 230,
          "a1": false
        },
        {
          "w": 211,
          "d": 72,
          "a1": false
        }
      ]
    },
    "waitChecks": 1870,
    "rawPairs": 5118,
    "neg": 1085.308031298792,
    "pos": 7844.888816615688,
    "retired": 1556,
    "controls": [
      {
        "eps": 0.1,
        "matched": 27936,
        "unstable": 21604,
        "stable": 6332,
        "checks": 17,
        "dominant": 5060,
        "partnerLoss": 0,
        "slotLevelMass": 6332,
        "markLevelMass": 6332,
        "rankCount": 4,
        "rankCut": 0
      },
      {
        "eps": 0.25,
        "matched": 27936,
        "unstable": 20756,
        "stable": 7180,
        "checks": 21,
        "dominant": 5272,
        "partnerLoss": 169.6,
        "slotLevelMass": 7392,
        "markLevelMass": 7180,
        "rankCount": 14,
        "rankCut": 0
      }
    ],
    "leafChecks": 1300,
    "smallLeaves": 51,
    "twoLeaves": 51,
    "smallLeafExamples": [
      {
        "Z": 8,
        "C": 133758,
        "end": 133782,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 8,
        "C": 142338,
        "end": 142362,
        "E": 2,
        "labels": [
          13,
          11
        ],
        "w": [
          13,
          11,
          13
        ]
      },
      {
        "Z": 16,
        "C": 142254,
        "end": 142290,
        "E": 2,
        "labels": [
          19,
          17
        ],
        "w": [
          19,
          17,
          19
        ]
      }
    ]
  }
]
```

Next: use the corrected physical rank census (including actual early anchors) for a bound on E_A1; exploit global resonance halo deletion for non-A1 forward suffixes via a disjoint block cover with controlled outside gain. The short unit-wait supplies may be genuine and no blanket local sparsity is assumed. Main and sibling branches not modified.
