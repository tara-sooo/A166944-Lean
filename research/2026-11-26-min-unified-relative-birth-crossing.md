# Integration XI: relative induced birth branches and certified crossing clocks

2026-11-26 JST. Parent [3852a30](https://github.com/tara-sooo/A166944-Lean/commit/3852a30e5b2286be9e0d9532ab6f2b78a80c0f4b); direct head [074993c](https://github.com/tara-sooo/A166944-Lean/blob/074993ce8fa710aea5f38060ec52ab4a1a28fca8/research/2026-11-26-min-direct-crossing-clock-and-factor-hierarchy.md). New: endpoint-relative induced branch threshold on the surviving positive measure, almost macroscopic INCOMING branch at true first meeting in the concentrated phase sector, with lifetime/deficit inequality and a subpolynomial number of two-large-history mergers. Independently import direct crossing-clock hierarchy on actual clock-rich tiles. No strict final contraction or Lean proof.

## 1. Relative induced branch pruning

Keep integration X source measure, all original pair identities and masks, U,L_*, B,H,T,u,ell, actual witness capacities. At true vertex (t,J) incoming branches are distinct jump labels, unique wait predecessor and possibly singleton root injection. Incoming jump p divides J+2I and t-2I, I=t mod2, with adjusted half-deficit k=(2t-J-6I)/2 a nonnegative multiple of p. Uniform bound d_max=ceil(20u/ell)+2 on number of branches for sufficiently large X follows since the product of distinct prime divisors of J+2I<=O(X), and product of first m odd primes has log >>m log(2+m). See earlier birth-pair lifetime support and historical forest.

At actual witness exit full original cohort Q, b=|Q|, induce its true birth tree on ALL members, including those with no retained charge. No induced retirement prior to witness. For an original ordered pair at its true first meeting, denote its TWO incoming branch populations in induced tree by b_i,b_j (not historical masses). For any real a>0 number of ordered pairs with BOTH b_i<a and b_j<a is <=d_max a b. Fix first tag i. Its induced group grows monotonically until witness. Consider LAST birth involving i with own incoming group size<a and partner from another incoming group size<a. Partners from earlier such births belong to incoming group at this last birth, size<a; at last birth at most d_max-1 other branches of size<a qualify. Later none. Thus <=d_max a partners per i, sum over i. Handles comb trees and high degree without counting every ancestor separately.

Use a=rho b/d_max, rho=ell^(-1/4). Existing physical ordered-pair marginal caps O(1/max(b0,b)) per occupied tick and O(1/(alpha max(b0,b))) per raw hybrid cut give extra payment O(rho NT): #bad<=rho b², sum tick b<=3NH and sum cut b=O(alpha NH). For earlier of two joint witnesses use appropriate marginal, split by order; no factor number of joint keys. Works on all short branches before or after bin selection. At least one of ORIGINAL pair's true incoming branches at birth now has >=rho b/d_max ACTUAL induced members surviving to witness, not merely a big third branch or historical set. Strengthens old fixed B^(1-o(1)) physical branch test. Does not force both large. Original birth and rank masks remain.

## 2. Concentrated phase: giant actual incoming branch and lifetime slack

Restrict to moderate cut branch K=pi(V), expensive q<=Q0=u^10 (any fixed polylog bound works). Use m_bin=H log²(2+q)/(u ell² K q z0) from X, z0 as there. Uniform lower m0=H/(u ell² K Q0 z0)=X^(1-o(1)). Concentrated earlier physical b>=eta0 m0, eta0=ell^-1/8; retained pair's induced incoming branch >=a0=floor(rho eta0 m0/d_max)=X^(1-o(1)). No conclusion that a0 is fixed fraction of N.

True first birth (t,J), predecessor (t-1,C_pre) with C_pre=J-p+1 for jump p, C_pre=J for wait. Root injection singleton, cannot be giant branch. Define d_pre=2(t-1)-C_pre>=0. Important correction found by finite audit: predecessor may be INSIDE an event wait, not its completed arrival. At actual completed prestate d<=6+5(C_pre-C0), since initial deficit6 and w<=3g. At any intervening wait tick d can increase by <=4B, or <=4p when incoming jump is p. Write F=4p for jump, 4B for wait. Then every branch member has C0<=C_pre-(d_pre-6-F)_+/5. No fringe omitted. For actual earlier witness exit horizon J_W all induced members have C0>=J_W-H. Distinct prime origins and uniform one-form interval upper sieve yield absolute c>0:
    (J_W-J)+(J-C_pre)+(d_pre-6-F)_+/5+c a log(2+a)<=H     (1)
for induced branch size a>=a0 (or sufficiently large a). This combines actual age, incoming gain, pre-birth deficit and survivor origin span. For wait use zero incoming gain and F=4B, not a fictitious label. For jump p, d_pre=2k+6I+p-3, so the deficit term is (2k+6I-3p-9)_+/5. The O(B) correction is asymptotically small relative to H, but essential pointwise.

For two distinct incoming jump labels p,q, pq divides J+2I and k. Thus for nonreset birth pq<=k<= (6+5H)/2 (completed jump poststate). If both exceed sqrt((6+5H)/2), such nonreset birth impossible. RESET k=0 separate. This does not force either label to be high. Original birth-pair support counts remain. Use earlier witness in (1); earlier induced population need not all survive later.

## 3. New near-macroscopic historical founder sector

Apply original retirement-preserving historical component forest (96656af) to FULL original graph at fixed threshold a0. At each surviving concentrated pair birth at least one of its two actual incoming branches has historical size>=a0. Partition whether BOTH incoming histories >=a0 or exactly one. Founder conservation A_attach+a0 J_merge<=N, where J_merge=sum(k-1) over vertices with k>=2 historical large inputs and A_attach is total historical mass first absorbed into large component. Hence #actual true vertices supporting two-large-history births <=N/a0=X^o(1), stronger than earlier B-scale threshold. Actual vertices, not projected horizons or canonical visits.

Reindex exact positive concentrated fractions by original birth. Pay each two-large-history vertex with aggregate positive load <=eta H a0, eta=ell^-1/4, total <=eta NH=o(NT). For attachment pairs unique small-history member crosses threshold at THIS birth and can play that role at most once. Either-role original source density<=10 in x, so its attachment load<=10 times actual eligible gain interval after birth, <=10H. Can pay attachments with remaining eligible gain<=eta H or aggregate positive charge<=eta H, total O(eta NH). Conditional support (1) restricts lifespan of original pair, not total all other partners. Historical mass never used as physical denominator.

Neither few two-large-history vertices nor unique attachments proved o(NT) total load. A long common continuation is compatible with this count.

## 4. Certified crossing-clock hierarchy on rich local tiles

Independently strengthen IX-X local witness route using direct 074993c actual crossing coverage and clock supply. Fixed theta hybrid parameters, theta=1/2 for example. Regular full-event tile block gain G=M0-O(B), W>=G/4, normalized cut mass G-o(G), M(event)=2/(alpha Q) times raw cuts. Fix k in {3,4,5,6} and
    A_k=max(V+1,ceil(lambda ell²),1+ceil(33*(7X+1)^(1/k))).
A_k<B eventually, A_k/lambda->infinity. H_k actual CROSSING events p>=A_k; U_k gain of ALL other events including high noncrossers; M_low normalized mass on crossers p<A_k. Outer smoothing ONCE to H_k, count<=G/(A_k-1), gives U_k<=M_low+2(lambda-1)G/(A_k-1)+o(G)=M_low+o(G).

Either M_low>=G/48, giving >=alpha Q G/96 distinct cuts on R<p<A_k; or U_k<=G/24 eventually. In latter, waits outside H_k<=3U_k<=G/8, waits in H_k with w<g/16 <=G/16, so expensive actual CROSSING events p>=A_k,w>=g/16 carry >=G/16 occupied ticks (>=M0/20 eventually). This requires actual crossing unlike previous large tick route, but complementary threshold may be larger than A. Alternative normalized transport, not simultaneous restriction of old and new short labels. Same rich tile selection and caps O(1) tick or O(1/alpha) cut. Product marginals if retaining previous routes.

Every such expensive crosser has all prime factors f of C±1 >=w/2>=g/32>(7X+1)^(1/k), by earliest eligible clock and w<=2p. Thus Omega(C±1)<=k-1 and Omega((C-e)/p)<=k-2, multiplicity counted. k=3 gives prime selected cofactor, other neighbor prime or semiprime. Not a twin certificate for C±1. Under finite twins repeated prime cofactors for fixed p differ by >=4 once past largest twin; on a contiguous block gain G certified gain of one p<=G/4+O(p) by spacing 4p-2 (allow conservative O(p)). Existing dimension-two upper sieve gives O((G+p)/log²(2+G/p)) per fixed certified p, uniform in block and label. With G~M0=X^(1-o(1)) and p<=B, any adaptive j=o(u²) selected labels per tile carry o(G) certified gain; w<=3g implies o(1) fraction of uniform certified tick witnesses. This is a payable o(NT) removal, so cannot support this branch on bounded label set. Do not infer a local cofactor bound without its shorter progression estimate. VIII projected expensive gate applies since w>=g/16; new low cut route K=pi(A_k), not old pi(A).

Constant-deficit run: high nonreset p divides d/2 or (d-6)/2. If d=0 or6, no such high nonreset; otherwise product distinct labels divides nonzero O(H²), hence O_k(1) labels. For tile with j changes of deficit, long flat runs of gain>=R0 B contribute O_k(G/log²(2+R0)) certified gain by local sieve, short flat runs <=R0 B(j+1). If certified flat gain positive fraction G, j=Omega_k(G/B) choosing fixed R0 large. Total certified gain>=G/48 (w<=3g); if nonflat gain>=G/96 directly j>=G/(96B), else flat gain>=G/96 and same conclusion. Thus every certified-rich tile has Omega_k(G/B) actual deficit changes. No lower on signed upward drift. Cheap first defects in X can still occur without these labels; this does not force expensive first defect. Separate actual rich tile route.

## 5. Proof status

Keep original positive partition and negative credit L_* unchanged, intersect new witness masks by normalized product if needed. P_giant remaining positive measure. Under finite twins NT/2-o(NT)<=U/2+(P_giant-L_*)/2+c_a(D_l+D_h). Strict normalized liminf <1 still unproved. Next: use few two-large-history vertices and actual origin slack to evaluate their whole continuations plus attachments; compare certified variation to phase defects. Main/direct unchanged.

## 6. Diagnostics

Run node research/min_unified_relative_birth_crossing_audit.mjs 4096 16384 65536. Actual ECMAScript execution. Full actual endpoint cohorts size2..80, dedup member set/horizon band, true birth via overlap of actual tick plateaux incl root/wait, jump/wait, jump/jump. Induced branch membership, inverse congruences, root lifetime/deficit slack before prime sieve, relative small-small counts at six thresholds and induced founder/attachment budget. Initial test of predecessor envelope WITHOUT wait fringe failed; corrected with explicit 4p/4B and reran; count cases needing correction. Finite rich tiles, two small hybrid cutoffs, raw crossing mass and outer expansion measured error, clock supply; finite A not asymptotic A_k, unclassified if neither finite condition. Actual factor certificates when actual wait roughness exceeds root threshold, flat support product. No full retired historical forest reconstructed, full positive transport or asymptotic prime sieve test, no Lean verification. Results:
```json
[
  {
    "X": 4096,
    "focus": false,
    "B": 170,
    "T": 1360,
    "N": 464,
    "events": 7448,
    "cohorts": 292,
    "pairChecks": 2486,
    "birthNodes": 814,
    "rootWait": 127,
    "jumpWait": 2051,
    "jumpJump": 308,
    "reset": 483,
    "nonreset": 1876,
    "productChecks": 2359,
    "slackChecks": 2755,
    "fringeNeeded": 422,
    "thresholdChecks": 1752,
    "smallPairs": 8886,
    "maxB": 15,
    "largePhysical": 30,
    "skipped": 0,
    "attachmentChecks": 1061,
    "mergeChecks": 1794,
    "forestChecks": 1752,
    "tiles": 426,
    "rich": 426,
    "massChecks": 426,
    "clockChecks": 426,
    "small": 116,
    "large": 1,
    "unclassified": 309,
    "factorChecks": 1111,
    "certCounts": [
      132,
      281,
      332,
      366
    ],
    "constantRuns": 2198,
    "constantSupportChecks": 8,
    "maxSupport": 1,
    "exactCrossers": 516,
    "roughChecks": 516
  },
  {
    "X": 4096,
    "focus": true,
    "B": 170,
    "T": 85,
    "N": 464,
    "events": 3292,
    "cohorts": 262,
    "pairChecks": 614,
    "birthNodes": 406,
    "rootWait": 64,
    "jumpWait": 476,
    "jumpJump": 74,
    "reset": 116,
    "nonreset": 434,
    "productChecks": 550,
    "slackChecks": 945,
    "fringeNeeded": 223,
    "thresholdChecks": 1572,
    "smallPairs": 2928,
    "maxB": 6,
    "largePhysical": 0,
    "skipped": 0,
    "attachmentChecks": 195,
    "mergeChecks": 1132,
    "forestChecks": 1572,
    "tiles": 2,
    "rich": 2,
    "massChecks": 2,
    "clockChecks": 2,
    "small": 0,
    "large": 0,
    "unclassified": 2,
    "factorChecks": 4,
    "certCounts": [
      1,
      1,
      1,
      1
    ],
    "constantRuns": 1142,
    "constantSupportChecks": 5,
    "maxSupport": 1,
    "exactCrossers": 1,
    "roughChecks": 1
  },
  {
    "X": 16384,
    "focus": false,
    "B": 339,
    "T": 2712,
    "N": 1612,
    "events": 33736,
    "cohorts": 1017,
    "pairChecks": 15576,
    "birthNodes": 3478,
    "rootWait": 671,
    "jumpWait": 13050,
    "jumpJump": 1855,
    "reset": 3632,
    "nonreset": 11273,
    "productChecks": 14905,
    "slackChecks": 14267,
    "fringeNeeded": 1983,
    "thresholdChecks": 6102,
    "smallPairs": 52438,
    "maxB": 28,
    "largePhysical": 137,
    "skipped": 0,
    "attachmentChecks": 5226,
    "mergeChecks": 7151,
    "forestChecks": 6102,
    "tiles": 1084,
    "rich": 1078,
    "massChecks": 1078,
    "clockChecks": 1078,
    "small": 454,
    "large": 25,
    "unclassified": 599,
    "factorChecks": 4240,
    "certCounts": [
      428,
      945,
      1357,
      1510
    ],
    "constantRuns": 9442,
    "constantSupportChecks": 36,
    "maxSupport": 1,
    "exactCrossers": 2229,
    "roughChecks": 2229
  },
  {
    "X": 16384,
    "focus": true,
    "B": 339,
    "T": 169,
    "N": 1612,
    "events": 15668,
    "cohorts": 1041,
    "pairChecks": 4584,
    "birthNodes": 2187,
    "rootWait": 269,
    "jumpWait": 3733,
    "jumpJump": 582,
    "reset": 1051,
    "nonreset": 3264,
    "productChecks": 4315,
    "slackChecks": 6084,
    "fringeNeeded": 1296,
    "thresholdChecks": 6246,
    "smallPairs": 18640,
    "maxB": 11,
    "largePhysical": 11,
    "skipped": 0,
    "attachmentChecks": 1950,
    "mergeChecks": 5650,
    "forestChecks": 6246,
    "tiles": 2,
    "rich": 2,
    "massChecks": 2,
    "clockChecks": 2,
    "small": 0,
    "large": 0,
    "unclassified": 2,
    "factorChecks": 3,
    "certCounts": [
      0,
      1,
      1,
      1
    ],
    "constantRuns": 5178,
    "constantSupportChecks": 11,
    "maxSupport": 1,
    "exactCrossers": 2,
    "roughChecks": 2
  },
  {
    "X": 65536,
    "focus": false,
    "B": 678,
    "T": 5424,
    "N": 5709,
    "events": 142413,
    "cohorts": 3720,
    "pairChecks": 79760,
    "birthNodes": 14593,
    "rootWait": 2904,
    "jumpWait": 67301,
    "jumpJump": 9555,
    "reset": 18943,
    "nonreset": 57913,
    "productChecks": 76856,
    "slackChecks": 65709,
    "fringeNeeded": 8140,
    "thresholdChecks": 22320,
    "smallPairs": 267168,
    "maxB": 42,
    "largePhysical": 636,
    "skipped": 0,
    "attachmentChecks": 22868,
    "mergeChecks": 28539,
    "forestChecks": 22320,
    "tiles": 2954,
    "rich": 2886,
    "massChecks": 2886,
    "clockChecks": 2886,
    "small": 1442,
    "large": 176,
    "unclassified": 1268,
    "factorChecks": 19776,
    "certCounts": [
      2352,
      4508,
      6056,
      6860
    ],
    "constantRuns": 39240,
    "constantSupportChecks": 321,
    "maxSupport": 1,
    "exactCrossers": 9273,
    "roughChecks": 9273
  },
  {
    "X": 65536,
    "focus": true,
    "B": 678,
    "T": 339,
    "N": 5709,
    "events": 75430,
    "cohorts": 3915,
    "pairChecks": 28195,
    "birthNodes": 10387,
    "rootWait": 1466,
    "jumpWait": 23195,
    "jumpJump": 3534,
    "reset": 6579,
    "nonreset": 20150,
    "productChecks": 26729,
    "slackChecks": 33120,
    "fringeNeeded": 5659,
    "thresholdChecks": 23490,
    "smallPairs": 104028,
    "maxB": 14,
    "largePhysical": 264,
    "skipped": 0,
    "attachmentChecks": 12228,
    "mergeChecks": 24191,
    "forestChecks": 23490,
    "tiles": 4,
    "rich": 4,
    "massChecks": 4,
    "clockChecks": 4,
    "small": 3,
    "large": 0,
    "unclassified": 1,
    "factorChecks": 4,
    "certCounts": [
      0,
      0,
      2,
      2
    ],
    "constantRuns": 23134,
    "constantSupportChecks": 79,
    "maxSupport": 1,
    "exactCrossers": 4,
    "roughChecks": 4
  }
]
```
