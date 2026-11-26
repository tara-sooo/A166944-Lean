# Integration VII: net pair-level record ledger, longer persistent witnesses and source phase census

2026-11-26 JST. Parent [c3e1906](https://github.com/tara-sooo/A166944-Lean/commit/c3e1906109a5727c05b305d1a56a0456eaaf8c9d). Independent direct latest [40a43f6](https://github.com/tara-sooo/A166944-Lean/blob/40a43f624b3f73df3c68b1bf0bcb2b4f665b9713/research/2026-11-26-min-direct-sieved-hybrid-twin-certificates.md), and [319d42d](https://github.com/tara-sooo/A166944-Lean/blob/319d42d2ac9bf3dcdfc2cfd34ce8a4117f1cd611/research/2026-11-26-min-direct-last-exit-corridors-and-record-support.md). New: cancel opposite crossings at the SAME ordered pair and deficit level before any source reindexing, obtain longer persistent witness room at o(NT) cost and a fixed-level phase/roughness source census, and apply direct record-only barrier nonconcentration to actual negative net records. Also import the sieved hybrid twin certificate to long shared persistence intervals with no sparse-root hypothesis. Paper deductions and finite diagnostics, not Lean verification or a strict final margin.

## 1. Frozen pair domain and exact level cancellation

Use all quantities and actual endpoint pair intervals I=[a,b) with denominator b_Q=max(b0,|Q|) of integration VI. Write d for the common interpolated ordinary deficit, m(x)=min_[x,x+z] d, M=(m-D_sh)_+, z=floor(D/ell²), D_sh=floor(D/ell), D=eta H/log(2+N), eta=ell^(-1/4). Old age and terminal margin give actual common paths throughout [a,b+z], including event fringes. Pair weights remain frozen until the explicitly stated denominator step.

By piecewise affine coarea, for almost every level y>D_sh, the number of upcrossings of m in I minus the number of downcrossings equals 1{m(b)>y}-1{m(a)>y}. Crossings alternate. Cancel opposite crossings separately on every ORIGINAL ordered pair and slab, retaining the last upward crossing when the net is +1, first downward crossing when net -1 (all others can be paired, not necessarily chronological up-then-down). Do not match between different pairs or denominators. The nonnegative unmatched amounts are exactly
    P_* = sum_(I,Q,i,j) (M(b)-M(a))_+ / b_Q,
    L_* = sum_(I,Q,i,j) (M(a)-M(b))_+ / b_Q.
Then P_z-L_z=P_*-L_* exactly and P_*<=P_z, L_*<=L_z, P_z-P_*=L_z-L_*. These are measures in level coordinates, not discrete integer counts; endpoints measure zero. This cancellation is different from paying the old positive and negative parts separately, and does not give a strict numerical improvement of their difference by itself.

If m(a)<y<m(b), the low point attaining m(a) is BEFORE b (otherwise it lies in [b,b+z] and contradicts m(b)>y). The last actual upward crossing of d through y before b lies at x in (a,b) and d(t)>=y for all t in [x,b+z]. It is the last upward crossing of m through y as well: until that crossing the left endpoint is below y locally, afterwards all future windows through b are above y. For a.e. y it is on an actual strictly increasing affine event segment, so the P_* density in x is at most (m')_+/b_Q<=5/b_Q. If m(b)<y<m(a), the first actual downward crossing of d after a+z lies at t in (a+z,b+z); all earlier d>=y on [a,t]. The first downward crossing of m is at t-z in I. Thus unmatched negative credits can be allocated to actual FIRST RECORD downward portions starting from a+z, not arbitrary decreasing events. Clipping at D_sh just restricts levels; it never creates artificial record jumps.

## 2. Strengthen the persistence length and retain source pair denominator

Put L=floor(D/sqrt(ell)) (eventually L>>z>>B), epsilon=ell^(-1/8). Pay unmatched positive levels whose last upcross x>b-L. For each pair interval their total length is <=5L by the positive derivative bound, even when its length<L; weighted total <=5L N(H/D+2)=o(NT). The remaining levels have actual d(t)>=d(x)=y for t in [x,x+L], indeed to b+z. There is no assertion that all original positive derivatives are persistent for L; the net cancellation and final strip are essential.

Unfreeze the positive measure to denominator max(b0,b(x)) exactly as integration VI; error <=5D N(log N+2)=o(NT). The surviving source per ordered pair/level/physical event is <=1/max(b0,b_V). For a fixed tag and event, each y is crossed upwards at most once on its actual affine segment. It can lie in only one original slab at that coordinate, and per partner has only one interval there. Thus row and column level densities at an actual source slot are <=1, total scalar density a(V,y)<=b_V. Even if different arrivals give different x at the same slot, the per-tag statement holds; no assumption that the affine interpolation is common to ALL arrivals. Both original members share the actual event because of old birth age. No need for A1-specific anchors in this record ledger.

Transport surviving positive measure to expensive actual tick and primorial crossing witnesses in the LONGER length L by the same proof as integration VI: complete gain>=L-2B, total wait>=(G-5B)/2, expensive w>=g/4 count>=L/8, strict P crossings>=L/(2P). Deficit on the suffix stays above y and <=y+5L+O(B). It need not be in a narrow relative band: L/D_sh grows like sqrt(ell), unlike previous z/D_sh; the per-tag bounded load proof only needs the fixed common L, not relative depth. Each role has density<=5 in x and marginal <=40/tick,10P/boundary. Delete variations>epsilon from source exit to either witness at O(N(L+B)log N/epsilon)=o(NT), since L log N/epsilon = O(H ell^(-5/8)). Both actual witness populations and original pair density caps follow as before. All old induced rank and projected/physical thin witness payments apply, with same o(NT) bounds. This is a new witness route for unmatched positive levels; one may retain prior short-z witness masks as well, as P_* is a subset of the old positive domain. No double counting of the two partitions or negative credit.

## 3. Fixed-level arithmetic census at the ORIGINAL positive source

At fixed ordinary real deficit level y in [D_sh,6+5H], an actual increasing event label p and exit indicator I=0,1 satisfies
    d<y<d'=6I+2ph <= y+3p+1,
    C=1-2I+p(2I-2h-1) mod 4p,
    n=(C+p-1+6I+2ph)/2,
since w<=2p and 2w-g>0. There are at most three possible h per side, and each fixes one true exit per projected C,p. These formulas also hold for label3 at deep positive y (its adjusted deficit is divisible by 6). The proof uses selected-clock divisibility at n and C, not just the projected horizon. Exact source upcross requires an actual arrival with d<y; we overcount the possible slots.

Positive drift requires w>g/2, so least eligible r(C)>g/4. The existing two-form upper sieve on the progression of step4p (exclude 2,p, all odd primes <=p^(1/40) eventually below r) gives O(X/[p log²(2+p)]) possible slots for fixed y,p uniformly; trivial bound for bounded p. The progression length O(X/p)>=constant B absorbs the sieve remainder. This is a fixed-deficit-level count, with NO factor H/p for the number of multipliers. Use the exact source effective mass a(V,y) after unfreezing, normalized as in Section2 (<=b_V). Pay all fractions at
    a(V,y)<=H log²(2+p)/(y u ell³).
Total <= sum_p O(X/[p log²(2+p)]) integral_(D_sh)^(6+5H) H log²(2+p)/(y u ell³)dy
          =O(XH/(u ell))=o(NT),
using sum 1/p=O(ell), log(H/D_sh)=O(ell). For high p>=ceil(B/u), strengthen cap to H u²/(y ell³) with cost O(XH/(u ell)), using log p~u and reciprocal sum O(ell/u). These are exact level-fraction deletions on the new positive envelope, independent of witness thin cuts, and make every retained source a heavy actual upward cut with high multiplier when p<=B: h>=c D_sh/B. Unlike the earlier global target-normalized deep-record cap, the source here has original pair lifetime weights. Can additionally apply induced root ranks at the source itself at O(rho NT): each slot positive-level interval contained in (d'-3p-1,d'), length O(p), and sum b_V p=O(NH); per-level pair density<=1/max(b0,b_V). This also handles arrivals with different predeficits. The required source mass gate does not imply that positive residual is empty.

## 4. Negative net record support and nonconcentration

For each pair interval with M(a)>M(b), let lo=max(D_sh,m(b)), hi=m(a), Delta=hi-lo. Starting at actual a+z, assign every y in (lo,hi) to its FIRST actual downward crossing. This is precisely the negative net record map of Section1. Every assigned level is on a record decrease relative to the running minimum started at a+z, clipped to (lo,hi). Even if the path increases or visits other low states, a level cannot be assigned twice. Both original pair members execute the actual provider; first birth and original denominator remain fixed.

Use the direct 319d42d barrier sets for ANY finite odd-prime support F (can depend on the pair interval). Product P_F, local barrier counts a_s=3 for s=3,5,7 and a_s=(s-3)/2 otherwise, theta_F=prod a_s/P_F. Every even barrier cut b for F forbids downward crossing by labels in F. A real level y in (b-2,b] has the same downward crossing predicate as b, since actual pre/post deficits are even. Restrict to full such bins inside (lo,hi), losing at most 4 units; complete periods of 2P_F then give
    Delta_out >= theta_F (Delta-2P_F-4)_+.
Here Delta_out counts only assigned negative net record length on labels outside F, not all actual negative drops. For |F|<=k, labels<=R and fixed k, P_F<=R^k, theta_F>=4^-k. If R^k=o(D), summing original weights yields
    L_*^outside >= 4^-k L_* - O((R^k+1)N(H/D+2))
                 = 4^-k L_* - o(NT).
This holds even if F is chosen as the k largest record-drop contributors separately for each pair interval. More generally the weighted error is the sum of theta_F(2P_F+4)/b_Q. It quantifies required recovery across labels for the ACTUAL negative net term. It does not prove L_* is a positive fraction of NT. The use of even bins avoids erroneously applying integer barrier residues to arbitrary affine real crossings. No cost from negative term is subtracted a second time.

## 5. Import direct sieved-hybrid offset witness on long persistent suffixes

The direct 40a43f6 result is a separate additional arithmetic restriction. Take balanced odd primorial P_R<=sqrt X maximal, S=floor(R/loglog R), V=S², smoothing length lambda=ceil(P_R^(4/11)). Use the direct hybrid cuts: multiples of 2P_S, ordinary R barrier at S<f<=R, extra sieve excluding +/-1 at R<f<=V. Its exact offset certificate shows that under finite twins, for all sufficiently large X every crossing label R<p<=V has strict offset, prehorizon NOT S-rough, and w<=2S; hence d-d'>=g-4S=(1-o(1))g. If an actual S-rough moderate crosser is found, the offset J-C±1 are actual twins>S. Anchor excluded by extra sieve. No sparsity of canonical visits, A1 or B assumed for this pointwise assertion.

Transfer the direct normalized union bound (7) to ANY actual contiguous gain interval of length G comparable to L (integer horizon coordinate length G/2). Its proof uses a fixed Bonferroni order k and periods <=P_R V^k, uniform mean-square error exp(-.001 pi_o(R)); here L= X/polylog(X) up to iterated logs, so P_R V^k=o(L) and lambda=o(L) for every fixed k. Cauchy-Schwarz period error is o(L), and fixed-order expectation gaps can be made arbitrarily small uniformly. Thus normalized cut coverage gives
    G <= F_hi + F_mod + 2lambda(m_hi+m_mod)+o(G),
where hi=actual crossing events p>V and mod=actual crossing events R<p<=V, counts m and gains F; no p<=R crosses. Use full events inside a retained source's length-L suffix (gain G in [L-2B,L]), which starts with deficit<=y+5B and ends >=y. Its total drift >=-5B. Each moderate crossing has drift <=-(1-o(1))g, all other events <=5g. Therefore
    (6-o(1)) F_mod <= 5G+5B,
and
    F_hi + 2lambda(m_hi+m_mod) >= (1/6-o(1))G. 
Equivalently, either F_hi>=G/12 eventually or m_hi+m_mod>=G/(25lambda) eventually (constants weakened slightly if desired). This is uniform for the ACTUAL shared suffix of each retained positive net level, conditional on absence of offset twins>S. It is a new local alternative connecting the signed pair envelope to the direct certificate, without the sparse-window assumptions of direct Section6. The count branch is not excluded; moderate crossings may have small waits and their number multiplied by lambda can be large. This does not imply a fixed positive gain share of high labels. The smoothing proof is imported, not re-certified here.

## 6. Updated sufficient criterion and scope

Let P_*^heavy be the remaining positive net measure after the endpoint strip, source thin/rank and long witness cuts (optional old short witness cuts). All payments are o(NT). Under finite twins,
    NT/2-o(NT) <= U/2 + (P_*^heavy-L_*)/2 + c_a(D_l+D_h).
It suffices that liminf [U+P_*^heavy-L_*+6(D_l+D_h)]/(NT)<1. Matching removes all internal excursions from BOTH positive and negative measures; do not subtract L_z instead of L_* from P_*^heavy. This reduces the positive proof obligation to persistent net levels, gives longer witness room and sharper source support without requiring sparse root or B populations. It does not establish a strict contraction. Next: combine the high-gain/count alternative with actual pair-level mass thresholds; obtain a supply bound for numerous cheap moderate crossings or a positive share of negative record credits. Main/direct branches unchanged.

## 7. Diagnostics

Run node research/min_unified_net_level_record_audit.mjs 4096 16384 65536. Exact function executed in ECMAScript tool runtime. Six actual prime-root controls, ordinary and focus gain targets, full endpoint denominators and up to 8 sampled members; first common completed exit proxy, no cumulative old masks. Actual affine endpoint minima, disjoint last-up/first-down level interval partition, persistence, source fixed-phase formula, one pair-source integer-level incidence, actual downward barrier and adaptive support examples, finite L/z strip, sampled level sign telescope (not exact count of all excursions). Independent finite hybrid-offset checks on actual events with small S,R,V (not asymptotic S=o(R), not large Fourier variance). Synthetic exact affine excursion test. No asymptotic sieve numerical test, no full product-witness or Lean verification. Results:
```json
{
  "results": [
    {
      "X": 4096,
      "focus": false,
      "N": 464,
      "events": 7448,
      "D": 340,
      "z": 42,
      "L": 113,
      "cut": 42,
      "pairs": 363,
      "positive": 10939.111904946458,
      "negative": 48.00909090909089,
      "signed": 10891.10281403734,
      "long": 5433.012270665841,
      "short": 5506.099634280563,
      "posRecords": 1710,
      "negRecords": 17,
      "phaseChecks": 1710,
      "barrierChecks": 95,
      "nonconcChecks": 1815,
      "massChecks": 39464,
      "matchedSamples": 973,
      "matchedUpDown": 50,
      "hybrid": 92,
      "twins": 40,
      "cheap": 52,
      "positiveHybrid": 25
    },
    {
      "X": 4096,
      "focus": true,
      "N": 464,
      "events": 3292,
      "D": 21,
      "z": 4,
      "L": 7,
      "cut": 42,
      "pairs": 610,
      "positive": 4585.322390557002,
      "negative": 245.53604506604512,
      "signed": 4339.786345490953,
      "long": 2741.8135984819783,
      "short": 1843.5087920750248,
      "posRecords": 419,
      "negRecords": 48,
      "phaseChecks": 419,
      "barrierChecks": 191,
      "nonconcChecks": 3050,
      "massChecks": 7014,
      "matchedSamples": 1526,
      "matchedUpDown": 29,
      "hybrid": 39,
      "twins": 17,
      "cheap": 22,
      "positiveHybrid": 8
    },
    {
      "X": 16384,
      "focus": false,
      "N": 1612,
      "events": 33736,
      "D": 678,
      "z": 84,
      "L": 226,
      "cut": 84,
      "pairs": 1002,
      "positive": 43392.59058614806,
      "negative": 163.9607843137257,
      "signed": 43228.62980183417,
      "long": 19979.878157445008,
      "short": 23412.712428703097,
      "posRecords": 4781,
      "negRecords": 17,
      "phaseChecks": 4781,
      "barrierChecks": 272,
      "nonconcChecks": 5010,
      "massChecks": 167649,
      "matchedSamples": 2601,
      "matchedUpDown": 273,
      "hybrid": 434,
      "twins": 104,
      "cheap": 330,
      "positiveHybrid": 43
    },
    {
      "X": 16384,
      "focus": true,
      "N": 1612,
      "events": 15668,
      "D": 42,
      "z": 5,
      "L": 14,
      "cut": 84,
      "pairs": 3443,
      "positive": 28106.170225051468,
      "negative": 1157.110665960764,
      "signed": 26949.05955909071,
      "long": 16637.118922646987,
      "short": 11469.051302404543,
      "posRecords": 2335,
      "negRecords": 184,
      "phaseChecks": 2335,
      "barrierChecks": 1361,
      "nonconcChecks": 17215,
      "massChecks": 61762,
      "matchedSamples": 8367,
      "matchedUpDown": 224,
      "hybrid": 177,
      "twins": 54,
      "cheap": 123,
      "positiveHybrid": 21
    },
    {
      "X": 65536,
      "focus": false,
      "N": 5709,
      "events": 142413,
      "D": 1356,
      "z": 169,
      "L": 452,
      "cut": 169,
      "pairs": 2891,
      "positive": 162805.4653643117,
      "negative": 1789.349972302939,
      "signed": 161016.11539200798,
      "long": 61566.01999628684,
      "short": 101239.44536802624,
      "posRecords": 13492,
      "negRecords": 130,
      "phaseChecks": 13492,
      "barrierChecks": 3804,
      "nonconcChecks": 14455,
      "massChecks": 746420,
      "matchedSamples": 7588,
      "matchedUpDown": 799,
      "hybrid": 1766,
      "twins": 682,
      "cheap": 1084,
      "positiveHybrid": 342
    },
    {
      "X": 65536,
      "focus": true,
      "N": 5709,
      "events": 75430,
      "D": 84,
      "z": 10,
      "L": 28,
      "cut": 169,
      "pairs": 18067,
      "positive": 188571.71219105468,
      "negative": 9607.207956871014,
      "signed": 178964.50423418358,
      "long": 111983.29641916139,
      "short": 76588.41577189529,
      "posRecords": 10332,
      "negRecords": 965,
      "phaseChecks": 10332,
      "barrierChecks": 12060,
      "nonconcChecks": 90335,
      "massChecks": 516608,
      "matchedSamples": 42409,
      "matchedUpDown": 1138,
      "hybrid": 900,
      "twins": 355,
      "cheap": 545,
      "positiveHybrid": 179
    }
  ],
  "synthetic": {
    "net": 16,
    "positiveStart": 24,
    "negative": -12
  }
}
```
