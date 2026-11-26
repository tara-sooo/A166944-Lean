# Integration X: phase-bin coupling and forced short first defects

2026-11-26 JST. Parent [505671a](https://github.com/tara-sooo/A166944-Lean/commit/505671abb114b9acef37379b9d1172c4cae7c187); direct preflight e9a7ec9c21df3b35764c6e814d1517ed2bbfa7cb (crossing clock and canonical excursion audit only), latest direct paper [c87f76d](https://github.com/tara-sooo/A166944-Lean/blob/c87f76d2e2b86110d5224c4f0c1f613fc44afe9b/research/2026-11-26-min-direct-weighted-crossing-mass-and-scale-alternative.md). New: the stable physical phase pairs of IX can be divided into nearly macroscopic joint-mass bins, then yield either an individually very large physical cohort or a genuinely distinct translated-phase comparison with a forced nonperiodic first defect at short gain distance. This couples DIFFERENT surviving ordered-pair units; it is not a nonzero lag between the two tags of one original backward pair. No final strict contraction or Lean verification.

## 1. Retain the local joint measure, increase the tile length

Use IX's actual relaxed positive net-level source measure, U, L_*, H,T,N,B,u,ell,D,L, frozen original pair/birth/rank masks, fixed theta hybrid alpha,Q,lambda,A,V. Replace its tile length by the even integer M0=2 floor(L/(2 ell²)). Then B,lambda=o(M0), M0=o(L), M0=X^(1-o(1)), and the proof of IX Sections1–5 is unchanged: uniform global L2 controls total irregular tile length o(L), complete event fringes o(L), clock-rich tiles >=L/(12M0); all local marginal and joint caps remain with this M0, and the two-form sieve in a tile has length M0/q>=X^(1/2-o(1)) for q<=B, absorbing its earlier remainder. This is a fresh choice of parameters, not a literal subset of the old smaller tiles. If earlier masks are retained, take product marginals rather than double count charge. Large tile branch remains as in IX.

For every short tile, condition on its actual selected cut J and choose its expensive tick. Delete fractions where the expensive event prehorizon is within 2M0/ell of J. For each fixed cut and tag, total occupied ticks of events with prehorizon in this range is <=3(4M0/ell+2B+O(1)), using actual disjoint gain intervals and w<=3g. Conditional tick set >=M0/10. Uniform probability O(1/ell), so cost o(NT) (positive measure <=5NH). This bound is on the conditional product choices BEFORE arbitrary masks; intersection with any old masks only reduces the paid measure. On every remaining joint key (J,C,p,C',q), the two prehorizons differ by >=M0/ell eventually since |J-C|<=A<=B. Order them E (earlier actual exit), F (later). The complete projected distance from posthorizon of E to posthorizon of F is >=M0/(2ell). Both original pair members actually execute these events. Keep IX stability, partial bijection, true induced ranks and projected thin gates. For brevity call this remaining short joint measure mu. Per-role projected joint cap c0 q/(alpha M0) for fixed sufficiently large absolute c0. Tick and cut marginal caps O(1) and O(1/alpha) continue.

## 2. Time bins retain almost macroscopic projected mass

Define Delta=floor(M0/ell^6), and L0 the largest even primorial<=ell. Let y0 be its largest prime factor, tending to infinity. For each projected joint key, split its physical earlier slots by floor(n_E/Delta) and n_E mod L0. Each slot is wholly in one bin. At fixed prehorizon the actual departure range has length O(H) since 0<=d'<=6+5H. Hence at most Z=O((H/Delta+1)L0) bins per projected key. Important: use relative departure range at a FIXED key, not all absolute times across X. Let z0 be an explicit sufficiently large upper bound, e.g. ceil((10H/Delta+10)L0). For each bin let mass a be its total retained measure divided by c0 q/(alpha M0), same units as IX joint effective mass. Every original tag executes at most one phase at a fixed earlier projection, so bin mass <= distinct focal tag count, and mass a_E of one physical phase <= its original full cohort b_E. These are actual weighted populations, not unweighted phase counts.

For subtype K=pi(V) or pi(A) delete bins with
    a <= m_bin(q;K) = H log²(2+q)/(u ell² K q z0).
This costs O(XH/(u ell))=o(NT): per projected key there are at most z0 bins, each cost <=c0 q/(alpha M0) times threshold; IX projected key count and reciprocal prime sum apply unchanged. For fixed delta>0 and q>=B^delta the strengthened threshold H u/(K q ell z0) follows identically. Since Delta=X^(1-o(1)), z0=X^o(1), the moderate subtype with subpolynomial q still needs bin mass X^(1-o(1)). This improves the structural restriction, not the numerical mass gate compared to IX. The time-bin restriction is on auxiliary comparison, not an assumption that all phases of a projected key are close.

## 3. Concentrated versus dispersed physical phases and exact auxiliary coupling

Set eta0=ell^(-1/8). In each surviving bin of mass a, declare focal phase E concentrated if a_E>=eta0 a, otherwise dispersed. Concentrated fractions already have b_E>=eta0 m_bin, and b_F>=exp(-epsilon)b_E by IX stability. In the moderate/subpolynomial-q sector this gives an ACTUAL physical cohort X^(1-o(1)), with original pair true birth and induced ranks. This conclusion is only for concentrated fractions; no projected-to-physical inference on the others.

For dispersed fractions draw an auxiliary unit independently from the SAME bin using its normalized original measure (all units, including concentrated ones). A unit is an original ordered-pair/level source with its selected witnesses; one may retain full source metadata. Coupling is dmu_focal dmu_aux / mu_bin, restricted to dispersed focal units. Focal marginal is exactly the dispersed measure, auxiliary marginal is at most the original bin measure since focal total <=mu_bin. Summing bins keeps both original per-role caps. The focal unit's original two tags have zero lag and share their own actual witnesses; the AUXILIARY unit also consists of a same-slot pair. Comparing one representative tag of each is a distinct comparison. Delete same earlier phase outcomes, with conditional probability a_E/a<eta0 for dispersed focal unit; cost O(eta0 NT)=o(NT). No duplication of positive source weight. Distinct earlier cohorts are disjoint, and their departure lag Delta_t is nonzero with
    |Delta_t|<Delta,   L0|Delta_t,   2s_E|Delta_t
where s_E is earlier selected label. By stable partial bijection their later phases are distinct too. We do NOT assume final lag equals initial lag or order is preserved.

## 4. Forced short actual first defect

Compare actual continuations from the two earlier poststates at the common gained horizon J_E, until their first nontranslated edge. While equal projected edges and waits persist, lag is constant Delta_t. A translated selected edge p has 2p|Delta_t (both actual exits obey same residue at fixed C,p). Its half-open gain interval cannot contain a multiple of |Delta_t|: the even offset from C would have to be +/-1 mod p, impossible in [0,p-2] because the only possible nonnegative residues are 1 (odd) and p-1 (outside interval). Thus any contiguous translated prefix has total gained length STRICTLY less than |Delta_t|. Both paths have completed actual continuations to their later witness, at gained distance >=M0/(2ell)>>Delta. Therefore a first defect must occur before gain |Delta_t| from J_E. At its common prehorizon at least one actual selected prime r has 2r not dividing Delta_t: if both periods divide lag, each actual candidate is available with the same wait on the other path, and earliest-hit plus least-prime tie selection forces equal wait and label. Choose that actual event, focal priority if both qualify. Since L0 divides lag, r>y0. This is a local nonperiodic defect of two DIFFERENT physical phases, not an inverse branching assertion and not a claim about all labels between the two witnesses. Both paths may rejoin the same projected horizon while retaining different physical times; this does not undo the first defect.

The actual chosen defect belongs to the focal OR auxiliary tag's path. If auxiliary, do not describe it as executed by the original focal pair. Preserve original focal source and pair identity, and record whose actual trajectory supplies the defect. The auxiliary marginal domination is what allows a global transport estimate; no arbitrary partner-column payment.

## 5. Defect supply capacity and an additional thin gate

For a fixed original representative tag and chosen projected defect (C_d,r), its corresponding earlier witness lies at a gained distance <=Delta+B+O(1) before C_d (allow the cut offset inside earlier event), by Section4. If the earlier witness is a cut J, sum original cut marginal capacity O(1/alpha) over all actual surviving raw cuts in this neighborhood. By the direct growing-order local RAW mass estimate on arbitrary translated intervals, #cuts=O(alpha Delta), since Delta=X/polylog(X) up to iterated logs and X exp(-.01 r_sieve)=o(Delta), where r_sieve=pi_o(R). If earlier witness is expensive event, its selected occupied ticks over this neighborhood have total <=3(Delta+3B+O(1))=O(Delta), by disjoint gain intervals, and tick marginal cap O(1). For fixed original tag the earlier event may be the cut in some keys and expensive in others; sum these two bounds, not a factor number of bins or keys. Auxiliary marginal dominated by original mu, so both possible defect roles contribute O(Delta) total per tag per projected actual defect. The same upper holds for a specific true physical defect slot. This uses only the fact that the first defect is near the earlier witness, not near the original positive source x. No bound on its own waiting time is needed.

For each label r>y0, possible C_d lie in two progressions modulo r, O(X/r) choices uniformly for r<=B. Define effective defect mass load/(c1 Delta), c1 sufficiently large, <= number of distinct actual supplying tags (if role counted twice use larger c1). Delete keys with
    m_def <= H/(Delta u ell²).
Total O(sum_r (X/r) Delta H/(Delta u ell²))=O(XH/(u ell))=o(NT). For polynomial r>=B^delta fixed delta>0, strengthen to H/(Delta u ell), using sum 1/r=O_delta(1), at same order. This is an actual projected defect support cut; the defect may be cheap and the expensive two-form sieve cannot automatically be used. For the chosen Delta~H/(u ell^(35/4)) (up to absolute constants), the first threshold grows like ell^(27/4), i.e. a diverging iterated-log gate, not a near-macroscopic gate. No assertion that this is sufficient to suppress all defects. This route buys short nonzero-lag arithmetic on the original backward residual, at the price of an auxiliary coupling and weaker destination mass.

One can keep a further necessary relation for any fixed bin and nondefective word fragment: the number of physical phases having an identical translated timed word through a gain span G is at most 1+floor(Delta/R_word), with R_word the lcm of all selected periods (including the initial period and L0). The strict gain barrier gives R_word>G. In particular for G>=Delta this bound is ONE. This is an exact constraint on identical label-and-wait words, not an assertion of distinct label-only words or independent choices. The forced defects above use the stronger direct lag bound and do not require enumerating words.

## 6. Updated proof obligation

After the stated negligible payments, every positive fraction is either a large-tile witness of IX, a concentrated phase with physical b_E,b_F>= (1-o(1)) eta0 m_bin, or a dispersed phase coupled to another actual unit in same narrow time/wheel bin and routed to a heavy projected nonperiodic first defect at gain <Delta. Denote remaining original positive mass P_bin, not the sum of all its alternative marginals. Then under finitely many twins
    NT/2-o(NT) <= U/2 + (P_bin-L_*)/2 + c_a(D_l+D_h).
The strict normalized liminf [U+P_bin-L_*+6(D_l+D_h)]/(NT)<1 still open. No new upper on concentrated physical cohorts or total heavy defect load; no substitution of projected defect mass for physical mass. Next: exploit inverse first-meeting branch restrictions for the new almost-macroscopic physical cohorts; for dispersed route test whether cheap nonperiodic defects must have a later expensive or lag-changing witness without excessive congestion. Earlier independent boundary routes remain unchanged.

## 7. Finite controls

Run node research/min_unified_phase_bin_defect_audit.mjs 4096 16384 65536. Exact ECMAScript execution of modified IX audit. Actual prior local phase matches (finite M,L, cutoff values unchanged), retain each physical phase's weighted finite transport. For EVERY distinct matched phase pair, reconstruct actual common continuation from earlier to later witness, compare actual waits and labels, verify translation period, strict lag barrier, nonperiodic first defect and gain-before-lag bound, and wheel exclusion if lag multiple 6. For finite same-bin controls Delta=floor(M/2), wheel6, relaxed dispersed ratio .75; exact finite auxiliary mass partition and marginal domination, forced defect for gain>=Delta. These finite controls do NOT impose analytic far-separation or bin mass thresholds, and no integrated destination defect capacity/rank/Lean or asymptotic sieve test. Large branch remains unexpanded into ticks as in IX. Results:
```json
[
  {
    "X": 4096,
    "focus": false,
    "S": 3,
    "events": 7448,
    "phasePairs": 3,
    "actualDefects": 2,
    "persistentPairs": 1,
    "longGap": 0,
    "shortDefects": 2,
    "wheelDefects": 1,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 4096,
    "focus": false,
    "S": 5,
    "events": 7448,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 4096,
    "focus": true,
    "S": 3,
    "events": 3292,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 4096,
    "focus": true,
    "S": 5,
    "events": 3292,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 16384,
    "focus": false,
    "S": 3,
    "events": 33736,
    "phasePairs": 23,
    "actualDefects": 16,
    "persistentPairs": 7,
    "longGap": 5,
    "shortDefects": 16,
    "wheelDefects": 6,
    "binControls": 1,
    "binMass": 0.49920780277923027,
    "smallPhaseMass": 0.031615210186638695,
    "samePhaseMass": 0.0020022153291289232,
    "auxMass": 0.031615210186638695,
    "auxDefectMass": 0,
    "auxChecks": 2
  },
  {
    "X": 16384,
    "focus": false,
    "S": 5,
    "events": 33736,
    "phasePairs": 3,
    "actualDefects": 2,
    "persistentPairs": 1,
    "longGap": 0,
    "shortDefects": 2,
    "wheelDefects": 2,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 16384,
    "focus": true,
    "S": 3,
    "events": 15668,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 16384,
    "focus": true,
    "S": 5,
    "events": 15668,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 65536,
    "focus": false,
    "S": 3,
    "events": 142413,
    "phasePairs": 93,
    "actualDefects": 77,
    "persistentPairs": 16,
    "longGap": 7,
    "shortDefects": 77,
    "wheelDefects": 28,
    "binControls": 1,
    "binMass": 0.28576965669988963,
    "smallPhaseMass": 0.28576965669988963,
    "samePhaseMass": 0.14858694017208474,
    "auxMass": 0.2857696566998896,
    "auxDefectMass": 0,
    "auxChecks": 4
  },
  {
    "X": 65536,
    "focus": false,
    "S": 5,
    "events": 142413,
    "phasePairs": 23,
    "actualDefects": 18,
    "persistentPairs": 5,
    "longGap": 2,
    "shortDefects": 18,
    "wheelDefects": 6,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 65536,
    "focus": true,
    "S": 3,
    "events": 75430,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  },
  {
    "X": 65536,
    "focus": true,
    "S": 5,
    "events": 75430,
    "phasePairs": 0,
    "actualDefects": 0,
    "persistentPairs": 0,
    "longGap": 0,
    "shortDefects": 0,
    "wheelDefects": 0,
    "binControls": 0,
    "binMass": 0,
    "smallPhaseMass": 0,
    "samePhaseMass": 0,
    "auxMass": 0,
    "auxDefectMass": 0,
    "auxChecks": 0
  }
]
```
Main/direct unchanged.
