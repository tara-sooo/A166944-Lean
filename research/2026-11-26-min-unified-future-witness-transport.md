# Adaptive deep-record suffix transport to expensive physical ticks and primorial crossings

2026-11-26 JST. Continues ad9a99e4a2c82efb66f5ba5f41985797d1a717e3 (global deep-record charges), using the stable-heavy recorded deficit identity and prime-root primorial barriers. Original independent branch heads 1a4005f2f336 and e1ad9e2b434c unchanged. New all-mass terminal trim, near-constant deep-deficit forward suffix with a half-gain clock lower bound, and simultaneous linear transport to two independently counted witness families. Controls reached positive excess only; not a proof of the baseline clock contraction or twin-prime infinitude. No Lean compilation.

## 1. Setup, birth slack and adaptive actual suffix

Keep original dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u), original gain-stopped completed paths and recorded graph. Each event has gain g=p-1<=B, wait w<=2r<=3g, d_post-d_pre=2w-g<=5g. Deficit is nonnegative, starts at 6, and is <=6+5H. The previous global suffix minimum mu_i at a recorded poststate and deep record interval L_i=(max(D0,d_pre),mu_i] (if nonempty), D0=floor(H/u), give tag-event charge c_i>=0 with sum equal to E_deep, the reached-target excess above D0 in deficit units. In particular c_i<=|L_i|<=5g and <=2w<=4p. On every tag E_deep<=6+5H by disjoint levels and unit harmonic load. If c_i>0, mu_i>max(D0,d_pre). Therefore the post-deficit d_i satisfies
    0<=d_i-mu_i<d_i-d_pre<=5B.
This is the birth slack; it does not require d_i small. All recorded future states on that tag have deficit>=mu_i, including all occupied ticks between jumps.

Let eta=1/ell², z_i=floor(eta d_i). Uniformly z_i>=eta D0-1>>B, z_i<=eta(6+5H), and z_i>>B u^A for each fixed A. Pay c_i if the actual terminal horizon is less than C_post,i+z_i. Every paid event lies in the last gain strip of width eta(6+5H)+B; its full gain interval is inside that strip. Disjoint gain intervals and c_i<=5g imply
    E_late<=5N(eta(6+5H)+B)=O(NT/ell²).
This is an absolute charge payment even on tags stopping before T, not a conditional root-count argument. For each remaining source use the actual subsequent completed suffix through first posthorizon >=C_post,i+z_i, excluding source event itself. Its gain G_i is in [z_i,z_i+B), its elapsed actual clock W_i satisfies
    2W_i=G_i+d_end-d_i>=G_i-5B.
Every occupied tick of this suffix has deficit in [mu_i, d_i+5G_i+4B], hence d=d_i(1+O(eta)) uniformly since B=o(eta D0). In particular this is a narrow RELATIVE band of deep deficit, not just a lower bound D0. Call a future event expensive when its actual wait w>=g/4. All other waits total <=G_i/4; expensive occupied tick count
    F_i>=G_i/4-5B/2>=z_i/8
eventually. Each expensive event has r>= (p-1)/8. This is independent of the natural HIGH classification and may include small labels.

At a fixed original departure slot (C,p,v), poststate, d_i, mu_i and z_i are common. All contributors surviving late trim execute the identical required future suffix, by deterministic continuation until original stops. One can rerun the earlier deep slot cap on the late-trimmed charge A'=sum surviving c_i at that slot (counting support with the same old cap, no additional logarithmic factor). If A'>4p m then >m distinct original contributors share that entire suffix, unconditionally. The same O(NT/ell) budget applies to this cap on the new charge. In particular the gain span >=H/(u ell²)-O(1) is far longer than the previous charge-derived B-times-polylog span, though this statement is after another o(J_a) payment. No extra observed or hypothetical continuation is used.

## 2. Two witness sets and bounded per-tag transport

Use P the largest even primorial <=B/u^4 as in the original unified boundary argument. Then P<=B, P=o(z_i), largest prime factor Theta(u). For each surviving original tag-event i let K_i be all grid multiples K of P in [C_post,i,C_post,i+z_i). Each is strictly crossed (pre A<=K<post A+q-1) by a unique completed event of the chosen suffix. Its selected q cannot divide P: if it did, the even nonnegative K-A would be +/-1 modulo q, at least q-1, incompatible with strict crossing. Number of boundaries >=z_i/(2P). Use PROJECTED key (K,A,q), ignoring time. Let F_i be the set of expensive physical occupied ticks (j,C,q) in that suffix; cardinality >=z_i/8. Freeze all source charges and choices. Split c_i uniformly over the Cartesian product K_i x F_i, giving weight c_i/(|K_i||F_i|) per cell. It is an exact partition, not two copies. Marginal charges to each boundary and tick are c_i/|K_i| and c_i/|F_i|.

For one original tag and a fixed physical tick witness of deficit d, every source contributing to it has d_i=(1+O(eta))d, z_i=(1+O(eta))eta d; all its source posthorizons lie between the tick prehorizon minus O(eta d+B) and the tick prehorizon. Their full gain intervals are disjoint inside a strip of width O(eta d+B). Thus sum of c_i is O(eta d), by c_i<=5g. Dividing by the comparable lower bounds F_i>=z_i/8 proves a uniform O(1) total load on each original tag-tick. For a fixed boundary key and original tag the crossing event is unique; use its post-deficit as d. The same argument holds for source posthorizons within O(eta d+B) of K, since that crossing lies in their suffix; division by |K_i|>=z_i/(2P) gives O(P) total load on that tag-boundary. These bounds do not assume independence, disjoint suffixes, or common arrival times at projected keys. Fix absolute constants L_t,L_K such that the respective per-tag bounds are L_t and L_K P for all sufficiently large X.

## 3. Linear payments at future witnesses

Let M_K=aggregate marginal charge at projected key (K,A,q). Its effective mass n_K=M_K/(L_K P) is at most its distinct original contributor count. For fixed K and q, pre A is even in [K-q+2,K] and q divides A+sigma for one of two signs; at most one A per sign. Number of keys O((X/P+1) pi(B))=O(XB/(P u)), including all q<=B even if relaxed. Thus paying all product cells at keys with n_K<=H/(B ell) costs at most
    O(XB/(P u)*P*H/(B ell))=O(NT/ell).
This is projected mass, NOT synchronous physical mass.

Let M_t=aggregate marginal charge at physical witness tick (j,C,q), n_t=M_t/L_t <= full original occupied tag count. For each selected q the expensive predicate implies r>=(q-1)/8. The two-form quotient sieve from 64bc43b (use primes <=q^(1/40) below this roughness threshold for large q, trivial bound for bounded q) gives O(X/[q log²(2+q)]) possible horizons C. At each such C there are O(H) original occupied ticks because 0<=2j-C<=6+5H+4B. Use caps
    m_t(q)=log²(2+q)/(u ell²) for all q,
    m_t,high(q)=u²/ell² for q>=Q.
Pay cells at ticks with n_t<=max applicable caps. The cost for all labels is O(sum_q XH/[q log²(2+q)] *log²(2+q)/(u ell²))=O(NT/ell) using sum 1/q=O(ell). High range cost O(XH/u³ * ell * u²/ell²)=O(NT/ell). A fractional cap below one is legitimate for effective charge, not an assertion about integer full mass. Distinct keys and masks use union accounting: overlapping product cells are paid once. Previous actual-clock deletions can also pay any routed cells whose witness tag-tick was previously paid, since per-tag tick load<=L_t; their contribution is <=L_t times the earlier absolute budget. Source-slot caps and other charge masks can be applied by priority or frozen on the eligible charge; never count the same unit twice.

## 4. Remaining two-witness condition

After the two key payments, each unpaid cell uses a projected boundary effective mass >H/(B ell) and an expensive physical tick effective mass >m_t(q); for q>=Q the latter >u²/ell². Both witness states belong to the same narrow relative deep-deficit suffix. A single source with residual fraction >epsilon must have >epsilon of its boundaries heavy and >epsilon of its expensive ticks heavy; with only two global masks the residual fraction is exactly the PRODUCT of the two retained fractions. With further arbitrary masks it is at most each retained fraction. Pay all residual source portions of fraction <=epsilon, epsilon=1/ell². Total <=epsilon sum c_i<=epsilon N(6+5H)=O(NT/ell²). Every remaining source has >=epsilon z_i/(2P) distinct heavy projected crossings and >=epsilon z_i/8 expensive heavy physical ticks in its actual suffix. These are O(1) fraction bounds per epsilon, not an assumption of independence between actual paths. Large source charge after the fresh slot cap also guarantees a common actual suffix for all its surviving contributors before any per-cell mask, as in section 1.

With the earlier primorial exposure J_a>=NT a/[4(P(a)+a)] under no twins, these new O(NT/ell) and O(NT/ell²) payments are o(J_a) when (P(a)+a)/(a ell)->0, as before. The result reduces the heavy deep-charge problem to occupation of these two witness families at deep deficit. It does not bound that remaining joint mass. In particular even E_deep=o(J_a) alone does not yield V_G,rem/J_a<1/2: the half-gain baseline remains. No new strict twin-prime inequality is asserted. The original absolute and normalized sufficient conditions remain valid. No external novelty claim or Lean verification.

## 5. Finite diagnostics

Source research/min_unified_future_witness_audit.mjs, derived from 336c270 and executable with node research/min_unified_future_witness_audit.mjs 256 1024 4096 16384 65536. Eight runs in ECMAScript tool runtime passed (five normal, three focus). Uses parent finite T,a,D0 and P=6, z=max(2P,floor(d/4),4(d-mu)), not analytic z; this ensures z>=4 actual slack, so W_exp>=G/4-slack/2>=z/8 even at small finite scale. Per-tag congestion checked with finite max/min z and B terms, not asymptotic constant. Product cap diagnostics boundary P normal or P/2 focus and tick 1 normal or .5 focus; epsilon=.125. Checks exact late and routed partition, actual suffix and drift bound, persistent band, strict crossing with q not dividing P, expensive roughness, equal recorded slot suffix signature, both marginal sums, inclusion-exclusion/product residual and low-fraction budget. No analytic sieve estimates, no literal gcd oracle repeated, no cumulative earlier masks or fresh analytic source-cap test.

| X/mode | deep charge | late charge | routed charge | after two witness masks | low-fraction residual |
|---:|---:|---:|---:|---:|---:|
|256|461.907227|34.749643|427.157584|266.880195|0.500256|
|1024|0|0|0|0|0|
|4096|1306.437068|289.557366|1016.879702|338.306930|5.779788|
|16384|5736.792498|1196.835052|4539.957446|3300.044361|3.309698|
|65536|9694.615680|612.390716|9082.224965|7240.023381|12.788910|
|4096 focus|6040.595409|2565.403562|3475.191848|2757.215868|4.894618|
|16384 focus|35578.336657|17753.691478|17824.645179|15110.880620|13.639573|
|65536 focus|206206.143161|108562.579705|97643.563456|86869.328463|57.836405|

Largest normal: 1150 routed tag-event incidences in 246 source slots, 13184 band checks, 38785 grid checks, 279312 expensive tick witness checks, 1844 grid keys,10161 tick keys. 780 tag-event sources retain >.125 of charge. Largest focus: 5845 routed incidences in2492 source slots, 28833 band checks,52519 grid checks,761855 expensive tick checks,8388 grid keys,97214 tick keys. Boundary payment3270.449495, tick payment9578.568027, overlap2074.782529. 4469 tag-event sources retain >.125 of charge. Finite observed max per-tag boundary load/P=2.886692, tick load4.524963; no assertion these equal analytic constants. Many targets unreached, so figures do not test the conjectural sufficient inequality. The first contents-API save timed out after execution; use Git tree/commit and verify remote content.
