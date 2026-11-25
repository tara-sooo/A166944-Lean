# Recent-anchor short-wait gains across bounded small-prime bridges

2026-11-25 JST. Continuation of d8dea6f212299e41ce4dcbc98e001bb59d139560 on research/min-prime-root-repeat-energy-2026-11-25. Extends the short-wait CRT gain estimate from immediate incoming labels to recent actual physical anchors within a slowly growing gain window, with arbitrary intervening selected words. The low-mass condition can hold at the earlier anchor even if the current state/group is heavy. Initial-near events are also paid. In the same fast disjoint quota ledger, the interval-cover proof therefore removes additional costs and imposes a recent-history restriction on BOTH residual segments. Does not establish the rarity of old anchors, heavy anchor groups, overlapping segments or the high residual. Paper proof and finite audit, no Lean compilation.

## 1. Definitions

Use X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts M in [X,2X), Q=ceil(B/u). All original gain-stopped MIN paths include terminal states; completed selections have odd prime p<=B, actual wait 1<=w<=2r<=3(p-1), where r is the least eligible prime at the input horizon. Total gain <H per root. At every original physical state (t,C),
    2X-2<=C<=7X, 0<=t-C/2<=3H+3.
Retain the original frozen sparse medium quota and gap-adaptive phase allocation of 8fd0a10, including all its already paid subcharges. No rerunning of MIN.

Use the preceding short-wait definitions of d8dea6f:
    eps=u^-1/64, beta=1/128, gamma=1/512, theta=u^-1/512,
    m=max(1,floor(u^beta)),
    q0(p)=min(Q,max(5,ceil(p u^(1-gamma)/log(2p)))).
A short-wait event has w<=eps(p-1). An actual anchor of a root is a noninitial original physical state (t0,D) entered by selected prime q. Its incoming-q mass g_q(t0,D) is the number of all original visiting tags with that incoming label, including terminals. It is not a count on the retained quota subset. A state may have several incoming labels on different tags.

Set Jmax=max(1,floor(u^(1/512))) and
    J(p)=max(1,floor(min(Jmax,eps(p-1)))).
For any actual short-wait event, eps(p-1)>=1, hence J(p)<=eps(p-1). We support the event by either of the following tests:
- initial-near: C-(2M-2)<=J(p);
- anchor-near: some actual anchor on its own prior original path (including the current input state) with incoming q>=q0(p), g_q(t0,D)<=m, and e=C-D in [0,J(p)].

In the anchor-near case choose the most recent qualifying anchor, or any fixed deterministic choice; this is only an accounting witness. The previously supported immediate incoming events are included via e=0. The same anchor can support different events or roots; the count below does not assume uniqueness of the anchor over all p/e. It only uses strict gain increase and deterministic continuation at fixed anchor and fixed e. In particular a light anchor need not stay light by the time the current event occurs.

## 2. Recent-anchor CRT count

Let (t,C) be the current input and (t+w,C+p-1) its successor. Fix the anchor (t0,D), lag e=C-D, total elapsed l=t+w-t0, and parities s0=t0 mod2, s1=(t+w) mod2. Actual waits and selected gains on all intervening completed steps give
    0<=t-t0<=3e,
    1<=l<=3e+eps(p-1)<=4eps(p-1).
Here e is even and nonnegative. The anchor incoming q and current outgoing p impose
    q | D+2s0,
    p | D+e+2s1-1,
    t0 = 0 or q+2 mod 2q according to s0,
    t0+l = 0 or p+2 mod 2p according to s1.
For all sufficiently large X, p!=q: otherwise p divides the odd nonzero integer e+2s1-1-2s0 in [-3,J(p)+1], of absolute value <p. Indeed p>=1+1/eps for a positive short wait, Jmax=o(1/eps). This proof uses no prescribed transcript or upper bound on its step count other than its gain span. For the finite diagnostic code, a smaller relative J(p) ensures the same distinctness.

For fixed (p,q,e,l,s0,s1) the two horizon conditions fix D modulo pq, and the two clock conditions fix t0 modulo 2pq if compatible. The original slab for t0 at fixed D gives at most
    (floor((5X+2)/(pq))+1)(floor((3H+3)/(2pq))+1)
possible anchor states. Each has at most m original tags with its incoming label q. Each such tag can visit D+e at most once on its original strictly increasing horizon path, so supports at most one current event for this fixed tuple. This remains true if the current physical state has many more tags than the earlier state; other sources that joined later are not counted for this anchor unless they visited it themselves.

The number of possible e is <=Jmax+1, and the number of positive integer l for each e is <=4eps(p-1). The latter estimate is important: no second factor Jmax is incurred in the clock enumeration because the gain window is truncated by eps(p-1). Multiplying by gain p-1 and summing primes gives the total anchor-near supported gain
    G_anchor << m eps (1+Jmax) X
                  sum_{p<=B} sum_{q0(p)<=q<=B,q!=p}
                                 [p/q + H/q²].             (1)
These are all original completed short-wait events, not just medium selections. Multiple witnesses may be overcounted in (1), which only increases its upper bound. The previous proof in d8dea6f established, by splitting the threshold into q>=Q and q>=p u^(1-gamma)/log(2p),
    X sum_{p,q>=q0(p)} [p/q+H/q²]
       << NH(ell/u^.75 + u^gamma ell).
Thus
    G_anchor << NT ell u^(beta+gamma+1/512-1/64)
             = O(NT ell/u^(1/256))=o(NT).                   (2)
The fixed q>=Q version alone gives O(NT/u^(3/512)) with the same Jmax. No asymptotic claim for arbitrary incoming mass or a longer gain window.

Initial-near gain: on each root, all events with input within Jmax of its initial horizon have total gain <=Jmax+B (monotonicity, with the last jump <=B). This bounds even the sum of all such events, not merely short waits. Hence G_initial<=N(Jmax+B), and G_initial/theta=o(NT). Count their union with anchor-supported gains once, for example give initial-near priority to newly supported tags. The enlarged supported measure G_* therefore satisfies
    G_* = O(NT ell/u^(1/256))+O(N(Jmax+B)).
All supports are marked on full original trajectories.

## 3. LOW bridges and the new exceptional history

For the established slow LOW boundary y, even primorial L=2 product_{3<=p<=y}p<=ell^.25, every contiguous block of actual selected p<=y has gain <L (earlier LOW barrier). If a short-wait p is immediately preceded by such a block, its preceding nonLOW selection q (if present) provides a poststate anchor whose gain distance e is the gain of that whole LOW block. Whenever J(p)>=L, that anchor is within the new window. For example this holds eventually uniformly for p>=u^(1/64+1/512), and in particular p>=B^delta for each fixed delta>0. If its label q>=q0(p) and its original incoming-q mass is <=m, the whole short-wait p gain is supported regardless of the number of LOW steps or the size of the current incoming group. If there is no preceding nonLOW event, and the initial LOW block has gain <L, the initial-near condition applies. This is not an estimate on all LOW blocks or on all transitions following a small label; the qualifying earlier q and mass are needed.

An unsupported short-wait event has initial pregain >J(p) and EVERY earlier original anchor within gain J(p) whose label is >=q0(p) has incoming-label mass >m. Equivalently either at least one such recent eligible anchor is heavy (and all are), or none exists. In the second case, if the last actual selection q>=q0(p) exists, its poststate lies at gain distance >J(p); every intervening selection before the current p is <q0(p). If none exists, the whole previous path uses labels below the threshold and its gain >J(p). Thus the second case has a small-label excursion of gain >J(p) between the last qualifying poststate (or root) and the current short wait. This is gain, not step count, and can be caused by one moderately sized selection. For p>=B^delta, q0(p)<=O_delta(p/u^gamma), so these excursions use smaller labels. The heavy alternative does not bound the number of heavy anchors or their gain.

## 4. Transfer by interval cover to fast disjoint medium quota

Keep the sparse quota and the full original small-pool normalization of 8fd0a10/d8dea6f. In the upper medium factor band P>=Q/u^1/24, an existing residual far pair whose elapsed-time segments have disjoint interiors has both actual durations <=2h/u^1/32 for h=E-C, and h>=p(E)-1 eventually, since the retained h>D_r>>Q. On either original segment the gain from non-short-wait events is <=2h/u^1/64. Use exactly the previous criterion on all full sparse long quota edges (including paid tags), now with the enlarged supported gain G_*(M;[C,E))>=theta h. Call these edges fast-supported.

For each source, extend every fast-supported interval [C,E) to [C,E+p(E)-1), length <=2h. Greedy longest-first disjoint interval selection covers the union by triple enlargement. Selected extended intervals are disjoint, and their unextended supported gains are disjoint original events. Hence union length <=6G_*(M)/theta. The actual gain intervals of distinct later medium hits are disjoint in this union; their actual medium clock plus attached LOW cost a(E)<=r+1.5L=O(p(E)-1) in the upper band. Each hit allocates exactly a(E) over k_P predecessors, so the total allocated cost of all fast-supported full quota edges is at most O(G_*/theta):
    R_*^quota = O(NT ell/u^(1/512)) + O(N(Jmax+B)/theta)
             = o(NT).                                      (3)
This proof does not count bridge gains repeatedly for each quota edge or restrict the supporting anchor to lie inside the repeat interval. The measure counts only the selected gain interval of the supported current event itself; the witness anchor may be earlier than C.

Pay both directions of the residual far disjoint allocation: if the focal tag's edge is fast-supported its allocated charge is bounded by its full quota cost; if only the partner edge is fast-supported, the total incoming contribution of all other focal tags in the same full small pool is <=w_r/k_P=O(a_partner(E)/k_P), since the pool shares the same r, and the denominator is s0-1. Focal priority yields a disjoint partition. This pays O(R_*^quota)=o(NT), including all previous direct-witness charges, without changing the partner allocation of 8fd0a10. In particular the incremental support over d8dea6f is absolutely negligible. Do not infer that the old entire uniform asynchronous moment is small.

The remaining upper-band disjoint far pairs have BOTH original segments carrying at least
    (1-O(u^-1/64)-theta) h
gain from short-wait events unsupported by ANY recent light eligible anchor or initial-near test. Each such event thus satisfies the exceptional history of section 3. This replaces the previous immediate-small-incoming or current-heavy criterion, and can cover a current heavy group by a light historical group. It does not force p>=B^delta on most of the gain, rule out long small-label excursions, or establish a small heavy-history moment. The high residual and large physical formation estimates are unchanged. Joint OPEN: remaining medium clock charges o(NT) and E_phys,admitbad+E_async,bad=o(T²Bu) on the same unbounded dyadic windows. No proof of twin-prime infinitude.

## 5. Finite audit

Standalone ECMAScript research/min_prime_root_recent_anchor_gain_audit.mjs, exact remote readback at 291fd9d88f2c5fdab7e10c315e9d501b340f79c3, blob a98889b46f84aa8fd08b9c24328d72488543a026. Run:
    node research/min_prime_root_recent_anchor_gain_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node process. All 42 runs (seven modes x six windows) passed. Inherited canonical SPF/literal comparator, LOW and sparse quota, phase allocation, natural tails and restricted physical potential, previous immediate short-wait CRT and interval cover. New checks full original incoming-q group mass, root-near gain bound, actual backward anchor gap and elapsed-time relation, both CRT progressions and per-tuple finite capacity, no repeated source tag in same tuple/anchor, exact enlarged gain partition, nested old/new supported quota edges, enlarged interval cover, and old vs incremental far-disjoint charges. The arithmetic envelope counts observed tuples, not a numerical test of the limiting prime sums. No full growing ladder, optional cumulative masks or Lean compilation.

Analytic mode uses the stated eps,theta,q0,m,J(p); finite Jmax=1 so no positive even bridge occurs; initial-near extension nonzero. Analytic residual remains empty. Diagnostics inherit d8dea6f modes and use Jmax=24, J(p)=max(0,min(24,p-4)) to exercise positive bridges while ensuring q!=p, finite y3,L6. This diagnostic J may exceed eps(p-1); only the exact l<=3e+eps(p-1) condition is checked there, not the analytic <=4eps(p-1). The finite parameter choices are not asymptotic bounds. The relaxed mode retains eps2.5,rho2,theta.35.

Largest X262144:
- Analytic: old supported gain36216, no positive bridge, initial-near195220; no new fast quota cost. This does not test the asymptotic growing bridge window.
- Short: previous supported gain2741338; new positive-bridge3020992, initial-near752166; 43188 new bridge tags, 42321 LOW-only with gain2902596; 146360 bridge gain at current incoming mass>m. 19327 distinct anchor states within tuples, 6333 tuples, max gap24, max depth7. Extra460 full supported quota edges cost6835 in addition to old1373/cost16184; no retained disjoint far charge.
- Phase/stress/broad: old gain2799136, bridge3099918, initial753262; 44146 bridge tags,43262 LOW-only (gain2969316), current-heavy gain162290. 19558 anchor states,6499 tuples; extra271 full supported quota edges cost657 in addition to old1772/cost4361. Broad retained disjoint cost gets no incremental payment at these settings; total residual7653.0703 unchanged from old fast-witness result.
- Relaxed: old supported gain4140578; new positive-bridge4566724 (4477766 formerly small incoming,88958 formerly heavy with qualifying immediate q), initial-near1176072. 73074 bridge tags, of which71791 LOW-only (gain4385640); 223966 gain at current incoming mass>m. 32318 anchor states in10645 tuples, max gap24, max depth7. Extra1690 full supported quota edges cost4236, compared with old3419/cost8317.3333. Disjoint after near-origin137.7778: old fast support94.2778, incremental bridge/initial support39.1667, remaining unclassified4.3333. Total residual7527.7925 compared with old7566.9592. At X16384 old disjoint payment32.6667 plus11.1111 new; X65536 old7.1667 plus3.4167 new. The finite improvement is for this deliberately relaxed diagnostic, not a test of the upper-band limiting speed.

Main and other branches unchanged by this checkpoint.
