# Short-wait gain witnesses for fast disjoint medium repeats

2026-11-25 JST. Continuation of 8fd0a103f5d0ce2172f68a78c173dabccb0e93db on research/min-prime-root-repeat-energy-2026-11-25. A new absolute gain bound on actual short waits preceded by sufficiently large incoming primes at low-mass physical states, proved by simultaneous horizon and clock CRT. A one-dimensional interval covering transfers this gain bound to the fast disjoint part of the gap-adaptive medium quota, without a repeated interval multiplicity loss. Both the focal and partner directions are covered. The remaining fast segments must concentrate almost all their gain in small-incoming-prime or heavy physical branches. This does not prove those branches rare, the full medium/high estimates, or twin-prime infinitude. No Lean compilation or external novelty claim.

## 1. Inherited setup

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime roots M in [X,2X), Q=ceil(B/u). Original MIN gain-stopped prefixes include terminal vertices; gain <H, actual waits 1<=w<=2r<=3(p-1), where p is the selected odd prime and r<=p the least eligible odd prime. At every vertex (t,C) one has C<=2t, t<=M+2+3H, C>=2M-2, hence
    0<=t-C/2<=3H+3.
Every original horizon lies in [2X-2,7X]. Only completed events have a positive selected gain; no event at an uncompleted cutoff is invented.

The sparse medium quota from 0ce6427 and gap-adaptive phase allocation from 8fd0a10 are unchanged. In each original source/r/aligned cell A_r=ceil((r+1.5L)^2 u^1.5), after the first k_P hits each later frozen medium hit E allocates its actual cost a_M(E)/k_P to its last k_P preceding hits C, with P<=r<2P, y<p<Q and
    k_P=ceil(u^1.5/ell^1.25+u^1.5 log(2P)(1+L/P)(P/Q)^.25/ell).
Here a_M(E) is the minimum-factor cost plus its attached original LOW block, in [r,r+1.5L], L<=ell^.25. The earlier paid first-use, short-gap, sparse-band, source-cell, gap-phase, tiny/close and near-origin charges are retained. In the remaining asynchronous class, both endpoint input lags are <W_{P,S}=ceil(S u^-1/16 (Q/P)^.75), S<=h=E-C<2S; both successor gaps exceed D_P=floor(P u^1/16). In the upper band P>=Q/u^1/24, W/h<=2u^-1/32 eventually (h grows sufficiently fast). If the two elapsed-time intervals have disjoint interiors, BOTH original segments have duration <W, as proved in 8fd0a10. Also h>D_r>>Q in this upper band, because D_r is of order r u^1.5 sqrt(ell) there. In particular h>=p(E)-1.

## 2. Short actual waits and simultaneous CRT support

Set
    eps=u^-1/64, beta=1/128, gamma=1/512,
    m=max(1,floor(u^beta)),
    q0(p)=min(Q,max(5,ceil(p u^(1-gamma)/log(2p)))).
A completed actual event is short-wait when w<=eps(p-1). At a noninitial original physical state (t,C), let q be that tag's immediately preceding actual selected prime. Use the full original group mass g_q(t,C) of all visiting tags with incoming label q, including tags terminal there. Declare a short-wait event supported if q>=q0(p) and g_q(t,C)<=m. An initial root has q=0 and is not supported. All definitions are on full original trajectories, not only medium hits, and may include actual high or LOW selections. Let G_good be the total selected gain p-1 of supported events over all roots, counting original tags.

The following physical-state count is unconditional. Let s=t mod2, s'=(t+w) mod2. The original incoming clock gives
    q | C+2s,
    t = 0 mod 2q if s=0, q+2 mod 2q if s=1.
The next actual p gives
    p | C+(2s'-1),
    t+w = 0 mod 2p if s'=0, p+2 mod 2p if s'=1.
For q>=5 one has p!=q: the two required residues of C differ by a nonzero integer of absolute value <=3. If p,q are distinct odd primes, the first two horizon congruences fix C modulo pq. The two clock congruences, if parity compatible, fix t modulo 2pq. The time slab above has length 3H+3 for each fixed C. Thus for each p,q,w,s,s' there are at most
    (floor((5X+2)/(pq))+1)(floor((3H+3)/(2pq))+1)
possible physical states. As pq<=B²=O(X), this is O((X/(pq))(1+H/(pq))). The parity factor is at most four; there are at most eps(p-1) possible positive integer waits (zero if this is <1). This counts possible labeled transitions, NOT original source tags or an independent trajectory distribution.

Since at each supported state and incoming label there are <=m tags, summing their gain gives
    G_good << m eps X sum_{p<=B} sum_{q0(p)<=q<=B,q!=p}
                          [p/q + H/q²],                 (1)
all sums over odd primes. Dropping the distinctness in this last positive upper sum is harmless; the CRT derivation applied only to the distinct actual labels.

First consider the fixed incoming threshold q>=Q (included for every p). Elementary prime counting and reciprocal bounds give
    sum_{Q<=q<=B} 1/q << ell/u,
    sum_{q>=Q} 1/q² << 1/(Q log Q) << 1/B,
    sum_{p<=B} p << B²/u, pi(B)<<B/u.
Their contribution inside (1) is O(B² ell/u² + H/u).

For the additional adaptive branch use the threshold R(p)=p u^(1-gamma)/log(2p), ignoring the harmless max5/ceil when bounding q from below. If R(p)>B there are no such q. Uniformly for p with a possible positive short wait, log(2+R(p))>>log(2p): if R(p)>=p this is immediate, otherwise log(2p) >=u^(1-gamma) and R(p)>=c p u^-gamma. The usual tail sum of reciprocal squares of primes therefore satisfies
    sum_{q>=max(5,R(p))} 1/q² << 1/(R(p) log(2+R(p)))
                                 << u^(gamma-1)/p.
Summing p with sum 1/p=O(ell) gives O(H u^(gamma-1) ell) for the H term. For the p/q term split p>=B/u² and p<B/u². In the first region R(p)>=c B/u^(2+gamma), so the reciprocal sum of q in [R(p),B] is O(ell/u); sum p<<B²/u. In the second region use the crude reciprocal bound O(ell) and sum p<=O(B²/u^4), already negligible. Thus the adaptive branch contributes O(B² ell/u²+H u^(gamma-1)ell).

The min in q0 is covered by the union of these two threshold branches, not their intersection. Combining with N~X/u, H~T~B²/u^.25 proves
    G_good << m eps N H (ell/u^.75+u^gamma ell)
           = O(NT ell/u^(3/512))=o(NT).               (2)
Indeed beta+gamma-1/64=(4+1-8)/512=-3/512. If one uses only q>=Q, the sharper O(NT/u^1/128) follows without the adaptive term. The adaptive threshold is smaller for many lower p, and for p>=B^delta with any fixed delta>0 one has q0(p)<=O_delta(p/u^gamma) (uniformly over that range). There is no bound here for all short-wait gains, high-mass states, or arbitrary incoming q. The cap is the original incoming-q group mass, not the whole physical state's mass; a supported branch may lie within a huge state.

## 3. Fast segments force almost entirely short-wait gain

For a full original segment [C,E) of gain h, the sum of actual waits of its events is t_M(E)-t_M(C). If this duration is <=2h u^-1/32, the gain from events with w>eps(p-1) is bounded by
    G_slow(C,E) <= (t_M(E)-t_M(C))/eps
                    <=2h u^-1/64.
This elementary inequality applies to all intervening actual selections, including those not on the frozen medium list. It makes no comparison of actual waiting time with the proxy r beyond the known upper wait bound. It does not claim a short-wait event has small r.

Let theta=u^-1/512. In the upper band P>=Q/u^1/24, call a full sparse quota edge (M,r,C,E) fast-supported if its duration is <=2h u^-1/32, h>=p_M(E)-1, and the supported gain from section 2 within [C,E) is >=theta h. Define this on ALL original sparse long quota edges, including paid tags and before any partner selection; this ensures it is available on both focal and partner roots. Only such full edges that have actual E selections are used. The definition is not restricted to the residual far pairs.

## 4. Interval covering avoids repeated segment charges

For each original root M, extend the gain interval [C,E) of every fast-supported edge to the half-open interval [C,E+p_M(E)-1), including the actual gain interval of the later medium hit. The extension has length <=2h and supported gain >=theta h in its unextended part. Select a disjoint family greedily in decreasing order of extended interval length (finite family, any tie order). Every discarded interval intersects an earlier selected interval of no smaller length, so it lies within that selected interval enlarged by its length on both sides. The length of the union of ALL extended intervals is thus <=3 times the sum of selected lengths. Selected intervals are disjoint, and their unextended supported-gain sets are disjoint subsets of the actual path gain. If G_good(M) is the full supported gain on that root,
    union length <= 6 G_good(M)/theta.                (3)
This is a direct finite interval-cover argument; no probabilistic density estimate. It works for heavily overlapping repeat edges, with different r and P, using a single family per root.

Each distinct later hit E appearing in at least one such edge has its actual gain interval inside the union; these gain intervals are disjoint for distinct hits on that root. In the upper band r>=Q/u^1/24 and L grows slowly, so a_M(E)<=r+1.5L=O(p_M(E)-1). The entire allocated cost of all fast-supported edges on M is at most the sum of a_M(E) over these distinct later hits, since at most k_P edges allocate the cost at each E. It follows from (2)-(3) that the total across all original roots is
    R_fast,supported^quota << G_good/theta
                           = O(NT ell/u^(1/256))=o(NT).    (4)
This is a bound on the actual allocated CLOCK-plus-LOW cost of these edges, not the sum of their interval gains or their unweighted repeat counts. The fixed-threshold-only version with q>=Q and theta=u^-1/256 also pays O(NT/u^1/256).

## 5. Cover both source directions in the far disjoint allocation

Keep the gap-adaptive allocation of 8fd0a10, with full sparse source/phase cells and small-pool normalization. At each key/cell, the far disjoint charges are a subset of the directed charges a_M(E)/(k_P(s0-1)) in the small pool of s0 tags. In the upper band with disjoint elapsed-time intervals, both edges satisfy the fast duration and extension hypotheses eventually. Pay the charge if either focal or partner edge is fast-supported, using focal priority to avoid double counting.

For focal supported edges the entire selected partner charge is at most the focal's allocated a_M(E)/k_P. For a supported partner M', sum over all other possible focal tags in the same small pool; there are at most s0-1, and each a_M(E)<=w_r=r+1.5L. Thus the incoming total is <=w_r/k_P=O(a_M'(E)/k_P), since the partner has the same r, a_M'(E)>=r. This bound holds when some focal tags or partner tags have already been paid, because the denominator uses the FULL pool. Each supported partner edge belongs to a single source/phase pool of that key. There is no multiplication by the number of potential repeat partners or by k_P. Summing (4) bounds both directions:
    R_disjoint,supported=O(NT ell/u^(1/256))=o(NT).     (5)
No reallocation beyond 8fd0a10 is made here. This is a subcharge exclusion from that ledger, not a new allocation and not a bound on the old uniform-partner async moment. All other paid classes can remain as in the previous result.

## 6. Residual structural consequence

Every remaining upper-band time-disjoint far pair (after near-origin and (5)) has both original segments of duration O(h/u^1/32), and each segment's supported gain <theta h. The slow gain is O(h/u^1/64) by section 3. Consequently on BOTH roots, gain at least
    h(1-O(u^-1/64)-theta)
comes from actual short-wait events for which either
    q<q0(p), including the initial label q=0,
or
    g_q(t,C)>m.
For p>=B^delta the first condition in particular implies q=O_delta(p/u^gamma); thus a large short-wait jump outside the heavy groups must have a substantially smaller immediately preceding prime. One can strengthen the latter observation to a count-free gain statement on this subrange, but it does not rule out alternation of large and small jumps. Nor does it force a positive fraction of the total gain to use p>=B^delta; lower labels may still carry the gain. No negligibility of small incoming or heavy branches is proved here. The initial event's total gain across all roots is <=NB=o(NT); if desired its gain can be added to the supported measure using (3) (even multiplied by 1/theta), but this optional extension is not included in the audit.

The remaining medium target is the sum of the previous large already/immediate physical formation charges and the remaining far charges (lower-band, overlapping, and upper-band disjoint with the new gain concentration) being o(NT). The previous high residual E_phys,admitbad+E_async,bad=o(T²Bu) is still independent and OPEN. Both must hold on the same unbounded dyadic windows. The actual new unconditional bound is (5), not a proof that fast disjoint segments as a whole have negligible cost. The next useful arithmetic target is a run of short waits following small incoming primes, e.g. skip a bounded chain of small labels to the preceding larger anchor, or control the heavy incoming-q group by first physical formation. The gain concentration is quantitative and applies to arbitrary intervening transcripts.

## 7. Reproducible audit

Standalone ECMAScript research/min_prime_root_fast_gain_audit.mjs, exact remote readback at eb7f07fc5149dbf30a7506377a037fb23d21571e, blob dbd4555c651d982e6b868a575ee171c61fe5518d, initial audit f6b9962b6097183222b3603b8a16bd481ffe0426. Run:
    node research/min_prime_root_fast_gain_audit.mjs 256 1024 4096 16384 65536 262144
Executed its function in the available ECMAScript runtime, not a separate Node invocation. All final 42 runs (seven modes x six windows) passed. Inherited canonical SPF/literal comparator, LOW, quotas, gap and two-ended phase, successor refinement, directed endpoint caps, near-origin and first-merger potentials, and independent immediate oracle. New full-original-path short-wait gain partition by incoming q and actual original visiting group mass, simultaneous horizon/clock congruences, slab and exact finite CRT progression capacities per observed p,q,w,parity group; segment prefix-gain difference and actual slow gain inequality; union and greedy disjoint interval cover, distinct endpoint clock envelope; supported focal/partner charge union and conservation. Arithmetic state envelope in the audit uses observed tuples and exact integer CRT bounds; it is not a numerical proof of asymptotic prime sum estimates. No full growing ladder or optional cumulative masks. The analytic code still inherits old raw first-merger cutoffs from 8fd0a10, and its residual is empty. Its finite upper-band/fast tests are vacuous at the tested sizes. Analytic eps,rho,theta,q0 and mass are evaluated as stated; their limiting ratios are not achieved here.

Diagnostics inherit the earlier modes and use q0=5,m=8, eps=1,rho=.85,theta=.1 (where rho is the upper elapsed/gain ratio for the fast test), all bands eligible, require h>=p(E)-1. Relaxed mode is broad (wide phase W=4H, T=4B, quota3, band cap2) with eps=2.5,rho=2,theta=.35, to exercise both focal and partner supported costs. These deliberately nonasymptotic choices do NOT justify an o(NT) statement for diagnostic thresholds. Floating roundoff can give a tiny negative zero for a complete partition; reported as zero. This audit exercises the abstract interval/CRT proof without extrapolating finite removal fractions.

Largest X262144:
- Analytic: total short-wait gain12797954, supported36216 (of which20650 added by adaptive threshold below fixed Q), heavy711426, small incoming11855092, initial195220. 11971 physical state-label congruence checks, 2119 observed tuples, 10123 additional states below fixed Q. No fast-supported analytic quota edge or retained cost. These counts do not estimate asymptotic fractions.
- Short: total cheap gain9538250, supported2741338, 50337 CRT state checks, 1373 supported of2457 fast full quota edges, 1313 source covers, union gain75224, selected supported gain34160, distinct endpoint cost16184, supported quota cost16184, no retained disjoint far pair.
- Phase/stress/broad: total cheap12990120=2799136 supported+2792090 heavy+7203674 small incoming+195220 initial; 52461 state checks,6728 observed tuples. 3981 fast full quota edges,1772 supported; 812 source covers,828 selected intervals, selected supported gain21014, union length53154, endpoint cost7074, allocated supported quota cost4361. Broad disjoint after near-origin137.7778, supported focal8.1667, partner0, remaining unclassified129.6111; total final after new exclusion7653.0703 vs prior7661.2370. Stress retained far is overlapping6.6667, unaffected.
- Relaxed: cheap19031438, supported4140578, heavy3852116, small incoming10721408, initial317336; 94084 state checks,11044 tuples. 9663 fast edges,3419 supported,1259 source covers,1301 selected intervals, selected supported gain41902, union length88132, distinct endpoint cost12104, supported quota cost8317.3333. Disjoint after near-origin137.7778 =77.5 supported focal+16.7778 supported partner+39.1667 unsupported fast+4.3333 unclassified. Total residual7566.9592. At X4096 relaxed disjoint15 all supported (12.3333 focal,2.6667 partner); X16384 53.1111=18.3333+14.3333+20.4444; X65536 10.5833=3.6667+3.5+3.4167. These are nontrivial checks of both directions, not examples of the upper-band limiting speed condition. Main and other branches unchanged.
