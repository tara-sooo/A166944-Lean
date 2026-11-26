# Integration XXX: dense rough-source transition graph and relay-shift diversity

2026-11-26 JST. Parent 79b2a00f01bfc53eb80133830248d5afd0072c2e. Direct preflight [d8a84b0](https://github.com/tara-sooo/A166944-Lean/blob/d8a84b0a98c00f921b5d94dc9b341709034d00c5/research/2026-11-26-min-direct-mandatory-cross-label-buffer-transport.md). This note uses the source-preserving XXIX extraction, and a DIFFERENT pair from the source-consumer pair: two consecutive actual upward sources with positive extracted weight. Both are rough; this permits a four-form sieve without incorrectly assuming a downward consumer rough. Under the near-minimal support hypothesis and a lower-scale bin-length hypothesis, a macroscopic supply requires a dense directed graph of source-label transitions AND order-Y many different actual shifts on many edges. In particular adjacent sources or sources separated by only one physical event cannot carry macroscopic extracted weight in that regime. No unconditional gap.

## 1. Selected source sequence and actual relay budget

Retain XXIX comparable narrow-guard regime and macro extracted cross-label mass >=rho0 NH after all its filters, with source labels Y<=p<=P<=K0 Y, Y->infinity, P<=B, fixed K0. Here P is an upper bound for SOURCES, not the old consumer bound. Work on each original tag's old prehorizon bin of length L, with L>=B Y^epsilon and L<=H as in XXVIII. Add the lower-scale hypothesis
    L >= P² Y^epsilon1
for fixed epsilon1>0. This is not automatic for top labels or recycling short bins. For example with L=X^.7, Y~X^.2, both polynomial inequalities hold for suitable epsilon,epsilon1. The short recycling bins of XXIX are NOT the bins used for the new CRT sieve.

Assume the original matched source support sum D_s<=D0 (NH/L) log²Y as in XXVIII. With M_*<=K Y and nonempty guards containing a selected p>=Y interval, a positive-weight bin has M_*>=Y-1. Since P=O(Y), min(1,M_*/p) is bounded below there. Thus total ordinary distinct source-label counts across original long bins is O(NH/L log²Y). Before extracting cross matches, discard the small mass of sources lacking both neighboring same-label halfgaps >=a0 log²Y in their original matched lists (XXVIII); choose tolerance small relative to rho0. Source-preserving extraction does not create occurrences or increase weights. In each old tag-bin aggregate retained cross weights a_s once per actual upward source; a_s<=3p+1. Sequence s_1,...,s_n in increasing prehorizon, label p_j. Consecutive retained source prehorizon gap D_j=C_j-C_(j-1) is the actual preceding source gain plus all intervening actual gain E_j>=0; gaps telescope to <=L, independently of consumer overlaps. First source weight <=3P+1 per bin, total o(NH). Weight on transitions D_j>A Y is <=(3P+1) L/(A Y) per bin, hence O_K0(NH/A) overall. Same label with D_j<=A Y is impossible for large Y, because retained good occurrences of that label have spacing >=2a0 p log²Y-2 even if other sources discarded. Fix A sufficiently large depending on rho0 and constants. Thus total weight on distinct-label short source transitions, weighted by actual ENDING source a_(s_j), is >=rho1 NH, rho1>0. No assumptions of consecutive physical events; relays may contain arbitrary events, reset or nonreset. This is a ledger on the actual extracted population, not a new source credit.

## 2. Four-form upper sieve for fixed ordered label pair and shift

Fix one tag-bin, distinct source labels p,r in [Y,P], sides e1,e2 in {-1,1}, and shift D (even, Y-1<=D<=A Y). Necessary horizon conditions
    C=e1 mod p, C+D=e2 mod r
give a unique CRT progression mod pr. On it both actual upward events have neighbors C-1,C+1,C+D-1,C+D+1 free of odd prime divisors f<(min(p,r)-1)/4, since 2w>g at both sources and any eligible rival f would fire within 2f. For odd f>4 below Y, coefficients pr are units; four distinct forbidden roots unless f|D(D-2)(D+2). D>=Y-1>2, so no zero determinant. Actual endpoint phase from XXIX C=e+p(2I-2h-1) mod4p can be retained as an additional parity restriction if desired; ignoring it only increases this count. Each C identifies at most one actual consecutive selected pair on the tag, and no count of hypothetical alternative successors is used as lower supply.

Use the same fixed-dimensional translated upper Selberg bound as direct 9e3203a and XXVI, padded parameter length ceil(L/(pr))+2, cutoff floor(min(Y,L/(pr))^(1/12)) reduced by a fixed factor if needed. The four-form singular correction is
    J(D)=J4(D) J4(D-2) J4(D+2),
    J4(n)=prod_(prime f>4 dividing n)(1-4/f)^(-1).
This overcounts shared singular primes and is an upper factor. The sieve error O(sqrt(parameter length)) is absorbed. Since L>=P² Y^epsilon1, log cutoff comparable to log Y. Thus #candidates at fixed shift and sides <<_(epsilon1) (1+L/(pr)) J(D)/log^4 Y. Ending weight <=3r+1, so the weighted capacity after summing four sides is
    <<_(K0,epsilon1) L J(D)/(Y log^4 Y).                (1)
No rough consumer assumed. This does not claim a four-form result for the earlier cross source-to-downward pair.

## 3. Uniform shift-set bound: no pointwise loglog loss

For each fixed positive integer q, the mean of J4(n)^q over 1<=n<=Z is O_q(Z). Expand J4(n)^q by nonnegative squarefree divisor coefficients f_q(d), with f_q(l)=(1-4/l)^(-q)-1=O_q(1/l) for primes l>4, zero otherwise; sum f_q(d)/d converges by Euler product. For D>=Y-1 up to AY, Hölder on the three shifted factors gives
    sum_D J(D)^2 <= [sum_D J4(D)^6 * sum_D J4(D-2)^6 * sum_D J4(D+2)^6]^(1/3)
                   <<_A Y.
Therefore for ANY subset of shifts Delta of cardinality t, sum_(D in Delta) J(D) <<_A sqrt(Y t). This is uniform even for a subset selected adaptively from actual transitions; no independence of shifts and labels. In particular for an ordered distinct label pair let t_pr be its actual number of distinct short prehorizon shifts in a bin, and W_pr total ending matched weight on those transitions. Sum (1):
    W_pr <<_(A,K0,epsilon1) (L/log^4 Y) sqrt(t_pr/Y).      (2)
Since t_pr<=AY, W_pr<=C L/log^4 Y. The estimate with sqrt(t/Y) is stronger than the uniform per-edge bound for a sparse shift alphabet. This uses fixed moment estimates, not a pointwise singular correction or a claim of exact prime asymptotics.

## 4. Necessary density and transition diversity in actual long bins

Let s_j distinct actual retained source labels in each original tag-bin. The aggregate support bound implies sum s_j=O(NH/L log²Y). The total extracted mass in a bin is <=sum_(sources in bin)(3p+1)<=O(L+P)=O(L), by first-to-last source prehorizon span and actual comparable final gain; NO bound B<<L_s on short bins is used. Choose large fixed C0 so that discarding bins with s_j>C0 log²Y loses at most rho1 NH/4, by the aggregate support bound. There are O(NH/L) bins. Thus at least c NH/L bins have distinct short transition mass >=c L and s_j<=C0 log²Y, for a fixed c>0. All these bins have
    #ordered edges with positive transition weight >= c' log^4Y
by (2), hence s_j>=c'' log²Y. More strongly discard edges with t_pr<=delta Y. On bins with s_j<=C0 log²Y their total weight <=C C0² sqrt(delta) L. Choose fixed delta sufficiently small depending on c and constants. In EVERY such busy bin at least c L/2 weight is on edges with t_pr>delta Y, and each edge has weight <=C L/log^4Y. Hence
    at least c''' log^4Y distinct ordered label pairs each realize >=delta Y distinct actual shifts.     (3)
There are also Omega(log²Y) starting labels with outdegree Omega(log²Y) in this graph: maximum degree <=C0 log²Y, so fewer high-degree vertices could not account for (3). The same holds for incoming degree. This is more than XXIX short-bin diversity: the old source labels cannot be reused with a fixed deterministic successor or a sparse relation and a small set of possible gaps.

Quantitative variants: on all retained bounded-support bins any per-bin directed relation with maximum outdegree d(Y)=o(log²Y) carries at most O(L s_j d/log^4Y) mass per bin, hence o(NH) in aggregate. Likewise ANY family of transitions with at most t(Y)=o(Y) allowed shifts per ordered pair in each bin carries o(NH) by (2) and s_j<=C0 log²Y. For arbitrary tolerance first choose C0 large fixed to discard high-support bins with arbitrarily small mass; take X->infty, then tolerance->0. Thus these two little-o conclusions hold for the whole macro extracted population's distinct short transitions, on the near-minimal aggregate support hypothesis. Constants depend on fixed A. Long-gap and first-source weights can be made arbitrarily small normalized by choosing A large before X, and same-label short transitions removed by the return sieve. No assertion that all actual upward occurrences have dense graph; the statement concerns the selected source sequence.

## 5. Consequences for intervening actual events

For fixed pair (p,r), D=p-1+E with E actual intervening gain. If there is no intervening event, D=p-1. If exactly one intervening event, E=q-1 with q prime <=AY+1. Thus the set of shifts for these two possibilities has size <=1+pi(AY+1)=O_A(Y/log Y)=o(Y). By the uniform shift bound, on the same hypotheses their combined ending weight is o(NH) (for fixed A; O(NH/sqrt(log Y)) on bounded-support bins). This is a genuine exclusion of a simple relay mechanism, not the false assertion that all gaps E are small. Almost all of the retained short distinct source-transition weight requires at least two intervening physical events, counting even unselected, reset, or low-label events.

Likewise if ALL intervening labels belong to the actual source support S_j, then each gain >=Y-1 and D<=AY, so at most floor(AY/(Y-1))<=2A intervening events for large Y. Their sum can take at most sum_(l=0)^(floor(2A)) s_j^l=Y^o(1) possibilities on bounded-support bins. Hence weight on this closed alphabet relay mechanism is o(NH). More generally for a bin-dependent alphabet of q(Y) labels and at most k fixed intermediate events, number of shifts <=sum_(l=0)^k q(Y)^l, which is o(Y) if q(Y)=o(Y^(1/k)) (k>=1). Such relays cannot supply macro short transition weight. These are necessary actual complementary events/label richness conditions; they do not by themselves force macro complementary GAIN outside the selected alphabet, because an outside label can be small. Do not infer a positive loss just from counting events or from (3): a dense graph with many shifts is arithmetically possible at these capacities. Also the lower-scale restriction L>=P² Y^epsilon1 matters: when L/P² is bounded, the four-log saving is not available.

## 6. Diagnostics

Run node research/min_unified_source_transition_graph_audit.mjs 4096 16384 65536. Extend XXIX actual six prime-root runs and 48 controls. Aggregate actual extracted weights once per source; form consecutive source list in old bins; finite A=16. Check actual gap ledger, distinct-label source CRT and actual endpoint phase, four rough forms and generic root collisions, enumerate necessary finite CRT candidates satisfying roughness for each observed tuple, weighted ending capacities and edge/shift support, physical relay length and one-intermediate-prime shift, closed/open source alphabet partition. Finite controls are not claimed to realize near-minimal repeated source support, polynomial bin condition or asymptotic dense transition graph. The prior buffer geometry checks remain in script; no full cumulative kernel, independent analytic sieve verification, Lean. 
```json
{
  "controls": 48,
  "transMass": 306478,
  "transFirst": 256094,
  "transLong": 8144,
  "transSame": 760,
  "transDistinct": 41480,
  "transCount": 2160,
  "transTuples": 1697,
  "transEdges": 1697,
  "transShiftCount": 1697,
  "transRootChecks": 2710,
  "transRoughChecks": 2710,
  "transCapacity": 325292,
  "transZero": 5352,
  "transOne": 6100,
  "transTwoPlus": 30028,
  "transInside": 5352,
  "transOutside": 36128,
  "transSparse": 41480,
  "transSupport": 12106,
  "transBins": 10065,
  "transPhase": 1697,
  "maxShifts": 1,
  "maxDegree": 1
}
```
Main/direct unchanged. Next: restrict multi-event relays or actual source shift diversity by using deficit level/phase constraints, or extend this supply restriction beyond near-minimal/lower-scale assumptions. Macro missing, reset-dominated, high-support and broad-guard branches still open; no final NT-scale strict gap.
