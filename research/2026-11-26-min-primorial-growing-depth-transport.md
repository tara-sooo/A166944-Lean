# Growing-depth small-set transport and nonsingular strip excursions

2026-11-26 JST. Continuation of e7355cf0165a8cfb44a72b8d137ddb49d3252559, research/2026-11-26-min-primorial-bounded-strip-ancestry-moments.md. Paper deductions and finite Python audit of the ordinary uncut offset MIN. No Lean kernel check, novelty claim, or proof of twin infinitude. No canonical branch or formal target changed.

## 1. Explicit first-bad transport inequality

Let a finite directed graph have outdegree at most one, and I(y) denote indegree. For M>=1 integer let H={y:I(y)>M}. For h>=1 and any target set S define Anc_{<=h}(S) to be all vertices having a forward path of length at most h ending in S (including S itself). Then

    |Anc_{<=h}(S)|
      <= (h+1) M^h |S|
       + (h+1) M^(h-1) sum_{y in H}(1+I(y)).              (1)

Indeed paths entirely outside H have at most M^j possible j-step origins for each target. For a path meeting H, consider its FIRST vertex y in H, counted from its origin. At distance j>=1 to y, there are at most I(y) M^(j-1) origins on paths with all earlier vertices outside H. At distance zero count y itself. Sum j from 0 to h and y over H. This bounds all such origins even if they subsequently visit more exceptional vertices. The estimate counts distinct origins by an upper bound on paths, so no independence or disjointness of exceptional ancestor trees is assumed. In particular it does not repeatedly multiply the exceptional indegrees at successive visits.

## 2. Uniform growing-depth transport in a strip

Fix C>1, a>=0, b>0 and gamma>0 with gamma(a+1)<b. Let Y tend to infinity and let D>=6 be even with D=O((log log Y)^a). Use all envelope-valid local states 12<=u<=C Y, u even, v=(u+d)/2, d even, 0<=d<=D, d<=u+2. Include their genuine MIN edges if the source label satisfies p<=u/2+1 and the destination remains in the same graph. This cut includes every pre-first-record edge from an arbitrary integer reset whose endpoints lie in the graph. There is at most one outgoing edge per vertex, and the offset increases strictly.

Let L=D/2+1. For an arrival (U,V), d'=2V-U and c=0 for V even, c=6 for V odd. The exact arrival identities give

    2p | (d'-c);
    p | U if V even, p | U+2 if V odd.

Each p forces its predecessor offset U-p+1, and leaves at most L choices of predecessor deficit. If d'!=c then I<=L omega_odd(|d'-c|/2), where omega_odd counts distinct odd prime factors. Otherwise I<=L omega(N), where N=U+c/3. There are at most two singular rows for any U, and N is positive <=CY+2. Off the singular rows, I<=L log(D+6)/log 3.

Choose a sufficiently large fixed K>0 and M=L ceil(K log log Y). All nonsingular vertices have I<=M for large Y. The elementary bound

    sum_{n<=Z} 2^omega(n) <= Z (1+log Z)

follows by counting squarefree divisors and bounding the resulting harmonic sum. For k0=ceil(K log log Y), use (1+j) <= C0 2^(j/2), j>=0. The exceptional indegree mass satisfies

    sum_{I>M} (1+I)
      <= C1 L sum_{N<=CY+2, omega(N)>k0} (1+omega(N))
      <= C2 L Y log Y 2^(-k0/2)
      = O_C(Y L (log Y)^(1-K log 2/2)).                   (2)

The constants in this display are uniform in D; a larger absolute constant handles the two singular rows and small U. This argument does not require any of the prior fixed-moment sieve estimates.

Now suppose |S|=O(Y/(log Y)^b) and

    h <= gamma log log Y / log log log Y.

Since log M <=(a+1) log log log Y+O(1),

    (h+1) M^h <= (log Y)^(gamma(a+1)+o(1)).

By taking K so that K log 2/2 > 1+gamma(a+1), equations (1)-(2) imply

    |Anc_{<=h}(S)|/Y
      = O((log Y)^(-b+gamma(a+1)+o(1))
           +(log Y)^(1-K log 2/2+gamma(a+1)+o(1)))
      = o(1).                                              (3)

For any fixed sigma<b-gamma(a+1) choose K still larger to get O(Y/(log Y)^sigma) origins. Unlike the earlier fixed-depth moment theorem, (3) permits a slowly growing strip width and a growing depth. It counts all local origins, hence also the subset of genuine reset origins, without assuming actual reset reachability of all strip states. The normalization is Y, not the total graph size O(DY).

## 3. Application: high-label departures from a low-deficit strip

Use the same graph's vertices as sources, but now do NOT require the destination of the departure to remain in the strip or below CY. Let S_T be the subset whose genuine next event has p>=T and p<=u/2+1. This source cut is necessary: the twin-derived large records are not part of this count.

If T>=max(17,2D+2), nonnegative postdeficit gives w>=(p-1-d)/2>=p/4. Every odd prime factor q of either neighbor has a competing clock within 2q, so q>=p/8. The selected neighbor is composite: p<=u/2+1<u-1 for u>=12. It has a proper factor <=sqrt(u+1), hence p<=8 sqrt(u+1). For fixed p and sign, write the selected neighbor p k. Both k and p k +/-2 avoid odd primes <p/8. The earlier two-form Selberg upper sieve (record-displacement-and-supply and descent-support-sieve notes) gives O_C(Y/(p log^2 p)) possible source offsets, because the multiplier interval length O(Y/p) is at least a constant times p. Each source offset has at most L possible deficit values. Summing over p>=T by Chebyshev's dyadic prime bound gives

    |S_T| <<_C L Y/(log T)^2.

Take T=exp((log Y)^theta), 0<theta<1 (or T=Y^epsilon with any fixed epsilon>0). Write theta=1 for the polynomial cutoff case in the next conclusion. For the growing strip in section 2 this gives |S_T|=O(Y/(log Y)^b) for every b<2theta. Therefore for gamma(a+1)<2theta, all but o(Y) of the integer reset seeds with initial offset in [Y,2Y] cannot reach such a high-label pre-record departure in the first h+1 events, provided every source state up to that departure remains in the strip 0<=d<=D and u<=CY. Take C>=2 for this application. The last event may leave the strip: only the prefix to its source is counted by (3).

This quantitative rarity of early high-label departures does not bound the first exit time from the strip. Small labels can accumulate deficit and leave the strip before a large departure; a long prefix is also not covered. It does not bound the frequency of actual first records, for which the source-label cut may fail. No twin-infinitude conclusion follows directly.

## 4. Deterministic length bound between singular arrivals

For any strip path (not necessarily with the source cut), an arrival with d'!=c has

    p <= |d'-c|/2 <= max(3,D/2) = B.

The factor 2 in the first inequality uses evenness of d'-c and oddness of p. This sharpens the previous D+6 bound on such labels. Let Q=2 product_{3<=p<=B, p prime} p. In any run of events with ONLY nonsingular arrivals the entire label alphabet divides Q. An even multiple J of Q cannot be strictly crossed by any such event. In fact if u<J and p|u+-1, then J-u is a positive even integer congruent to +/-1 mod p, hence J-u>=p-1. At u=J no such label is eligible. Thus the run is contained in one interval between successive Q-walls (allowing arrival at the upper wall), and its total gain is <=Q, length <=Q/2. This applies to a run beginning at any state, including a singular state, and holds uniformly in the offset scale. The bound is generally very large as D grows; it is not a uniform bound on all strip paths.

For a segment having s singular arrivals, there are at most s+1 runs with only nonsingular arrivals, so total event count <=s+(s+1)Q/2. In particular, for fixed D, unbounded strip-path length requires unbounded visits to the two singular rows d=0,6 with their appropriate time parities.

There is an induced graph on the singular states: connect a singular source to the next singular arrival if the whole intervening path stays in the strip graph and has no earlier singular arrival. This graph still has unique forward successors. For a singular target y, each immediately preceding state x has at most Q+2 singular origins that can reach x without an intervening singular arrival, since their offsets lie within Q behind x, and there are at most two singular states per even offset. If x is already singular only x is used. Consequently the induced indegree J(y)<=(Q+2)I(y).

For FIXED D, apply (1) to this induced graph with cutoff (Q+2)M. Its exceptional mass is bounded by (Q+2) times the original exceptional mass in (2), since J>(Q+2)M implies I>M. Thus the same conclusion (3), with a=0 and gamma<b, holds for origins reaching a set of O(Y/log^b Y) singular targets in at most h singular returns, even though the number of intervening ordinary events can be larger. For arbitrary strip targets, replace each target by the possible last singular origins at distance <=Q, at most Q+2 per target, and apply the induced graph result; include targets already singular. This proves the corresponding estimate from singular reset origins to arbitrary small target sets after at most h singular returns. No uniform-in-D claim for this induced graph is made.

The deterministic excursion bound supplies a way to compress the local dynamics to singular visits without making any stochastic assumption. It does not bound the number of singular returns themselves. Indeed the earlier direct-reset CRT chains show that the number of such returns need not be uniformly bounded.

## 5. Executed audit

Source research/min_primorial_growing_depth_audit.py at 90ab9ceadeb2251a2858611846077815522c8ed3; verified remote blob 4982a5ba47cd9d30f2644f749c4273871d32b0ae equals the locally executed git hash-object. Requires SymPy and sibling min_primorial_record_supply_audit.py. Run:

    python research/min_primorial_growing_depth_audit.py 20000

For each strip, all envelope-valid local states at even offsets 12<=u<=20000 were enumerated, keeping edges with p<=u/2+1 and destinations inside the strip/cap. Results:

    D     vertices   edges    max I   Q     max nonsing run   max nonsing gain
    6     39980      27064    16      6     1                 2
    12    69965      52508    23      30    3                 8
    24    129920     105031   33      2310  7                 28

All arrival-label divisibilities and exact degree upper bounds passed. For each graph, 96 finite transport cases were checked using M=2,4,8,16; targets equal to the bad set, a sparse residue sample, or the singular rows; and h=1,...,8. The exact forward reachability sets and the sets of origins whose first bad encounter occurs within the depth satisfy (1) and both component bounds. Largest exact origin-set sizes in these tests: 28077, 53172, 107525 respectively. All 288 transport cases passed. The graph audit does not test asymptotic bounds at an unbounded scale or the full induced graph; the latter and (2)-(3) are separate paper deductions.

## 6. Remaining issue

The small-set transport estimate now has explicit growing-depth and growing-width parameters, and the rank-line crossing strategy can use it for low-deficit prefixes with few enough events or, in a fixed strip, singular returns. But the relevant high-rank crossings require deficit proportional to Y. There is no upper bound yet on the full number of strip returns or on mass transported across an increasing sequence of deficit strips. A false first-record trajectory may have many small-label exits and long ancestry outside these strips. The result does not establish a short-displacement bound G(r), nor unbounded existence of twin records. No Lean verification was performed.
