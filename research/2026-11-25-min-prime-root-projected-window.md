# Local projected-contact component forests, exact-factor weighted memberships, and endpoint ranks

2026-11-25 JST. Continuation of 66e720fbf1a462ee57415a751df993d45d3aeefe. New absolute medium actual-clock and high proxy exclusions. A local projected contact is not a physical meeting; connect original source tags through a graph of common visited horizons, retaining transitive connections within a finite window in both sweep directions. Resetting the graph between windows has a compensated cost. Refinement down to EACH exact least factor, and more general frozen history classes, is possible without paying a factor for the number of classes, using a weighted membership budget. No full origin-fibre bound or proof of twin infinitude. Paper deductions and finite JS audit, no Lean compilation.

## 1. A finite hyperedge component lemma

Let V consist of n distinct original source tags, ordered by source M. Start with n singleton components. Process a list of hyperedges (subsets of V) in any fixed order, replacing ALL components touched by an edge by their union. Untouched components remain. No vertex expires inside this auxiliary graph; no claim that transitive connections are actual physical meetings. One can initialize all participating roots as singletons before the first edge since a root cannot be connected until it occurs in an edge.

Every unordered pair that ends in the same component has a unique first connection, when its two components first merge. At a merge let the incoming component sizes be a_i, total n_v=sum a_i. The number of newly connected unordered pairs is (n_v²-sum a_i²)/2. At first connection of M<M', define rho(M,M') as its rank among ALL larger partners of M first connected so far in this sweep, with ties at the same hyperedge broken by increasing partner M'. If A is the previous component of M and U their new union,
    rho = # {K in A: K>M}
          + # {K in U minus A: M<K<=M'}.
For each M the rank is a distinct positive integer for each larger connected partner. Thus the total number of first-connected pairs with rho<=m is <=mn. A first connection may be via a chain of other roots, even if neither endpoint or only one is in that hyperedge. The same counting applies.

An independent local gap score g is the difference of positions of M,M' in the sorted NEW union U at the first connection. Let l_v=n_v-max_i a_i, choosing one largest incoming component. Then every newly connected pair has at least one endpoint outside that chosen largest component. The number with g<=k is <=2k l_v. For f(a)=a log a, f(0)=0, the entropy increment is >=(log 2)l_v. Summing telescopes, since singletons have f(1)=0 and no tags expire within this auxiliary graph:
    sum_v l_v <= sum_final f(|A|)/log 2 <= n log(n)/log 2.
Hence at most mn+2kn log(n)/log 2 pairs satisfy rho<=m OR g<=k. All these are entire unordered pair counts per graph, not counts of their shared visits. The rank and gap need not use the original actual arrival times. If n<=N=Theta(X/u), log N=O(u). Taking k=max(1,floor(m/u)) and m/u tending to infinity gives O(mn) covered pairs, including gap-close pairs deep inside a large union. Reverse the edge order independently; the union of both covers costs at most twice this count. Each hyperedge must be processed as a single batch; an arbitrary pairwise ordering inside a shared horizon would change the score. In the constructions below an edge is the full original tag set at one projected horizon in the specified static class/window/cell.

## 2. Actual medium endpoint charges within local windows

Use the inherited X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u), m_g=u^(19/4)/ell^4, LOW primorial L growing at most ell^.25. Original full paths, original gain threshold, sparse medium quota, fixed finest original source cells and normalized partner pools unchanged. For a later-hit least-factor dyadic band P<=r<2P, actual focal E-plus-LOW time b_M(E) and arbitrary subset of charges at that later hit from M to M' obey
    c(M,M',E) <= C0 (P/Q)^(1/8) b_M(E)/m_g.
There are at most k_P original earlier-hit choices, as already proved. Sum over E always uses the original disjoint actual blocks. This holds after arbitrary previous masks, even fractional waiting unit removals. A fixed unordered pair can contribute in BOTH directions; use separate bounds for each.

In an aligned absolute-horizon window of width w, the actual block sum on ONE focal root over any later hits of this band in the window is <=3w+O(P+L). Indeed the waits from first to last such pre-horizon telescope to <=3 times their gain difference <=3w; the last block costs <=2(r+1.5L)=O(P+L). Intermediate selected primes need not be in the band or the medium list. Thus each ordered pair's total remaining charge inside the window is
    O((P/Q)^(1/8) (w+P+L)/m_g).                  (1)
Do not assume the partner's actual wait comparable to focal. Extension beyond the end of the window is harmless by the single last-block bound, not by a restriction of the dynamics. The bound works for a pair that shares only the later horizon, and with arbitrarily many earlier quota predecessors outside this window.

## 3. First-connection ranks in band windows

For each P, use either w=ceil(2(P+L)) or ceil(8(P+L)), independently. For each aligned horizon window and fixed original source cell, use all original frozen medium hits of the band whose pre-horizon lies in the window. Vertices are the distinct participating roots; hyperedges are the sets of visiting roots at each of these horizons, using no previous paid masks. Sweep the horizons in increasing and decreasing order. Every charged pair at E in this window belongs to the same original cell and is in a common hyperedge at E, so it necessarily obtains a first-connection score in both directions. No assertion that these roots ever share a physical state.

Put a_P=(Q/P)^(1/16), m_P=max(1,floor(a_P m_g/u^.25)), k_P^gap=max(1,floor(m_P/u)). Pay the entire remaining pair-window charge if at least one sweep has rho<=m_P or g<=k_P^gap. For arbitrary remaining subset this only decreases the bound. A root participates in O(1+H/w) windows of this band, since its original gain range has length <H. Across all disjoint source cells the sum of window vertex counts is O(NH/w) (w=o(H)). By section 1 and (1), both sweep directions at this scale cost
    O((P/Q)^(1/8) (w/m_g) m_P NH/w)
      = O(NT (P/Q)^(1/16)/u^.25).
Sum over dyadic P geometrically and over the two scales:
    W_window=O(NT/u^.25)=o(NT).
Both the forward and reverse ranks are local to the window, not ranks among all previous projected contacts or physical meetings. The reverse score can be small when a pair had many previous connections but few near the end of the window. This method includes time-disjoint and never-waiting-meeting pairs, and both already-synchronous and immediate-synchronization residuals. It does not require any density of good times along the common repeat segment. No reason that all pairs in a window connect at low rank.

## 4. Weighted membership theorem: exact factors and arbitrary frozen partitions

The preceding bound based on the maximum number of windows per root would overcount if repeated independently for EVERY exact r. Instead partition the frozen medium hits into disjoint static classes within each band P, with ANY rule depending on the original history of that hit. For each class use aligned windows of width w=ceil(c(P+L)) for a fixed c>=1, and fixed source cells as before. Only charge pairs whose later E hits belong to the SAME class. In particular partition by the exact least factor r, which covers every original pair with common E. Alternatively partition by a specified incoming/outgoing label, or joint labels, or other original history signatures; this then covers those pairs agreeing in that signature. Multiple fixed partitions may be unioned with a fixed multiplicative factor, but not arbitrarily many partitions of the same incidences for free.

Let n_A be the number of distinct roots in a class/window/cell graph A, P_A its factor band. Each participating root has at least one ORIGINAL medium incidence in A. For one partition and scale, each incidence belongs to just one A, hence
    sum_A P_A n_A <= sum_original medium hits P(r) <= R <=1.5NH.
This is a weighted membership inequality, not a count of possible arithmetic keys and not a prime-root distribution assumption. In particular no loss proportional to the number of exact factors or history signatures. The window width is O(P+L). Use rank cap
    m_A=max(1,floor((P/(P+L)) a_P m_g/u^.25)),
    k_A=max(1,floor(m_A/u)).
The unrounded caps tend uniformly to infinity (also after division by u); max1/floor harmless. Apply section 1 in each graph and (1) for each covered pair. The total over ALL classes, windows, cells and bands is
    W_class << sum_A (P_A/Q)^(1/8) (P_A+L) m_A n_A/m_g
            << u^(-.25) sum_A (P_A/Q)^(1/16) P_A n_A
            <= O(NT/u^.25).
Unlike the length-count proof of section 3, there is not even a dyadic sum penalty here: the weighted memberships already sum to the actual original gain budget. This argument also works for the band-only partition with this slightly reduced cap. It licenses genuine factor-specific local graph ranks; a very large band union need not mask a small first connection in a single exact-factor graph. In the finite code use the two width constants in section 3 for both band-only and exact-factor partitions, with analytic cap reduced only for exact factor. Diagnostic caps intentionally small. The arbitrary frozen history refinement follows from the same membership proof, but is not separately audited.

## 5. Direct later-endpoint projected ranks for remaining medium charges

At a later E in a fixed source cell use the full frozen original medium hit list at E. All have the same r, hence P. Sort by M, by (original prestate time t,M), and by (actual selected exit time s,M), not by the time after attached LOW. Also partition by actual incoming selected prime q (q=0 for an initial root) and outgoing p. In each cohort sort by M. For each focal M, admit partners at rank distance <=m_P in any of the three global orders, or at relative rank distance <=c_P=max(1,floor(m_P/u)) in any of the incoming or outgoing label cohorts, even when M itself is not in that cohort. Relative distance is number of cohort members between M and M' excluding M and including M'; for the clock orders both tags are in the global list. Use directed links. No need for either partner to be near an end of its own cohort.

There are O(u/ell) candidate incoming positive q (divisors of E(E+2)) and similarly outgoing p (divisors of (E-1)(E+1)), plus at most one root cohort. Thus the directed degree is O(m_P + (u/ell)c_P)=O(m_P), including arbitrary thick groups. Apply the actual relative endpoint bound directly, not an interval cover:
    W_endpoint <= sum_(M,E) O(m_P) C0 (P/Q)^(1/8) b_M(E)/m_g
               <= O(u^(-.25)) sum_(M,E) b_M(E)
               = O(NT/u^.25).
The blocks over all original medium events of a root are disjoint. This is a further absolute deletion, valid on arbitrary earlier-mask subsets. It does not require a first projected or physical contact at E, small numerical exit lag, or a favorable density of good gain-coordinate positions. It is not a bound for ALL deep-rank partners.

## 6. High proxy projected-window energy, including exact-factor graphs

Freeze the natural high incidence set I (selected p>=Q and r(C)>p/sqrt(log p)), prior to accounting holes, as in the earlier high lemmas. For each aligned horizon window w=2B, build the projected contact graph of ALL original high tags with pre-horizons in that window, one hyperedge per horizon. Use both forward and reverse sweeps, rank cap m_h=floor(B u^1.5), gap cap max(1,floor(m_h/u)). For a fixed unordered pair all shared high weights r in this window (both ordered directions) are at most 3(w+B) by the original gain budget on a focal root. Thus each covered unordered pair contributes O(w). Window memberships <=O(NH/w); by section 1,
    E_high,window=O(NH m_h)=O(T²Bu^.75)=o(F0), F0=T²Bu.
No source-cell restriction necessary for this high graph. These are direct projected energy pair/window products, not first physical suffix energies. Include pairs at different actual times and those with no common physical future. Rank membership computed on full original I, so the same estimate applies to any retained subset.

For an even stronger refinement use exact factor r, window width w=2r, or generally a disjoint frozen history partition within a dyadic least-factor band P with w comparable to P. A fixed pair's ordered energy in a graph is O(P): all pre-horizons lie in the window, prior completed gains up to the LAST such pre-horizon are <=w, and the last weight r<=2P. This is important even if the final selected gain p-1 is much larger than P. For exact r the explicit bound is 2(1.5w+r). Sum graph memberships using
    sum_A P_A n_A <= sum_original high hits r = R_I = O(NH),
or weight r exactly for exact-factor graphs. With the same m_h, gap m_h/u, the energy over ALL refined graphs and both sweeps is again O(NH m_h)=o(F0), with no number-of-classes loss. One can use a static partition by (r,incoming q), (r,outgoing p), etc., for matching-history pairs, or a fixed finite family of such partitions. Finite code tests global w=2B and exact r,w=2r; it gives priority to previous direct projected ranks, then global window, then exact factor. This is an absolute direct energy deletion on the retained pair products; union with earlier synchronous and asynchronous exclusions, counting intersections once. No claim that the new graphs' components bound actual physical ancestry mass. Joint residual estimates remain open.

## 7. Reproducible finite audit

Derived standalone research/min_prime_root_projected_window_audit.mjs, latest code commit 9e25e05251f0c508f8286743c69d79c17c38b814, blob de5eb9f4f47d53c7ddb266e6e7956ccb2647e91a, exact readback. Run:
    node research/min_prime_root_projected_window_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_projected_window_audit.mjs --crt-stress --gain-stress --window-stress 256 1024 4096 16384 65536 262144

Executed actual audit function in available ECMAScript runtime. Initial code 12 runs (analytic/concurrent/stress four X256..16384), 8 further (analytic, concurrent, combined three stress, stress X65536/262144). Final exact-factor extension 18 runs (analytic, concurrent, combined three stress, six X256..262144), all successful. Other final modes not rerun. Full original paths and previous gain-axis, waiting/entropy, CRT, and actual quota checks retained. Record exact remaining fractional actual endpoint weight after earlier masks (tolerance <=1e-9 for omitted floating residuals). New graph hyperedges from full original lists even in queried windows selected by residual. Verify total new-pair count via final component sizes, entropy via final components, rank count <=cap*n, gap count <=2*k*minority, query first connection and independent BFS oracle X<=1024 (high query pairs there nonempty), pair window actual block bound, later endpoint arithmetic cohort counts/degree, exact residual partition. Verify high exact factor weighted membership <= full natural R_I, pair/window energy bound, disjoint new high masks. High tests natural high set after previous direct-rank classifier ONLY, not cumulative high residual. Diagnostic bases m=2 medium,4 high (stress 4,8), entropy caps 1 or2; analytic finite retained medium empty. Entropy and fractional cost calculations use floating tolerances, not Lean formalization. The asymptotic arbitrary class weighted membership bound is a paper deduction.

| X | preceding never cost (normal concurrent) | after new window and endpoint masks | total remaining actual cost |
|--:|--:|--:|--:|
|4096|3.833333|1.166667|1.166667|
|16384|53.856061|43.401515|43.401515|
|65536|13.666667|9.5|62.433333|
|262144|118.055556|62.518519|114.315831|

Largest normal concurrent X262144: previous total169.852867592; window masks pay17.833333333 (all never; rank, not additional entropy-gap); endpoint masks another37.703703704 (all never), final114.315830555. Reverse-only window payment7.333333333; second band scale only14; exact-factor incremental0 in tested medium cases. These overlapping subcounts not additive. 144 medium graph sweeps (including both directions and all four graph types), 4028 total root memberships, 277 merges, 66708 first-connected unordered pairs across sweeps, 4704 queried pair scores, max component63. No queried medium first connection via a third root in these tests. 164 endpoint degree checks, max degree9. Combined stress largest previous never30.870370 ->12.222222, new window2.666667 and endpoint15.981481, total82.667682->64.019534. X4096 combined stress remaining never0. Normal X65536 endpoint pays4.166667, window0.

Largest normal high natural E211641172, previous direct rank paid118054019 ordered offdiag. New GLOBAL window additional409772 (async114592, gap-only3863, reverse-only14702, chain-cover4235), exact factor extra0. 390 global graph sweeps, 401230 first-connected pairs across sweeps, 189162 queries, 630 transitive first-connection queries, max component115. Exact-factor 6498 sweeps, 47980 root memberships, 492854 first pairs, 282300 queries, max101, weighted memberships9700710=R_I. Combined stress high global additional21803424 (async6619207, chain-cover57263), exact factor additional163279 (async155313) beyond both global windows and old direct ranks. At X16384/65536 combined stress exact extra1211/29261. This demonstrates nonvacuous exact-factor refinement without an inference about limiting prevalence; medium incremental exact factor remains zero. Natural high energy is not the actual cumulative high residual.

## 8. Remaining proof targets

New residual medium pairs have large projected local first-connection ranks in both sweep directions AND large later endpoint ranks in addition to previous physical/clock/gain-axis restrictions. Exact-factor forests can be refined by actual history classes at no class-count cost, but matching class is required for a given pair. A useful next step is to bound component growth or partner-rank tails by arithmetic of actual reverse histories (especially source groups connected through multiple distinct horizons), or to use the same weighted memberships with a proved bound on high-degree class structure. We have not shown that deep ranks are rare in full original paths. Joint actual medium residual o(NT) and high energy residual o(T²Bu) on the same unbounded dyadic windows remain OPEN, as does twin-prime infinitude. Main unchanged.
