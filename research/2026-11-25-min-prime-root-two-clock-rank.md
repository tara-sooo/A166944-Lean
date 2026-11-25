# Two-clock CRT occupation and entropy control of internal source-order gaps

2026-11-25 JST. Based on 6aa99f5f79bf6a66a5cea76008dc5894fddae676 (waiting cohorts). Two additional absolute deletions for the existing actual-medium and high-proxy ledgers. The first works without a first meeting, including never-meeting pairs. The second covers pairs deep inside interleaved branches at their first meeting, including jump/jump. Original trajectories, partner pools, stopping thresholds and all previous paid masks remain unchanged. Paper deductions and actual finite audit; no Lean compilation, no external novelty claim, twin infinitude OPEN.

## 1. Setup and exact two-clock arithmetic

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) original prime roots, T=floor(X/u^.25), H=T+B, Q=ceil(B/u), m_g=u^(19/4)/ell^4, and the fixed finest original source cells of 8fd0a10. Original actual completed time W_all<=3NH. For a root active at integer tick j, let (C,t0,q,p,s) be its waiting horizon, ORIGINAL entry time, incoming selected label (q=0 for root), outgoing selected label, and scheduled completed exit time. Thus t0<=j<s. Grouped waiting states have the same p,s, but may have different t0,q; do NOT treat the latter as physical-state invariants.

For q>0 the actual incoming congruences are
    q | C+2(t0 mod 2),    t0=0 mod 2q if even, q+2 mod 2q if odd.
The outgoing congruences are
    p | C+sigma(s),       s=0 mod 2p if even, p+2 mod 2p if odd,
where sigma(s)=+1 if odd and -1 if even. These follow directly from the MIN transition and parity clock. For q,p>=5 they are necessarily distinct: equality would imply that the prime divides 2(t0 mod 2)-sigma(s), a nonzero integer of absolute value <=3.

Put Y=max(5,ceil(B/u)), d=max(1,floor(u^1/8)), m=max(1,floor(m_g/u^2)). Let Amax=ceil((Q+1.5L)^2 u^1.5)=O(B²/u^.5) be the inherited repeat gain envelope, with the inherited slowly growing LOW modulus L. At fixed j and source cell, restrict candidate PARTNER tags to q',p'>=Y. A prescribed entry tick t0' determines at most O(1) possible large incoming primes q' (their product divides t0' or t0'-2), and a prescribed exit tick s' determines at most O(1) possible large outgoing primes p'. All such divisors are of positive O(X) integers, and log Y~u. For any fixed distinct q',p' and specified entry/exit parities, even horizons C' obey one CRT residue modulo 2q'p'. In |C'-C|<=Amax there are at most 1+floor(Amax/(q'p'))=O(u^1.5) such horizons. If a parity is unspecified, take both; at most four choices. This is a uniform bound on candidate horizons, not on the number of source tags.

## 2. A sparse concurrent relation with two-clock cohort ranks

At each fixed (j,cell), partition active tags with q,p>=Y into fine cohorts (C,q,t0) and aggregate cohorts (C,q). Sort the original tags of each cohort by M. A tag's two-sided rank is the smaller of its positions counted from the two ends. A cap m selects at most 2m tags in ANY cohort, even if its full original mass is huge.

For each active focal tag a, consider distinct-horizon active partner b in the same cell with |C'-C|<=Amax and q',p'>=Y. Keep a directed link if one of these four tests holds:
    A: |t0'-t0|<=d AND |s'-s|<=d, fine rank<=m;
    B: p'=p AND |t0'-t0|<=d, fine rank<=m;
    C: q'=q AND |s'-s|<=d, aggregate rank<=m;
    D: q'=q AND p'=p, aggregate rank<=m.
The focal's q may be zero in A or B. For C,D it must equal a large positive partner q'. The partner's rank is computed in the FULL active cohort, not after prior deletions. No mass cap on a whole waiting-horizon group is used.

For fixed focal tag, A has O(d²) possible prescribed tick/large-label choices, B and C O(d), D O(1). Each yields O(1+Amax/Y²) candidate horizons after the allowed parity choices. In A,B the entry tick is fixed, hence at most one fine cohort for a given horizon and q'. In C,D the entry tick is intentionally NOT fixed: use the aggregate cohort, with all entry times included, rather than multiply by their number. The outgoing p',s' are already deterministic for a given active waiting horizon at j. Therefore the directed tag degree of the union is
    O(m (d+1)^2 (1+Amax/Y²)) = O(m_g/u^.25).
Symmetrize; the TOTAL ordered pair count is at most twice the directed count even if individual reverse degrees are large. Summing over clock times and disjoint original cells gives
    sum_ordered |G2_(M,M')| << (m_g/u^.25) W_all.
This relation depends only on the full active original paths at j, not on repeat key, quota or future first meeting. B can allow arbitrarily separated exit ticks, C arbitrarily separated entry ticks, D both. A can cover distinct labels and horizons at distances much larger than the old close-horizon cutoff. The rank selection can cover tags of thick exact groups; it does not bound all their pair products.

## 3. Transfer to never-meeting medium pairs

Use the existing concurrent-occupation transfer: for a directed slow overlapping far repeat charge at shared (C,E), extended actual focal interval I=[t_M(C),t_M(F)), common unextended interval J, let eta=u^-1/16. Pay the charge if |G2 intersect J|>=eta |I|, or apply the same test to the union of G2 and the previous good occupation relation. The latter allows payment even if neither relation separately meets the density threshold. The existing actual-relative endpoint bound c/b<=C0/m_g and same-union depth-two cover on the time axis give
    W_new << (1/(m_g eta)) sum_ordered |G2_(M,M')|
          << NT/u^(3/16) = o(NT).
For the union use the sum of the two degree budgets; use priority to count earlier exclusions only once. This proof makes no hypothesis of a later merger; it applies to every never-meeting overlapping pair satisfying the new density test. It is NOT a bound on all never-meeting pairs, or on lower-band time-disjoint pairs. It does not assert that most simultaneous times satisfy the alignment conditions.

## 4. Entropy budget for first-meeting source-order gaps

An independent deterministic lemma on ANY of the existing waiting-state forests or physical tail-layer forests. At a first-meeting vertex let incoming branch masses be a_i, n=sum a_i, and l=n-max_i a_i (choose any largest branch on ties). Let f(n)=n log n, f(0)=0. The local entropy increment is
    D_v=f(n)-sum_i f(a_i)=sum_i a_i log(n/a_i) >= (log 2) l.
Indeed every nonchosen-largest branch has a_i<=n/2. All nonexpired tags map intact to one successor in the corresponding forest. Each root is injected as a singleton, with f(1)=0. For e_v tags expiring at v the loss is f(n)-f(n-e_v)<=e_v(1+log N), including n-e_v=0. The exact telescoping identity is
    sum_v D_v = sum_v [f(n_v)-f(n_v-e_v)] <= N(1+log N).
This holds on all fixed disjoint cells together, or on the entire original forest; at a physical tail layer replace the number of injected/expired roots by N_x<=N. No monotonicity of actual active mass and no assumption of balanced branch sizes.

At each vertex sort ALL n original visiting tags by M; for a first pair in distinct incoming branches let g_v be the absolute difference of their positions in that sorted union. This is not the two-sided rank inside either incoming branch, and not the chronological first-partner rank. Every cross-branch pair has at least one member in a nonchosen-largest branch. Each such member has at most 2m other tags at position-distance <=m. Thus for ANY integer cap m>=1, the total number of unordered first pairs with g_v<=m over the forest is at most
    2m sum_v l_v <= 2m N(1+log N)/log 2.                 (E)
The gap can be small even when both members are deep inside their own branches, the merged total is enormous, and their absolute root distance is large. This covers arbitrary incoming labels, including jump/jump with no stationary endpoint. Pair gap is frozen at the first meeting (at each auxiliary layer for the physical version); do not recompute it on accounting-deleted tags. It is not a bound on all first pairs.

## 5. Medium and high applications of (E)

Medium: for a pair with first waiting meeting at j*, and charged unit j, put x=|j-j*|, H0=ceil(4H)+2. At later-hit least-factor dyadic band P use
    m_gap(P,x)=max(1,floor((m0/u) (Q/P)^(1/16) sqrt(H0/(x+1)))),
    m0=max(1,floor(m_g/u^.25)).
Pay a charged unit if its frozen g_v<=m_gap(P,x), after the existing waiting mass, chronological and local-cohort rank exclusions. At each P,x, (E) bounds the pairs by O(m_gap N u), with at most two clock times and two focal directions. The stronger endpoint density <=C0(P/Q)^(1/8)/m_g from 6aa99f5 applies. Summing over x and geometric dyadic P gives
    W_gap << (Nu/m_g) sum_P (P/Q)^(1/8) sum_x m_gap(P,x)
          << (N m0 H/m_g) sum_P (P/Q)^(1/16)
          = O(NT/u^.25).
Here m0/u tends to infinity; floors and max1 are harmless. This is an additional absolute deletion of actual charged units; it pays some pairs not selected by the two-sided branch rank criterion. Never-meeting pairs have no g_v and are untouched by this second method.

High: F=T²Bu, use the natural high suffix layer x of the existing physical first-merger integral (physical-tail-potential, branch-degree). At every layer x>0 order its original surviving tags at each physical vertex by M, and let g_v(x) be the gap of a first pair's positions in that layer. Prefix restriction keeps the first meeting for any pair present at that layer, including terminal layer snapshots; the potential proof works with layer expiry. Take
    m_high(x)=max(1,floor(B sqrt(u) sqrt(H/x))), 0<x<=1.5H.
The ordered pair count at each layer is at most twice (E), hence the entire natural high synchronous energy slices with g_v(x)<=m_high(x) are
    E_gap << N u integral_0^(1.5H) m_high(x) dx
          << N u B sqrt(u) H
           = O(F/u^.25) = o(F).
Apply to the retained high subset by the existing natural suffix layer upper bound, and union with earlier absolute pair/slice exclusions. No change to linear deletion masks. This covers interior source-order interleavings even for huge groups, including many pairs not selected by branch-boundary ranks. It does not control large-gap thick/thick formations or full reverse ancestry. The joint remaining sufficient conditions still require o(NT) for the actual medium residual and o(F) for high physical plus asynchronous residual, on the SAME unbounded dyadic windows.

## 6. Reproducible finite audit

Derived standalone audit research/min_prime_root_two_clock_rank_audit.mjs, latest source commit 1114d00fe1de89ef9b00c5aa7d05c356f88e8b35, blob eb9b93da2a2ef48e01e9ccb10a8f22cc53be83c4, exact remote readback. Run:
    node research/min_prime_root_two_clock_rank_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_two_clock_rank_audit.mjs --crt-stress 256 1024 4096 16384 65536 262144

Executed the actual audit function in the available ECMAScript runtime (not a separate Node process). Initial version: 28 runs (seven modes at X256..16384), six further short/stress/concurrent runs at X65536/262144. Final version adds up to 64 independent actual-path active-time control samples and optional CRT-stress with Y=5,d=8; all 18 final runs (analytic, concurrent, concurrent CRT-stress at six windows) passed. The other final-version modes were not rerun. All previous exact ledger, literal small-window comparisons, waiting first pairs and potential checks remain. New exact incoming/outgoing congruences, distinct consecutive large labels, degree envelope and two-sided cohort rank selection, symmetric total degree, combined occupation union/cover, entropy increment/loss (floating logs with tolerances), exact integer rank-gap pair counts and medium charge units; three sampled natural high physical tail layers with actual layer expiry. High layer tests use fixed gap cap4, not a full integrated high residual audit. Finite diagnostic thresholds are not limiting savings.

At X262144 normal concurrent: first-wait entropy D=36875.28848298, nonlargest-branch mass19024. Rank-gap unordered counts at caps1/2/4/8/16 =17550/30499/48800/69606/86997. After the inherited waiting/cohort masks, remaining medium cost250.5106727; new gap pays13.45410138 on632 charged units (all outside old raw local rank cap), remaining237.0565713, of which never-meeting185.2592593. In stress mode at X262144 the earlier audit paid an additional .92952381 via48 gap units, remaining20.68112554. At normal X65536 no new gap charge. The high natural sample layers1/338/1355 at X262144 concurrent have 10992/8588/2108 roots, nonlargest masses10184/8087/2007 and 27226/21807/5360 first pairs at cap4. Not an assertion of cumulative high residual reduction.

Normal analytic and concurrent finite quota charges see no newly covered CRT edge. Independent active controls exercise the relation (e.g. X16384 analytic 137 two-clock checks and 8 directed links; X65536 analytic 306 checks and48 links). Diagnostic CRT-stress at X16384:1021 checks,3667 directed links,1008 queried hits (944 beyond old tests), no additional paid edge. X65536:918 checks,2624 links,426 hits (262 new), extra .5 actual charge; never-meeting cost16 ->15.5. X262144:1961 checks,1029 links,382 hits (342 new), extra .33333333 actual charge; final after gap236.72323796, never-meeting184.92592593. The new occupation union is tested before the waiting ledger, so downstream retained sets are recomputed with the same original paths and allocations, not by adding independent paid totals. These are nonvacuous finite diagnostics, not a proof of limiting prevalence.

## 7. Next targets

The new arithmetic relation captures time alignments of two consecutive large clocks, including a subset without any eventual merger. To cover the large remaining never-meeting cost, need a bound for pairs with neither these entry/exit alignments nor the earlier sparse-occupation tests, e.g. a source-conditioned two-path CRT or actual order-gap evolution over long concurrent segments. The entropy lemma pays only rank-close parts of first meetings; need an arithmetic bound on interleaving at large source-order gaps or on actual reverse origin fibres, not another assertion that group masses are small. No complete high or medium asymptotic estimate, no Lean proof, no change to main.
