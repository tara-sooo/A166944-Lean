# Ordered larger-partner ranks at first physical mergers

2026-11-25 JST. Continuation of 1f0cadb86f66cb3bd345f002022554f6902bdf42. An asymmetric rank ledger strengthens the previous global and two-source-cell first-merger potential. The key additional fact is that a physically merged larger source never stops before its smaller companion. Thus the smaller root can count larger companions persistently, even with expirations, and classify portions of arbitrarily large merger batches without charging the entire batch. This is a whole synchronous energy exclusion, not a linear deletion of incidences. Remaining high and medium estimates OPEN; no Lean compilation or external novelty claim.

## 1. Ordered persistence and exact rank

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime sources M in [X,2X), F=T² B u. Use the original gain-stopped MIN paths including initial and final vertices. Freeze natural high I (selected p>=Q=ceil(B/u), r>p/sqrt(log p)), before source-specific marks. R_M(v) is the remaining natural high clock at physical vertex v, including any outgoing natural high event. The previous note proves R_M(v)<=R_M'(v) if M<M' both visit v. More strongly, all later vertices of the smaller root occur on the larger path, because gain threshold 2M-2+T and time cutoff floor((7M-1)/4) increase with M and the dynamics is deterministic. This statement concerns only the suffix after a physical meeting.

Fix M. Along its original path maintain the set of larger sources M'>M which have ever physically met M. Every member of this set is present at every subsequent original vertex of M, including its terminal vertex. Therefore the set is increasing, not just in cardinality. The same holds after restricting partners to any fixed source cell. It would be false for smaller companions, arbitrary source-specific accounting masks, or purely projected contacts.

Define the global rank rho(M,M') of a larger physically meeting partner by ordering all such partners of M by first physical meeting horizon, breaking ties by increasing source M'. Define rho_d(M,M') similarly but restrict to partners in the fixed aligned source cell [X+jd,X+(j+1)d) containing M'. The cell containing M is irrelevant to the count. For the cell operation below use distinct cells only. For every fixed smaller M and fixed target cell, the ranks are distinct positive integers; each pair is ranked once, even if it has no future natural high clock. Global rank is the same definition with one cell containing the whole source interval.

At the original first physical meeting v=(t,C) of M<M', let A be the predecessor group containing M, with a starting root treated as its own singleton group. Then
    rho_d(M,M') =
      # {larger partners in target cell at v already in A}
      + # {larger partners in target cell at v outside A with source <= M'}.
The first term is exactly the previously encountered partners, by ordered persistence and the fact that two roots in the same immediate predecessor group have already met. The second term orders the new batch by source. This is an exact state-local reconstruction of the cumulative rank, including zero-tail pairs and terminal meetings.

At any tail layer x>0 for which R_M(v)>=x, every larger partner at v is also qualified (monotonicity). Hence the larger-partner count and rank are independent of x throughout this pair's active natural suffix interval. In contrast, the global mass and the count of smaller partners can change substantially with x.

## 2. Absolute rank-layer exclusion

For an integrable cutoff m(x)>=0, classify the natural synchronous energy slice of a first physical pair M<M' at x in (0,R_M(v)] as covered if rho(M,M')<=m(x). At fixed x each smaller source has at most floor(m(x)) such larger partners, across ALL merger vertices. Counting ordered off-diagonal energy (factor two), and integrating,
    E_rank <= 2N integral_0^(1.5H) floor(m(x)) dx.    (1)
One can replace N by N_x=#sources with initial natural tail>=x inside the integral. There is no restriction on total physical group mass, incoming label, incoming predecessor degree, or number of later shared hits.

Take m0=floor(B u^1.5), m(x)=floor(m0 sqrt(H/x)) for x>0. The integral is O(m0 H); thus E_rank=O(N T B u^1.5)=O(F/u^.25)=o(F). With integer natural clocks the exact per-pair covered energy equals
    2 min(R_M(v), floor(m0² H/rho²)).
For the real integral the floor on the second argument is not required; the discrete integer layer version using integer x yields the displayed equality. We use discrete layers in the finite audit; the same asymptotic bounds follow by sum_{x>=1} x^(-1/2)=O(sqrt H). In the continuous version cutoff m(x) need not be forced to >=1; asymptotic choices here are already >=1 throughout the relevant interval.

The previous global small-total mass condition n_v(x)<=m(x) implies rho<=m(x). The new global rank criterion also covers a pair when there are arbitrarily many smaller ancestors, and covers individual first contacts at the beginning of a large batch even if its final larger mass exceeds the cap. It does not subsume the previous small SAME-LABEL aggregate condition, which is kept independently. In particular no monotonicity of same-incoming-label memberships is used.

## 3. Multiscale one-sided partner-cell ranks

At width d partition sources into aligned cells. Any physically meeting pair satisfies 2|M-M'|<H, by the original gain bound. A fixed smaller M can meet larger roots in its own cell and at most K_d=ceil(H/(2d))+1 distinct cells to its right. For cross-cell pairs only, apply the preceding rank count independently for each target cell. For any m_d(x),
    E_rank,d <= 2 N K_d integral_0^(1.5H) floor(m_d(x)) dx. (2)
This uses the rank order, not the two-cell restricted forest potential, and charges each smaller root once for each allowed target cell.

Use the existing ladder d_j=B2^j<=B u^2.25, m_j0=floor((d_j/B)u^1.75), m_j(x)=floor(m_j0 sqrt(H/x)). Then
    E_rank,d_j = O(N H² u^1.75/B)=O(F/u^.25).
Union over O(1+ell) scales plus the global rank bound gives o(F). All earlier near-pair exclusions are compatible: every pair with separation>B u^2.5 lies in distinct cells at every chosen scale for sufficiently large X. All upper bounds apply to arbitrary retained J subset of natural I by charging the corresponding cumulative natural suffix intervals, not by redefining rank on thinned paths.

This criterion strictly extends the small restricted TOTAL mass test in 1f0cadb: if the larger endpoint's target cell alone has <=m_j(x) qualifying roots larger than M, then rho_d<=m_j(x), regardless of the mass in the smaller endpoint's cell. Even if the larger target cell is thick, the early ranks within a new batch are covered. At distinct cells all roots of the target cell exceed M, so this one-sided condition is exactly a bound on that cell's own mass (and all are tail-qualified whenever M qualifies). The previous small restricted SAME-LABEL test is retained, not automatically subsumed. This is genuinely asymmetric: it does not exclude arbitrary thin smaller-cell vs thick larger-cell pairs, because smaller companions can expire.

Consequently every residual far synchronous pair at its natural tail layer must simultaneously satisfy rho>m(x) and rho_{d_j}>m_j(x) at every scale, in addition to earlier label-specific, global, mixed-high and other conditions. In particular its larger endpoint's source cell must itself be thick; the previous two-cell mass condition only forced at least one of the two cells to be thick. The rank condition additionally requires enough earlier partners or enough earlier-in-batch partners in the larger cell. No bound on such ranks is established. The ordering is chosen by us for the energy ledger; it does not alter MIN.

## 4. Integration

The natural first-physical-meeting interval representation of ae921f73 is exact for full I; for arbitrary final J, restrict the energy intervals to natural hits retained on both roots. Thus all rank slice bounds remain absolute o(F) even after cumulative incidence deletion. Union with previous first-merger and whole-pair bounds. With E_phys,rankbad denoting the resulting synchronous residual, the previous exit-phase absorption gives
    E_J <= (1+O(1/u))(E_phys,rankbad+E_async,bad)+o(F).
The joint sufficient conditions remain Z_m=O(NBu³) and E_phys,rankbad+E_async,bad=o(F) on the same unbounded dyadic windows. No proof of these remaining conditions. In particular, rank budgets alone allow a root to encounter very many larger partners, so no contraction of the full synchronous energy follows. Next: exploit arithmetic restrictions on the sequence of larger-partner arrivals into a given cell, especially large first-contact batches and same-incoming-label merges. Medium and asynchronous estimates unchanged.

## 5. Reproducible audit

Standalone ECMAScript research/min_prime_root_ordered_partner_audit.mjs, exact remote readback at 5df215a13eb1f482b78d0a5e4eec6dd10da54040, blob b04414ad8c076e39b013504a18c5350859a2cf5d. Run:
    node research/min_prime_root_ordered_partner_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node invocation. All 18 runs (three modes x six windows) passed. Canonical SPF original trajectories, literal parity-GCD comparison on X256/1024 (short1183,wide1707,analytic1719), ordered natural tail comparisons, exact state-square synchronous energy versus first-merger min-tail pair sum, chronological global and cell rank counters versus independent state-local predecessor formula at every first physical pair, including zero tails. Checks source-cell localization, one-sided whole-mass cap implies rank cap, integer layer integration and per-layer rank budgets at x=1,128,512, previous global/two-cell hierarchical cap union, extra one-sided and partial-batch energy, disjoint residual. Tests two cell scales only, not growing asymptotic ladder or cumulative earlier near/CRT/other exclusions. All values exact safe integers at tested sizes, with floating threshold evaluation in analytic mode.

Diagnostic short T=B,Q=max(5,ceil(B/8)), wide T=4B,Q7, relative r>p/2, global base cap4/8 respectively. Cell widths d0=max(4,floor(B/16)),d1=4d0, base caps2/4. Analytic T=X/u^.25,Q=ceil(B/u) min5, r>p/sqrt(log p), global cap floor(Bu^1.5), d0=B,d1=4B, cell caps floor((d/B)u^1.75). At finite analytic scales global cap covers all, so no nonempty final residual tested there.

| X | wide sync energy | previous total/label and two-cell union | extra rank union | remaining |
|---:|---:|---:|---:|---:|
|256|4768|4768|0|0|
|1024|12946|12946|0|0|
|4096|197588|197588|0|0|
|16384|1907350|1895650|11700|0|
|65536|19256438|17471980|1725262|59196|
|262144|174040038|138777724|33325066|1937248|

At largest wide X262144,B1355,N20390,T5420: 126505 first physical pairs, 3668455 ordered tail comparisons over all co-visiting root pairs. Each of three ranks checked for every first pair. Previous global and cell union138777724 matches 1f0cadb. One-sided full larger-companion mass gives additional29436706, partial-batch rank slices another3888360; union additional33325066, residual1937248. Global rank alone covers159808908, max global rank100. Fine d84 rank alone covers137160570 across distinct cells, max rank12, 49552 observed root/cell keys including same-cell counters. Coarse d336 covers97586886, max rank25, 26965 keys. These overlapping covers cannot be added. At x512 fine cross-cell covered pair count46256, coarse33290, global52420. Short largest prior32570532, extra8046644 (7306832 one-sided,739812 partial), remaining336604. Analytic largest E120546712 all previous-covered. This is a diagnostic partition of the full natural synchronous term, not the actual cumulative hybrid residual or evidence of the limiting estimates. Main and other branches unchanged.
