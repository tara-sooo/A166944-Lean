# Nested predecessor-clock potentials and source-local lag graphs

2026-11-25 JST. Continues 4580e75ba854faf268cd3f48335dac94ea2d17af (direct partner quotas), 2c5f5f0b1852ada0bc0837ab279a302e92981ff5 (fractional cohort potential), e15eb81dd0e0e1fe2b98086421b9c5023fd2f313 (rough near-B mergers). Adapts the matching argument of the parallel prime-root branch-degree note d179af254862f3cf24aa064d6c49c6e29b34d579 to fractional destination cohorts and arbitrary small or large same-label incoming primes. NEW nested clock-cell hierarchy pays all clock widths at once, and two-source-cell restriction plus summably weighted lag graphs forces both local aggregate mass and an actual large incoming branch. No full residual bound or Lean compilation.

## 1. Setup

Use all-odd short-clock MIN prefix as in 4580e75: dyadic X,N=X/2,B=ceil(sqrt(7X)),H=4B,a=2B,G=2H+B+6, s=M+2,C0=2M-2,K=floor((7M-1)/4). Original prefix includes first post-state at or beyond relative H or twin terminal. Assume H+2B<=min(K-s), eventually. Strict gain C growth, wait<=2r(D)<=2p at selected p, total gain<=G. For any frozen reference family and final sector/mask, 0<=w_M(C)<=natural clipped wait/(2r(C))<=1. R=sum_C r(C)U(C)<=NB,E=sum_C r(C)U(C)^2,U=sum_M w_M. Original histories always used, no reruns.

Fix final occupied horizon C and cohort of positive-weight tags. All leaf weights fixed to w_M(C) throughout their prefix histories to C. A physical merger v=(t,J) has actual predecessor groups (and root singleton if any), with masses equal to sums of fixed leaf weights. Distinct predecessor groups follow identical suffix after v, so their cross products are assigned uniquely to first physical meeting. At a same-label physical merger with common p>0, predecessor horizon D=J-p+1 is the same, their times t_i distinct and both waits in [1,2r(D)], hence

    1<=h=|t_i-t_j|<2r(D)<=2p.                         (1)

This holds for every original pair first physically meeting by that label, irrespective of any earlier projected contact or asynchronous lag behavior. No assumption about preceding incoming labels. The same-label subgroups can have many predecessor states and arbitrary masses.

## 2. Fractional physical potential

For m>0 use f_m(x)=x^2 if x<=m, 2mx-m^2 otherwise. Nonnegative, superadditive, derivative <=2m. For each merger with masses a_i and total a, D_m=f_m(a)-sum_i f_m(a_i)>=0. On each cohort physical forest, telescoping over all physical mergers (including possible different final arrival times) gives

    sum_v D_m(v) <= 2m U(C).                          (2)

Within a merger first group children by incoming label p, b_p=sum of child masses. Nonnegative decomposition D_m(v)=[f_m(a)-sum_p f_m(b_p)]+sum_p [f_m(b_p)-sum_{i:label p}f_m(a_i)]. All subsequent inner hierarchies or graph arguments can use the latter label potential. Sum over v and p bounded by (2). All labels include root0, but new terms only same p>0. This works for fractional weights, not just integer counts or common unthinned tails.

## 3. NEW all-width predecessor-clock hierarchy at no log cost

For a fixed v,p collect distinct predecessor times t_i and corresponding whole branch masses a_i (one group per physical predecessor). Consider two nested ternary interval grids indexed j>=0:

    [3^j(n+theta),3^j(n+theta+1)), n integer, theta=0 or 1/2.

Each grid is nested, since 3theta-theta is an integer. Width1 intervals contain at most one integer time; all times are positive, so at sufficiently large scale they lie in one interval in either grid. Thus each grid gives a finite hierarchical tree of branch leaves, ignoring empty nodes and unary edges if desired. For each node with mass b and child masses b_l, potential increment f_m(b)-sum_l f_m(b_l)>=0. Sum over this entire tree exactly f_m(b_p)-sum_i f_m(a_i), independent of number of widths.

If two branches have some common cell with total mass <=m, then their lowest common cell also has mass <=m. At that node potential increment equals the entire ordered cross-child product. Thus all pairs admitted by any such light common cell, simultaneously over ALL widths, cost at most the label potential for that grid. Union of two grids costs at most twice the physical potential. Multiply by r(C) and sum final C:

    E_clock(m) <=4m R.                                (3)

This is actual ordered pair energy at final C, assigned at first physical merger. All masses are final occupation weights of actual branches. No cap on full merger mass or same-label aggregate is required; a small nearby clock cell inside an otherwise huge same-label group suffices. Unlike summing independent light-clock-bin estimates, (3) has NO logarithmic factor for the full ladder of widths.

Coverage geometry: for h=|t_i-t_j|>=1 choose 3^j strictly greater than 2h and <=6h. Boundaries of the two grids at this scale are separated by 3^j/2>h, so the closed interval between t_i,t_j cannot intersect boundaries of both. At least one grid contains both in a common cell of width <=6h. (Using closed interval is stronger than needed for half-open cells.) For a pair unpaid by (3), both minimal common cells have mass >m; in particular one of width <=6h has mass >m. Such a cell has at most floor(6h)+1 distinct integer predecessor times, so at least one actual branch in the cell has mass >m/(6h+1). That branch need not be one of the two focal branches. This is an explicit short-clock local concentration certificate at a same-label merger.

## 4. NEW source-local restrictions, including widely separated cells

For d in [1,B], partition original source M-X into aligned half-open cells of width d. At final C all cohort sources in an interval width <=G/2, hence at most K_d(C)<=ceil(G/(2d))+2=O(B/d) occupied cells. Form restricted cohorts for every unordered pair of DISTINCT occupied cells and for every singleton occupied cell. Each tag belongs to exactly K_d(C) such cohorts. Assign each original unordered tag pair to its unique two-cell union, or its singleton cell if same. Recompute physical histories in that restricted cohort, preserving original leaf weights and full original prefixes. First physical meeting and its incoming labels/times are unchanged for a retained pair. Branch mass includes only tags in the indicated union of source cells, including other companions in those cells that reach C.

Apply (3) to each restricted cohort but charge only assigned pairs. Their total admitted energy for that source width satisfies

    E_clock(d,m_d) <= 4 sum_C r(C) m_d K_d(C) U(C)
                   = O(m_d (B/d) R).                  (4)

No assumption that the pair's two cells are close. A clock-residual pair has >m_d weight within a predecessor clock cell of width <=6h, in its two source cells only. The branch certificate becomes >m_d/(6h+1) weight in some one physical predecessor state in those same two source cells. At least one of those two source cells individually contains more than half that mass. This last statement does not identify which source cell, or assert it contains a focal source.

Use source widths d_j=max(1,floor(B/2^j)) and

    m_j=M0 (d_j/B)/(j+1)^2.                            (5)

Then sum_j m_j B/d_j<=M0 sum_{j>=0}1/(j+1)^2=O(M0). In particular the union of ALL source widths down to one, combined with ALL clock widths in each of the two grids, has energy O(M0 R). This costs one summable budget rather than a Cartesian product of two logarithmic ladders. One can use any subladder for a stronger per-scale interpretation. The small m_j at very fine d may yield trivial conditions, but the inequality remains valid. We use the same source ladder lengths as 4580e75 in the finite audit and below. No global component-size cutoff used.

## 5. NEW lag-graph constraint on the pair's OWN predecessor groups

The clock certificate only guarantees a large branch somewhere in the short clock cell. To constrain the pair's own branches, use an additional graph at each restricted same-label subgroup. For k>=0 let h_k=2^k, consider pairs with h<=h_k and, for k>0, h>h_k/2 (k=0 is h=1). Times are distinct integers, so the graph of these edges has max degree <=2h_k. Restrict edges to those whose two actual branch weights both <=mu. For a,b<=mu,

    f_mu(a+b)-f_mu(a)-f_mu(b) >= ab,

since when a+b>mu the increment is 2ab-(a+b-mu)^2 and a+b-mu<=min(a,b). For a matching of graph edges, sum of increments <= label potential by superadditivity and merging remaining nodes. Greedy edge coloring needs <=2Delta-1 colors for maximum degree Delta>=1. Hence ordered sum over these light-light graph edges <=2(2Delta-1) times label potential <=8h_k times that potential. By (2), summed across physical forest, at C the admitted ordered weight <=16 h_k mu U(C). For all restricted two-cell cohorts at source width d_j this becomes <=16 h_k mu K_d(C) U(C). This bound pays all cross products of the two light branches even if a different branch is huge, and does not require a light containing clock cell. It generalizes the prime-root matching argument to these fractional cohorts and exact source-cell unions.

Choose

    mu_jk=m_j/[2^k (k+1)^2].                            (6)

Then sum_k h_k mu_jk=O(m_j); all clock gap scales 1<=h<2B, and then all source scales in (5), cost O(M0 R). Overlap with (3) or any earlier exclusions handled by union or priority; these are whole actual pair incidences at evaluation C, not whole source deletions. A pair not covered by (6) has max(a_i,a_j)>mu_jk for its own two predecessor branches in its two source cells. This is a complementary certificate to (3), which imposes local total clock mass but may be witnessed by a third branch. The finite tests have no additional graph-only energy after prior quotas and the new clock hierarchy, but the paper bound is independent.

## 6. Combined asymptotic targets

Use natural MED z<p<=T, z largest prime cutoff with L_z<=B^1/16,T=ceil(B^1/4), and HIGH p>T (not the incoming label p of the current analysis). As in 2c5f5f0 and 4580e75 the sufficient joint targets are natural E_m=o(XB^(13/8)u³) and retained E_h=o(XB u³), u=log B, with o(XB) high-only linear removal and optional o(X) original-root pruning. LOW destination accounting as before. Write l=1+log u. Choose

    M0_HIGH=u³/l,
    M0_MED=B^(5/8)u².

Equations (3)-(6) give O(M0 R) for the union of both new schemes and all widths, i.e.
    HIGH O(XB u³/l)=o(XB u³),
    MED O(XB^(13/8)u²)=o(XB^(13/8)u³).

No need for the u^11/4 cutoff of the earlier quota ladders here. Use source widths through j=floor(log_2(u)/4) HIGH and floor(log_2(B)/8) MED, as in 4580e75 (can extend farther with (5)). At finest HIGH source width ~B/u^.25, m_j has order u^(11/4)/l³ (with constants), and at finest MED ~B^.875, m_j has order B^.5. For a small same-label incoming p, h<2p, and h_k<2h for h>1. Thus the graph residual forces an actual one of the two predecessor branch masses

    > c m_j / [p(1+log p)^2],

and the clock residual additionally forces >m_j total mass in a clock interval of width <=6h<12p inside the two source cells. Some physical predecessor there has mass >m_j/(6h+1). For example if HIGH final sector and incoming p<=u^.5, the finest-scale graph threshold is at least order u^(9/4)/l^5, growing polynomially in log B. For MED final sector and incoming p<=B^.25, it is at least order B^.25/u². These are statements about actual fixed final weights, not raw source counts or time-independent occupancies. Every residual pair in the same-label class after all new marks must satisfy both types of condition at every included source scale. Smaller incoming labels enforce stronger local branch requirements. Distinct incoming labels, asynchronous final pairs, and heavy local branches satisfying these inequalities are not bounded by these new estimates. Full two-sector residual targets remain OPEN. This does not assert asymptotic suppression from the finite data.

## 7. Actual verification

Standalone research/min_clock_local_predecessor_audit.mjs, exact readback b87deebad4ee11236a9ece310be13016a083991f, blob 6b0692150790e72d6b10ce491129e17764713fe8. Run
    node research/min_clock_local_predecessor_audit.mjs 1024 4096 16384 65536

Final script executed in available JS runtime for 16 successful runs (four windows x four modes), batched. Original parity-GCD simulation, actual first projected/physical pair-prefix scan, previous weighted cohort and bidirectional quota union inherited from 4580e75. Independent same-label first-merger records include actual predecessor times and check (1). Reconstruct every actual same-label predecessor group by scanning original prefix of each positive final tag; restrict exactly to pair's two source cells. Verify each grid's lowest common cell and potential over ALL cross-time branch products, min width<=6h, per-bin lag graph max degree and matching-derived inequality, summed restricted potentials <=2m_j K U(C), per-k graph bound and actual assigned products, and exact disjoint energy ledger. Floating tolerances for fractional weights. No independent cumulative e15eb81 rare-state cap or other older masks; prior comparison is precisely 4580e75. Same-cell union includes only that cell. Graph budget audit uses actual finite k range and diagnostic md/Hk (without (k+1)^2 factor); analytic uses summable factors. NewScale per-scale raw columns overlap, graphBound field denotes actual assigned graph sum (not theoretical bound); graphPotentialBound is the corresponding upper bound. NewScale clockExtra/graphExtra fields are unused zero placeholders, use sector-level disjoint extras. No limiting inference.

At X65536,B678,N32768 standard previous quota parameters mH8,mM12,z3,T27, source widths 678,339,169. New diagnostic M0=12 and m_j=M0 d_j/B (not analytic (5)); wide previous quota mH16,mM24 and new M0=24. Stress uses SAME prior quotas as standard and M0=64, deliberately larger finite new cap. Analytic uses (5),(6), M0_MED2499.77,M0_HIGH96.38 at largest, one HIGH width/two MED widths, previous residual already zero, not asymptotic scale growth. No changed dynamics.

Largest natural MED E2733359.93, HIGH15313316.11. Same-label first physical merger raw energy MED2456804.73,HIGH13817252.16. Standard previous residual72644.62/884732.13, within same-label class71449.86/845938.20 (about 98.36%/95.61% of respective total residual). New hierarchy extra131.20/1971.95, graph-only extra0, total residual72513.42/882760.19. Same-label raw hierarchy union371124.29/1859556.12 and lag graph raw66736.86/314357.55 (overlap, not additive). 1718244/773547 source and clock checks, 281604/124748 potential checks. Maximum actual lag603, max restricted predecessor arity8, largest min-width/h ratio5.785714... (<=6). Wide previous residual924.50/77856.58, new extra0/347.47, residual924.50/77509.12. Stress previous same standard, hierarchy extra37534.56/284871.96, residual35110.07/599860.18, incremental 51.67%/32.20%. Stress raw clock union2032563.83/10131908.33, raw graph298909.59/1454196.45, graph-only extra0. Stress is larger finite threshold, not an improvement at identical constants. All new graph-only extras zero in these 16 runs; independently checked graph bound, not claim independent numerical reduction.

## 8. Next step

The main finite residual is confirmed to be same-label first physical mergers (not merely same-state overlaps), and we now have simultaneous source-local aggregate and focal branch constraints at every lag scale. Next seek an independent upper bound for the actual local predecessor branch mass, via reverse paths with small clock lag, or a bound on the number of repeated attachments from those branches. Mere count of possible high reset vertices cannot control this main term. The local graph/clock results do not rule out large incoming branches or show either full sector energy bound. Main untouched; no Lean compilation or twin-prime proof.
