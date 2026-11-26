# Variation-charged repeated returns and moving-stratum capacity

Continuation of [9e3203a](https://github.com/tara-sooo/A166944-Lean/blob/9e3203a1b5c380f1a5b8b3328cddd230a86a7f05/research/2026-11-26-min-direct-repeated-cofactor-cluster-sieve-and-stratum-capacity.md). The previous twin criterion was based on a narrow tube of few post-deficit values, which guaranteed one adjusted stratum per selected label. Here moving strata are allowed. A spacing loss at a repeated label forces large ordinary-deficit variation on a short physical interval. A depth-two subcover of the union of such intervals pays all short-return endpoints by actual variation with no factor for the number of selected labels or dyadic scales. This gives variation-corrected capacity for arbitrary supports, and a more general estimate for stratum-changing short returns. Paper deductions and finite exact diagnostics; no twin-infinitude proof or Lean kernel verification.

## 1. Exact short-return classification

Use the actual MIN convention and ordinary event-plateau deficit d=2t-H. At event p with gain g=p-1, wait w, side e=1-2I, selected cofactor q=(H-e)/p, write d'=d+2w-g and adjusted D=d'-6I=2ph for p>=5. Fix a physical finite contiguous event block of horizon gain L. Let T>=11 be an integer lower label bound. Select an arbitrary subset of its events with p>=T and w>6, whose q are prime. In the intended asymptotic application select long events 4w>=g, p>=T_3=max(256ell+1,1+ceil(9(Y+1)^(1/3))) from the preceding cube certificate. One may further filter to actual surviving-cut crossers, nonresets, or any other subset. The finite arithmetic below also holds when primality of q has been directly checked. Order the selected events of each fixed p by physical position, using only consecutive visits in this filtered list. Other events, including unselected occurrences of p, are unrestricted.

For two successive selected occurrences of p, let m=(q_2-q_1)/2>=1. Recall the exact identities
    H_2-H_1=2mp+e_2-e_1,
    D_2-D_1=2p(l-m),
    l=(n_2-2I_2-n_1+2I_1)/p>=1,
    l=I_2-I_1 mod2.
Since w>6 at both endpoints, H_1=H_2=0 mod3. Put s_i=+1 or -1 representing e_i*p mod3. Then q_i=-s_i mod3. Thus
    m=0 mod3 for same side;
    m=s_1 mod3 for opposite sides.
Let A=6+(s_1-s_2)/2, so A=6,7,5 in the same-side,+ to -, and - to + cases respectively. If D_1=D_2, then l=m and the side parity requires m even on the same side, odd on opposite sides. It follows that the first possible non-twin m is A in the equal-stratum case. Without equality of D, the least non-twin m is A-3. The only possible m=1 case is the + to - change of s (A=7), giving prime cofactors q_1,q_1+2.

Define eta=1 when m=1 and zero otherwise, chi=1 when m is 2,3,4 and zero otherwise. These are precisely the two ways the lower bound m>=A can fail. We have the exact correction
    m>=6+(s_1-s_2)/2 -3 chi -6 eta.                     (1)
For chi=1 the shortfall is exactly 3. In this case parity makes l=m impossible, so D_1!=D_2, |D_2-D_1|>=2p, and
    |d'_2-d'_1|>=2p-6.                                  (2)
This does not need any restriction on the number, labels or clock phases of intervening events. The m>=5 cases may still change stratum; the statement is not that they must preserve it. Nor does arithmetic compatibility of a gap certify an actual path realizing it. For m=1 the prime assumption gives a direct twin witness; the variation requirement is not imposed on that case.

For a selected list of n_p>=1 visits of p, let h_p=sum chi and r_p=sum eta over successive pairs. Telescoping (1) yields q_last-q_first>=12(n_p-1)-2-6h_p-12r_p. Since the pre-horizon span is <=L,
    12p n_p <= L+14p+2+6p h_p+12p r_p.                  (3)
Let b be the number of distinct selected labels, F their total gain, W_short=sum_p p h_p, W_twin=sum_p p r_p, and B_end=sum_{used p}(14p+2)/12. Then
    F <= bL/12+B_end+W_short/2+W_twin.                   (4)
This extends the previous equal-stratum inequality to arbitrary moving strata, at the cost of the new short-return term. W_twin is a nonnegative weight of actual twin-gap incidences in the chosen lists. No finite-twins hypothesis has been used.

## 2. Bounded-overlap physical cover and variation charge

Define the ordinary total variation on the block by
    V_d=sum over all physical events |d'-d|.
For each chi=1 pair take the half-open physical horizon interval
    J=[H_1+p-1,H_2+p-1).
It consists of entire physical event jumps from just AFTER the first selected event up to and including the second. Its length |J|=2mp+e_2-e_1<=8p+2, and the actual ordinary variation V(J) of these events satisfies
    V(J)>=|d'_2-d'_1|>=2p-6.
Using the post-to-post interval, rather than a pre-to-pre interval, is important for the endpoint variation. Every such interval contains the entire ending event jump, of length p-1. Those ending events are distinct across all chosen pairs (including across different labels), since each selected event has at most one predecessor in its filtered p-list. Therefore
    sum_p (p-1)h_p <= length(union J).
Although these intervals can overlap heavily and involve different prime scales, their finite union admits a subfamily covering the same union with multiplicity at most TWO. Proof: choose a subfamily minimal under deletion. If three intervals have common interior, the one which reaches neither furthest left nor furthest right is contained in the union of the two extreme intervals (or one interval contains the others); it could be deleted. This contradicts minimality. With the half-open convention the same argument applies at any common point. Equivalently one can greedily choose the furthest right endpoint at each advance, as in the audit. The overlap bound applies to physical event steps, since all endpoints are plateau boundaries.

For p>=T, both p/(p-1) and (8p+2)/(2p-6) decrease with p. Summing length versus variation over the depth-two subcover gives the finite bound
    W_short <= A_T V_d,
    A_T = 2T(8T+2)/((T-1)(2T-6)) = 8+O(1/T).           (5)
Indeed W_short<=T/(T-1) times the disjoint ending-event gain sum, which is at most the union length, hence at most the sum of subcover lengths. That sum is at most max ratio times the subcover variation sum <=2V_d. There is NO factor b, log X, or number of repeated-label intervals in (5). This charge uses ordinary variation of the actual ray, not the sum of variations along overlapping hypothetical repeated-label paths.

Consequences:
    F <= bL/12+B_end+(A_T/2)V_d+W_twin.                 (6)
For the cube-certified population T=T_3->infinity, the coefficient of V_d is 4+o(1). In particular on any macroscopic crossed block with V_d=o(X), if twins are finite then the total gain of endpoints of short cofactor returns of half-gap <=4 is o(X), even when the support size b is unbounded. Indeed the non-twin short-return endpoint gain is <=W_short, and all twin returns disappear beyond the last twin upper member. More generally without assuming finite twins it is <=W_short+W_twin. Including BOTH endpoints gives at most twice this bound. The total gain in components of size>=2 formed using the half-gap<=4 connection is also at most twice this bound, since every vertex in such a component is incident to a short edge. Thus the result complements the preceding high-dimensional cluster sieve: it constrains short returns independently of the number of selected prime labels, but requires small variation.

## 3. Relative large variation and a general gap cutoff

The previous variation bound can be paid only by the physical events whose ordinary change is large relative to their own gain. For a fixed eta_0>0 define
    V_{>eta_0}=sum_{physical events |d'-d|>eta_0*g}|d'-d|.
In any physical interval the variation of the omitted events is <=eta_0 times its horizon length. Hence for the short non-twin intervals of section 2,
    V_{>eta_0}(J)>=(2-8eta_0)p-6-2eta_0.
Take eta_0=1/8. Then the lower bound is p-25/4>0 for T>=11. The same cover argument gives
    W_short <= B_T V_{>1/8},
    B_T=8T(8T+2)/((T-1)(4T-25))=16+O(1/T).              (7)
Thus (6) remains valid with (B_T/2)V_{>1/8} in place of (A_T/2)V_d. The coefficient is 8+o(1). This version does not require the ordinary variation of all tiny changes to be o(X). The choice 1/8 is a convenient fixed margin; any 0<eta_0<1/4 with positive denominator at T works, giving asymptotic coefficient for W_short of 8/(1-4eta_0).

There is also a uniform general cutoff estimate. Let K>=1 be an integer, not necessarily fixed. Consider ANY selected lists of p>=T>=11 (one list per p, ordered as before), and let W_K^chg=sum p over their consecutive pairs with m<=K and D_2!=D_1. In this part neither long clocks nor prime cofactors are needed, only the exact event coordinates, distinct q, and multiples D of 2p. The intervals [H_1+p-1,H_2+p-1) have length<=2Kp+2, ordinary variation>=2p-6, and distinct ending events. The cover argument proves
    W_K^chg <= A_(T,K) V_d,
    A_(T,K)=2T(2KT+2)/((T-1)(2T-6)),
    W_K^chg <= B_(T,K) V_{>1/(2K)},
    B_(T,K)=2KT(2KT+2)/((T-1)(K(T-6)-1)).              (8)
The second lower bound on relative large variation follows from 2p-6-(2Kp+2)/(2K)=p-6-1/K>0. The formulas are O(K) uniformly T>=11 and asymptotic to 2K and 4K respectively as T->infinity, uniformly in K>=1. This includes m=1 stratum changes, whether or not they yield twins. The first formula at K=4 matches (5) for the deficient non-twin subfamily; the second matches (7).

For components formed by consecutive half-gaps<=K, remove the selected vertices incident to a stratum-changing such edge. Their total gain is <=2W_K^chg. Every remaining connected component has constant adjusted D, even though there may be many different strata in the whole block and arbitrary intervening events. If V_d=o(X/K) along macroscopic windows, these removed vertices have o(X) total gain. The assertion is about remaining components of the ORIGINAL connection graph after vertex deletion: we do not reconnect across removed vertices, which could change stratum. At the prime-cofactor threshold with finite twins, surviving components also have the equal-stratum average spacing of section 1 with no twin correction. This provides a way to reduce short-gap clusters to constant-stratum pieces using a measured variation budget. It is not a claim that most of the total gain lies in short-gap clusters.

## 4. Moving-stratum support partitions and a new twin criterion

For any family of pairwise disjoint physical contiguous blocks B_i, let L_i be their gains, F_i their selected long prime-cofactor gain, b_i their distinct selected support sizes, and B_i^end=sum_{p used in B_i}(14p+2)/12. The selection may differ arbitrarily between blocks. Apply (6) inside each block; the full variation budgets are additive over disjoint blocks. In particular
    sum_i F_i <= (1/12)sum_i b_i L_i
               +sum_i B_i^end+(4+O(1/T)) sum_i V_d(B_i)
               +sum_i W_twin(B_i).                     (9)
There is the parallel bound with (8+O(1/T)) sum_i V_{>1/8}(B_i). The twin terms count only pairs lying in their own block. If b_i<=b0 fixed and the label cap is C, the endpoint sum is O(b0 C times #blocks). Or one can retain its exact weighted discovery mass sum_i sum_{p used in B_i} p, which is better for small labels and varying block lengths. This theorem does not require a tube, a bound on the number of ordinary deficit levels, constant h, or the absence of resets among intervening events. Even the selected events may include resets (D=0); the previous factorization-based small-alphabet support proof did not apply to those. The price is the independently measurable variation and actual support bound.

For example at T=T_3, suppose on arbitrarily large crossed windows one can cover physical blocks of total gain L_* comparable to X, with at most eight chosen labels per block, endpoint discovery mass o(X), and chosen high long gain >=(2/3+delta)L_* for fixed delta>0. Under finite twins no W_twin remains for sufficiently large X, so (9) forces
    sum_i V_d(B_i) >= (delta/4-o(1))*L_*,
    sum_i V_{>1/8}(B_i) >= (delta/8-o(1))*L_*.
These are separate necessary lower bounds; the second excludes supplying the entire required variation with tiny relative changes. If either relevant variation budget is o(X), the same hypotheses instead FORCE a twin-cofactor witness with q>=T_3, arbitrarily large. More quantitatively without assuming finite twins, sum_i W_twin(B_i)>=delta L_*-sum endpoint charges-(4+O(1/T))sum variation (or the trimmed version). The constant 2/3 here matches the former narrow two-deficit-value criterion, but the hypothesis is now bounded chosen support, not a fixed pair of deficit values. In the previous tube case the support was <=8 and all returns already same stratum, so that older theorem still applies without a variation charge. The present extension permits varying and widely separated deficit values, as well as selected resets, when the support and variation conditions hold. It does not prove that a small-support low-variation cover is forced by MIN.

Another concrete consequence uses a greedy partition: starting at the first physical event, keep a block until the next selected event would introduce a (b0+1)st distinct selected label, then start a new block at that event. All intervening unselected events are included. For any selected gain F>(b0/12+delta)G on a window, if finite twins and V_d=o(X) or V_{>1/8}=o(X), (9) forces
    sum_blocks sum_{p used} p = Omega_delta(X).
Hence many repeated local support discoveries are necessary, counted with their prime sizes rather than just the number of distinct labels globally. In particular there are Omega_delta(X/(b0 C)) such blocks and, except the last, each contains exactly b0 selected labels. This follows directly by bounding B_end by a constant multiple of weighted discovery mass for p>=T. It is valid for any adaptive partition with support bound, not just the greedy one. If endpoint discovery mass is not small, this is an alternative to large variation/twins, not a contradiction.

## 5. Connection to the actual crossing-clock alternative

On [X,16X] at the previous cube threshold, let H_T be the actual surviving-cut crossers with p>=T, and U the total gain of ALL events outside H_T. The preceding crossing-clock mass bound gives U=o(X) if smaller-crossing mass is o(X), since T/ell->infinity. Every physical event has |d'-d|<=5g (w<=2p,p>=3); inside H_T it is <=(3+4/(T-1))*g. Define F_move as gain of events in H_T with |d'-d|>g/8, regardless of whether they have prime cofactors or are nonresets. Then
    V_{>1/8} <= 5U+(3+4/(T-1))*F_move.                  (10)
If the above eight-support cover has selected gain >=(2/3+delta)L_* and endpoint charge o(X), under finite twins and smaller-crossing mass o(X) it follows that
    F_move >= (delta/24-o(1))*L_*.
Without any support hypothesis, the same connection gives W_short<= (16+O(1/T)) [5U+(3+4/(T-1))*F_move]. Thus a macroscopic short non-twin return population in the actual long crossers itself forces a macroscopic gain of actual large crossers with relative deficit movement >1/8, unless smaller-crossing mass is macroscopic. This removes the possibility of explaining that population entirely by tiny per-event deficit changes. These are local-to-global necessary conditions on the same physical trajectory, not a comparison of independent ensembles.

The earlier crossing-clock theorem only forces a macroscopic long population OR smaller crossing mass; it does not force chosen gain fraction above 2/3, small support blocks, or small relative variation. Large relative movements, long-gap/isolated visits, and the smaller-crossing alternatives all remain open. No finite-twins contradiction follows from (9) or (10) alone. Next target: control the weighted local discovery mass or the macroscopic relative-movement population, preferably using the event multiplier and exact earliest competing clocks; alternatively force a short-return witness at unbounded p.

## 6. Finite diagnostics and persistence

[Final audit b9837eb](https://github.com/tara-sooo/A166944-Lean/blob/b9837eb7d63c0986d89cf7b79cdf29a9619ddc3d/research/min_direct_return_variation_cover_audit.mjs), blob c8c1bbafa6e63a9e4ae54a8808830fbb0083423f. Exact remote readback. Run node research/min_direct_return_variation_cover_audit.mjs 60000. Actual ECMAScript executed in tool runtime, not a separate Node process. 29998 odd canonical roots through60000,549085 actual MIN events,0 unresolved cap180. 124565 nonempty block/cutoff controls at T=11,17,47, including selected varying-support subblocks and partitions. 243100 selected long w>6 prime-cofactor incidences,228294 per-label spacing checks,14806 repeated filtered pairs,1810 twin-gap incidences,6318 deficient non-twin returns (half-gaps2/3/4 counts2106/2714/1498). All exact post-to-post length, variation and trimmed variation checks passed. 124565 subcover/union/capacity checks,6266 selected cover intervals,maximum actual cover multiplicity2,5584 positive deficient-return blocks,1671 blocks with twin incidences. 10000 independent randomized finite interval-cover controls,maximum multiplicity2. At T17,87831 general K=4,8,32 controls,10678 changed-stratum pair incidences (2705/3508/4465), all general ordinary/trimmed bounds, cover and vertex-removal inequalities checked. 8880 adaptive four-support partitions with11550 blocks, exact aggregate gain/variation and capacity tests. Counts overlap across roots and control choices, not distinct physical twin pairs.

Example p17, q41/47, H696/798, D0/34, ordinary post6/40, m3, post-to-post gain102, variation106, variation from relative moves>1/8 equal104. Example p17 q43/47 H732/798 D0/34 post0/40, m2, post-to-post gain66, total variation88, trimmed86. These finite controls use directly SPF-verified prime q and small cutoffs, not the cube certification at large X. They include resets intentionally, demonstrating that moving strata need not be nonreset. The general-gap proof needs no primality hypothesis; the finite controls use the same selected population for convenience. All final assertions passed, including depth-two overlap and positive changed-stratum/twin cases. No formal Lean verification or new external novelty claim. Main and sibling branches not modified.
