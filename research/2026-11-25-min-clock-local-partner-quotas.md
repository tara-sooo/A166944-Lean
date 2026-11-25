# Direct partner quotas on source/merger cells and incoming gain

2026-11-25 JST. Continues 2c5f5f0b1852ada0bc0837ab279a302e92981ff5 (projected connectivity and weighted destination cohorts), bc057caad390631a6a94b6bcab5ca3bb690c0fb6 (wide primorial transfer), and the ordered-partner idea of the independent prime-root note 0f74d826a528f527d56ac45c285ed00200fc964f. New: direct first-contact partner quotas for arbitrary fractional relative-slab weights, in both projected and physical histories, both endpoint orientations, two independent source/merger spatial scales, incoming-gain budgets, and both forward/reverse contact order. These handle repeated small-to-large attachments without charging all pairs by the historical component size. The remaining two-sector estimates are OPEN. Paper proof, no Lean compilation.

## 1. Setup

Dyadic X, N=X/2 odd original roots M in [X,2X), B=ceil(sqrt(7X)), s=M+2, C0=2M-2, H=4B,a=2B,K=floor((7M-1)/4), H+2B<=min(K-s) eventually. Original canonical MIN prefixes include root and first post-event at/beyond s+H, or twin terminal. Strict increase in even horizon C and time t, C<=2t, gain<=G=2H+B+6. At any selected p, wait<=2r(C), r<=p. Natural weight w_M(C) is wait duration clipped to relative [a,H)/(2r(C)). Sector or masked weight is between 0 and natural w, hence <=1. All proofs hold for any fixed reference subset of original tags, and any such weight assignment; paths and first contacts use FULL original histories, not thinned lists.

For a fixed sector or mask, set U(C)=sum_M w_M(C), R=sum_C r U<=NB, E=sum_C r U^2. Diagonal<=R. Each unordered distinct pair contributes ordered energy 2r(C)w_M(C)w_M'(C) at C. At a shared horizon the two sources differ by <=G/2. All their earlier horizons lie in [C-G,C]. Under no twins the full natural R=NB. The least-factor support S(T)=O(XT/log^3(2+T)) and S(B)=O(XB/log^3 B) are inherited.

For MED choose z largest prime cutoff with primorial L_z<=B^(1/16), T=ceil B^(1/4), eventually z=Theta(log B), z<T. MED means z<p<=T, HIGH means p>T. From 2c5f5f0 and bc057ca, sufficient joint targets on unbounded dyadic windows are natural MED E_m=o(X B^(13/8) u^3), retained HIGH E_h=o(XB u^3), u=log B, and o(XB) HIGH-only linear loss, after o(X) original tag deletion if desired. MED must retain natural weights or explicitly account for amplified/assigned LOW destination losses. The new estimates below apply to both sectors separately, no LOW energy bound.

## 2. Direct contact lists and fractional quotas

At each final C fix the positive-weight cohort I(C)={M:w_M(C)>0}. Each tag's entire original prefix up to C exists. For each tag i, consider the partners j != i in this cohort. In projected contact mode J_ij is the FIRST ACTUAL common horizon of the two original prefixes, not the historical connectivity LCA from the previous note. In physical mode restrict partners to the same arrival time at the final C; J_ij is the horizon of their FIRST ACTUAL shared physical vertex (t,J). This exists and is <=C. Since a shared physical vertex has deterministic continuation, for two tags reaching C a physical meeting implies same final arrival time, and every subsequent common state up to C has same physical time. For two distinct tags in the projected mode, their incoming labels p_i,p_j at J_ij differ (root label 0 allowed): if the same nonzero p, both had visited J_ij-p+1 earlier; two roots cannot share their initial horizon. In the physical mode incoming labels may coincide if predecessor times differ. All these labels refer to the event ENTERING J_ij, not the final selected label at C.

Given ANY partition of tag i's partner list into bins, assign a nonnegative quota q_b to each bin. Order the partners in that bin by J_ij, ties by increasing original source M_j (or reverse this total order). For a given partner j, let A be the sum of the final weights of partners preceding j in its bin. Pay weight

    a_ij=min(w_j(C), (q_b-A)_+), f_ij=a_ij/w_j(C).

Then 0<=f_ij<=1 and exactly sum_{j in bin} a_ij=min(q_b,sum_{j in bin}w_j(C))<=q_b. Partial payment is an allocation of energy, not deletion of an actual original root or a modification to the dynamics. At every unordered pair take the maximum of the fractions offered from its two endpoint directions, or from further independently valid schemes. The energy charged to one scheme at C is no more than

    2 r(C) sum_i w_i(C) sum_b q_b.                    (1)

Indeed max(f_ij,f_ji)<=f_ij+f_ji, and multiplication by 2r w_i w_j and summation over unordered pairs gives (1). If each leaf's quota sum is <=K m, the energy of this scheme summed over C is <=2KmR. This covers arbitrarily old histories and arbitrary light-heavy/heavy-heavy products, not just a complete pair with a small integer partner rank. The same argument works for independent projected and physical lists, and their max-union costs at most the sum of their separate bounds.

The GLOBAL scheme is one bin with quota m, so bound 2mR per contact type/order. The prior prime-root ordered-rank bound used monotone natural tails and larger-source persistence. Here fixed final fractional weights remove the need for monotone clipped tails, and both endpoint orientations and projected contacts are allowed. This does not assert that first projected contact causes persistent synchronization.

## 3. NEW joint source/merger-cell quotas

For 1<=d,D<=B, partition original source M_j-X into half-open cells of width d, and FIRST contact horizon J_ij-2X into half-open cells of width D. Use the pair of cells as the bin for fixed tag i. All partners' sources at C lie in an interval of width G/2, and their contact horizons in an interval of width G. Thus the number of occupied bins per leaf is <=(ceil(G/(2d))+2)(ceil(G/D)+2), uniformly O(B^2/(dD)). Assign every bin quota

    q(d,D)=m dD/B^2.

Then total quota per leaf O(m), and for either contact type and either order

    E_local(d,D) <= O(m R).                           (2)

This is an actual energy bound using new partners at their first direct contact, even for arbitrarily many small attachments to a historical giant. It does not charge the size of a child component as if all of its roots visited an indirect connectivity merger. Partner source cells and merger-horizon cells are independently aligned, no cover assignment is needed: every partner has exactly one bin relative to each focal tag for a fixed scale pair. The proof does not assume that a cohort's time or gain spans are typical.

For a residual positive fraction after imposing both endpoint directions and both orders, in EACH scale pair the total partner weight through the pair (including its own partner weight) in the forward order must exceed q(d,D), and the same is true in reverse order. In particular the OTHER partners preceding the pair have weight >q(d,D)-w_j>=q(d,D)-1, and likewise those following it. These are disjoint sets for that fixed list and ordering. They all have sources in the cell of M_j and FIRST contacts within the same horizon cell as J_ij. Thus the total bin weight >2q(d,D)-w_j. Ties in J count in source order; this is not necessarily strictly earlier and later horizon. The same condition holds with i,j exchanged, and for both physical and projected lists when the pair shares its final physical time. The certificate describes actual direct encounters in a short horizon interval, not indirect connected components.

For a physical residual pair at merger v, partners with strictly earlier J belong to the focal tag's own incoming physical group at v (deterministic continuation through C), while strictly later J are new companions arriving after v on that common suffix. Same-J partners are in other predecessor groups at v. Hence, writing Q=q(d,D)-1, either preceding weight contains >Q/2 from earlier physical meetings or >Q/2 from the simultaneous batch (with the specified source order), and either following weight contains >Q/2 from later physical meetings or >Q/2 from its simultaneous batch, whenever Q>0. This is a useful necessary alternative for repeated attachments: both endpoint histories must contain local partner mass before/after the pair in the total order, unless a thick simultaneous batch supplies it. No independence between the four lists or their companions is asserted.

## 4. NEW incoming-gain quotas

For each focal tag i and first direct contact horizon J, let p_i(J) be its actual incoming label, or 0 at its original root. Define g_i(J)=max(1,p_i(J)-1). Over all visited horizons of that prefix, sum g_i(J)<=G+1 (one root, all other gains p-1); this includes the final state. Use bins (partner source cell width d, exact first contact J). Assign quota

    q_i(d,J)=m d g_i(J)/B^2.

At a given J, the number of partner source cells is <=ceil(G/(2d))+2. Thus the sum of quotas over all bins is <=m d (G+1)(ceil(G/(2d))+2)/B^2=O(m). Therefore

    E_incoming(d) <= O(m R)                            (3)

for either contact type/order and either endpoint orientation combined. Unlike a uniform cutoff at every merging vertex, this spends more partner budget on a large selected incoming label and less on a small one, in exact proportion to the gain spent by the focal original tag. It does not depend on how many actual mergers happen. A large incoming child can be charged even if the other side is already heavy under the previous formation classification. More precisely if all newly contacting opposite partners of a focal tag in a cell at J have total weight <=q_i(d,J), all those interactions are covered by this scheme regardless of raw historical group sizes. This condition is on the aggregate in that bin, not each individual other child separately. If using the reverse order as well, any residual positive fraction requires >q_i(d,J)-1 weight on both sides of the partner in source order within that exact simultaneous J batch. For small incoming gains the quota can be <1; then the necessary condition is weak, but the fractional bound (3) remains valid.

For HIGH with m=u^(11/4), a focal incoming p>=B/u^(1/4) and source width d=B/u^(1/4) yields quota of order >=u^(9/4). For MED m=B^(5/8), incoming p>=B^(3/4) and width d>=B^(7/8) yields quota >=c B^(1/4) (the incoming event is in the original history, not necessarily a MED selected label). These are examples of why a repeated sequence of thin attachments can now be covered even when no whole merger has small total mass. They are not caps on all actual partner groups.

## 5. Simultaneous growing ladders and exact sufficient residual

Take m_H=floor(u^(11/4)), m_M=floor(B^(5/8)). For HIGH choose widths d_j=D_j=floor(B/2^j) for 0<=j<=floor((log_2 u)/4); for MED choose the same widths through j<=floor((log_2 B)/8). Include ALL combinations (d_j,D_k) of the two scales, all incoming quotas at each source scale, and global scheme. Use both endpoint orientations, projected and physical contact types, and both chronological orders. Treat overlaps by maximum fractions or disjoint priority; energy of union <=sum bounds. By (1)-(3), since R<=NB, total charged energy is

    HIGH: O(XB u^(11/4) (1+log u)^2) = o(XB u^3),
    MED:  O(X B^(13/8) (1+log B)^2) = o(X B^(13/8) u^3). (4)

This is unconditional on all original histories and sector weights; no assumed small global E or negligible deleted pair-energy. The number of scales grows, and the proof controls the complete Cartesian product, not just a fixed finite number. For the smallest HIGH local cells, quota >=c u^(9/4), widths of order B/u^(1/4)=o(B). At the smallest MED cells, quota >=c B^(3/8), widths of order B^(7/8)=o(B). Thus every pair-incidence with residual positive energy after these schemes must satisfy the simultaneous direct-partner certificates of section 3 on both endpoint sides at ALL scales; at the finest scales these imply many actual partners in a substantially shortened source and first-contact interval. For synchronized pairs the physical version adds the common-suffix constraint. These conditions do not give an upper bound on their total residual energy; it is possible in an abstract merger tree to have many partners satisfying them.

The previous projected-cohort small-total potential uses m_H and its all-light-child bound uses floor(u^2) in HIGH (NOT m_H for the latter, since Dmax=O(u/log u)). The physical small-total and same-label internal potential uses m_H. In MED the same m_M can be used for all these. Combine those proved terms with (4) by max-union, disjoint priority, or upper bound by sum. The raw historical light/light forest of 2c5f5f0 and all other applicable prior estimates can also be imposed but are not included in the numerical ledger below. Diagonal is O(XB). Remaining E_m,rest=o(X B^(13/8) u^3) and E_h,rest=o(XB u^3) on the same unbounded windows would suffice with wide primorial transfer, using natural MED and valid HIGH-only masks as before. Neither full residual bound is established here.

## 6. Finite audit

Standalone research/min_clock_local_partner_quota_audit.mjs, final exact remote readback d7f565617decc2efcb3a6e476584bd47bd62e84f, blob b2796989d623e00116bac57c7b7579d1ae640193. Run

    node research/min_clock_local_partner_quota_audit.mjs 1024 4096 16384 65536

Initial forward-only version c138242e7d5c21a5d6cea2e2123d06eaf2aba208 passed 12 runs. Adding reverse and rerunning all windows in one tool call timed out; final script was then committed and read back, and all 12 final runs succeeded in four separate batches (nine smaller-window runs, then one largest-window run per mode). Actual JavaScript function executed in available runtime, not separate Node invocation. Independent canonical MIN paths, literal parity-GCD comparisons at X1024, direct two-pointer prefix intersections per positive sector pair incidence, actual incoming labels at first projected/physical contact, independent previous projected/physical cohort fusion, fractional quotas, per-leaf gain/bin bound, projected/physical union and exact energy partition checked using floating tolerance. The residual certificate counter verifies that neither direction's max fraction reaches one under any of the forward/reverse schemes (equivalent to cumulative partner condition); does not independently prove distribution of strictly earlier/later horizons. No prior root pruning, raw forest exclusions, other masks or cumulative earlier energy deletions. Audit uses natural MED/HIGH sectors. At finite X analytic high ladder has only one width (B), analytic medium at X65536 two widths; diagnostics use three widths B,floor(B/2),floor(B/4). Therefore growth of the full asymptotic ladders is not numerically exercised.

Largest X65536,B678,N32768,794415 events,R402074. Diagnostic z3,L6,T27, m_H=8,m_M=12; wide m_H=16,m_M=24. Previous priority is union of projected cohort small-total/all-light and physical small-total/same-label (not raw historical forest or cumulative prior notes). Prior overlap counted exactly once. In this diagnostic m_LL=m, while analytic high uses floor(u^2) for all-light and m_H for small-total. Each quota has its own finite constant; do not interpret increased coverage from more bins/schemes as a fixed equal-budget optimization or as a proof of negligible asymptotic E. Reverse order adds no new type of mathematical cost, but permits a stronger local residual certificate.

Largest standard diagnostic disjoint ledger:

| term | MED | HIGH |
|---|---:|---:|
| total E |2733359.93|15313316.11|
| diagonal |41523.52|183442.18|
| previous cohort union |552688.46|1797263.97|
| new forward global |606400.71|2395566.05|
| new forward joint local |1143136.94|7374089.88|
| new forward incoming |20915.97|103795.74|
| new reverse union |296049.72|2574426.16|
| remaining |72644.62|884732.13|

Prior residual (after diag and previous union) is 2139147.96 / 13332609.96, so added covered energy is 96.60% / 93.36% of that residual, respectively. Positive weighted pair-incidences625964 / 282995; same-final-time618514 / 277465; first projected strictly before first physical573320 / 258046 among these synchronized incidences. Direct prefix comparison counts25295021 / 11522064. Remaining incidence counts6385 / 11710, all-scheme forward/reverse certificates166010 / 304460. Residual MED asynchronous197.94; HIGH asynchronous0; no claim asymptotic asynchronous suppression.

Among projected historical light-heavy formation incidences at this diagnostic threshold, pre-quota/classification energy1773534.12 MED / 9206811.80 HIGH; remaining after entire new priority union49289.22 / 590123.16. Heavy-heavy residual23355.40 / 294608.98. These are overlapping formation labels and quota classifications, not a separate summable upper bound. Main quantitative finding: repeated light-heavy contributions are substantially covered in these finite diagnostics.

Largest wide same natural E, with larger diagnostic quotas: MED prior1185412.01, global687871.99, local703254.77, incoming13049.93, reverse101323.22, residual924.50 at128 pair-incidences. HIGH prior3743672.86, global3187820.56, local7022307.08, incoming77705.43, reverse1020511.41, residual77856.58 at1225 pair-incidences. Both residuals wholly synchronized; all 3328/31850 certificates. Analytic largest residual0 both sectors with m_H173,m_M58, z2,T6; other finite analytic residuals also zero after reverse. This is a finite cap effect and does not establish (4) as a full energy bound. The larger wide threshold is not a stronger asymptotic theorem.

## 7. Remaining problem

Direct partner quotas convert the prior heavy-component obstruction into dense local FIRST-contact lists, including both orders and both endpoint directions. In physical lists earlier/later strict horizon contacts correspond to persistent old companions and actual later arrivals on a common suffix. The next substantive arithmetic step is to bound thick simultaneous incoming batches, or bound the frequency of dense direct partner arrival sequences in a short gain window with narrow source cells. The new method alone cannot rule out balanced large groups or repeated dense attachments, and does not independently establish either MED or HIGH target. Main unchanged; no Lean compilation, twin-prime proof still OPEN.
