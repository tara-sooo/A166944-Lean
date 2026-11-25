# Inherited-level later-origin horizon crossings: exact-hit transport, skip quotas and order reversals

2026-11-25 JST. Continues 58ad11653c20284437953f31dc3e3cfbfeadb598. New paper results: every old independent inherited level has an exact first crossing of its later upward-origin horizon by the earlier-origin trajectory before or at its true first physical contact. Exact hits (including genuinely disjoint time slots at that horizon) transport to full projected occupation and mixed positive-wait/net-negative-drift moments with an absolute constant, independent of upward-origin separation. Skips have actual later-upcross token capacities and a rough skipped-origin arithmetic tuple bound. Order-reversed contacts force a genuine strict horizon overtake. These estimates concern I^sharp, not one-for-one original cross W_g payments. No Lean compilation; twin infinitude OPEN.

## 1. Setup

Retain original all-odd dyadic sources M in [X,2X), N=X/2, B=ceil(sqrt(7X)), u=log B, H=4B, s=M+2,C0=2M-2 and original K(M)=floor((7M-1)/4). Actual fixed-cap MIN, all original completed waits including crossing event, e_M<=s+H+2B. All actual true deficits d=2t-C in [0,12B+6] and original total gain <=12B+6. No occupation after twins.

Use the donor anchors and actual normalized donor rows of a068c67 and the inherited pair-level coarea of 58ad116. For each internal unordered donor pair and lambda>=7, b_ij(lambda)=sum_{g:mu_ij(g)>=lambda}(r_g/B)x_i(g)x_j(g). Its cap U0=27 follows from distinct actual target slots and per-source gain. Its sum over pairs and levels is I^sharp. Internal pairs share an original donor anchor and |i-j|<=6B; O(XB) possible pairs. Both last stationary upward crossings through the first actual meeting tau are independent of later contributing anchors. Neither root nor reset contacts support such high inheritance.

As before, pay levels <=6+ell and those with at least one origin less than ell ticks before tau, ell=max(1,floor(u^11/4)), for O(XB ell)=o(XB u³). Work on any actual unpaid portion, without changing original waits. All following statements refer to positive b_ij(lambda) after these filters; the code uses diagnostic ell=4 or16.

## 2. NEW exact later-origin crossing

For one inherited pair-level, denote the earlier-upcross source E, later-upcross source L, origins (z_E,C_E),(z_L,C_L), z_E<z_L. The origin horizon difference is exactly C_L-C_E=2(z_L-z_E)>0, since the even true post-upcross deficit is the same at both (lambda if even, lambda+1 if odd). The last upward crossing has survived independently to tau and then to the contributing anchors. Both sources are active by z_L and their true deficits are >=lambda there. Thus C_E(z_L)<=C_L, with equality impossible because z_L<tau. So E is strictly behind L at z_L. Both have nondecreasing horizons and share J_*>=C_L at tau. Consequently E has a unique first event crossing C_L from below at clock b with
    z_L<b<=tau,
    D<C_L<=J=D+p-1,
    d_E(b)>=lambda,
    2(b-z_L)>=J-C_L.                                    (1)
The last inequality uses even deficits: d_E(b)>=lambda implies d_E(b)>=d_L(z_L), not just a one-unit weaker bound. The prior E horizon D is even. The first crossing exists in the ACTUAL prefix through tau and its next wait also completes in the original prefix, since both sources reach the later contributing donor anchor (same labeled event, hence shared predecessor at t_g-1). It is not a potential trajectory.

Partition exactly:
- HIT if J=C_L, a real visit of E to the later origin horizon.
- SKIP if J>C_L, so p>=5 and even offset delta=J-C_L lies in [2,p-3].
No other case. Pair-level assignment independent of contributing later g because the two last upcrosses and first physical contact are fixed. For HIT, L's wait at C_L contains its last upcross and has started earlier than b. If the two departure clocks coincide, they meet at b=tau (same completed slot). Otherwise L's departure v_L<=b and waits are disjoint slots of the same projected horizon. Indeed overlapping true states would already force the same departure. Thus exact-hit classification distinguishes actual same-slot and genuinely distinct-slot energy, not merely horizon equality.

There is also an exact accumulated gain identity: between the origins and tau, G_E=J_*-C_E, G_L=J_*-C_L, so G_E-G_L=2(z_L-z_E); clock duration difference tau-z_E minus tau-z_L is z_L-z_E. This does not force the excess gain to happen in a single jump or imply the origin-gap persists at all later times.

## 3. NEW full exact-hit transport, including short arrivals

Use actual full completed waits, no original delayed mask. At an exact hit horizon C=C_L let r=r(C), w_L the length of L's wait and w_E the length of E's later visit. L's wait is positive net drift because its last stationary upcross survives through its own subsequent recorded post-state to g: initial deficit below lambda, final >=lambda, so 2w_L>p_L-1. E's wait need not have positive drift. The actual distinct unordered source pair visits C at most once each. Orientation of L versus E for all its assigned HIT levels at C is fixed by arrival order at C. At most 2w_L integer levels arise in L's single actual stationary wait. With the already aggregated cap U0 (not a later-anchor count), total charge for that fixed pair/horizon is <=2U0 w_L=54w_L.

Define natural projected occupation weights:
    V(C)=sum_all actual tags visiting C in a completed wait w/(2r),
    V_+(C)=sum_positive net drift actual waits w/(2r),
    D_-(C)=sum_all actual waits (p-1-2w)_+/(2r).
Each sum has at most one term per tag at C; all r>0. Put
    E_proj=sum_C r V(C)^2,
    E_+,-^proj=2 sum_C r V_+(C) D_-(C).
E_proj includes diagonal and distinct-slot projected products. The second is a mixed positive full wait / ACTUAL net recorded descent moment at the same horizon, not true-tick jump size or selected-gain moment and not necessarily at the same clock. Its linear marginals sum_C r V, sum_C r D_- are O(XB) by original clock/gain budgets, but that does not bound their quadratic product. For sharper target one can restrict either moment to actual HIT supporting pairs/horizons.

Fix epsilon=1/4. In a long hit w_E>=r/4, its actual offdiagonal projected contribution e=w_L w_E/(2r)>=w_L/8. Thus the pair/horizon charge <=432 e. Summing distinct pair/horizon products gives
    I_hit,long^sharp <=432 E_proj.                     (2)
No coefficient depending on z_L-z_E, unlike near-origin transfer. The argument also works with any fixed epsilon>0, coefficient 4U0/epsilon.

In a short hit w_E<r/4, with actual outgoing selected p_E>=r,
    delta_E=(p_E-1-2w_E)_+ >=p_E/2-1>=p_E/6>=r/6,
using p_E>=3. Hence e_down=w_L delta_E/(2r)>=w_L/12, and
    I_hit,short^sharp <=648 E_+,-^proj.                 (3)
The positive tag and net-negative tag are distinct, and fixed orientation prevents double charging either ordered product. This is why a short actual occupancy on E need not be forced into E_proj by an unproved lower wait bound. No condition that the short wait's descent is a first downcross of the inherited level: in fact the level survives through the anchor. Its actual recorded decrease is used only for the mixed product.

Combining (2),(3) covers ALL exact hits in the eligible inherited ledger:
    I_hit^sharp <=432 E_proj+648 E_+,-^proj.             (4)
These are upper transports to two different unbounded quadratic moments. Neither is established o(XB u³), and E_proj is not the same-slot positive-only E_+^full of a068c67. Thus (4) is not a proof of contraction or self-absorption. It is a reduction independent of origin-gap and later-reference length. E_proj already includes all actual same-horizon distinct-slot pair terms; one cannot replace it with only same-slot occupation without accounting for those. For an alternative even simpler arrival-count bound, I_hit <=O(sum_C r n(C)^2), where n(C) counts full actual visits, but (4) retains actual wait and descent weights.

## 4. NEW skip token payment and arithmetic rough-origin tuple

For each SKIP pair-level assign the actual key (b,J,p,C_L) and the later-upcross token (M_L,z_L,lambda). The skipped interior offset delta=J-C_L is in [2,p-3], even, and has at most (p-3)/2 possibilities at a fixed crossing. For any fixed pair, crossing event and C_L the total assigned charge is <=54 w_L by the same stationary level count. The crossing's prior wait length <=2p, but w_L can be arbitrarily larger than that; do not use a uniform comparison with natural projected occupation at J or D without new control.

At each later-upcross token aggregate ALL remaining actual SKIP charges incident in this role, regardless of the earlier-origin sources' crossing keys or future g. Pay that entire group when its total <=m=u^(11/4). Each original source has at most two level tokens per actual stationary tick, so the number of such tokens over all sources is O(XB). Each pair-level has exactly one later token. Therefore
    P_skip,thin=O(XB m)=o(XB u³).                        (5)
This is an independent absolute quadratic payment on I^sharp. Remaining tokens need >m/U0 distinct actual earlier-origin skip partners at that particular level. No assumption on the number of physical crossing keys. Could also impose an opposite-role constraint per actual earlier token with the same budget, by iterative degree peeling; only the one-sided version is numerically tested here.

Additional arithmetic support for ROUGH skipped later-origin horizons C=C_L with r(C)>=R=cB/u² and r(C)<=B. For fixed selected skip p>=5 and side s=b mod2, the actual event requires
    J=C+delta,   J+2s=0 mod p,
    b=rho(p,s) mod 2p,  rho(p,0)=0,rho(p,1)=p+2,
    J/2<=b<=(J+12B+6)/2.
For each even delta in [2,p-3] (O(p) choices), C in O(X) range has one congruence modulo p. The established uniform two-form sieve for C±1, omitting p and2, on a progression of length >=cB, with cutoff B^1/64 and error O(B^1/64 log B), gives O(X/(p u²)) C candidates. There are O(B/p) phases. Thus for fixed p the number of relaxed tuple keys satisfies
    S_p=O(XB/(p u²)).                                 (6)
For p<=B^1/8 further select r'=r(C) in [R,B] and side sigma with r'|C+sigma. Eventually p!=r'. CRT step 2pr' leaves interval length >=c B^7/8; the same two-form upper sieve on (C+sigma)/r', C-sigma with determinant -2sigma, omitting p, gives O(X/(pr'u²)) candidates. Sum over r' reciprocal O(log u/u), and offsets/phases:
    S_p=O(XB log u/(p u³)), p<=B^1/8.                 (7)
See the earlier uniform sieve applications in 6852f2c and 24bfe41. These count physical crossing/rough-origin TUPLES, not all ancestor pairs or actual source tags. In particular the same p event can skip many different C; the O(p) offset factor is necessary. Actual MIN, persistence and first crossing only reduce the support.

Use actual aggregate inherited energy per tuple across all eligible pairs and lambda, not a count per subsequent donor anchor. For small p<=B^1/8 or near-top p>=B/u² use quota u^23/4; for intermediate labels quota u^19/4. For each tuple pay min(actual remaining weight, quota). In small band reciprocal sum O(log u), intermediate O(1), near-top O(log u/u). Equations (6),(7) yield
    P_skip,rough=O(XB u^(11/4)(1+log u)^2)=o(XB u³).    (8)
Independent of (5), use disjoint priorities on the actual remainder if combined. Small actual tuple mass is fully paid, large keys retain residual weight; this is not a bound on raw skip mass. Nonrough skipped origins are not covered by (8), though (5) still applies. No inference from a finite realized-key count to asymptotic source multiplicity.

## 5. NEW genuine overtake witness

For eligible inherited pair-level, at z_L the earlier-origin trajectory is strictly behind. Suppose at tau-1 it is ahead. Since the true first contact is tau, there was no equality at any common prior tick. Hence a strict order reversal occurred at some selected event clock t in (z_L,tau). Choose the last such reversal before tau. It is the same physical event for all reversed levels of this pair, whenever the last reversal is after their later upcross. It is distinct from the eventual true merger. Both trajectories retain d>=lambda throughout.

If winner and loser have horizon gains p-1,q-1 at t (use label 1 for an actual stationary tick only), let gap_before, gap_after be their positive absolute horizon gaps. Exact identity
    p-q=gap_before+gap_after >=4.
Thus the overtaking prime p>=5, p>q. If the overtaken path was stationary, its horizon is strictly in the interior of the winner's jump; if that horizon is rough, the relaxed physical tuple support (6),(7) also bounds such overtakes (paper only). At a jump-stationary true first contact, reversal is equivalent to the EARLIER upward-origin path being the stationary recipient: the jumping donor comes from a strictly smaller horizon at tau-1. If earlier-origin is donor, it may have had an even number of prior reversals; no claim of absence of earlier overtakes. This witness is not an energy bound; the audit records the actual reversed mass and stationary/simultaneous jump types. An additional quota on these overtakes would need a disjoint allocation rather than reusing the skip quota and adding overlapping paid mass.

## 6. Result and scope

For the actual eligible inherited ledger of 58ad116, combining disjoint low/recent filters, exact-hit transfer and skip thin/rough payments gives
    I^sharp <=432 E_proj +648 E_+,-^proj + I_skip,res
                +O(XB u^(11/4)(1+log u)^2).             (9)
Here I_skip,res is actual unpaid skip mass after the stated priorities, which can still have heavy nonrough tokens or heavy rough tuples. Earlier excursion entropy can be applied before these steps on the actual unpaid pair-level weights. (9) has no origin distance factor. It does not imply little-o for I^sharp because both projected moments and skip residual remain open. In particular E_proj has the original projected coalescence difficulty and E_+,-^proj includes disjoint slots. Any subsequent bound must avoid circular use of I^sharp or the full old terminal energy. The earlier cross-to-donor transfer coefficient chi, recipient reuse, E_+^full and previous terminal/immediate/later/low-r/MED residuals remain.

## 7. Reproducible finite diagnostics

Standalone research/min_clock_inherited_horizon_crossing_audit.mjs, initial commit 76953e42fdfb1a45a3ef64e6fa549852b8cbb7ea; second 8545778c149ee60f642cfc7a3ca40e3da9358672; final b7addbf255040f9e3bc22f2956443a6fe98cf740, exact remote blob 2d253e8741e46203a17e2473b1b5b327afb188b0. Retains prior literal forward and inverse sampled-slot engine, exact donor last-upcross and excursion checks. New binary searches of actual recorded waits for each first crossing, independent literal tick first-crossing scans up to128 per nonempty ledger, same/ distinct-slot conditions, positive late wait, skip offset, independent first-contact order reversal via actual simultaneous event batch, fixed pair/horizon counts, natural and short-hit mixed negative transfer, one-sided late-token skip quota and independent rough skipped-origin tuple congruences/relaxed support. The relaxed support is enumerated only for realized labels but across all even horizons in O(X) original range. All final assertions passed.

Run:
    node research/min_clock_inherited_horizon_crossing_audit.mjs 4096 16384 65536
Actual JS function executed in available runtime, not separate Node invocation. Final 24 crossing ledgers: 3 X, two occupations, two independent LOW classifications L30/y5,L6/y3, delay ell4/16; same 12 selected original origin-levels per X and original masks, no full energy estimate. Fixed epsilon1/4; finite skip token cap8, rough R=ceil B/16 and rough tuple cap8. These are diagnostic choices, not asymptotic parameters or fitted sieve constants. Hit transfer sums restricted actual supporting pair/horizon products, not the full E_proj and E_+,-^proj. Skip token and rough tuple payments are INDEPENDENT on the same eligible skip mass, not cumulative. Earlier entropy also measured independently; low/recent filters precede hit/skip split. The sieve and asymptotic budgets are paper deductions using earlier sieve lemmas.

X65536 full-positive samples:
| LOW classification | delay | eligible I | exact hit | skip | skip token paid | skip token residual |
|---|---:|---:|---:|---:|---:|---:|
|L30|4|28017.19764|26189.82006|1827.37758|1827.37758|0|
|L30|16|24663.67257|22970.33923|1693.33333|1693.33333|0|
|L6|4|81618.77581|49094.20354|32524.57227|32025.77286|498.79941|
|L6|16|57961.09735|31747.77286|26213.32448|26213.32448|0|

At delay4, L30 exact hits same slot26069.93805, distinct119.88201; all w_E>=r/4, restricted natural pair moment22185.77661 (782 distinct pair/horizon keys), max actual charge/energy ratio3.45277. L6 same40800.23304, distinct8293.97050; all long hits, natural pair moment83150.34526 (10704 keys). At delay16 corresponding natural restricted moments7836.31343/39747.61076. These restricted energy values need not be small at asymptotic scale. The largest actual origin-clock gap102, lag from later upcross to crossing154. X4096 L6 delay4 (same inherited moment in late/full) eligible255.65882, hit254.56471 (same43.76471/distinct210.8), long253.10588 with restricted natural1643.89474, one short hit1.45882 with mixed down moment1.8 (nonvacuous check of (3)), skip1.09412 fully token-paid. All eligible X4096 vanish at delay16; X16384 and larger late-HIGH samples empty.

At X65536 delay4, L30 skip mass1827.37758 at six actual crossing keys (labels7,11,37,43,127), 626 later tokens. L6 skip32524.57227 at21 keys, 11686 tokens, p<=sqrt(B) mass30551.83776, largest single label17 mass17272.37463. L6 token payment leaves498.79941 at delay4; at delay16 fully paid. This is finite with cap8; no general smallness of skip tails follows. Rough skipped-origin tuple support at diagnostic R43: L30 one p127 tuple mass974.04130 vs102018 relaxed keys, quota8 leaves966.04130; L6 two tuples p7,p127 mass5761.82891 vs1111911 and102018 relaxed keys respectively, quota16 leaves5745.82891. The same keys at delay16 carry884.12979/5576.38643 in L30/L6. This tuple quota is not added to the already measured token payment. Diagnostic rough support is not an empirical proof of (6),(7).

True horizon-order reversals before contact, delay4 L30=1903.12684 (6.79% eligible), L6=34567.97640 (42.35% eligible); delay16 L30=1813.21534, L6=28865.33923. All observed last reversals involved an actual stationary overtaken path; no simultaneous two-jump reversal observed here, not a theorem. All eligible inherited true contacts in these samples still jump-stationary. Checked75080/352014 pair-level crossings at delay4 L30/L6, 65610/240852 at16, each with128 independent literal crossing checks. The data show genuine HIT, distinct-slot HIT, SKIP and overtake cases. No claims of proof of limiting little-o. Main and other branches unchanged.

## 8. Next direction

For exact hits, investigate same-slot sub-sector (which dominates the current L30 sample) separately from disjoint slots: at same-slot HIT arrival b=tau, the late-origin L tag has positive full drift, early E tag's next wait may be positive or negative. A sharper per-pair transfer to earlier same-slot positive occupation or actual net descent could reduce reliance on full projected E_proj. For distinct-slot hit, use arrival lag, outgoing prime phases and actual first-crossing structure to bound the projected cross products rather than all E_proj. For remaining skips use earlier-origin donor crossing keys and actual opposite-token partner counts, small labels in nonrough regions, and last genuine overtake where present. Preserve earlier E_+^full, chi/recipient reuse, and all previous unresolved energy sectors. No Lean proof or twin infinitude claim.
