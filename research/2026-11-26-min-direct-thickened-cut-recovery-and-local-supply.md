# Thickened primorial-cut neighborhoods and localized deficit recovery supply

Continuation of [3793617](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md), returning to the small-crossing branch of the weighted master. The previous offset witness constrained the crossing event itself. Here extend it to every event whose start lies within a whole radius-S^2 neighborhood of a pinned cut. A forward corridor anchored at each moderate crossing has gain at least S^2, without needing to control a large jump that entered the neighborhood from the left. Disjointness transfers this cost to actual localized low-label gain or deficit reduction, and thence to external positive variation. This is a submacroscopic supply condition for the moderate portion of the small-crossing alternative, not a bound for the entire small/middle populations.

## 1. Two-sided offset lemma

Use even horizons H, actual adaptive MIN events with label p, gain g=p-1, wait w, ordinary plateau deficits d,d'=d+2w-g>=0. All actual events satisfy w<=2p, -g<=d'-d<=5g. Let S>=3 be an integer, P_S the product of odd primes <=S, K=2P_S, and take an integer radius V with 1<=V<=S^2 and K>2V. Let J be an even multiple of K. Suppose a plateau start H with H+1>=S^2 satisfies
    0<|H-J|<=V.
Put u=|H-J|, a positive even integer. For any odd prime f<=S, divisibility of H-1 or H+1 by f is equivalent to divisibility of u-1 or u+1 by f, with the side interchanged when needed. If neither neighbor has such a divisor, u=2 is excluded by 3|u+1. Thus u>=4 and u-1,u+1 are odd integers >1 with no prime divisor <=S. Since u is even and u<=S^2, u+1<=S^2+1; even when S is even, u+1<=S^2+1<(S+1)^2. A composite integer below (S+1)^2 has a prime divisor <=S. Hence
    (u-1,u+1) are twin primes, both >S.                 (1)
Otherwise some f<=S divides a neighboring integer at H. Its eligibility follows from H+1>=S^2, and its strict future clock is at most 2f ticks away. Every actual selected event starting at H therefore has w<=2S, irrespective of its own label p. In particular for any cutoff L>4S and p>L,
    d-d' >= g-4S >= (1-4S/L)g.                         (2)
Here g>=L when L is integer. Under finite twins, take S beyond the lower members of all twin pairs: (1) is absent throughout the entire two-sided neighborhood except its center. This is a pointwise conditional theorem, not an assumption of equidistribution. The exact finite offset lemma also permits using locally witness-free neighborhoods without assuming global finiteness.

The offset witness is the same pair extraction as in [40a43f6](https://github.com/tara-sooo/A166944-Lean/blob/40a43f624b3f73df3c68b1bf0bcb2b4f665b9713/research/2026-11-26-min-direct-sieved-hybrid-twin-certificates.md), but previously required the offset to lie strictly inside the selected jump and p<=S^2. Here only the distance of the pre-horizon to J matters. In particular the witness may arise AFTER a moderate crossing, at the start of a different event, even one with arbitrarily large label.

## 2. Disjoint forward corridors without an entry exception

Consider a finite contiguous event block with all pre-horizons satisfying H+1>=S^2. Take any designated distinct pinned cuts J with actual STRICT crossings
    H<J<H+p-1,    p<=V.
The surviving hybrid cuts of the previous note satisfy this for R<p<=V: no p<=R crosses them and H=J is excluded by the extra V-roughness sieve. The theorem here also applies to any strict crossing of the pinned lattice, even if the other hybrid conditions are omitted. Because K>2V, a moderate event crosses at most one pinned cut.

For each designated cut include the crossing event and every subsequent event until the first plateau with horizon >=J+V. If that plateau is beyond the block end, mark the corridor pending; at most one designated cut is pending because it then lies in (H_end-V,H_end), and the cuts are K-spaced. For each completed corridor I_J:
* The crossing pre-horizon is H>=J-(V-1), and after that event every pre-horizon in the corridor lies strictly between J and J+V. No event starts at the exceptional H=J.
* All pre-horizons have 0<|H-J|<=V. Thus either an actual plateau provides (1), or ALL corridor events obey w<=2S. We need not bound the label of any later event.
* The horizon gain G_J of the corridor, including the whole last event, satisfies G_J>=V. It is not just the gain of the crossing event.
* These physical event intervals are pairwise disjoint. For successive designated cuts J1<J2, every pre-horizon in the first corridor is <J1+V, whereas the next crossing starts >J2-V>=J1+K-V>J1+V. Even a last jump with large overshoot cannot duplicate an event in the second corridor, by monotone event horizons. We never truncate a physical event jump.

The choice of a forward corridor is deliberate. A left neighborhood ending at the crossing can be skipped by an arbitrary preceding large event that lands close to J. Here the crossing itself anchors the start, and the full forward gain V is guaranteed, with no entry-event exception. No assumption on the number or labels of events inside the corridor is used.

## 3. Localized low-label and decrease budgets

Let m be the number of completed designated corridors without a witness, and let Q be their disjoint union of event intervals. Put
    G_low(Q) = sum_{events in Q, p<=L} g,
    P_-(Q) = sum_{events in Q} max(d-d',0),
    P_+(outside Q) = sum_{block events not in Q} max(d'-d,0),
    alpha=1-4S/L>0.
Using (2) on all high-label events in Q and summing G_J>=V,
    V m <= G_low(Q) + P_-(Q)/alpha.                    (3)
For each individual corridor the same bound holds with m=1. Moreover its net ordinary change obeys
    d_start-d_end >= alpha G_J-(alpha+5)G_low(I_J)
                   >= alpha V-(alpha+5)G_low(I_J).     (4)
Indeed the high events each decrease by at least alpha*g, while low events can increase by at most5g. Summing (4), exact telescoping on the full physical block with initial ordinary d_a and final d_b>=0 gives
    alpha V m <= (alpha+5)G_low(Q)
                         + P_+(outside Q)+d_a.         (5)
This is stronger in localization than charging all P_+: positive changes inside the corridors have already been paid by their actual low-label gain and need not be charged again. In particular from a fixed canonical root d_a=6 for the full prefix. On a later block one must retain d_a or account for earlier actual variation. We do not assume that initial deficit is small on a crossed window.

For any selected corridors with G_low(I_J)<=theta V, where theta<alpha/(alpha+5), each has net drop at least [alpha-(alpha+5)theta]V. Such corridors demand initial deficit of at least that amount; collectively their net drops must be supplied by outside positive variation and the initial deficit. This is independent of their individual crossing label, which may be much smaller than V.

One can also count the number of events in a corridor: if d_start<=V/2, since d_end>=0, 2 sum w=G_J+d_end-d_start>=V/2 and every wait <=2S, it has >=V/(8S) events. If d_start is small, (4) forces low-label gain as well. Specifically
    G_low(I_J) >= (alpha V-d_start)/(alpha+5).
These are actual constraints on the surrounding event population, not just on the single moderate crossing.

## 4. Relation to the small-scale crossing alternative

Use the preceding balanced cut family, with S=floor(R/loglog R), V=S^2, R~(log X)/2, S=o(R). Then K=2P_S>2V eventually, and take L=R so alpha=1-o(1). Let n_mod count actual surviving-cut crossers with R<p<=V. Each carries exactly one surviving cut and normalized mass kappa. Under finite twins at sufficiently large S every completed such corridor is witness-free; at most one is pending. Therefore, for the union Q of these corridors,
    (n_mod-1)V <= G_{p<=R}(Q)+(1+o(1))P_-(Q),
    (1-o(1))(n_mod-1)V
       <= (6+o(1))G_{p<=R}(Q)+P_+(outside Q)+d_a.       (6)
For the normalized moderate mass M_mod=kappa*n_mod, the first inequality gives
    M_mod <= kappa + (kappa/V)[G_{p<=R}(Q)+(1+o(1))P_-(Q)].
This is an actual supply upper bound, albeit conditional on the budgets and generally weaker than the total mass upper bound if those budgets are macroscopic. It does not presume the moderate portion dominates the small-crossing term. In the old alternative n_small includes all R<p<=D=2P_S+1, and V is much smaller than D.

If the moderate portion itself has n_mod=Omega(X/kappa), the necessary localized gain/recovery resource is Omega(V X/kappa). This improves the earlier per-crossing ordinary-loss scale R for crossers concentrated at p=O(R): the cost now extends over a full radius V, so the alternative is larger by a factor of order V/R. It may be paid by low-label gain, however, not solely by ordinary decrease. The resource V X/kappa is still o(X); neither budget is presently proved small enough to contradict it. If d_a is negligible compared with V X/kappa, (5) additionally requires either localized low-label gain or actual outside positive variation of this order. Without a small d_a condition the inherited deficit can pay it. Alternatively sum (5) over disjoint physical windows from a fixed canonical root: apply the net-drop argument directly to the union of all completed corridors (even with varying S,R,V), rather than summing the initial deficit term in each window. The total weighted demand sum_J alpha_J V_J is bounded by sum_J (alpha_J+5)G_low(I_J)+P_+(global complement)+6. This prevents repeatedly charging the same inherited deficit across scales. Disjointness of physical windows is essential; no assertion of disjointness across arbitrary overlapping windows is needed.

Extension to all labels with small overshoot: take any strict crossing of a pinned cut J, of any label, landing at H_post in (J,J+V/2]. Begin the corridor AFTER that crossing and stop at first plateau >=J+V. Its gain is >=V/2, all starts satisfy the same offset lemma, and corridors are disjoint for distinct pinned cuts (provided one crossing is designated per cut, and all chosen landings obey the condition). If a single event crossed several cuts, at most one can have that small positive overshoot since K>2V. This gives (3)-(5) with V/2 in place of V for this different population, including large and middle labels, and with its own Q. A cut with landing overshoot >V/2 is not covered by this extension; an anchor landing exactly J would likewise require a different argument. The moderate theorem covers all strict moderate crossings, not just those landing close.

Remaining task: to eliminate the full small branch, control crossers p>V or prove the moderate corridor resources o(V X/kappa); for the middle branch the normalized crossing scale is ell rather than kappa and the above radius is insufficient. Large positive supply from the previous precursor theorem remains a separate alternative. No finite-twins contradiction or Lean kernel verification.

## 5. Diagnostics and preservation

[Audit bdda873](https://github.com/tara-sooo/A166944-Lean/blob/bdda873b4e25e20e8f3cab01f6d2ebac53c454d6/research/min_direct_thickened_cut_recovery_audit.mjs), blob da8ba620fe42ade9698f177737ada76357e66882, exact remote readback. Run node research/min_direct_thickened_cut_recovery_audit.mjs 60000. Actual ECMAScript execution, not separate Node. 29998 canonical odd roots through60000,549085 actual MIN events,0 cap180 unresolved. Finite configs S5,7,11, radii14,49,121, K30,210,2310, low cutoff L=5S, hybrid base cutoff next prime after S. Broad strict pinned crossing controls (including non-surviving cuts)14958,2778 also pass hybrid and additional sieve;3534 pending,11424 completed;10090 completed with offset twin witness,1334 without witness; among clean corridors285 actual surviving cuts, among witnessed1695 surviving cuts. Clean corridors3846 physical-event incidences,247 with high-label events, maximum length5. 37668 exact fast-clock checks and588 high-drop checks (including nonrough events inside witnessed corridors),11424 nonoverlap checks,1334 local budget checks and87795 full-block aggregate budget controls.91 offset controls (12 rough) and546 translated congruence checks;1164 synthetic high-drop inequality checks. Counts overlap over roots/configurations. Representative clean surviving cut J6090,S5,V14,root2945,H6084->6104, labels11,5,7, waits6,1,5, gain20, low gain20, negative variation2, positive variation6. Representative actual offset witness at root237,J480,H492,p17 gives (11,13) from a later plateau; this is a strict pinned-cut control, not claimed a surviving hybrid-cut instance. The final audit tests (3) and the full variation budget with P_+ +d_a; (4)-(5), varying-window accumulation and small-overshoot extension are algebraic deductions not independently tested in that code. The first attempted stricter scan required coverage of all cases and stopped at its coverage assertion; the final scan broadens to strict pinned cuts, retaining a separately counted surviving subset. All final assertions passed. No infinite trajectory or asymptotic no-witness window realized in the finite scan. No external novelty claim, Lean kernel proof or final contradiction. Main and sibling branches unchanged.
