# Reverse-horizon Kraft bound and first-meeting expiry charging

2026-11-25 JST. Continues 065b449cd0a91b1ec0a6660cd7ddf231fbe2044d (short-clock middle-pair bounds) and 25473614cf384cff0d8af534e34404cd774ae053 (relative-clock slab). New unconditional bounds on actual original-root masses and on entire shared suffixes after first meetings of bounded-complexity histories. High-complexity first-meeting mass and the full short-slab energy bound remain OPEN. Paper proofs, not Lean-compiled.

## 1. Setup

All odd original roots M in [X,2X), dyadic X, N=X/2, s=M+2, C0=2M-2, original K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). Use the original MIN dynamics. Let H=4B, a=2B, assume H+2B<=min(K-s) as holds eventually. Keep all actual states through the last event whose waiting state starts before s+H, including its post-event vertex if it is beyond s+H. Stop at a twin. The graph has at most one outgoing edge at each physical vertex, and t,C strictly increase along edges. Truncation does not change any included edge, and two roots sharing a physical vertex follow an identical suffix until the earlier truncated path ends.

As before, at a waiting state C, r(C)>0 is the least eligible prime, ell_M(C) is the wait length in the relative slab [a,H), w_M(C)=ell_M(C)/(2r(C)) in [0,1]. Define U(C)=sum_M w_M(C), R=sum_C r(C)U(C)<=NB, E=sum_C r(C)U(C)^2. The per-root cost is <=B. The sufficient asymptotic energy scale is E=o(XB log^2 B) along unbounded dyadic windows, using S0=sum_C r(C)=O(XB/log^2 B) and the preceding exact clock identity. We do not establish that whole estimate.

## 2. A uniform reverse ancestry mass bound

Choose a LOW cutoff y>=2 and its even primorial L=2 product_{3<=p<=y}p, so L=2 if y=2. All selected primes are odd. Any contiguous LOW-only block has gain <L. For completeness, at an even multiple of L every LOW prime is inactive. A LOW jump from an even D below that multiple cannot cross it: if p|D-1 then the smallest positive possible distance to the multiple is p-1, and if p|D+1 the smallest positive even distance is p+1. Thus at most the jump endpoint reaches the multiple, where the block stops. This also bounds a partial LOW block. No bound on the number of LOW events in a whole trajectory is assumed.

For a candidate even post-event horizon J, let

    P_y(J)={odd prime p: y<p<=B, p|(J or J+2)},
    d_y(J)=|P_y(J)|, A_y(J)=sum_{p in P_y(J)} log p.

These are arithmetic candidate labels, not a claim that they were selected. The actual post-event divisibility p|J or p|J+2 holds from the even/odd MIN clock. For a nonempty candidate set put

    pi_J(p)=1/(2 d_y(J)) + log p/(2 A_y(J)).

This is a probability distribution on the finite candidate set; it is used ONLY to assign weights in a deterministic enumeration, not to model the dynamics. Since A_y(J)<=2 log(7X+2),

    L/pi_J(p) <= min(2 L d_y(J), 4 L log(7X+2)/log p).  (1)

For any actual root M and any of its visited horizons C (including root and terminal), enumerate the selected labels p_i>y before C and their post-event horizons J_i. Define the monotone reverse branching complexity

    kappa_M(C)= L product_i [ L/pi_{J_i}(p_i) ].          (2)

Each factor is >=L>=2. LOW events do not change kappa. The empty product gives L at the initial state.

THEOREM (Kraft mass). For every C,

    sum_{M visiting C} 1/kappa_M(C) <= 1.                 (3)

Proof. Build a finite relaxed reverse horizon tree from C. At every node D, choose an even e with 0<=e<L, assigning weight 2/L to each of the L/2 offsets. Put J=D-e. Stop with additional factor 1/2, declaring J the candidate initial horizon, or continue with factor 1/2 and choose p in P_y(J) according to pi_J. The predecessor node is J-p+1. Discard invalid horizons, absent candidate sets and invalid initial horizons. This only decreases total mass. Thus every stop edge has factor 1/L and every continuation edge has factor pi_J(p)/L; total outgoing mass including stops is <=1. Continuing strictly decreases the even horizon, so the sum of all terminal-path masses is <=1 by induction. Compress each actual prefix to its successive LOW gain offsets and non-LOW labels in reverse, followed by the initial LOW gain offset. The LOW barrier and post-event divisibilities show that this is one valid terminal path. Its mass is exactly 1/kappa_M(C). Distinct original M yield distinct terminal paths since the terminal horizon 2M-2 identifies M uniquely. No time constraints or cutoffs need be used for this overcount. Therefore (3). QED.

A simpler version uses weight 1/L for each possible even offset (subprobability), terminal factor 1/(2L) and continuation factor log p/(4L log(7X+2)), giving kappa=2L product_i(4L log(7X+2)/log p_i). It is also valid, but the adaptive distribution above improves the useful uniform divisor-count bound.

Consequently the number of original roots visiting a horizon C with kappa<=tau is at most floor(tau), even if all such roots have already coalesced physically. This is an actual source-tag cap, not a count of physical vertices.

## 3. Unconditional energy removal for bounded-complexity tags

Call a state of a root GOOD if kappa<=tau, with tau=o(log^2 B). This is a monotone-prefix predicate: once false, never true later. Write U_g(C) for the occupation weights of GOOD incidences. By (3), U_g(C)<=tau. Therefore

    R_g=sum r U_g <= tau S0 = o(XB),
    E-E_notgood=sum r (2 U U_g-U_g^2)
               <=2 tau R = O(XB tau)=o(XB log^2 B).      (4)

This removes every pair incidence with at least one CURRENT good history, including good-bad pairs at equal or different arrival times, without assuming anything about the other root's ancestor mass. It also yields an unconditional bound on the number of roots which have not reached a twin before H and remain good through the slab: each such root contributes B to R_g, so their number is <=tau S0/B.

The more important result below controls shared suffixes even AFTER BOTH histories become bad.

## 4. First-meeting expiry identity and entire-suffix bound

Let G_v be the set of GOOD original root tags at physical vertex v=(t,C) in the truncated graph (include terminal and final post-event vertices). For each root that ever is good, its GOOD states form a prefix; call its last such physical vertex its expiry. Let D_v subset G_v consist of the tags expiring at v, and put g_v=|G_v|, e_v=|D_v|. Let F_gg count UNORDERED distinct original-root pairs whose first common physical vertex occurs while both histories are good.

THEOREM (expiry identity).

    F_gg = sum_v [e_v (g_v-e_v) + binom(e_v,2)].          (5)

Proof. For each such pair, charge it to the vertex of the earlier expiry in absolute time. After their first meeting, the paths coincide until the earlier path ends. Both were good at the meeting, and each remains good until its own expiry. If the earlier expiry occurs strictly before the other, the other tag must reach that vertex while still good; otherwise it could not reach its later good vertex along the common deterministic suffix. If the expiry times tie, strict increase of time and determinism imply the same vertex. Thus the charged pair has one tag in D_v and the other in G_v, counted once, including simultaneous expiry. Conversely any pair counted by the right side has met by v while both good, so monotonicity implies both were good at first meeting, and v is their earlier expiry. This proves the identity. It does not require the roots' relative slab windows to agree.

As g_v<=tau from (3), and sum_v e_v<=N,

    F_gg <= N max(0,floor(tau)-1).                       (6)

More generally any good-prefix predicate with a uniform cap m on g_v satisfies the same conclusion with m, whether or not defined by (2). An independent first-meeting formula is sum_v [binom(g_v,2)-sum_A binom(|A intersect G_v|,2)] over incoming predecessor classes A including injected root singleton. These are identical by (5).

Each unordered pair has ordered total common-suffix energy <=2B, since w_other<=1 and each root's entire slab cost <=B. Hence the ENTIRE SAME_STATE energy arising from pairs first meeting with two good histories is bounded by

    E_same,gg <=2B F_gg <=2BN tau
              =O(XB tau)=o(XB log^2 B).                  (7)

This counts all shared states after meeting even if the two kappa values grow arbitrarily large later. It includes every source pair in an already-heavy class, not merely representative demotions. In particular ROOT first meetings with a good old history are included because the injected root starts good (when L<=tau). Formula (7) is stronger than merely deleting currently good incidences in (4). The two deletions overlap and may be combined by a union upper bound. It does NOT cover first meetings where one or both histories are already bad; a small class merging with a large bad class can create many such pairs.

## 5. Explicit growing-scale subclass: two arbitrary medium events, unlimited LOW blocks and near-B events

Let S=max(1,log log log B), choose the largest even primorial L<=6 S^(1/4), with its associated cutoff y, and set Q=ceil(B/S^(1/4)). For asymptotically large B, y grows, Q>y and Q<=B. Call y<p<Q MEDIUM and p>=Q LARGE. Let tau=(log B)^2/log log B.

Use the actual prefix up through the possible final crossing event. By C<=2t before that event and its gain <=B-1, total gain is <=2H+B+6. Therefore each root has at most O(B/Q)=O(S^(1/4)) LARGE events over the entire prefix, without any label-distinctness assumption. By (1) each LARGE branching factor is O(L), since log Q~log B. The product of all LARGE factors, with any fixed number of extra powers of L, is

    exp(O(S^(1/4) log(2S))) = (log log B)^{o(1)}.

Uniformly in J<=7X, d_y(J)=O(log B/log log B). Indeed k distinct primes dividing J(J+2)=O(B^4) have product at least k!, and the elementary factorial lower bound forces this estimate. The factor for ANY MEDIUM event is therefore <=O(L log B/log log B) by the first term of (1). For histories with at most TWO MEDIUM events before a given state, with arbitrarily many LOW events and all the allowed LARGE events,

    kappa_M(C) <= (log B)^2/(log log B)^{2-o(1)}
               = o(tau).                                 (8)

The fixed implicit constants are absorbed as B tends to infinity. This is for the adaptive mixture distribution, not necessarily the simpler pure-log weights. Thus eventually every such history is GOOD. In particular the shared suffix energy of all pairs whose FIRST physical meeting occurs when each has at most two MEDIUM selections is

    O(XB log^2 B/log log B) = o(XB log^2 B).              (9)

This unconditional deletion includes arbitrary prior LOW blocks, arbitrarily coalesced sources, and the automatically bounded number of near-B selections. The pair can later have arbitrarily many medium events. By (4), all current incidences with at most two medium selections can also be removed, and the number of roots surviving to H with at most two medium selections over their prefix is O(X/log log B). In a hypothetical no-twin window almost all original roots must therefore have at least three medium events in the prefix; this does not bound the cost of such longer histories.

## 6. Actual finite verification

Standalone ECMAScript research/min_clock_ancestry_kraft_audit.mjs, exact remote readback at d2635f0acc4f95b5b42c6ccc0589fd237ffeee8e, blob c8b2b496406b11f9421f4379b6507d572287f44a. Run from repository root:

    node research/min_clock_ancestry_kraft_audit.mjs 1024 4096 16384 65536 262144

Executed the actual audit function in the available JS runtime for all five windows in adaptive and noLOW (y=2,L=2) modes, also the simpler log weights at X1024/4096/16384. This is not a separate local Node invocation. Prefix cutoff gate excludes X256. For each mode: actual all-root prefix, 4658 literal parity-GCD clock comparisons at X1024, LOW barrier, actual post-event divisibility, monotone complexity, summed inverse complexity at each horizon including twin terminal horizons, exact integer first-meeting counts gg/gb/bb using incoming predecessor classes, exact expiry identity, uniform good mass cap and pair bound (also using measured max good horizon count). Four classifications per mode: analytic threshold log^2 B/log log B, exploratory fixed 4096 and 262144 thresholds, and actual at-most-two-medium predicate with a deliberately crude valid finite complexity upper bound. For X<=65536 constructs the charged unordered pair sets, verifies uniqueness and count, then sums their actual full shared-suffix slab energy. At X262144 verifies counts but does not enumerate the corresponding suffix energies. Complexity and fractional energies use floating-point tolerances; pair counts exact integers.

Adaptive y=3,L=6 in all these windows, Q=B because S=1 at finite sizes, so the medium predicate is effectively <=2 non-LOW events except possible p=B. This is not an asymptotic large-Q test.

| X | all unordered first meetings | both <=2 MEDIUM at first meeting | shared suffix energy of those pairs (ordered) | total distinct-pair shared-state energy |
|--:|--:|--:|--:|--:|
|1024|3221|726|210.34|771.27|
|4096|19857|3381|43414.47|271578.71|
|16384|137526|13803|165367.66|1733321.14|
|65536|941252|58250|934020.74|18553205.71|
|262144|5477756|238397|not enumerated|180324100.37|

At X262144 B1355: 3941922 prefix events, 4072994 original source-state incidences, 466351 physical vertices. Maximum summed inverse adaptive complexity at a horizon 0.436026 (rounded up). For the two-medium predicate max good horizon count=21, first-meeting split 238397 gg, 1580332 gb, 3659027 bb; expiry count exactly 238397. At exploratory threshold 262144, gg=424928, gb=1946315, bb=3106513; max good horizon count34 (including terminals). At the analytic tau=26.3233 the adaptive gg count is zero (threshold too small for any high event at this finite scale). The noLOW mode at the same tau has 19148 good-good first meetings and max good horizon count4, hence a nonvacuous analytic-threshold diagnostic, though y fixed. For X65536 the noLOW analytic threshold gives 4125 gg pairs and ordered suffix energy 62580.06. At X65536 adaptive threshold262144 gives 105189 gg and ordered suffix energy1653236.31 (about 8.91% of total distinct-pair shared-state energy); these exploratory thresholds are not asymptotic estimates.

Current good-current shared energy is zero in these finite slab diagnostics, yet the shared suffixes of previously good-good pairs have positive weight, directly demonstrating why (7) covers more than instantaneous good-tag deletion. The finite prefix paths are mostly already terminated at age H, and L,Q have not reached their growing asymptotic regime. There is no proof of a small total high-complexity mass from these data.

## 7. Remaining obstacle

This is an actual unconditional source-weighted early-first-meeting deletion at the target energy scale, including entire later common suffixes. It is not a bound on all first meetings. In the remaining SAME_STATE term at least one original history exceeds the adaptive complexity threshold at its FIRST physical meeting; in particular at least one history has >=3 MEDIUM selections there. The difficult task is to control the two incoming root masses in these high-complexity histories, or derive an additional small weighted class via exact reverse clocks rather than multiplying by an assumed average multiplicity. The first-meeting/expiry identity suggests studying complexity transitions and the original tags entering a bad class, including the good-bad pair products; it does not make those products small automatically. The short-slab asynchronous residual from 065b449 also remains. Main untouched; no new Lean proof or twin-prime infinitude proof.
