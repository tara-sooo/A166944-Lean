# Multi-event negative shadows and local predecessor stride bounds at the square-root scale

2026-11-25 JST. Continues 93b0ef2377a1b8ea5bd261e814c58a7ef2a9d2d7 on the SAME research/min-cycle-forest-2026-11-24 branch. Two new results: deterministic multi-event signed cancellation after a short-wait large label, and a latest-discovery residue/divisor bound for a repeated target whose preceding high label has a short FIRST-to-current gain span. The second reaches the square-root scale for bounded or slowly growing upward ratios, even when the target has a long first-to-return span. Original paper derivations and finite path diagnostics. No external literature search or Lean compilation. Neither full signed-peak convergence nor actual physical far-coalescence upper bound is proved.

## 1. Model and notation

Use the common independent CRT ghost for the infinite odd-prime alphabet or a finite initial segment. Conditional on common initial time parity, each prime has independent uniform horizon/time coordinates modulo p. Executed event label p adds gain p-1, with its completed preceding wait w<=2p. The exact tick-history law gives first-selection hazard <=2/p^2 for every unused p>=z0=ceil(sqrt(2U)) through integer time U. The history is the original path, not an artificially restarted one.

Fix A>=5, LOW primorial L=L_A=2 product_(3<=ell<A)ell, and HIGH labels >=A. Consecutive high poststates have intervening LOW gain <L and LOW maximum uncorrected signed height increment <=5L. Write h=2s-g_post and J=h-6chi, where chi is actual clock parity. The sentinel at s=g=0 has J=-6epsilon. Let a_i=J_i-J_(i-1) between consecutive HIGH poststates (or the sentinel). Then a_i<=2w_i-(p_i-1)+5L+6. Every positive attained peak through U is in the prefix whose POST-gain<=2U, since gain is increasing; its total prime weight is <=3U.

## 2. Multi-event negative shadows

Consider a HIGH event q at index j with q>=40L+56 and w_q<=q/4. Let i>j be ANY later HIGH event, and let G=g_i-g_j and T=s_i-s_j be actual gain and elapsed time between the poststates of q and i, including every intermediate event of every scale.

The uncorrected change between the previous HIGH poststate j-1 (or sentinel) and the poststate of q is <=5L+2w_q-(q-1) <=5L+1-q/2. For EVERY executed odd prime r, its uncorrected height change is 2w_r-(r-1)<=3r+1<=5(r-1), since r>=3. Consequently the uncorrected change after q is <=5G. It also equals exactly 2T-G, so is <=2T. The parity correction telescopes over the WHOLE interval and costs at most 6, not 6 per event. We have the stronger pathwise inequality
    J_i-J_(j-1) <= -q/2+5L+7+min(5G,2T-G)
                  <= -q/2+5L+7+min(5G,2T).
In particular, if EITHER
    G<=q/20  OR  T<=q/8,
then
    J_i-J_(j-1) <= -q/8.                              (1)
Call these the gain and time shadows of the short-wait anchor q. These are conditions on actual cumulative gain and time, not on the number or identity of intervening labels. They allow arbitrary mixtures of previously selected or fresh labels, and the time version even permits arbitrarily large intervening gain. As both cumulative coordinates are increasing, the union of the two shadows covers an initial consecutive set of subsequent high poststates (possibly empty). This is a multi-event extension of the previous downward pair rule, not a claim of improvement of its constants for every two-event pair. It holds without a gain cap or square-root lower bound on the later label.

Extend the backward peak-prefix erasure scan: at a positive repeated ordinary candidate endpoint i, if it is in either shadow of any earlier qualifying anchor j, jump to j-1 and keep the exact signed change as one nonpositive interval. One may choose the latest such j for definiteness. If no shadow applies, optionally apply the previous downward-pair rule, then the ordinary equal-label nonrecord erasure, then a single ordinary step. Strict backward index decrease guarantees disjoint coverage and exact telescoping. Every retained ordinary repeated event still strictly updates its original same-label J record, and no such positive retained endpoint can lie inside a shadow of a prior short-wait anchor. No physical process is restarted or modified.

Let C_shadow denote the sum of minus the actual J changes of the selected shadow erasures. It satisfies C_shadow>=sum_(selected anchors) q/8 by (1). These are distinct anchors, and their actual gains and elapsed intervals are charged exactly once. Let C_other denote the other disjoint erasure credits and Nminus the negative ordinary increments. With R the ordinary repeated positive increments, the existing LOW-tail and fresh-wait argument gives
    D(U) <= 5L+12 +2F_wait(U)+(5L+6)K_U
                 + [R-C_shadow-C_other-Nminus]_+,
where K_U is the number of distinct selected labels, E K_U=O(sqrt U/log U), E F_wait=O(U/log U). As before for L<=U^(1/4) the expected additive/fresh part is O(U/log U). The scan is an accounting rule on the actual path. It does not prove a lower bound on the total shadow credit relative to the full repeated surplus, since a large negative anchor may have no later positive endpoint within its shadow or may already be in a different erasure interval.

## 3. Local predecessor bound for consecutive high transitions

Take consecutive high events q,p with p repeated, p,q>=z0, in the gain-capped prefix. Eventually z0>L+3, so q=p is impossible by the even gain/sign condition of the previous notes. Let u_p,u_q be the first pre-gains of p,q. Their current pre-gains have unique representations for p,q>=7,
    G_p=u_p+m p+a,  G_q=u_q+n q+b,
    m>=1, n>=0, a,b in {-2,0,2}.
When q is fresh n=b=0. The intervening LOW gain d even, 0<=d<L, gives
    m p-(n+1)q=u_q-u_p+b-a-1+d.                     (2)
This note restricts the PREDECESSOR stride n<=K, where K>=1 and K+1<z0. There is NO restriction on the target's m except the original gain cap. In particular the target may be far beyond the earlier first-span deletion range. q may also be repeated; this is not the fresh-predecessor-only result.

For bands p in [P,2P), q in [Q,2Q), P,Q>=z0, assign necessary tickets at the LATEST first selection among p,q, as in 51c90c61c02d43629de2ac666cc5c0274ca1b5f0. The tick pre-gain u and the other label's first pre-gain are known from history. Use only u<=2U, and relevant known first pre-gains <=2U. Actual tuples are included. Distinct realized pairs have distinct target pre-gains, so their tuples identify distinct tickets. Count their target weights p. At a tick there are two cases:

P-latest: q is known and p newly selected. For each n in [0,K], offsets a,b, and d, (2) forces
    p | M=(n+1)q+u_q-u+b-a-1+d, M=m p>0.
Retain only M=O(U), which covers all actual capped witnesses by m p<=2U+2. The number of prime divisors of each such M in the p-band is O(1) since P>=sqrt(2U); discard M<=0. For each known q there are O((K+1)(L+1)) tuples. Conditional expected ticket weight is <=2/P for each candidate fresh p. Thus conditional new total weight is O((K+1)(L+1) K_Q(s)/P), where K_Q(s) is the number of previously selected distinct q-band labels. Importantly this counts n directly instead of all O(U/Q) possible strides.

Q-latest: p is known and q newly selected. Use (2) as a CONGRUENCE for the candidate q rather than enumerating the long unknown target stride m. For each n in [0,K], a,b,d,
    (n+1) q == u_p-u+a-b+1-d (mod p).
Because 1<=n+1<=K+1<p, this specifies exactly ONE residue of q modulo p. There are at most 1+Q/p <=1+Q/P integers q in the q-band in that residue. Ignore their primality for this count; each actual candidate unused prime has hazard <=2/Q^2. For a candidate q, (2) determines m uniquely; impose m>=1 and cap as necessary. This is crucial: no enumeration of the O(U/P) possible target strides is required. Ticket weight is p<=2P. Conditional new ticket weight is at most
    O((K+1)(L+1) P (1+Q/P) K_P(s)/Q^2).
Neither case treats an already selected label as fresh, nor conditions the discovery hazard on later return success.

The previous hazard stock estimate E K_R(s)=O(U/(R log R)) applies to each band R>=z0. Summing both discovery orders over U ticks gives the new rectangle theorem for the total p-weight W_localQ,[P,Q]:
    E W_localQ,[P,Q] <= O((K+1)(L+1) U^2/log(2U)
                         * (1/(P Q)+1/Q^2)).              (3)
The constant is uniform for the allowed K,L,bands, in either infinite or finite initial-segment model. No roughness condition or record condition is required. This is a bound on all qualifying pair weights, not the probability of zero occurrences. In the special case P=Q=z0 it is O((K+1)(L+1) U/log U). Compared with the unrestricted preceding two-stock divisor estimate O((L+1)U^3/(P Q^2 log U)), (3) removes a polynomial factor at the square-root scale for these localized predecessor transitions.

## 4. All scales with a bounded upward ratio

Let W_localQ(U;K,F) count the same capped pairs with p,q>=z0, predecessor n<=K, and p<=F q, F>=1. Take both dyadic band families starting at z0 and ending at 2U+1. A contributing pair of bands must satisfy P<2FQ. Sum (3) over this larger region. The sum of 1/(P Q) over all bands is O(1/z0^2)=O(1/U). For the other term, at Q=2^j z0 there are O(1+log(2F)+j) eligible P bands. Therefore
    sum_(Q>=z0 dyadic) sum_(z0<=P<2FQ dyadic) 1/Q^2
        <= O((1+log(2F))/z0^2).
It follows that
    E W_localQ(U;K,F)
       <= O((L+1)(K+1)(1+log(2F)) U/log(2U)).         (4)
For example take L<=log^(1/8) U, K=floor(log^(1/2) U), F=log^(1/4) U (at least1), so that K+1<z0 eventually. The normalized expectation is O(loglog U/log^(3/8) U), tending to zero. These slowly growing choices are selected for simplicity, not optimality. Downward ratios p<=q can be arbitrarily small; only the upward ratio is bounded. Unlike the prior comparable fresh-to-known theorem, q can be a repeated label. Unlike the prior weighted local-span sieve on p, the target p may have an arbitrarily large first-to-current span within the gain cap. We cannot simply remove the upward ratio restriction: summing the 1/Q^2 term over all P bands may lose a full log U, and the displayed rate then need not vanish.

There is an elapsed-local version when q is a strict same-label corrected-height record or is fresh. If q's current tick s_q is within H q of its first tick t_q and J_q>=J_first,q, then
    n q+b =2(s_q-t_q)-6(chi_q-chi_first,q)-(J_q-J_first,q)
           <=2H q+6.
Hence n<=2H+8/q<=2H+1 for q>=11. Taking H<= (K-1)/2 suffices. This observation applies only when the corrected height has not decreased relative to that first occurrence; mere elapsed locality alone need not bound n when height has decreased. The main theorem (4) uses gain locality directly and needs no record of q.

## 5. Application to the signed residual

For p>=z0 eventually p>=10L+14, so a_i^+<=2w_i<=4p by the preceding-LOW bound. Thus (4) implies expected positive surplus o(U) for all the indicated transitions, including those in the original-history strict-record and retained ordinary sets of the new shadow scan. Delete this additional class, once, along with the earlier positive-step deletions; keep all disjoint negative credits. The result is
    E[(D(U)-[R_new-C_shadow-C_other-Nminus]_+)_+]=o(U).
In particular a remaining positive ordinary repeated transition with p,q>=z0 and p<=Fq must have predecessor first-to-current stride n>K. The earlier local-first-span theorem also removes targets with short first-to-current stride (its K can be larger). These constraints hold even when the predecessor is not itself a retained ordinary step. In addition, such a positive endpoint cannot be within the gain or time shadow of a prior short-wait large anchor. This is a deletion of a genuine additional subset at square-root scale, not a theorem that every known-to-known transition at square-root scale has sublinear weight. The long spans of both endpoints, upward ratio failures, and smaller-scale repeatedly used labels still require control. The full signed residual and physical far-coalescence estimate remain open.

## 6. Finite diagnostics and persistence

Saved research/min_ghost_local_predecessor_shadow_audit.mjs and research/min_ghost_local_predecessor_shadow_results.json, exact remote readback at d7e62d322e58c659d7ffea1eeeab512f24d8967a. Run node research/min_ghost_local_predecessor_shadow_audit.mjs 256 1024 4096 16384 65536. Executed script logic in the available JavaScript runtime, no separate Node or Lean run. Fixed pseudorandom common CRT phases, finite initial alphabet <=4U, 96 paths per window except64 at largest. A5,L6, K6,F4, diagnostic base=max(7,floor(ceil(sqrt(2U))/8)). The lower diagnostic threshold is for structural testing, not the analytic hazard. No estimate of the implied asymptotic constants or calibrated finite-to-infinite sampling error.

For every qualifying capped local-predecessor pair, check (2), exact latest-p positive divisor or latest-q congruence via modular inverse, and integer progression count. Across the suite 298 pair checks, 26 both repeated, 230 with target stride m>diagnostic K, 8 P-latest and290 Q-latest. Only 2 pairs at the actual root threshold (both at U1024), so the nonvacuous both-repeated and long-target tests primarily concern the diagnostic smaller labels. The script checks necessary arithmetic constraints rather than enumerating the entire hypothetical ticket budget of (3). No numerical asymptotic inference.

For each actual short-wait large anchor enumerate all subsequent high poststates in its gain or time shadow and check the bound J_i-J_(j-1)<=-q/8. Then scan backwards from the last high state before the first attained peak, prioritizing the latest available shadow for positive repeated endpoints, otherwise equal-label record erasure, otherwise ordinary steps. The finite scan uses the shadow and record rules; the optional previous downward-pair rule is not included in this audit. Check disjoint coverage, exact signed telescoping, nonpositive erased changes, strict retained repeat records, equal-label erasure lattice and final peak bound.

Across the five windows 1115 anchor-endpoint shadow checks and12 shadow erasures in actual peak-prefix scans. At U65536,N64:4153 events,65 short-wait anchors,507 shadow endpoint checks (271 gain-shadow endpoints,507 time-shadow endpoints; overlap is intentional),263 positive repeated endpoints counted with anchor multiplicity, largest tested shadow interval has60 HIGH events INCLUDING its anchor. Seven shadow erasures in the actual peak scans, total actual shadow credit8426, separate record credit16856. The credit totals are aggregate descriptive statistics, not net residual estimates; no cancellation across paths. In addition 6976 synthetic worst-case bounds for multi-event cumulative gain/time at L=6,30,210, with up to13 events including anchor. All assertions passed. No Lean compilation.

## 7. Next target

Use the new local-predecessor congruence rather than an enumeration of both long first-return strides, and the actual disjoint shadow credits, to analyze transitions where BOTH labels have long first-to-current spans. The square-root result requires predecessor locality and an upward-ratio cap; removing those restrictions or bounding their surviving signed contribution remains necessary. No new branch, no main edit, no twin-prime proof.
