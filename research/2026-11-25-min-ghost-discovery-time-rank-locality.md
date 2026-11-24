# Discovery-time and discovery-rank locality for long-span known-to-known transitions

2026-11-25 JST. Continues 498dd222951e084b286664881075edcad0f00425 on the SAME research/min-cycle-forest-2026-11-24 branch. New two-stock bounds with no restriction on either first-to-current stride: locality of the two first-discovery TIMES, or locality of their order among the distinct large labels discovered. A further early-stock corollary. The rank proof combines a bounded history-measurable stock with a variable-length rough-stride sieve. Both reach the square-root scale for the stated classes. Original paper derivation and finite ticket audit, no external search or Lean compilation. No full signed peak or actual physical far-coalescence theorem.

## 1. Setting and tickets

Use the common independent CRT ghost, conditional on common initial time parity, with infinite odd-prime alphabet or finite initial segment. An event p adds p-1 to the even gain, with completed wait w<=2p. Through integer time U the exact conditional first-selection hazard for unused p>=z0=ceil(sqrt(2U)) is <=2/p^2. Initially revealing a disjoint small-prime set preserves this hazard. All selections and discovery ranks refer to the original trajectory.

Fix HIGH cutoff A>=5 and LOW primorial L=2 product_(3<=ell<A)ell. Consecutive high events q,p have intervening even LOW gain d in [0,L). Restrict to the prefix whose POST-gain is <=2U, containing every positive attained peak. The total prime weight there is <=3U. Suppose q,p>=z0, p repeated; take U large so z0>L+3. Consecutive equal high labels at this scale are impossible as proved earlier. Let u_r,t_r be the FIRST pre-gain and first-selection tick of label r. Write current pre-gains G_p=u_p+m p+a, G_q=u_q+n q+b, with m>=1,n>=0,a,b in {-2,0,2}. These representations are unique and m p,n q<=2U+2. For q fresh n=b=0. The consecutive-high relation is
    m p-(n+1)q=u_q-u_p+b-a-1+d.                     (1)
No bound on either stride other than the gain cap is imposed in this note.

As in 51c90c61c02d43629de2ac666cc5c0274ca1b5f0, assign a p-weighted necessary-condition ticket at the later of the two first selections. If p is later, enumerate n,a,b,d and positive M=(n+1)q+u_q-u_p+b-a-1+d=m p. If q is later, enumerate m,a,b,d and positive M'=m p+u_p-u_q+a-b+1-d=(n+1)q. The first pre-gain of the newly selected label at that tick and the earlier label's data are known BEFORE the tick. Retain positive targets O(U) (actual witnesses obey this). Each has O(1) prime divisors >=z0, and the other stride is determined by division. Actual distinct pairs consume distinct tickets because the tuple fixes G_p, which grows strictly. We only count tickets assigned when the candidate label is actually newly selected. No known label is treated as unused.

## 2. Time-local first-discovery pairs, no upward ratio bound

Let W_time count the total p-weight of the above transitions satisfying
    |t_p-t_q| <= K min(p,q), K>=1.
Both current selections can be very far from their first selections, and no upper ratio restriction on p/q is needed.

For p in [P,2P),q in [Q,2Q), P,Q>=z0, the earlier first tick must lie in the preceding T=ceil(2K min(P,Q)) ticks before the later first tick s. Intersect with [1,s-1] if needed. Let K_R(s;T) be the number of previously selected distinct primes in band [R,2R) whose first tick lies in that deterministic preceding window. For each s,
    E K_R(s;T) <= O(T/(R log R)).
This follows by summing the exact fresh hazard and the elementary prime-count bound over the at most T ticks; it does not condition on the later first-selection event.

At a candidate p-first tick, enumerate at most O((L+1)U/Q) possible known-q stride/offset tuples per q in this recent stock. Each positive divisor target has O(1) candidate p>=P; weight times hazard <=2/P. The conditional expected weight is <=O((L+1)U K_Q(s;T)/(P Q)). For q-first, enumerate O((L+1)U/P) tuples per known p in the recent stock; each candidate q>=Q has hazard <=2/Q^2, weight <=2P. Conditional expected weight <=O((L+1)U K_P(s;T)/Q^2). Thus the preceding stock estimates and U ticks give
    E W_time,[P,Q] <= O((L+1) U^2 T/(P Q^2 log(2U))).           (2)
All bands have logs comparable to log U; rounding T is absorbed since min(P,Q)>=z0. The local-stock condition at the tick is predictable; the final pair time locality does not condition the fresh hazard on future success.

Sum over both dyadic band families from z0 through 2U+1. For P>=Q the sum of min(P,Q)/(P Q^2)=1/(P Q) is O(1/z0^2). For P<Q it is 1/Q^2, with at most j preceding P bands for Q=2^j z0; the sum of j/4^j is finite. Therefore
    E W_time(U;K) <= O((L+1) K U/log(2U)).                     (3)
This holds for all K>=1 (may overcount when K min(p,q)>U). L<=log^(1/8) U and K=log^(1/2) U give O(U/log^(3/8) U). There is no roughness requirement, no time-locality requirement on the current pair other than consecutive high, and no upper bound on p/q.

An additional corollary uses first PRE-gain separation. If |u_p-u_q|<=K min(p,q), let x be the later-discovered label, y the earlier. Between the earlier first POST-state and the prestate immediately preceding the later first event, all completed waits total <=3 times their gains (2r<=3(r-1) for every odd prime r). Thus
    |t_p-t_q| <= 3|u_p-u_q|+2x.
If x<=F min(p,q), F>=1, this implies the time gate with parameter 3K+2F. In particular this handles nearby first gains for comparable label sizes, and for all discovery orders with the later label smaller than the earlier. It makes no claim when a much larger later first event spends a long preceding wait.

## 3. Early-stock corollary

If both first ticks <=T0<=U, then use the ordinary (nonlocal) two-stock tickets but sum only the first T0 ticks, with E K_R(s)<=O(T0/(R log R)). The maximum stride lengths still depend on U, not T0, since the realized pair may occur much later. This gives
    E W_early,[P,Q] <= O((L+1) U T0^2/(P Q^2 log(2U))).
Geometric summation from z0 yields
    E W_early(U;T0) <= O((L+1) T0^2/(sqrt(U) log(2U))).           (4)
For T0=floor(U^(3/4) log^(1/4) U) (capped at U) and L<=log^(1/8) U the bound is O(U/log^(3/8) U). Thus the contribution of pairs both discovered during this early portion can be deleted even if both later spans and their first-discovery time separation are large. There is no ratio restriction or roughness assumption. This does not estimate pairs with only one early first tick.

## 4. Rank-local first-discovery pairs and a variable-length stride sieve

Order the distinct labels >=z0 by their first-selection ticks. Denote their one-based rank by rho(r). The rank does not increase at repeats or at discoveries of smaller labels. For integer k>=1 consider pairs satisfying
    |rho(p)-rho(q)|<=k,
    w_p>p/4,
with p repeated as before. This rank locality is independent of first-to-current gain spans and of the elapsed time between first discoveries. At the later first-selection tick, the earlier label is among the last k distinct large labels first selected before the tick. That list is history-measurable and contains at most k entries, even if many ticks have elapsed since its earliest entry. Use it instead of estimating the entire previously selected stock.

Take z=ceil(U/log^(5/2) U), which eventually exceeds z0. First handle target p<z. For a known label r in [z0,z), the stride interval in the ticket proof has length N=O(1+U/r) and can be enlarged to an integer interval of length comparable to U/r. In particular N is at least a fixed positive multiple of log^(5/2) U. Because w_p>p/4, all available odd ell<=p/8 are ineligible at G_p. For the known-r stride j (n when p later, m when q later) the candidate target G_p is V+j r for a known shift V (absorbing the +q term if required). At every odd ell<min(p/8,r), the target roughness forbids exactly TWO residues of j, since the known prime r is invertible modulo ell. No exceptional-coordinate event or random collision estimate is needed. The slope r is known; the new candidate prime is not part of this sieve variable.

Apply the explicit elementary Selberg quadratic bound from the preceding rough-stride note (93b0ef2377a1b8ea5bd261e814c58a7ef2a9d2d7), now at the variable scale N. Put D_N=floor(N^(1/20)) and Y_N=N^kappa with fixed sufficiently small kappa>0. The mean log d of the normalized unrestricted divisor weights is O(log Y_N), so choose kappa so that at least half of the weight has d<=D_N. The local product over odd ell<=Y_N is O(1/log^2(2N)), and the error O(D_N^6)=O(N^.3) is absorbed by N/log^2(2N). Thus uniformly in V,r and the revealed coordinates,
    #rough j <= O(N/log^2(2N))
              <= O((U/r)/(log log U)^2).                    (5)
For all large U, Y_N<z0/8, as N=O(U/z0). One can initially reveal a FIXED disjoint set of all ell<=U^kappa (increasing the harmless constant cutoff if needed, or decreasing kappa), and use the relevant subset ell<=Y_N for each r. This preserves the exact fresh hazard for candidate p,q>=z0. If the finite initial alphabet lacks a qualifying pair it contributes zero; otherwise the small sieve primes are present. The bound (5) holds on every realization of revealed coordinates.

There are two discovery-order cases at a later tick s.
- P-latest: earlier q is on the list of at most k large labels. If q<z, apply (5) to n, enumerate a,b,d in O(L+1) choices, and enumerate the O(1) prime divisors >=z0 of the positive target M=m p. Ticket weight times fresh hazard <=2/z0. Per known q the conditional expected ticket weight is at most O((L+1)U/(q z0 (log log U)^2)) = O((L+1)/(log log U)^2). If q>=z, do not use the sieve at all. Its unsieved stride count O(U/q) gives O((L+1)U/(z z0)), which is O((L+1) log^(5/2) U/sqrt U), smaller than the displayed bound. This covers arbitrarily large predecessor q, not just middle bands.
- Q-latest: earlier p is on the list, and p<z by the current target restriction. Apply (5) to m, enumerate offsets, and take O(1) candidate divisors q>=z0 of the positive M'=(n+1)q. Each has hazard <=2/z0^2 and weight p. Per known p the conditional expected ticket weight is O((L+1) U/(z0^2 (log log U)^2)) = O((L+1)/(log log U)^2).

The bound is per known list entry, not per dyadic band: the divisor count already covers ALL new primes >=z0, so no extra factor log U arises from summing bands. Sum over at most k entries and U ticks, with the same injective actual ticket assignment, obtaining
    E W_rank,<z(U;k) <= O((L+1) k U/(log log U)^2).            (6)
For p>=z, the earlier weighted single-position rough-return theorem bounds ALL gain-capped long-return weight by O(U (log log U)^3/log^(1/2) U), regardless of q or ranks. Therefore for the whole rank-local long-target class,
    E W_rank(U;k) <= O((L+1) k U/(log log U)^2
                          + U (log log U)^3/log^(1/2) U).    (7)
Choose L<= (log log U)^(1/4), k=floor((log log U)^(1/2)) (at least 1); A can still grow to infinity slowly. The first normalized term is O((log log U)^(-5/4)), and the second vanishes. These slow choices are sufficient rather than optimized. No restriction on the absolute first-selection separation, either current stride, or p/q. This is a distinct class from time locality (3): intervening large first discoveries may be few even over a long elapsed gap.

For the subregion p,q<=U^(1-epsilon), fixed 0<epsilon<1/4, all relevant N>=c U^epsilon. The same proof replaces the first term in (7) by O_epsilon((L+1) k U/log^2 U) for that subregion alone, without the top deletion term. This allows k to grow faster there. This is not a bound for unrestricted rank gap; k must satisfy the stated growth conditions.

## 5. Signed peak consequences and remaining obstacle

In the backward scan of 498dd222951e084b286664881075edcad0f00425, retained positive ordinary repeated high steps p>=z0 have a_i^+<=4p and w_p>p/4. The estimates (3),(4),(7) thus give additional positive-step deletions in the existing signed residual inequality. Use a common slowly growing LOW cutoff with L<= (log log U)^(1/4), the above K,k,T0, and keep the disjoint negative shadow/record/ordinary credits. The union of these additional deletions costs o(U) in expectation:
    E[(D(U)-[R_new-C_shadow-C_other-Nminus]_+)_+]=o(U).
All earlier positive-step classifications are on the original trajectory. A remaining positive repeated target with predecessor and target >=z0 must, after deleting these classes, have all three:
    |t_p-t_q|>K min(p,q);
    max(t_p,t_q)>T0;
    |rho(p)-rho(q)|>k.
The earlier first-to-current long-span constraints, roughness, record and shadow exclusions still apply in their respective ranges. These are necessary residual conditions, not a sufficient proof of sublinear residual. In particular a late pair of widely separated discovery ranks and times may have long spans at both endpoints. The current gain and time of the pair are not assumed independent of those discovery data. The result does not treat q or p below the square-root threshold, nor solve the global signed limit or actual physical far-coalescence bound. No new branch, no main edit, no twin-prime proof.

## 6. Finite diagnostic and persistence

Saved research/min_ghost_discovery_time_rank_locality_audit.mjs and research/min_ghost_discovery_time_rank_locality_results.json; exact remote readback at 42353783c60b2255564091ad0ef4e491f7accfe7. Run node research/min_ghost_discovery_time_rank_locality_audit.mjs 256 1024 4096 16384 65536. Executed script logic in the available JavaScript runtime, not separate Node or Lean. Fixed pseudorandom CRT phases, finite alphabet <=4U, 64 paths per window except48 at largest. A5,L6,K4,k3, diagnostic base=max(7,floor(ceil(sqrt(2U))/8)); separately record the analytic root stock and ranks. Diagnostic z=max(root,ceil(U/log^2.5 U)) equals root at these finite scales, so the new rank-local analytic interval [root,z) is empty in the finite suite. The base is intentionally lower for nonvacuous structural testing. No empirical estimate of implied constants, limiting rates or calibrated coupling error.

At each fresh capped large selection enumerate tickets against earlier labels qualifying by the time gap or rank gap (using both diagnostic and root rank lists where applicable). In each discovery order enumerate the earlier label's stride, offsets and LOW gains, solve the positive divisor relation and retain parity and gain-cap constraints. For rank tickets also check roughness at odd ell<=min(47,p/8), not the asymptotic variable sieve set. Record the total candidate budget. For actual consecutive high pairs with repeated target verify relation (1); compute original first times and ranks and both strides. Verify unique ticket coverage for the qualifying time-local pair or long rank-local pair, and per-path weight bounds. Both locality classes are counted separately, with intentional overlap; the union consumes each actual tuple once.

Across U=256,1024,4096,16384,65536 there are 304 diagnostic capped pairs, 70 time-local pairs, 126 diagnostic rank-local long-target pairs, including 49 with both labels repeated. Among the latter rank-local long-target class, 79 endpoints do not meet the time-local gate (this count includes fresh predecessor cases). 23 time-local pairs have both m,n>4; 31 long rank-local pairs have both m,n>4. 149 distinct actual ticket checks pass, of which 31 P-latest and118 Q-latest. No actual qualifying pair was found at the analytic root threshold in these samples. The lower diagnostic tests are arithmetic/injection tests and do not apply the analytic root hazard there. At U65536,48 paths:2712 events,3 diagnostic pairs, one rank-local long-target pair with nonlocal first time gap, target weight53, matching unique ticket. All assertions pass. The proof of the expectation bound is analytic; no numerical sieve rate or early-stock corollary is tested here.

## 7. Next target

Use the three discovery-separation conditions together with the previous long first-to-current spans and record/shadow credits. In particular the new rank gate says that an untreated pair above root must have at least k intervening distinct large discoveries between its first selection ticks (rank difference >k). A further estimate must exploit this crowded discovery interval without charging its same stock repeatedly to different future pairs, or derive a global signed cancellation. The full peak and physical far-coalescence limits are still open.
