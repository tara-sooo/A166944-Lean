# Two-endpoint phase localization for sparse medium repeat costs

2026-11-25 JST. Continuation of b6180907e414b6a2af1ac12ad92444933c7a1adb on research/min-prime-root-repeat-energy-2026-11-25. New band-adaptive phase cells at BOTH repeat endpoints, a bilateral near-phase exclusion using deterministic refinement of successor groups, and an upper as well as lower bound on the remaining asynchronous lags. This changes the previous accounting, not the original MIN dynamics. Neither the new far residual nor the large physical formation residual is bounded. No Lean compilation or external novelty claim.

## 1. Setup and segment duration

Use X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u). Original gain-stopped MIN paths include initial and terminal vertices. A completed selected p at a horizon D has actual wait between 1 and 2r(D), where r(D)<=p, and gain p-1. Thus wait <=3(p-1). In particular at every visited physical vertex (t,D), with original start M,
    M+2<=t<=M+2+3H.
At two visited horizons C<E on a root, h=E-C,
    0<t_M(E)-t_M(C)<=3h.                              (1)
The sum is over ALL original completed events between C and E, not only medium or retained hits. For any two roots visiting both, write signed input lags delta_C=t_M'(C)-t_M(C), delta_E=t_M'(E)-t_M(E). Then
    |delta_E-delta_C|<=3h.                             (2)
These statements are independent of whether the selected words agree. In particular an order reversal of two nonzero lags requires |delta_C|+|delta_E|<=3h. If the two closed elapsed-time intervals are strictly disjoint, their time order agrees at both endpoints; if they touch, the same weak ordering holds. We use nonoverlap of interval interiors in the audit (touching classified with disjoint).

Freeze actual medium events y<p<Q, possibly after previously paid marks, least factor r=r(C), actual attached clock cost a_M(C)<=w_r=r+1.5L, with a_M(C)>=r and L<=ell^.25. For dyadic P<=r<2P use l_P=log(2P). The established sparse quota k_P of 0ce6427 pays first k_P per original root/r/aligned horizon cell A_r=ceil(w_r² u^1.5) and allocates each later hit E's cost a_M(E)/k_P to its last k_P preceding same-cell hits C. Both endpoints are actual medium events with equal r. The first-use, short-gap, bandwise sparse-overlap, and multiscale thin source-cell exclusions are already o(NT). Retain their original classifications and costs. Let V^q count the original sparse common origins per key (r,C,E). In a fixed finest source cell of width d=ceil(H/2^floor(log2(u)/4)), the full original sparse key set A has n>m_P whenever it contains a surviving focal. Partners may be paid tags. Here
    J_d=ceil(H/(2d))+2=O(u^.25),
    m_P=max(1,floor(b_P/J_d)),
    b_P=max(1,floor((B/P)^2 u^-1.5 sqrt(P/Q) f_P)),
    f_P=l_P^6/(1+log l_P)^4 for P>=u²,
        l_P²/(1+L/P)^2 otherwise.
The previous support bound b_P K_P^arith << X B² sqrt(P/Q) l_P/P and quota allocation bound w_r/k_P << ell P (Q/P)^.25/(u^1.5 l_P) imply sum of allocated costs of at most O(b_P) tags per key is O(NT ell/u^.25), independently of actual intersections. K_P^arith is the arithmetic support count, not an exit group parameter.

## 2. Band-adaptive two-endpoint phase cells

Set
    W_P=ceil(H u^(-1/16) (P/Q)^(5/4)),
    J_phase=ceil(4H/W_P)+4,
    m_phase,P=max(1,floor(m_P/J_phase)).
Partition each full original sparse source-cell set further by the pair of aligned time bins
    (floor(t_M(C)/W_P), floor(t_M(E)/W_P)).
These are fixed integer bins for that factor band. We use input times at both horizons; actual successor ticks will be used for near-degree tests. This is a new choice of partner pools, made before the exit reallocation. It is NOT an assumption that equal bins imply physical synchronization.

All original common origins of a key span a source interval <H/2 since C-H<2M-2<=C. At each endpoint their input times consequently span an interval of length <3.5H by the original wait bound. At a fixed first time bin, (1) confines the second times to an interval of length <=W_P+3h. Therefore the number of occupied bin pairs in any one source cell is bounded by
    (ceil(4H/W_P)+4)(ceil(3h/W_P)+3).
Here the crucial uniform estimate is
    h<A_r, A_r/W_P=o(1).
Indeed w_r=O(P+L), H~B²/u^.25 and Q~B/u. Ignoring harmless ceilings,
    A_r/W_P << u^(-3/16) (P/Q)^(3/4) (1+L/P)^2.
For P>=L the last factor is bounded; for P<L the positive power of P/Q dominates any log factor from L. The displayed RHS is uniformly o(1), and W_P tends to infinity uniformly since its minimum is of polynomial order B^.75 times log factors. Thus the phase cell count is O(J_phase) uniformly. We use the full finite envelope in the audit, where diagnostic h/W may be large.

Pay all remaining focal costs in any original phase/source cell with mass <=m_phase,P. Each key has at most J_d source cells and O(J_phase) occupied phase cells in each, so the total paid tag count per key is O(b_P) for sufficiently large X. This uses the asymptotic lower bounds below ensuring the min1 and floors are harmless. Summing the previous arithmetic support and quota weight estimates yields
    R_phase,thin=O(NT ell/u^.25)=o(NT).                 (3)
This is fractional clock payment, not deletion of the entire endpoint hits. Even when the original full intersection is huge, its thin phase portions are paid. The new pool consists of full original tags in one source/phase cell, possibly including already paid partners; the surviving focal subset is not required to be dense on its own. We do not recompute the phase classes iteratively.

Every pair in a retained pool now satisfies
    |delta_C|<W_P, |delta_E|<W_P.                       (4)
For small P the upper bound shrinks by (P/Q)^1.25 compared with the largest band. This avoids assuming uniform distribution of times. It exploits the duration bound to use O(H/W_P) bins rather than O((H/W_P)^2).

## 3. Bilateral successor-near exclusion

Use the reallocation rule of b6180907 but within each full phase/source cell of mass n>m_phase,P. At the later horizon E, partition by the actual successor (s_E,p_E), where s_E is the chosen tick and the new horizon is E+p_E-1. Use
    K_P=ceil(u^.125 u/l_P),
    U=u^1/32,
    D_P=floor(P u^1/16).
Groups of mass >=n/K_P are large (finite guard min2); each large focal allocates uniformly among other tags in its same successor group. All other groups comprise the small pool of mass s_0. If s_0<n/U pay its focal costs as tiny; otherwise distribute each small focal uniformly among the other s_0-1 small-pool tags. For large X the denominators are positive as proved below. Same as previous paper: the tiny aggregate costs O(NH(1+L)/U)=o(NT), since each tag's allocated cost lies between r/k_P and w_r/k_P and the sum over full key/cells is bounded by total medium clock.

At either endpoint C or E, the number of eligible primes >=P is O(u/l_P) by their product dividing (C-1)(C+1) or (E-1)(E+1). Each actual selected tick for a fixed prime p lies in a single class modulo 2p, and different selected labels cannot have the same output tick at a fixed horizon by the least-label tie rule. For any focal output tick, at most
    Delta_P(D_P)=O((1+D_P/P) u/l_P)
distinct successor keys at that endpoint have output tick difference <=D_P.

New refinement: the partition by EARLIER successor (s_C,p_C) refines the partition by LATER successor (s_E,p_E), within the full original common-source phase cell. If both roots share the actual successor at C, they then have the same deterministic physical suffix until one stops. Both reach E and complete its medium event, so the successor at E is identical. This also holds if the first successor is at E itself. The earlier partition of the small pool thus has each group of size <n/K_P, not merely the later partition.

For a small-pool focal, the fraction of partners with output tick difference <=D_P at C OR E is at most
    4 Delta_P(D_P) U/K_P = O(u^-1/32).
Indeed each endpoint has at most Delta near groups, each <n/K_P, and s_0-1>=n/(2U) eventually. Use disjoint priority later close, then earlier close. Summing allocated actual cost gives
    R_bilateral,close=O(NT/u^1/32)=o(NT).             (5)
No bound on the old uniform-partner async component is asserted. All large-group focal costs are instead assigned to physical synchronization classes at E as before.

Every remaining asynchronous small-pool pair satisfies at BOTH endpoints
    |s_C-s'_C|>D_P, |s_E-s'_E|>D_P,
    D_P-4P < |delta_C|, |delta_E| < W_P,              (6)
because each output differs from its input by a wait in [1,2r] and r<2P. Eventually the lower bound exceeds D_P/2. No earlier physical meeting is possible since both visit E asynchronously. The actual pair also satisfies drift (2). A reversal of clock order requires the sum of absolute lags <=3h; time-disjoint and time-overlapping segments can be classified exactly, but no bound on either class or on reversals is proved. The upper/lower lag windows are both new simultaneous restrictions relative to b6180907, and the lower condition at C is new even without time bins.

## 4. Endpoint transfer and physical formation budgets survive

A fixed directed pair M,M' at the later endpoint E can receive charges from <=k_P quota predecessors, regardless of which phase cells were used for different keys. For large group partners the denominator is >=m_phase,P/(2K_P), and for non-tiny small-pool partners >=m_phase,P/(2U). The total transferred charge is thus <=
    W_r^clock=2 max(K_P,U) w_r/m_phase,P.             (7)
Do not confuse the weight W_r^clock with time width W_P.

Uniform lower bound: for P>=sqrt Q, l_P~u, 1+log l_P~ell, and
    b_P >> u^6.5/ell^4 (Q/P)^1.5,
    J_d J_phase = O(u^(1/4+1/16) (Q/P)^1.25),
    K_P=O(u^.125), 1+L/P=O(1).
Therefore
    m_phase,P/((1+L/P) max(K_P,U))
          >> u^(97/16)/ell^4 (Q/P)^.25.
For P<sqrt Q the residual factor (Q/P)^.25 dominates all powers of u, even after accounting for the small-band expression for f_P, 1+L/P and K_P=O(u^1.125/l_P). This also proves uniformly that m_P/J_phase and m_phase,P/K_P grow to infinity, justifying all floor and denominator arguments. Consequently with m_*=u^6.25/ell^4 as in 0ce6427,
    W_r^clock << r u^(3/16)/m_*.
The sum of these natural weights on each original trajectory is O(H u^(3/16)/m_*). It is deterministic at a shared physical state (natural medium classification only, no root-specific marks).

The preceding single-source-cell potential remains applicable because every partner pair belongs to one fixed original finest source cell; the additional time bins can depend on the quota key and are NOT treated as fixed root forests. Use original source-cell forest and raw local mass at first physical meeting, including all starts and expirations. With the previous m_a=floor(u^6/ell^4) (min1), the number of unordered pairs at cell-local first meetings of mass <=m_a is <=m_a N. Each already-synchronized pair's entire allocated charge is bounded by O(H u^(3/16)/m_*), via (7) and the natural common suffix. Thus
    R_already,small=O(NT/u^1/16)=o(NT).               (8)
For immediate synchronization at E's actual successor, the charge is at the one pre-merger horizon of each pair, even if first meeting is terminal. Its two-direction cost is O(Q u^(3/16)/m_*). Retain m_b=max(1,floor((H/Q)m_a)); potential at this cap pays at most m_b N pairs. Hence
    R_immediate,small=O(NT/u^1/16)=o(NT).             (9)
The latter larger cap is ONLY for the unique immediate charge, not subsequent synchronous cost. In both cases the previous asymptotic budgets lose u^1/16 from phase localization but still vanish. Hierarchical or tail-layer extensions are available by the same natural weight argument, not independently tested here.

## 5. Result

After prior quota exclusions and this new reallocation,
    R_med <= o(NT)+R_already,bad^(phase)+R_immediate,bad^(phase)+R_far^(bilateral).
The first two residuals require actual original source-cell first meeting mass exceeding m_a or m_b respectively. The far residual has two equal-minimum-factor horizons in one aligned r-cell, actual sparse common-source phase-cell mass >m_phase,P, relatively small later exit groups and a non-tiny small pool, and simultaneous bilateral lag constraints (2),(6). In particular the new phase-localization prevents unrestricted large phase spread at low P without any bound on the full old async energy. It is not monotone as an allocation of individual pair costs: choosing different pools can increase some synchronous contributions.

The joint OPEN sufficient conditions remain a medium residual sum o(NT) and the existing high E_phys,admitbad+E_async,bad=o(T²Bu) on the same unbounded dyadic windows. No proof of either residual or of twin prime infinitude. A next target is actual arithmetic control of the remaining bilateral far contacts, splitting whether their two temporal segments overlap and using bounded lag drift, or a sharper physical formation estimate. The current lemma does not show that a clock order reversal forces a physical merger.

## 6. Audit

Standalone ECMAScript research/min_prime_root_two_phase_audit.mjs, final exact remote readback at b7fab9eb24c9deb23353781f6a8b25aa90b9e1bf, blob e68f2d1b3622229c492dcc17d258b9ba28e95aca, initial commit 1e1b3dcc13e53043d444ae0cfefe0d1ba79eb966. Run:
    node research/min_prime_root_two_phase_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node invocation. All final 36 runs (six modes x six windows) passed. Inherited original SPF/literal, LOW, sparse quota, source-cell caps, exact reallocation, endpoint multiplicity, common natural tail bound, and restricted source-cell potentials, independent full-medium immediate-synchronization oracle. New checks actual earlier successor, actual segment duration, phase bin count using the general finite envelope, earlier->later successor refinement, earlier degree and small-pool capacity, bilateral lag inequalities and drift on retained far pairs, exact disjoint/overlap partition, full cost conservation including phase-thin/earlier-close components. No test of asymptotic constants or full growing cell ladder; no cumulative optional marks.

Analytic mode uses stated W_P, m_phase,P, K_P,U,D_P with inherited finite guard max(2,n/K_P) and finite y3,L6; analytic residual is empty at all tested windows before phase partition. Diagnostic modes short/wide/phase/stress inherited from b6180907; time width ceil(H/4 sqrt(P/Qm)) (min2) in short/wide/phase, H/32 instead in stress. Diagnostic phase cap uses mcell divided by ceil(4H/W)+4, min1; finite h/W may be large, hence the general phase count check, not the asymptotic thin-cap estimate. Broad mode is stress with W=4H, deliberately wider to exercise far-pair checks. Diagnostic constants do not imply limiting rates.

Largest short X262144: phase thin0, pre-reallocation5886, tiny50, large already5836, first-small1276.3556, remaining4559.6444; earlier refinement64 and degree10 checks. Phase largest294->278.3441; analytic/wide0. No selected immediate cost in any finite modes, as in previous audit; independent immediate oracle retained.

Largest stress X262144: original quota residual18523.3333, phase thin299.6667, remaining18223.6667, tiny2.6667, later close8.3333, earlier close0, far0, large already18212.6667, small-first already10732.3927, final7480.2740. 1160 occupied phase pools tested with surviving focal before phase-thin exclusion, 1026 source-cell phase-count checks, max occupied phase count4,7440 earlier refinement and1061 earlier degree checks,14263 synchronous tail checks, maximum elapsed187 among examined tags. The phase count can include full sets with no surviving tags. Earlier-close incremental charge zero in all finite runs; the upper bound is paper proof, and the refinement and pool capacity checks are independently exercised.

Largest broad X262144: phase thin0, prior18523.3333, final7664.1259 as before, far178.5185 = disjoint140.6667 + overlap37.8519, no reversal, max lag drift57;7562 refinement,1177 earlier degree checks. At X4096 broad far25.6667 = disjoint15+overlap10.6667, max drift40; X16384 far93.2525=60.6061+32.6465; X65536 far33.8333=10.5833+23.25. No early-close or order-reversal positive retained examples at these finite sizes. This is why the broad diagnostic was added: the narrower stress phase cells had no surviving far contribution. These numerical partitions do not prove the limiting bounds. Main and other branches unchanged.
