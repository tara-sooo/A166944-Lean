# Gap-adaptive phase cells and two-ended quota transfer for medium repeats

2026-11-25 JST. Continuation of d18bbd422750741bd45b834039d974c5b5cd4448 on research/min-prime-root-repeat-energy-2026-11-25. The new phase width depends on the actual repeat gap as well as the factor band. A dyadic gap-specific arithmetic support bound pays for the additional bins. Near the top medium band, the residual asynchronous lags are o(h), where h is the repeat gain, and disjoint elapsed-time segments must both have actual duration o(h). A two-ended quota transfer and a band-adaptive near-source exclusion also follow. This is a sufficient reduction, not a proof of the fast or overlapping residual costs, nor of twin primes. No Lean compilation or novelty claim.

## 1. Inherited sparse accounting

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, Q=ceil(B/u), N=Theta(X/u) original prime roots M in [X,2X). Freeze medium actual selections y<p<Q, or a subset after previous paid accounting marks. Let r be the least eligible odd prime, P its dyadic band (P<=r<2P), l_P=log(2P), w_r=r+1.5L, L<=ell^.25 the slow primorial LOW threshold. The actual cost a_M(E) (r plus the attached original LOW block) lies in [r,w_r]. Total original cost O(NH), no rerunning MIN.

The previous sparse quota at each original source/r/aligned horizon cell of width A_r=ceil(w_r² u^1.5) pays the first k_P hits, k_P=ceil(u^1.5/ell^1.25+u^1.5 l_P(1+L/P)(P/Q)^.25/ell). Each subsequent hit E allocates a_M(E)/k_P to its last k_P preceding same-list hits C in the same cell. First-use, short gap h=E-C<=D_r (D_r=max(1,floor(r u^1.5 log²(2+min(r,u))/ell^1.5))), original sparse common-origin band cap and thin-source-cell tests remain paid o(NT). In particular long gaps satisfy h>D_r>>r uniformly. The finest fixed source cells have width d=ceil(H/2^floor(log2(u)/4)); each key (r,C,E) occupies <=J_d=ceil(H/(2d))+2=O(u^.25) source cells. Use original full sparse sets even if some tags have already been paid.

Let A_P=ceil((2P+1.5L)^2 u^1.5), so h<A_r<=A_P. Recall b_P from 9780b569:
    b_P=max(1,floor((B/P)^2 u^-1.5 sqrt(P/Q) f_P)),
    f_P=l_P^6/(1+log l_P)^4 for P>=u²,
        l_P²/(1+L/P)^2 otherwise.
From the earlier arithmetic support and quota bounds,
    b_P K_P^env << X B² sqrt(P/Q) l_P/P,
    w_r/k_P << ell P (Q/P)^.25/(u^1.5 l_P).
Here K_P^env denotes the numerical upper envelope in the next section, not an observed count, and not the exit group threshold. Total cost of O(b_P) tags per possible key in that envelope is O(NT ell/u^.25) after summing bands.

## 2. Gap-specific arithmetic support

Use dyadic gap S=2^j with S<=h<2S. Count only long pairs in the arithmetic envelope, regardless of which actual roots or quota edges visit them. For fixed r in band, a possible h lies in 0 or +/-2 modulo r, and there are O(S/r) such shifts in [S,2S) because any band containing a long pair has 2S>D_r>>r. For each shift use the same quotient four-form sieve as 711a0db, with h<A_r and r>=u² (small P bands may use the elementary bound throughout). Uniformity in h holds by the same logarithm-of-exception-product argument. The count per fixed shift is O((X/r)((1+loglog r)/log r)^4), or simply O(X/r) for small r. Sum over r in the band using the ordinary prime counting bound:
    K_{P,S} << X S (1+log l_P)^4/(P l_P^5), P>=u²;
    K_{P,S} << X S/(P l_P), otherwise.
Equivalently K_{P,S} << (S/A_P) K_P^env, where
    K_P^env = X u^1.5 P (1+log l_P)^4/l_P^5 for P>=u²,
            = X u^1.5 P(1+L/P)^2/l_P otherwise.
For large P use A_P~P²u^1.5; for small P A_P~(P+L)^2u^1.5. This is a bound on possible arithmetic keys, not on pair multiplicity or on actual distribution of visits.

There are O(u) dyadic gap bands with S<A_P. Introduce the gap-specific budget
    b_{P,S}=max(1,floor(b_P A_P/(u S))).
Uniform floor/min1 issues disappear asymptotically since b_P>>u and S<A_P. Therefore
    sum_S b_{P,S} K_{P,S} << b_P K_P^env.             (1)
This pays for more phase bins at smaller gaps; it costs a factor u in the budget for the largest gap. The constants in all envelopes are absolute; using the stated cap requires no unknown sieve constant as a parameter. The sum is over dyadic S with possible long keys, not over every integer h.

## 3. Gap-adaptive phase cells

For a given factor/gap band define
    v_P=u^(-1/16)(Q/P)^.75,
    W_{P,S}=ceil(S v_P),
    J_{P,S}=(ceil(4H/W_{P,S})+4)(ceil(6S/W_{P,S})+3),
    m_{P,S}=max(1,floor(b_{P,S}/(J_d J_{P,S}))).
Use input time bins of width W at BOTH C and E, within each original fixed source cell. Here W tends to infinity uniformly (S>>r and v_P>=u^-1/16), W=o(H) uniformly because S<A_P and W/H << u^-5/16 (P/Q)^1.25(1+L/P)^2. In particular the upper width bound is asymptotically smaller than the previous width H u^-1/16(P/Q)^1.25, even when P is small (L grows slowly). The general phase-count envelope now matters: h may be much larger than W.

For every original root with both hits, the elapsed duration is positive and <=3h, since every completed wait<=2r<=3(p-1). Across all common origins their times at either endpoint lie in an interval of length <3.5H, because their sources span <H/2 and each wait sum from the root is <=3H. For each first-endpoint bin the second endpoint lies in an interval of length <=W+3h, so the number of occupied pairs of bins is <=J_{P,S}. Thus thin phase/source portions of full original sparse sets (mass <=m_{P,S}) have total at most b_{P,S} tags per key eventually. Pay these costs directly using (1):
    R_gap,thin=O(NT ell/u^.25)=o(NT).
The lower bound in section 5 ensures m_{P,S} grows uniformly and justifies the min1, flooring, and thin-tag bound. No assumption that the sparse tags are evenly distributed in time. Partner pools are now defined by the full original source/phase cell for each key, not by iteratively deleting partners. The earlier fixed source-cell tests can be retained; the previous phase partition is replaced, not counted twice.

## 4. Bilateral far lag and fast disjoint segments

Reapply the successor reallocation of d18bbd4 to each new phase cell with mass n>m_{P,S}: let K_P=ceil(u^.125 u/l_P), U=u^1/32, D_P=floor(P u^1/16). Large later-exit groups of mass >=n/K_P allocate to their own other tags. Small-group pool with total s0<n/U is paid tiny; otherwise normalize over other small-pool tags. The earlier successor partition refines the later one. At either endpoint the near-exit degree is O((1+D_P/P)u/l_P). Therefore the union of close-exit fractions at C or E costs O(NT/u^1/32) as before, and tiny costs O(NT(1+L)/U). The same proof applies because the new pool is a subset of actual original tags sharing the key. Floors and denominator lower bounds follow from section 5.

For remaining asynchronous pairs define delta_C=t_M'(C)-t_M(C), delta_E=t_M'(E)-t_M(E), and h=E-C. Then
    D_P-4P < |delta_C|, |delta_E| < W_{P,S},
    |delta_E-delta_C| <=3h and <2W_{P,S}.
The actual later and earlier successor ticks both differ by >D_P. The pair cannot have met physically before E, by deterministic persistence.

In particular in the upper medium subrange P>=Q/u^(1/24), v_P<=u^-1/32. As h>=S>>1, W_{P,S}/h=O(u^-1/32). There the two nonzero signed input lags and their drift are o(h). If the elapsed-time segments [t_M(C),t_M(E)] and [t_M'(C),t_M'(E)] have disjoint interiors, BOTH durations are <W_{P,S}: after orienting the disjoint intervals, the first duration is bounded by the gap between the start times and the second duration by the gap between the end times. Thus in that upper subrange each disjoint residual segment has actual elapsed time O(h/u^1/32), on both roots. In particular a segment with duration >=h times a fixed positive constant cannot participate in the disjoint class there, for sufficiently large X. This is a genuine quantitative restriction on the actual waits, not on the sum of minimum-factor clock proxies. No estimate on the frequency or cost of these fast segments is proved. At smaller P we retain the exact W_{P,S} bounds but do not claim W=o(h). Overlapping segments and clock-order reversals need further analysis; the lag inequality alone does not force physical merging.

## 5. Uniform capacity and transfer to either endpoint

For the capacity calculation put v=v_P. Up to constants, since W=o(H) and W tends to infinity,
    J_{P,S} << (H/S) (1/v)(1+1/v).
Using b_P A_P/H >> u^.25 sqrt(P/Q) f_P(1+L/P)^2, the unrounded phase-cell cap therefore has the lower bound
    m_{P,S} >> u^-1 sqrt(P/Q) f_P(1+L/P)^2 min(v,v²).
For P>=sqrt Q, f_P~u^6/ell^4, K_P=O(u^.125), 1+L/P=O(1). When v<=1, the factor sqrt(P/Q)v² equals u^-1/8(Q/P); when v>=1, sqrt(P/Q)v equals u^-1/16(Q/P)^.25. Thus, uniformly in possible long gaps,
    m_{P,S}/((1+L/P) max(K_P,U))
        >> (u^(19/4)/ell^4)(Q/P)^.125.                (2)
Indeed the powers of Q/P obtained in either case are at least .25. For P<sqrt Q, v>1 eventually, and the remaining factor (Q/P)^.25 dominates every fixed power of u and ell; after retaining (Q/P)^.125, the other half absorbs the small-band f_P, K_P and L factors. This proves (2) with uniform constants and shows that unrounded m_{P,S} and m_{P,S}/K_P tend to infinity uniformly, so floor/min1 and denominator estimates are valid. Put m_g=u^(19/4)/ell^4.

For a fixed directed source pair at E, the focal root has at most k_P quota predecessors C, hence the total charge from ALL such keys (including variable gap widths and different allocation rules) is at most
    sup_S 2 max(K_P,U) a_M(E)/m_{P,S}
          << a_M(E)/m_g * (P/Q)^.125.                (3)
This uses the denominators >=m_{P,S}/(2K_P) or >=m_{P,S}/(2U). In particular a state-dependent natural weight envelope is O(r/m_g), with per-root sum O(H/m_g). We use this upper envelope for arbitrary frozen subsets, not equality of separately thinned tails.

NEW earlier-endpoint version: for a fixed root M and fixed earlier hit C in its frozen same-r/cell list, C is among the last k_P predecessors of at most k_P later hits E, because E must lie within the next k_P positions of that list. Those E have the same r and their cost is <=w_r. Thus for a fixed directed source pair at C the total transferred charge over all later endpoints and gap bands is at most
    sup_S 2 max(K_P,U) w_r/m_{P,S}
          << r/m_g * (P/Q)^.125.                    (4)
Unlike the later bound this need not use the actual cost at C; the envelope suffices. This is a two-ended transfer, so for ANY class of allocated pair charges the whole class is bounded by the smaller of the corresponding summed earlier- and later-endpoint envelopes. One may select which endpoint receives each charge and pay the sum of the two separate envelope budgets; no simultaneous double payment is necessary. No extra factor counting arithmetic repeat partners. It does not assert that every pair meets at both endpoints physically.

## 6. Near-origin exclusion and physical formation

Choose the band-dependent source-distance cutoff
    d_P^origin=max(1,floor(u^(9/2)/ell^4 * (Q/P)^.125)).
For a fixed focal source M and later hit E, at most 2 d_P^origin other integer sources can lie within that distance; use no distribution assumptions about the actual prime starts. From (3), the allocated far asynchronous charge to all such partners is O(a_M(E) u^(-1/4)). Summing focal medium hits yields
    R_far,near-origin=O(NT/u^.25)=o(NT).               (5)
The same bound also holds for the union of synchronous charges to such partners if desired, but we use (5) only on the remaining asynchronous class. In particular new far residual pairs have |M-M'|>d_P^origin as well as the two time-lag conditions. This is a band-adaptive source-separation bound, not merely a consequence of different physical times.

For synchronous charges use the original disjoint fixed source-cell forests, NOT key-dependent time cells as if they were fixed root ensembles. The truncated quadratic potential gives <=mN unordered pairs first meeting with local raw mass<=m, including terminal visits and expirations. As in b6180907, already-synchronous total charge per unordered pair is O(H/m_g), from the whole natural common suffix, and the immediate-synchronization charge is unique at the one pre-merger horizon with cost O(Q/m_g). Here we reduce the previous formation cutoffs to
    m_a'=max(1,floor(u^(9/2)/ell^4)),
    m_b'=max(1,floor((H/Q)m_a')).
The first-small already-sync and first-small immediate charges each cost O(NT/u^.25)=o(NT). The new thresholds are SMALLER than those in d18bbd4: tighter lag windows are obtained at the cost of weaker unconditional physical formation exclusions. The old method is an independent alternative; the allocations are not monotone and one cannot assume both versions' residual conditions simultaneously for free. The immediate cap is only for the unique pre-merger charge, not the subsequent common suffix.

## 7. Joint remaining estimates

After the inherited sparse exclusions, gap-specific phase-thin, tiny and bilateral close, near-origin far and new physical first-small formation exclusions, we have
    R_med <= o(NT)+R_already,bad^(gap)+R_immediate,bad^(gap)+R_far,bad^(gap).
The last term has dense original sparse phase/source cells, both endpoint output lags >D_P, input lags <W_{P,S}, drift<=3h and <2W, and origin separation>d_P^origin. At P>=Q/u^1/24 its time-disjoint subcase requires both actual durations O(h/u^1/32). The other two terms require cell-local first physical merger masses >m_a' or >m_b' respectively. These are new conditions on the actual cost allocation; no bound on the old uniform partner residual is implied.

Joint OPEN sufficient conditions on the same unbounded dyadic windows are the new three medium residuals summing to o(NT) and the previous high residual E_phys,admitbad+E_async,bad=o(T²Bu). Neither is proved. The next actual obstruction is to bound fast disjoint segments (actual tick duration, not the r-cost proxy), and overlapping asynchronous pairs with small relative lag/drift; or to obtain a stronger physical formation estimate. No proof of twin prime infinitude.

## 8. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_gap_phase_audit.mjs, final exact remote readback at 00b534d617ea6786a34f8dc774101dac68de81fe, blob 41beb3fff677d4f54c58715eb44d4b6bc6598560, initial audit 590989ab677e8bcec78e3659331d95663c131615. Run:
    node research/min_prime_root_gap_phase_audit.mjs 256 1024 4096 16384 65536 262144
Executed audit function in the available ECMAScript runtime, not a separate Node invocation. All final 36 runs (six modes x six X) passed. Inherited canonical SPF/literal, LOW and sparse quota, actual successor/refinement, two-endpoint phase and near degree, exact fractional partitions, natural tail and restricted potential, independent immediate-merger oracle. New checks gap band, phase-cell general envelope, min cap over possible dyadic gaps, two-sided endpoint multiplicity/cost bounds, disjoint both-duration<W, localized drift, near-origin far partition and endpoint envelope. Does not independently audit the asymptotic four-form support constants, gap-cap summation, full growing source ladder or the exact asymptotic first-merger cutoffs of section 6. Analytic mode inherits previous analytic raw merger caps in the code; its residual is empty before the new allocation, so analytic transfer and first-merger assertions are vacuous there. The diagnostic modes use intentionally small finite thresholds and do not prove asymptotic savings.

Analytic widths and gap caps as stated, finite y3,L6, source widths approximate three-point ladder. Short/wide/phase diagnostics use W=2S (min2); stress W=S (min2), broad W=4H. Diagnostic gap-cap formula uses original diagnostic b_P,A_P and u, min1 floors; diagnostic origin cutoff16, raw formation caps4/8 and immediate3 times raw. The broad diagnostic is included to exercise the nonzero far/disjoint classes rather than to exhibit the upper-band fast asymptotic constraint.

Largest X262144 analytic: 3960 long gap key checks, all prior band-covered, residual0. Short: pre-reallocation5886, already5836, tiny50, small first1276.3556, final4559.6444, 556 earlier directed endpoint checks. Phase:294->278.3441, 7812 earlier endpoint checks. Wide residual0.
Stress largest: old quota residual18523.3333, phase thin304.6667, new pool cost18218.6667, tiny2.6667, already18209.3333, far6.6667 all overlap, first-small already10737.7260, final7478.2740. 2573 gap key and1164 phase-cap checks,89412 earlier directed endpoint checks (max multiplicity2), two retained far directed edge checks, max lag/h .8333. No near-origin far cost in this mode. The previous phase reallocation's stress far was zero; a changed allocation need not improve every component.
Broad largest: 89710 earlier directed endpoint checks, max multiplicity2 (later3),2573 gap checks and959 phase-cap checks, 638 retained far directed edges,486 disjoint both-duration checks. Far178.5185=disjoint140.6667+overlap37.8519, near-origin2.8889 (four directed edges), far-origin175.6296; final7661.2370 after the independent near-origin exclusion (previously7664.1259). Broad X4096 far25.6667->15, X16384 far93.2525->77.5354, X65536 far33.8333->25.1667. Broad width intentionally large, so these are not examples of the asymptotic fast restriction. No positive retained earlier-close, reversal or immediate-synchronization charge; inherited independent oracle tests actual immediate merging. No cumulative optional marks. Main and other branches unchanged by this checkpoint.
