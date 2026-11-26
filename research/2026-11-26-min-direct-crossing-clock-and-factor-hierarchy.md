# Actual crossing clocks, factor-count hierarchy, and complete-excursion deficit supply

Continuation of [c87f76d](https://github.com/tara-sooo/A166944-Lean/blob/c87f76d2e2b86110d5224c4f0c1f613fc44afe9b/research/2026-11-26-min-direct-weighted-crossing-mass-and-scale-alternative.md). Combine the previous quantitative crossing mass with the global clock balance. This yields a scale hierarchy whose large-event alternative consists of actual long-wait crossers with bounded factor counts (prime cofactors at the cube threshold), rather than arbitrary large B/reset gain. No sparsity or no-witness hypothesis is needed for the hierarchy itself. For fast resets and other fast events in complete canonical excursions, the deficit supply can be localized to preceding/in-excursion increases. A further local sieve excludes bounded-support constant-deficit nonreset runs as the principal source of certified gain unless there are many changes of deficit. Paper deductions and exact finite audits, not a Lean kernel proof or twin-prime contradiction.

## 1. Coverage by actual large crossings controls ALL remaining gain

Use the previous balanced R, P=P_R, ell=ceil(P^(4/11)), S=floor(R/loglog R), V=S^2, D=2P_S+1, normalized actual surviving-cut mass M, and cut weight kappa=2/(alpha Q). Thus D,kappa=X^o(1), ell=X^(2/11+o(1)) and ell<=ceil(X^(2/11)). Fix a canonical ray starting at a fixed root. Consider its event block crossing [X,Y], Y=16X, with first/last event plateaus as endpoints, G total gain, C=floor sqrt(Y+1), ordinary deficits d_a,d_b at endpoints, and W elapsed ticks. As before,
    G=15X+O(sqrt X), d_a<=5X+O(sqrt X),
    2W=G+d_b-d_a, G-2d_a>=5X-O(sqrt X).
The deficit bound is the elementary canonical envelope d<=6+5(H-H_root), not a stationarity assumption. Set T>D, T>=7; we later take T between ell and C. Define H_T to be the set of actual crossing events with p>=T, m_H its count, U the total horizon gain of ALL events outside H_T (including noncrossing events of ANY size), G_H=G-U. Let M_<T be the actual normalized mass of crossing events with p<T.

By the previous upper mass inequality, applied once to the disjoint H_T jumps,
    G+O(E_X)=M(total)=M_<T+M(H_T),
    M(H_T)<=G_H+2(ell-1)m_H+E_X,
where E_X=O(X exp(-.0005r)), r=pi_o(R). Thus
    U<=M_<T+2(ell-1)m_H+O(E_X)
     <=M_<T+2(ell-1)G/(T-1)+O(E_X).                    (1)
This conclusion includes the gains of large NONcrossing events; it is not just a small-label gain bound.

Write n_s=#actual crossings R<p<=D, n_m(T)=#actual crossings D<p<T, and G_m(T) their actual gain. Because small crossings cover exactly one cut,
    M_<T<=kappa*n_s+G_m(T)+2(ell-1)n_m(T)+E_X.          (2)
Every small/medium crossing here is far for T=o(sqrt X) and sufficiently large X, because near p=(1-o(1))*sqrt(H). We do not restrict H_T to far events. If T/ell->infinity and M_<T=o(X), (1) forces U=o(X). This is stronger than a conclusion about how many small crossings there are: essentially all the gain is then carried by actual large crossings.

## 2. Crossing-clock master and factor-count alternatives

Call a long event one with 4w>=g=p-1; call the complementary event fast. Define F_L to be total gain of LONG events in H_T. Every event satisfies w<=2p, including p=3. Therefore
    4w<=12g          outside H_T,
    4w<g             fast inside H_T,
    4w<=(8+8/(T-1))*g  long inside H_T.
Summing and using the exact time balance,
    G-2d_a <= 4W-G
            <=11U+(7+8/(T-1))*F_L.                   (3)
Combine (1)-(3):
    G-2d_a-22(ell-1)G/(T-1)-O(E_X)
       <=11*kappa*n_s+11*[G_m(T)+2(ell-1)n_m(T)]
                                   +(7+8/(T-1))*F_L.   (4)
The exact analogue with M_<T replacing its upper bound (2) is also valid. No finite-twins assumption, reset count, B count, or absence of the offset witness is used in (1)-(4).

For k in {3,4,5,6}, put
    T_k=max(256*ell+1, 1+ceil(9*(Y+1)^(1/k))).
As X tends to infinity, D<T_k<C. On [X,16X] the left side of (4) is at least (5-330/256-o(1))*X>3X for all sufficiently large X, and for k<=5 it is 5X-o(X), since T_k/ell->infinity. Because G_m(T)<= (T-1)n_m(T), every sufficiently large crossed window satisfies at least one of the following quantitative alternatives:
    n_s=Omega(X/kappa),
    n_m(T_k)=Omega(X/T_k),
    F_L=Omega(X).                                      (5)
The first count is X^(1-o(1)) in lower exponent. The second has lower orders X^(2/3), X^(3/4), X^(4/5), X^(9/11), respectively. For k=6, T_6=256ell+1 eventually, and the upper bound ell<=ceil(X^(2/11)) gives the literal last Omega exponent. These are alternatives for each k separately, not four simultaneous middle-band lower bounds. Unlike the preceding A1-based master, (4) also applies when the direct twin-offset certificate occurs; under finite twins all sufficiently large windows of the chosen ray are crossed and earlier no-witness restrictions on moderate A1 remain available.

The earlier long-clock roughness lemma applies: every prime factor f of H-1 or H+1 satisfies f>=w/2 (if f<p it is eligible, and its strict future clock is within 2f; if f>=p use w<=2p). Hence a long event p>=T_k has
    f>=(p-1)/8>(Y+1)^(1/k).
Neither neighbor, of size at most Y+1, can have k prime factors counted with multiplicity. For selected H-e=pq, q>=p and is an integer, so
    Omega_arith(H-1), Omega_arith(H+1)<=k-1,
    Omega_arith(q)<=k-2.                               (6)
Here Omega_arith is the number of prime factors with multiplicity, not asymptotic Omega. For k=3, q is prime and the other neighbor is prime or semiprime; square semiprimes are included. Consequently the third alternative of (5) at the cube threshold is macroscopic gain from actual crossing events with prime cofactors, not just arbitrary large B or resets. At fourth/fifth/sixth-root levels one obtains a stronger middle-count exponent at the cost of allowing more prime factors in q.

For a direct comparison with the previous three-scale theorem put T0=ceil(8ell/3), n_m0=#crossings D<p<T0, and G_band(T)=gain of actual crossing events T0<=p<T. By one additional application of the mixed/upper mass estimate,
    M_<T<=kappa*n_s+(T0-1+2ell)*n_m0
                 +(1+2ell/(T0-1))*G_band(T)+O(E_X).
Thus if the two previous small/middle populations are o(X/kappa), o(X/ell), respectively, then for EACH k in (5) either G_band(T_k)=Omega(X) or F_L=Omega(X). This is a refinement of the remaining global large-scale alternative; G_band includes all crossing types (including A1), and we do not assert that its gain consists solely of B/reset events. It does not eliminate either of the new alternatives.

## 3. Fast large resets and B in complete excursions require upward nonreset supply

With the same H_T and U, let L_up be the gain of actual NONRESET events in H_T with 2w>g (strictly increasing ordinary deficit on their full plateau step). Every such event is long, and the factor lower bound improves to f>g/4; in particular they have the certification (6) at T_k. For any event the ordinary increment is delta=2w-g. Its positive part is <=5g outside H_T and <=(3+4/(T-1))*g inside H_T. A reset inside H_T has post deficit 0 or6, so its positive increment is <=6 even if the clock is long.

For all fast events p>=T, irrespective of actual crossings, delta<-g/2. Let F_fast be their total gain. On the whole event block total downward changes are at most d_a plus total upward changes, by d_b>=0. Therefore
    F_fast <=2d_a+10U+(6+8/(T-1))*L_up+12G/(T-1).       (7)
This keeps the boundary reservoir d_a explicitly. For complete canonical-to-canonical excursions it can be removed.

Split the actual continuing ray at its canonical visits. Consider any family of complete excursions wholly contained between the event-block endpoints, each containing at least one designated fast event p>=T. Their event intervals are disjoint. For an excursion beginning at a quiet canonical tick, replace only the first event wait by the elapsed time since that tick, which is positive and no greater than its original wait. The first step then has pre deficit6. The final canonical visit may be at most three quiet ticks after the last event: its ordinary deficit is6 and the last post deficit is nonnegative. The sum of positive event increments plus the final quiet increase (at most6) equals the sum of negative event increments exactly. No reset may be counted as an increase larger than6. A designated fast event has actual excursion increment no greater than its original increment, hence still decreases by >g/2. Each selected excursion contains at least T-1 gain and there are at most G/(T-1) of them, and at most G/(T-1) large crossing resets. Summing the exact balances over the disjoint excursions, their designated fast-event gain F_fast,comp satisfies
    F_fast,comp <=10U+(6+8/(T-1))*L_up+24G/(T-1).         (8)
This applies to fast nonreset B as well as fast resets; only fast events in complete excursions can discard the boundary deficit.

Now designate all fast resets p>=T. Every reset p>=7 has a distinct associated canonical visit within seven ticks before another p>=7 event, on an infinite ray. Apart from at most one reset in each of the two incomplete boundary excursions, all are in complete excursions. A complete excursion contains at most one such large reset, at its ending normalization. Thus if F_fast,reset is the total fast large reset gain in the whole block,
    F_fast,reset <=10U+(6+8/(T-1))*L_up
                              +24G/(T-1)+2C.           (9)
There is a stronger causal statement for each completed fast reset: its pre deficit in that excursion is >g/2, so starting from6 it needed at least g/2-6 net increase BEFORE the reset. All preceding large crossing increments in its excursion are nonresets (otherwise there would be an intervening canonical visit before this reset). Positive increments can be charged only to preceding events in that same excursion, giving the alternative bound F_fast,reset<=10U+(6+8/(T-1))*L_up+12G/(T-1)+2C. The looser (9) is enough here and also follows directly from (8). This preceding-only allocation is separate from the full-excursion allocation for arbitrary fast B.

For k<=5, if M_<T=o(X), then U=o(X) by (1), so macroscopic fast-reset gain (or macroscopic fast-B gain in complete excursions) implies L_up=Omega(X). In other words the final large reset cannot carry such a fraction using short waits alone: an earlier population of long, upward, nonreset crossers must supply it. At k=3 this is a macroscopic gain of certified nonreset events with prime cofactors. For k=6 the U estimate has a fixed 2/256 factor; one may increase the fixed multiplier 256 depending on a specified positive target gain share, or take it slowly to infinity (which changes the middle count to X^(9/11-o(1))). We do not claim U=o(X) for the fixed k=6 cutoff.

This treats an actual nonsparse reset mechanism instead of assuming sparse canonical visits. Boundary root-free fast-B intervals still obey (7) with d_a and may need different control. The presence of many fast resets is not by itself a contradiction.

## 4. Local sieve and bounded-support certified gain

For p>=T_k and a long clock, both neighboring integers are free of factors <=(T_k-1)/8, a power of X. The dimension-two upper sieve of [global-sieve](https://github.com/tara-sooo/A166944-Lean/blob/c87f76d2e2b86110d5224c4f0c1f613fc44afe9b/research/2026-11-26-min-direct-global-sieve.md) applies not only in the prime-cofactor case but for all k=3..6: if the selected neighbor is pq, the integers q and pq+2e both avoid small prime factors. At fixed p and e the two forbidden q residues modulo f are 0 and -2e/p for odd f small enough, distinct because f<p. Use the previous sieve cutoff floor(N^(1/12)) on an arbitrary q interval of length N. All these small primes are below the certified roughness threshold because T_k>=256ell is a power of X with exponent at least 2/11-o(1). For bounded N absorb into the same absolute constant.

On a physical contiguous subblock of horizon gain L0, every q for a fixed p lies in a consecutive integer interval of length N<=ceil((L0+2)/p)+1. On one ray q strictly increases between occurrences of p>=5, since H increases by at least p-1 and the side correction varies by at most2. Summing the two signs, the certified gain at p on that subblock is at most
    O((L0+p)/log^2(2+L0/p)).                            (10)
Apply the same sieve in the whole window: the gain at one p is O(X/log^2 X), uniformly. For a fixed cofactor q use p<=min(q,floor((Y+1)/q)), a range of size at least T_k whenever an event exists and at most sqrt(Y+1). The residues forbidden for p are 0 and -2e/q (q is invertible modulo the small primes even if composite). A fixed p,q pair cannot repeat because the two possible pre-horizons differ by2 and the gain p-1>2. Thus each fixed q also has gain O(X/log^2 X). If F_L=Omega(X), this implies Omega(log^2 X) distinct selected labels and Omega(log^2 X) distinct cofactors (prime in k=3, otherwise certified almost-prime). Moreover discarding labels with fewer than c log X occurrences removes at most c log X * sum_{p<=C}(p-1)=O(cX); choose c sufficiently small relative to the positive macroscopic share. The remaining Omega(log^2 X) labels each have Omega(log X) occurrences. These global diversity conclusions extend the prior certified-return sieve to the actual crossing population and the almost-prime thresholds.

More locally, on any family of pairwise disjoint contiguous physical subblocks each of gain L0>=L*C, choose at most j certified labels per subblock, with choices allowed to vary arbitrarily between subblocks. Since p<=C, (10) gives total certified gain on all the chosen labels at most O(jG/log^2(2+L)). If L->infinity and j=o(log^2 L), this is o(X). Thus macroscopic certified gain cannot be supplied by long blocks with such small selected supports, even if the supports vary adaptively. This is a local upper supply bound, not a claim that all trajectories admit such a cover.

In the k=3 case, under finite twins, all certified q are eventually beyond the largest twin member. Two occurrences of the same certified p then have q difference >=4, since q is odd prime and distinct. Their pre-horizon difference is >=4p-2. Hence for any physical block of gain L0 the total certified gain on a fixed p is at most L0/4+(p-1) (count disjoint spacings between successive selected occurrences, including the last event gain). A set of j labels carries at most jL0/4+sum_{p in set}(p-1). This elementary complementary bound does not use sieve asymptotics; it does not imply a contradiction for arbitrary varying supports or force a minimal cofactor return.

## 5. Constant ordinary deficit restricts high nonreset support

Consider a maximal run of consecutive events with unchanged ordinary deficit d'=d. For a nonreset p>=T_k in the run, d>=2p and p divides (d-6I)/2. Thus every such p divides the positive integer
    (d/2)*((d-6)/2).
The product of the DISTINCT high nonreset labels in this run divides that integer. By the global canonical envelope d=O(X), the integer is O(X^2), and because T_k>=256ell=X^(2/11+o(1)), at most 13 such distinct labels are possible for all sufficiently large X. The constant is deliberately loose; no bound on the number of small labels in a flat run is asserted. No large reset belongs to such a high-deficit constant run. All the flat high nonresets have 2w=g and therefore are long, regardless of actual crossings.

Let J be the number of events with d'!=d in the block, and F_flat the gain of certified high nonreset crossers in the constant-deficit runs. There are at most J+1 runs. For runs with gain >=L*C apply (10) to their at most13 high nonreset labels. Short runs contribute at most L*C each. Thus uniformly for any L>=1,
    F_flat <= O(G/log^2(2+L)) + L*C*(J+1).              (11)
In particular J=o(sqrt X) implies F_flat=o(X), by choosing L large fixed and then letting X grow (or choosing L sufficiently slowly growing). If F_flat>=delta X then some fixed L depending on delta gives J=Omega(sqrt X). This controls the possible constant-deficit component of a macroscopic long nonreset population, not all of its gain: many changes of d, or nonflat high events, remain possible. The bound does not require finite twins.

## 6. Diagnostics and persistence

[Audit e59b861](https://github.com/tara-sooo/A166944-Lean/blob/e59b8611ca474f5dcfd35f5ac143a11d4cd55149/research/min_direct_crossing_clock_factor_audit.mjs), blob 45e88d63764a8b47e624d75bd763706e6106a008. Exact remote readback. Run node research/min_direct_crossing_clock_factor_audit.mjs 30000. Actual ECMAScript execution in tool runtime, not a separate Node process. 14998 odd canonical roots through30000,243497 actual events,0 unresolved180 cap; 24 additional targeted canonical starts (238 candidates searched) whose first event satisfies the exact cube certificate. Three finite hybrid sieve periods (510615 positions),26945 block/cutoff controls with exact BigInt mass accounting,26945 each coverage, clock and combined checks;45791 crossing incidences,40284 high crossing incidences,31517 long high crossing incidences. 125106 actual roughness checks; factor-count certificates 24/4524/10055/14252 for k=3/4/5/6 respectively. The 24 cube-certified starts all cross surviving cuts in all three finite controls,72 control incidences and1468 cut incidences. 26237 independent literal gcd-clock checks for the targeted first events. For example M582781,H1165560,p977,q1193,w488, both H-1=1051*1109 and H+1=977*1193 semiprime; ordinary deficit6->6. M557557,H1115112,p1051,q1061,w1573, H-1=1051*1061,H+1=1115113 prime. These certify prime cofactors, not a twin pair between the two neighboring integers.

35121 complete canonical segments,7191 selected excursions containing fast events,8388 marked fast events (7000 resets,1388 nonresets),1127 upward high crossing incidences;7191 exact excursion balance/transfer tests and26945 boundary reset tests. Example canonical horizon4428, labels19/5/3/61, fast reset61, T17,S5,R7,V17, prior upward large crossing gain18. Finite controls use small arbitrary T and exact periodic mass, not the macroscopic threshold T_k or absence of twins. In scans the final quiet canonical visit after a terminal plateau is not added; formal event-tick endpoints are allowed in the finite balance checks. The theoretical statements apply to continuing rays. 53714 constant-deficit runs,2604 high nonreset divisibility checks,2570 support-product checks,maximum observed support2. 20937 repeated long-label spacing checks,1077 incidences where two successive tested cofactors actually are prime with difference2 (overlapping small-cutoff blocks, not distinct pairs and not necessarily cube-certified). The local sieve estimate (10) uses the previously proved upper sieve; not a new numerical test of its asymptotic sharpness. All final assertions passed, including the extended audit. No observed large-X asymptotic crossed window is claimed.

Remaining objective: bound the actual small/middle crossing capacity, or exclude a macroscopic certified high population using the prime-cofactor gap restrictions and localized deficit changes. The new factor hierarchy has traded the unclassified large-B/reset branch for either an additional intermediate-band supply or a certified long-clock population; neither is yet ruled out. No Lean executable/kernel verification, no new Fourier exponent and no finite-twin contradiction. Main and sibling branches not modified.
