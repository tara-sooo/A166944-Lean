# Time-height localized upward source capacity and scale-restricted supply

Continuation of [26ada2c](https://github.com/tara-sooo/A166944-Lean/blob/26ada2c8c9c572aefa93941460ff1625e785f7e8/research/2026-11-26-min-direct-height-localized-flux-and-sparse-support.md). Localize the guard-potential balance in the horizon as well as in deficit height. The upper capacity for positive sources at a fixed prime becomes proportional to the local horizon length rather than the entire macroscopic window. A very large upward label cannot contribute more than the total guard width per occurrence, regardless of its own gain. Consequently a macroscopic collection of fast drops with small total local guard widths forces an actual scale-restricted, locally diverse positive-source population, unless small labels pay for it. This is an upper bound on localized upward supply in terms of source support and scale, and a conditional transport theorem, not a universal o(X) upper bound or twin-infinitude contradiction.

## 1. Local positive-source sieve

Use the established adaptive MIN event model, with even H, selected odd prime p, gain g=p-1, wait w, side I, e=1-2I, d'=d+2w-g, 0<=d, and w<=2p. Fix a physical contiguous canonical block with pre-horizons in [X,Y], Y=lambda X, lambda>1 fixed, C=floor sqrt(Y+1), G=O_lambda(X). Let integer T->infinity, T<=C. Fix a horizon length L satisfying C T^epsilon<=L<=X for some fixed epsilon>0; take integer L. Statements apply when this interval of choices is nonempty. Partition the pre-horizons into bins [jL,(j+1)L), and assign each entire event to its bin, including its actual gain and deficit movement. Each nonempty bin is a contiguous physical block of gain G_j<=L+C. The bins partition the original block; the number is O_lambda(X/L). In the asymptotic regime C/L=o(1). Empty bins have zero gain. No event is truncated at a bin boundary.

A positive ordinary-deficit event satisfies 2w>g. Hence both neighbors H+-1 avoid every odd prime f<g/4: such a prime would be eligible, and its strict future clock at distance <=2f<w preempts the actual choice. Fix p>=T and a side e within one bin. Write H=pq+e. The possible q lie in an integer interval padded to N=ceil(L/p)+2 consecutive integers. For all odd primes f<=z=floor(min(p,L/p)^(1/12)) and sufficiently large T, both q and pq+2e must avoid zero modulo f. The two forbidden roots are distinct, since f<p and f is odd. Also z<g/4, z^6<=sqrt(N). The earlier elementary [Selberg upper sieve](https://github.com/tara-sooo/A166944-Lean/blob/26ada2c8c9c572aefa93941460ff1625e785f7e8/research/2026-11-26-min-direct-global-sieve.md), with its uniform translated-interval error, gives at most
    O(N/log^2(2+min(p,L/p)))
actual occurrences. Distinct occurrences on one ray have distinct H. Since L/p>=T^epsilon and p>=T, summing the two sides gives the bound
    N_up(j,p) <<_epsilon L/(p log^2 T).                  (1)
In particular the total upward gain associated with one prime within one bin is O_epsilon(L/log^2 T). No prime-cofactor hypothesis, twin-finitude hypothesis or bound on multipliers/deficit variation is used. The use of L in place of X is essential: it permits repeated occurrences of the same label in different bins without assigning its full macroscopic capacity to each bin.

## 2. Guard potential and upper capacity of the sources

Within each bin choose ANY subset of fast nonreset events p>=T, where k=floor sqrt(T)>=3 and fast means k w<g. In particular all chosen events decrease ordinary deficit. Let F_j denote their gain. Define the finite height union E_j=union over chosen events [d',d'+g], with width M_j=length(E_j), and Phi_j(d)=length(E_j intersect [0,d]). If none are chosen use E_j empty. This is the preceding guard potential, but it can be different in every bin. Every chosen event has its whole deficit decrease inside its assigned interval, so its localized drop is g-2w>alpha*g, alpha=1-2/k. The total of ALL positive Phi_j increments in that bin is denoted P_j. By exact telescoping,
    alpha F_j <= P_j+Phi_j(d_start,j)-Phi_j(d_end,j)
                <= P_j+M_j.                            (2)
This retains the endpoint cost for EACH different potential. We do not assume that potentials cancel between consecutive bins.

For any event with positive Phi_j increment, d'>d, and the increment is
    length(E_j intersect (d,d']) <= min(M_j,3p+1).
Moreover if this increment is positive, there is a height u in E_j intersect (d,d') (up to endpoints); thus the source begins below u, ends above u, and both ends lie within 3p+1 of u. This is actual height locality, not a statement that a source ends at one of the selected ending heights.

For any cutoff B_j>=T (integer, allowed to exceed C), split actual positive sources into p<T, T<=p<=B_j, and p>B_j. Put G_low,j equal to the gain of ALL p<T events in the bin. The low positive flux is <=5 G_low,j. The large positive flux is bounded without a sieve by
    P_large,j <= M_j G_j/(B_j-1),                      (3)
since each large event supplies at most M_j and their count is at most G_j/(B_j-1). This applies to arbitrarily large jumps that pass entirely across the guard union. If B_j>C the contribution is zero.

Let S_j be the set of DISTINCT primes of actual middle sources with positive Phi_j increment (not all prime labels in the bin, nor all eligible divisor candidates). Applying (1) and the overlap bound gives
    P_mid,j <<_epsilon (L/log^2 T)
                         sum_(p in S_j) min(1,M_j/p).   (4)
The factor 3p+1 is absorbed in an absolute constant. One can equivalently use the sharper individual log^2(2+min(p,L/p)) from section 1. Each source label is counted once in its bin even if its occurrences traverse many disjoint guard components. In particular, with D_j=sum_(p in S_j)min(1,M_j/p), the new upper supply inequality is
    alpha F_j <= 5 G_low,j + M_j
               + M_j G_j/(B_j-1)
               + K_epsilon L D_j/log^2 T.             (5)
This is valid without a bound on total ordinary variation, relay gain, multiplier size, absolute height baseline, or global number of distinct ending heights. Its usefulness depends on the actual local guard width and local source support. It does not assert that S_j or D_j is small in an arbitrary trajectory.

## 3. Aggregate transport and local diversity

Let F=sum_j F_j, M=sum_j M_j, G_low=sum_j G_low,j. Assume for a sequence of canonical macroscopic blocks that
    F>=rho X,   M=o(X),   G_low=o(X)                    (6)
for fixed rho>0. The selected fast population and height unions may differ from bin to bin. No common global height support is needed. Choose a fixed delta>0 small in terms of rho and lambda, and B_j=max(T,1+ceil(M_j/delta)). Then M_j/(B_j-1)<=delta, including M_j=0. Summing (2)-(3) yields
    sum_j P_mid,j >= alpha F - M-5G_low-delta G
                  >= rho X/2                          (7)
for sufficiently large X and sufficiently small delta. Combining (4) and (7),
    sum_j D_j >>_(lambda,rho,epsilon) (X/L) log^2 T.    (8)
In particular the count of distinct (bin, middle upward-source prime) incidences has the same lower bound. This is stronger than merely demanding Omega(log^2 T) primes somewhere in the entire window when X/L grows. It counts local label diversity, not globally distinct primes; the same label may appear in different bins.

There are also Omega(X/L) actual bins in which both the chosen fast gain and the localized middle positive flux are Omega(L), and hence D_j=Omega(log^2 T). Proof: the number of nonempty bins is at most c_lambda X/L, and G_j<=L+C<=2L eventually. Select bins with F_j>=rho L/(2c_lambda); their total selected gain is >=rho X/2, so at least rho X/(4L) bins qualify. From M=o(X), G_low=o(X), all but o(X/L) bins have both M_j and G_low,j below any fixed positive multiple of L. Let f0=rho/(2c_lambda). In those qualifying bins, use alpha>=1/2, M_j<=f0 L/16 and 5G_low,j<=f0 L/16 (these hold outside o(X/L) bins), and delta<=f0/32. Then (2)-(3) give
    P_mid,j >= (f0/2-f0/16-f0/16-2delta)L
              >= f0 L/4.
By (4) D_j>>log^2 T in each such bin. All constants fixed; no limit exchange over a changing number of bins. This proves a local positive-source necessity for many distinct horizon intervals, including when the selected ending heights across the entire window are numerous and the total ordinary variation is macroscopic.

## 4. Restrict the actual source scale

Suppose additionally the fast population in each bin uses p<=R0, T<=R0<=C, and at most K distinct ordinary ending heights per bin, where R0,K may depend on X. Then M_j<=K(R0-1). If K R0=o(L), the sum of local guard widths is o(X), so the M hypothesis of (6) follows automatically. In this case
    B_j <= max(T,2+K(R0-1)/delta) = O_rho,lambda(K R0)
for nonempty selected bins. Hence if F>=rho X and low-label gain is o(X), there are Omega(X/L) local bins with both Omega(L) fast gain and Omega(L) ACTUAL localized positive flux from upward events with labels
    T<=p<=O(K R0),
and with at least Omega(log^2 T) distinct upward labels in EACH such bin. Their upward gain is also Omega(L), since each positive increment is at most 5g. All source segments intersect the actual selected-height guards. If the cutoff is above C the scale restriction is vacuous, but the local diversity conclusion remains.

Example of a nontrivial scale separation: fixed 0<a<=b<1/2, T=ceil(X^a), R0=floor(X^b) (choose admissible T<=R0, or b>a), K=(log X)^A for fixed A>=0, L=ceil(X^(1/2+eta)) for fixed 0<eta<1/2, take epsilon small with a epsilon<eta. The condition K R0=o(L) holds, and every such good bin has upward sources at p<=O(X^b (log X)^A), which cannot be supplied entirely by square-root-scale upward events. The number of required local bins is Omega(X^(1/2-eta)), and each needs Omega(log^2 X) distinct source primes. This is a conditional restriction on actual fast drops; the original crossing alternative does not force F>=rho X with these height and low-label hypotheses. Neither general high positive supply nor the large variation branch is excluded.

A possible next step is to bound the production of these scale-restricted sources in their actual height neighborhoods or derive a direct twin witness from their repeated visits. The main global obstruction remains: the previous crossing arguments have not forced small local guard widths, fast dominance, or small low-label gain. This theorem transfers demand to the intermediate scale instead of allowing it to be paid by unrelated very large jumps, but does not by itself eliminate that scale. No finite-twins contradiction or Lean kernel verification.

## 5. Diagnostics and preservation

[Audit cda75f3](https://github.com/tara-sooo/A166944-Lean/blob/cda75f31a31642975c497223fcff455730524b3f/research/min_direct_time_height_flux_audit.mjs), blob 6d03f5f788049f5dfc4813a5187ffe45530ae6c2. Exact remote readback. Run node research/min_direct_time_height_flux_audit.mjs 40000. Actual ECMAScript execution in tool runtime. 19998 odd canonical roots through40000,352451 actual events,0 unresolved cap180. 155912 finite block/selection controls with T9/17/31/61, local bins length 4T^2, fast subsets all or near the first ending height;197850 bin incidences,44750 nonempty guard bins,64746 selected fast incidences,4318 disconnected guard unions,7318 controls with multiple nonempty guards. 308460 positive localized source incidences (249619 low,46446 middle,12395 large with finite B=max(T,2M+1));26647 bins nonzero middle,10968 nonzero large. 1133656 exact flux bounds,44750 local telescoping and large-tail budget checks,155912 aggregate balances;45776 fixed-prime/side local progression checks,141060 rough residue checks,46446 source-height locality checks,44200 distinct (bin, middle source prime) incidences. 2000 independent synthetic overlap controls (not MIN trajectories). Example T9,L324,guard [176,192], M16,B33,F26,G320,low flux16,middle6 from label13,large16. Counts overlap over controls. Finite checks use B=2M+1 and finite local bins, not the optimized asymptotic delta or hypotheses (6); (1),(4),(7)-(8) and local-bin density conclusion are analytic deductions, not measured asymptotic constants. All assertions passed. No Lean executable/kernel verification, external novelty claim or final contradiction. Main and sibling branches unchanged.
