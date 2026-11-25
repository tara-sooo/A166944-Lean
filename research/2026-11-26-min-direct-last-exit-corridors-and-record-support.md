# Last-exit recovery corridors, record-only support, and nonconcentration

Continuation of [5ca09ca](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-laminar-support-and-leaf-packing.md), on the independent direct-arithmetic branch. We construct actual contiguous low-label recovery blocks for almost all marks in the dense dyadic band of the existing sparse-window theorem. No assumption of rapid completion, decreasing trajectory throughout, or bounded number of intervening labels is needed. Across dyadic bands a three-color decomposition removes overlapping charges. Moreover only NEW RECORD LOW events within the extracted interval are needed for the deficit barrier obstruction. This forces both distinct recovery labels and a quantitative amount of recovery outside any adaptively chosen small set. Paper deductions and finite diagnostics; no Lean verification or novelty claim.

## 1. Last-exit corridor extraction

Use the actual adaptive MIN plateau states x=d+3, d=2t-H even and nonnegative. Event p has gain p-1, wait w>=1 and d'=d+2w-(p-1). For p>=5 post adjusted deficit d'-6I=2ph, h>=0; a reset has h=0, and nonreset x'>=2p+3. A decreasing nonreset has x/x'<3/2. A1 means p>=47, p>=5x, h=1, and implies x'>10x. Label3 never decreases ordinary deficit. A decreasing reset has pre x<=p+6, label>=7 on canonical rays, and distinct associated canonical visit within seven ticks before another such reset (at most one pending at a block boundary). These are the earlier branch identities, especially [level slabs](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-level-slab-recovery.md) and [far recovery](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-far-recovery-tail.md).

Consider a finite contiguous canonical event block with all pre-horizons >=6250001, label cap C, and cutoff R>=47. Fix a band [T,2T), T>=47, and mark any subset of A1 with p>R in this band; m_T is their count. Use the exact real thresholds
    L_T=2T/5, U_T=19T/10.
For a mark at event i, start just after it (x>2T). Its core ends at the first later plateau state x<=L_T, if it exists in the given block. Any next mark in this same band has pre x<=p/5<2T/5, so the cores have disjoint event intervals and at most one marked core is pending. Inside a completed core, take the LAST plateau state a with x_a>=U_T, and let b be the core endpoint. The corridor is the contiguous event interval [a,b). Every event in it satisfies
    x_pre>L_T, x_post<U_T.                            (1)
In particular no A1 of ANY size (marked or unmarked) can occur in the corridor: it would have x_post>10x_pre>4T. This is why the last-exit construction is stronger than treating the full core as a low-label run. There may be arbitrary upward excursions and other A1 before the extracted corridor. A reset p>=5 has x_post<=9<L_T and hence can occur only as the last event. Label3 may remain in the corridor, irrespective of its adjusted-deficit convention.

Any nonreset p>=5 in the corridor has p<U_T/2=.95T, since its post state is below U_T. If it decreases and is the first event then x_pre<(3/2)U_T=2.85T; if not first, x_pre<U_T. Label3 cannot be first because the first event decreases. Thus any nonreset p>R in the corridor satisfies
    R<p<.95T, .4T<x_pre<2.85T,                         (2)
and is B (the established A0/A1/B classification). It is FAR: by the earlier near-square lemma, any near label after the marked A1 of label p0 is >=.96 p0>=.96T at these pre-horizons. This contradicts (2). The numerical 6250001 threshold is inherited from the previous smoothed-cluster note, with its fixed near definition. For smaller pre-horizons one may instead count ALL nonreset B in the exception set. No approximation to the cutoff is involved.

Call a corridor good if it contains neither a reset p>=5 nor an event p>R. It consists entirely of labels<=R. It begins with a decreasing nonreset and ends with a decreasing nonreset. Every plateau in it satisfies
    (4/15)T < x < (57/20)T,
with x_a>=1.9T and x_b<=.4T, by the 3/2 decrease ratio at the first/last steps. Let Delta=d_a-d_b=x_a-x_b, g=H_b-H_a, W=t_b-t_a. Then
    Delta >= 1.5T,   g=Delta+2W >=1.5T.                (3)
The same drop/gain inequality holds for bad completed corridors. Good corridors lie in distinct maximal <=R runs for one band, because the intervening A1 is >R. No endpoint or time upper bound beyond the actual corridor is needed.

Charge a bad completed corridor to its reset if any; otherwise to one of its >R nonreset events. These are actual disjoint event charges within the band. Let Z_T count decreasing resets with pre x>.4T in the block, and B_{R,T} count far nonreset B with (2). If n_T is the number of good corridors, then
    n_T >= m_T-1-Z_T-B_{R,T}.                         (4)
In particular Z_T<=N+1 where N counts canonical visits, and B_{R,T}<=B_R (all far B with p>R). No near-event O(sqrt X) error is needed here; the nonreset near events are excluded inside the corridor itself. A far B with label>=.95T cannot serve as this exception. This is a direct population transfer from marks to contiguous blocks, not merely a bound on some assigned downward events.

## 2. Three-color cover and localized exceptional tail budgets

Fix integer T0>=47 and bands T=T0*2^j, 0<=j, T<=C. Use the above construction for all marks p>R with p>=T0. Two good corridors from bands with ratio>=8 cannot share an event, because for each good event .4T<x_pre<2.85T. Two such T values would require ratio <2.85/.4=7.125<8. Together with within-band disjointness this proves:
* every physical event is in at most THREE good corridors;
* partitioning the band indices j by j mod3 gives three collections of pairwise disjoint contiguous blocks (also disjoint half-open H intervals).
The same factor-three incidence bound applies to any nonreset high B chosen as an exception in section1, since (2) holds for that event even in a bad corridor. This resolves the varying-support overlap problem for these naturally occurring recovery intervals. It does not assert cores before the last exit are disjoint across all scales.

Write J=#bands with T<=C, G total block gain, M_bad count of pending or bad marks, W_bad=sum of their labels. For each decreasing reset q put
    b(q)=# {bands T<=C: .4T<q+6}.
Any reset can pay at most one charged mark per such band, since pre x<=q+6. The sum of charged mark labels for that reset is <10(q+6): each mark p<2T and the geometric sum of such T is <5(q+6). A high B of pre x can be charged at most three times and has total charged weight <=3C and <10x by the same geometric estimate. Pending marks have total weight <4C. Thus
    M_bad <= J + sum_{dec resets q} b(q) + 3 B_R,      (5)
    W_bad <= 4C + 10 sum_{dec resets q}(q+6)
                     + sum_{far B nonreset p>R} min(3C,10x_pre).  (6)
The sums may be restricted to actually charged events, which can make these much smaller than a uniform C times exception count. In particular the charge to nonreset B has no log number of bands multiplier; reset counts retain their true scale-dependent b(q). Summing good corridor gains gives <=3G.

For the previously established H-barrier mean-square theorem let P=P_R, ell=ceil(P^(4/11)), normalized moving-average variance sigma_ell^2 <= exp(-.001*pi_o(R)) for sufficiently large R (the previous [4/11 smoothing proof](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-smoothed-cluster-recovery.md) uses the same bound). The following argument applies to any ell<=P and actual variance. If T0>=8ell/3, (3) implies every good corridor has H/2 interval length >=2ell. These intervals contain no R-barrier. At least half of each interval's integer positions start length-ell windows wholly inside it, so the moving average is zero there. Within each color these starts are distinct, and the whole block has at most (G/2+P)*sigma_ell^2 zero starts by periodicity. Summing the three colors gives
    sum_good g <=12*(G/2+P)*sigma_ell^2,
    M_good <=8*(G/2+P)*sigma_ell^2/T0,
    W_good <=16*(G/2+P)*sigma_ell^2.                    (7)
Here p<2T<=(4/3)g. Combine with (5)-(6) for all marks p>=T0. For one band one can instead use 4, 8/3,16/3 as the respective constants, and replace T0 by T. The argument counts the zero-window starts in H, not in deficit coordinates where intervals can revisit the same values.

At the balanced cutoff P_R<=sqrt X maximal, in crossed [X,lambda X] with N,B_R=o(sqrt X), choose T0=ceil(8ell/3). Then J=O(log X), W_bad=o(X) using (6), W_good=o(X) by (7), and M_good=o(X^(9/11)/log X). M_bad=O((N+1)log X+B_R+log X)=o(X^(9/11)/log X) as well. This recovers the known exceptional tail conclusion with an explicit physical corridor explanation and localized exception counts. It does NOT improve the 4/11 Fourier exponent.

## 3. Record-only support: forced distinct high recovery labels

Within a good corridor [a,b), take running minima of d starting at d_a. At a strict new minimum event i, allocate only the newly reached deficit interval
    (d_{i+1}, min_{a<=j<=i} d_j],
of length r_i>0. Call these record decreases. Since x_b<=.4T and every earlier core state >.4T, the last state is a strict new minimum. The record intervals partition (d_b,d_a] exactly. Each record is an actual decreasing nonreset of label s>=5 (h>=1), and
    r_i <= d_i-d_{i+1} <= s-3.
There are at least Delta/(R-3) such events. This definition ignores nonrecord decreases, all increases and quiet ticks. Let F_rec be the DISTINCT prime support of record decreases, P_rec=prod_{s in F_rec}s. It is nonempty. Every downward deficit barrier for F_rec is impossible in (d_b,d_a], even if the other labels outside F_rec occur many times: a first downcross of any cut in that interval must be a record decrease.

Recall the local downward barrier residues of [deficit-barriers](https://github.com/tara-sooo/A166944-Lean/blob/5ca09caf2cea726e965efb593ea31889254ce78c/research/2026-11-26-min-direct-deficit-barriers.md): for odd s>=5, even cuts except residues 2,4,...,s-3 and 8,10,...,s+3 modulo 2s are barriers; for s=3 every even cut is a barrier. For any finite odd-prime support F with product P_F>=5, both 2nP_F and (2n+1)P_F+5 are barriers. Indeed odd multiples of P_F are s mod2s, and s+5 is allowed for s>=5 (also s3 trivially). Their maximum successive gap is P_F+5 (at P_F=5 the two families coincide). Thus
    Delta < P_rec+5,    P_rec>1.5T-5.                 (8)
This is stronger than applying a horizon support product to ALL selected labels, as it forces the actual decreasing record population to have large product even in the presence of arbitrary relays. Separately the whole corridor support F_all has g<2P_all from the horizon barrier. The record-only product need not bound horizon gain, and we do not claim g<2P_rec.

For any S<R put P_S=prod odd primes<=S, j_rec=# distinct record labels >S. Since all corridor labels <=R,
    P_S R^j_rec >= P_rec >1.5T-5.                    (9)
Consequently j_rec is at least max(0,1+floor(log((1.5T-5)/P_S)/log R)). Strict inequality is important when the logarithm is integral. This has no elapsed-time or event-count budget. On polynomial mark scales T=X^a (or T=X^(a+o(1))), R~rho log X, S~b0 log X, 0<b0<min(a,rho), PNT gives
    j_rec >= (a-b0+o(1))*log X/loglog X.              (10)
All those labels are genuine ordinary-decreasing far B once S>=47. Every record post x>(4/15)T, so its multiplier h satisfies
    2s h = x_post-6I-3 > (4/15)T-9.
In particular h diverges uniformly when T/R tends to infinity. Also a fixed record label s can occur at most 2(1+floor(Delta/(2s))) times in the corridor, since its post deficits are strictly decreasing and on each side lie in one lattice 6I+2s*h. This local bound is not an upper count across different corridors.

## 4. Arbitrary-support quantitative nonconcentration

For ANY finite set F of odd primes (possibly selected after observing the corridor, e.g. top record-drop contributors), define P_F as above (empty product1), a_s=3 for s3,5,7, and a_s=(s-3)/2 for s>=11. Put A_F=prod a_s, theta_F=A_F/P_F. CRT in d/2 counts A_F downward barriers per period P_F. The record intervals partition (d_b,d_a], and every F-barrier in it must be paid by a record whose label is OUTSIDE F. Let D_out be the sum of record-drop lengths r_i from those outside labels, not all ordinary drops (which could overlap after an upward excursion). The exact lower bound is
    D_out >= 2 * # {F-barriers in (d_b,d_a]}
          >= 2 A_F floor(Delta/(2P_F))
          >= theta_F*(Delta-2P_F).                   (11)
The first inequality uses at most r_i/2 even cuts in a record interval; the second counts complete periods in the contiguous cut list. The corresponding outside-event gain is >=D_out, and their number is >=D_out/(R-3). This is a deterministic local bound for arbitrary support and no defect multiplier independence. It does not use the horizon laminar-repeat forest. The lower bound is trivial if the interval is shorter than a full period, though the half-period argument (8) still forces some outside label for smaller supports.

For |F|<=k and F contained in primes<=R, P_F<=R^k and theta_F>=4^(-k) (indeed all local densities>=4/11). If R^k=o(T), (3),(11) imply for EVERY such choice
    D_out >= (1.5-o(1))*4^(-k)*T.                    (12)
For fixed k this is a positive fraction of the recovery scale outside any k labels, including the k largest actual contributors. Therefore the recovery cannot have essentially all of its record decrease on a bounded support at polynomial mark scales. More generally choose F={odd primes<=S} union J, where J consists of any k labels in (S,R]. Then P_F<=P_S R^k and theta_F>=4^(-k)*theta_S. If P_S R^k=o(T),
    D_out >= (1.5-o(1))*theta_S*4^(-k)*T.             (13)
All outside records have label>S and are not among the chosen k. This says more than merely requiring some high-multiplier occurrences or a distinct-label count: the required recovery amount itself cannot concentrate on those labels. For S~b0 log X, T=X^a, k~theta log X/loglog X with b0+theta<a, the right side is T*X^(-o(1)). Constants in the finite inequalities are independent of the adaptive choice of F. For all good corridors in one band these outside-gain charges are disjoint; over all bands they can be added separately within the three colors. Neither (12) nor (13) is a uniform positive fraction of the ENTIRE macroscopic horizon gain when the good marks themselves carry sublinear weight.

One may also apply the previous laminar leaf packing (13) of 5ca09ca to these actual disjoint blocks. In one band choose any distinguished F_i of at most k primes in [S0,C0*S0] contained in [3,R], with fixed C0>1. Let B_tot be total gain on other labels in the good corridors, K_tot distinguished event count, Q=2^k-1, U0>=0 the small-leaf threshold and U0^+=2(floor(U0/2)+1). Write A_k(G,S0,U0) for the prior bound (10), valid for S0>=5,U0<S0-1. The number of nonempty distinguished blocks is <=n_T. Since sum corridor gains>=1.5T*n_T and each distinguished gain<=R-1,
    B_tot >= max(0, [1.5T*n_T-(R-1)*Q*(n_T+A_k)]
                         /[1+(R-1)*Q/U0^+]).         (14)
This supplies a genuine unconditional inequality on the extracted good population, with support chosen independently for each corridor. For all bands use the three colors. The direct record barrier (11) is often stronger at T>>R^k; the previous leaf packing can be nontrivial at smaller comparable scales or for other repeat-rich blocks. The previous no-outsider fixed-k cover cannot cover entire polynomial-scale good corridors because (8) already forces unbounded record support.

## 5. Matching to the previously necessary A1 population

Use the existing balanced cutoff P_R<=sqrt X, crossed window [X,lambda X], and assume N=o(sqrt X), B_R=o(sqrt X) along a sequence. Prior 4/11 smoothing and far-gain recovery give m_f=Omega(X^(9/11)) far A1 with p>R. Pigeonhole over dyadic bands starting T0=R+1 to obtain a band with m_T=Omega(X^(9/11)/log X) such marks, as in the smoothed-cluster note. By (4),
    n_T >= m_T-(N+2+B_R) = (1-o(1))*m_T.              (15)
Thus almost every mark in that band has an actual contiguous good corridor, with every label<=R, bounded deficits comparable to T, total gain and record drop >=1.5T, and record-only support product >1.5T-5. This conclusion did NOT follow from the earlier rapid-recovery/discovery conditions. It addresses the missing construction of disjoint recovery blocks; the support of the whole block is not assumed bounded. The time and event count of each corridor can be large. By (7) and the sparse hypothesis, a band carrying this many marks cannot have T>=8ell/3 (ell=ceil(P_R^(4/11))); the previous tail results are consistent. If T is polynomial in X, (10),(13) provide many distinct, high-multiplier record decreases and substantial outside-record gain in each such corridor. If T=O(log X), no growing distinct-label bound is supplied by (9). The prior log-scale two-label examples concerned recovery only to x<=p and are not counterexamples to the present longer corridor requirement.

Remaining mathematical target: bound the supply of these bounded-deficit low-label corridors or their record minima on ONE trajectory, not just over all roots. In particular the new extraction does not force polylogarithmic time or the small new-wait budget of event-index packing; when T is polynomial there are already Omega(T/R) record events, so that hypothesis would be inappropriate. Need quantitative restrictions on variable-support/high-multiplier record histories, including log-size bands, or a method to eliminate the nonsparse N or B_R alternatives. Neither sparse condition follows from finite twins. No contradiction yet.

## 6. Diagnostics and preservation

[Final corridor audit 1a6984d](https://github.com/tara-sooo/A166944-Lean/blob/1a6984d6f1d9945f974403dcfd0fe58f8cdd3bdd/research/min_direct_last_exit_corridor_audit.mjs), blob 60db41005201beba822dbb85e7da37deb1d42cea. Exact remote readback. Run node research/min_direct_last_exit_corridor_audit.mjs 60000. Actual ECMAScript in tool runtime (not separate Node). 29998 odd canonical roots through60000,549085 events, no unresolved cap180; also reconstructed earlier9962-digit witness word7687/5233/3541/2389/1621/1093/733/7369,22195 literal BigInt GCD ticks,20600 stage residue checks. Four separately classified timed relaxed controls (selected clocks and eligibility, not first-hit competition). 11260 band controls,11357 marks (overlapping cutoff controls),831 completed cores,10526 pending,35 good corridors (9 actual incl witness controls,26 relaxed),723 reset charges,73 high-B charges;284 near-exclusion checks,1311 corridor event incidences,1648215 overlap checks. 35 record-product checks,177 record events/multiplier checks,175 distinct support forcing checks;210 arbitrary-support record barrier tests,732006 exact cut incidences,70 positive nonempty-support period lower bounds. All passed. In this main scan maximum good overlap was one and same-color adjacency test count was zero; the separate controls below ensure the overlap issue is real. Good witness at R5233,T6016: p7687, corridor labels5233/3541/2389/1621/1093, x15377->2189, gain13872,342 ticks, drop13188,5 distinct record labels. Same word with R47 gives a high-B exception. This witness is a previously constructed root, not a newly discovered one. The small finite scan does not estimate any asymptotic population.

[Overlapping corridor controls 6fa6015](https://github.com/tara-sooo/A166944-Lean/blob/6fa601556aa43af535e269c2f6879429c3d65ed2/research/min_direct_overlapping_corridor_controls.mjs), blob 0360103b60e37c537f5be75ea6b03c887deecf9c, exact remote readback. Run node research/min_direct_overlapping_corridor_controls.mjs. Four constructed timed relaxed paths on distinct prime labels, CRT fixes actual even starting H and the designated selected clocks, all adaptive eligibility checks pass (64 events). At p/q=2551/9461,3391/12553,8431/31237,12007/44449 two good corridors at T=p,2p each contain five events and overlap on three, root sizes52/54/60/63 decimal digits. E.g. first control corridors [11,16) and [9,14) in event coordinates. These are NOT asserted actual adaptive MIN trajectories: competing earlier hits are not excluded. They test the necessity of handling overlap in the relaxed arithmetic setting.

The audit was extended in commits 54c3780 and 1a6984d after record-only and nonconcentration deductions, rerun completely, all assertions passed. No Lean executable available, no kernel verification, no new Fourier exponent, no finite-twin contradiction or external novelty claim. Main and sibling branches not modified by this work.
