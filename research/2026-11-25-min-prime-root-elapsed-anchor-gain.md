# Elapsed-weighted anchors and long small-label excursion gain bounds

2026-11-25 JST. Continuation of 86f67c8e1a6de6a89e38a84434cefc58800281a2 on research/min-prime-root-repeat-energy-2026-11-25. Two new unconditional gain exclusions extend the recent-anchor support. First the anchor threshold depends jointly on gain distance and actual elapsed time, allowing some anchors beyond the fixed recent window and some smaller incoming primes. Second an amortized per-band bound pays short-wait jumps preceded by sufficiently long sub-band excursions, without any ancestor-mass or arithmetic condition. Both support measures transfer by the existing interval-cover and partner accounting. No bound for all intermediate-length small-label excursions or heavy groups, no twin-prime proof or Lean compilation.

## 1. Setup

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts M in [X,2X), Q=ceil(B/u). All original gain-stopped MIN paths, including terminal vertices, are unchanged. Every completed event at (t,C) has selected odd prime p<=B, gain p-1, actual wait 1<=w<=2r(C)<=3(p-1); every original state satisfies 2X-2<=C<=7X and 0<=t-C/2<=3H+3. Each source has total gain <H.

Use the previous eps=u^-1/64, m=max(1,floor(u^1/128)), theta=u^-1/512, q0(p)=min(Q,max(5,ceil(p u^(1-1/512)/log(2p)))), Jmax=max(1,floor(u^1/512)), J(p)=max(1,floor(min(Jmax,eps(p-1)))). A short-wait event has w<=eps(p-1). The previous supported measure counts its gain if an initial-near or a recent light eligible actual anchor of gain distance <=J(p) exists. Its total gain is O(NT ell/u^1/256)+O(N(Jmax+B)). This previous measure remains included; the additional marks below are disjoint from it and may be given priority in the order elapsed anchor then excursion. All measures count current actual event gain once, not the gain of its witness history. The original frozen medium quota and gap-adaptive phase and small-pool allocation from 8fd0a10 are unchanged.

## 2. Elapsed-weighted actual anchor

For a completed short-wait event p at (t,C), consider any noninitial original state (t0,D) on the same path, including the current input, entered by an actual selected q. Put
    e=C-D, l=t+w-t0, z=(e+1)^(3/2) l.
The new support test is
    0<=e<=p-4,
    q>=R(e,l):=max(5,ceil(z u^(33/16)/log(2+z))),
    g_q(t0,D)<=m,
where g_q is the full original incoming-label mass (including terminal tags). The support choice may be the most recent qualifying anchor. No condition that e<=J(p) or q>=q0(p) is needed. Actual l is a positive integer and l<=3e+eps(p-1)<=4p for sufficiently large X. This test can cover even a current heavy group by a light earlier anchor.

The same horizon and clock congruences of 86f67c8 apply:
    q|D+2s0, p|D+e+2s1-1,
    t0 = 0 or q+2 mod 2q according to s0=t0 mod2,
    t0+l = 0 or p+2 mod 2p according to s1=(t+w) mod2.
The primes are distinct because otherwise p divides the odd nonzero number e+2s1-1-2s0 whose absolute value is <p for p>=5 and even e<=p-4; p=3 admits no e. For fixed p,q,e,l,parities the anchor horizon is fixed mod pq and time mod 2pq. The actual state slab gives O(X/(pq)(1+H/(pq))) anchors, since pq<=B²=O(X). Each anchor has <=m original q tags and each such tag visits D+e at most once by strictly increasing horizons. No prescribed transcript, independence assumption or bound on the number of descendant tags arriving later is required.

Multiplying by p-1 and summing p, admissible e,l and q bounds the total new support gain by
    G_elapsed << m X sum_{p<=B} sum_{0<=e<=p-4, 1<=l<=4p}
                         sum_{R(e,l)<=q<=B} (1/q + H/(p q²)).       (1)
We may ignore the parity constraint on e, and omit q!=p in this positive upper sum after the distinct-prime count. The threshold provides the extra decay that pays for the longer bridge; there is no unweighted summation over all possible lag pairs.

For all allowed e,l, z=O(B^(5/2)), so log(2+z)=O(u). In particular u^(33/16)/log(2+z)>>u^(17/16), and R(e,l)>=z eventually. A nonempty q sum forces
    (e+1)^(3/2) l = z << B/u^(17/16).
The total number of such integer (e,l), even when independent of p, is O(B/u^(17/16)) by convergence of sum_{e>=0}(e+1)^(-3/2). The crude prime reciprocal sum is O(ell), and pi(B)=O(B/u). Thus the contribution to the sum in (1) from 1/q is
    O(B² ell/u^(33/16)).
For the other term, the elementary prime reciprocal-square tail bound gives
    sum_{q>=R} 1/q² << 1/(R log(2+R))
                       << 1/(z u^(33/16)),
since log(2+R)>=log(2+z). Use the convergent e sum, sum_{l<=4p}1/l=O(log(2p))<=O(u), and sum_{p<=B}1/p=O(ell). The H term in (1) is O(H ell/u^(17/16)). Consequently N~X/u, H~T~B²/u^.25 give
    G_elapsed << m X ell (B²/u^(33/16)+H/u^(17/16))
              = O(NT ell/u^(7/128))=o(NT).                        (2)
The two exponents after normalization by NH before m are respectively -13/16 and -1/16; the latter dominates. This is a sufficient explicit arithmetic condition, not a uniform increase of the old J(p) for all q and l. With q<=B it still restricts the admissible lag product severely. It can certify anchors outside J(p) in cases of small elapsed and/or larger q. Even at e=0, the threshold depends on the actual wait l=w and not directly on p, so it can be much smaller than q0(p) when the wait is sufficiently small relative to p. No claim of positive frequency in the limiting regime.

## 3. Absolute bound for long sub-band excursions

This is a separate deterministic estimate and does not use CRT. Here P is the dyadic band of the CURRENT SELECTED PRIME p (not the least-factor band of the sparse medium endpoints): P<=p<2P. Define a(P)=u^(1/16) log(2P). Let F_M(P,p) be the poststate horizon of the most recent preceding actual completed selection >=P on that root, or its initial horizon if none exists. For the current input C put g=C-F_M(P,p). All original selections in that gap are <P, regardless of their actual waits. Mark a short-wait event if
    g >= a(P)(p-1).                                             (3)
For this estimate it does not matter whether the current event has an elapsed or recent anchor, and in fact the gain bound holds also if one marks non-short-wait events satisfying (3).

For fixed P and root M, the preceding gain intervals [F_M(P,p),C) for distinct marked current events are disjoint. Each current event itself is a selection >=P, so the next such interval starts no earlier than its poststate. The preceding intervals can overlap between DIFFERENT P; do not assume disjointness across bands. The sum of their lengths within a band is <=H. Thus the total marked gain in band P over N roots is <=NH/a(P). Summing all nonempty dyadic P<=B,
    G_excursion <= NH u^-1/16 sum_P 1/log(2P)
                = O(NT ell/u^1/16)=o(NT).                         (4)
The marked gain may be assigned by priority to a subset of these events; the same upper bound still holds. The bound uses only the original gain budget. There is no assumption on group sizes, on actual trajectory lengths in steps or on the frequency of small p.

For any fixed delta>0, when p>=B^delta, q0(p)<=O_delta(p/u^1/512)<P eventually. If a residual short-wait p has no eligible recent anchor (whether light or heavy), let D_q be the poststate of its last preceding selection >=q0(p), or root if absent. If C-D_q >= a(P)(p-1), then the sub-P excursion is at least this long, since a preceding >=P selection is also >=q0(p). Such an event is marked by (3). Therefore any still unsupported short-wait p in this range, in the no-recent-eligible-anchor case, satisfies the bracket
    J(p)<C-D_q < a(P)(p-1).
This excludes excessively long small-label excursions but not the intervening scale range. Even without the no-recent-anchor case, every still unsupported short-wait p satisfies g<a(P)(p-1) and fails the elapsed-weighted test at every allowed anchor of original light mass. Do not use this bracket at p so small that q0(p)>P, or identify a sub-P run with a LOW run. This estimate is not a bound on the total gain of moderately long small-label excursions.

## 4. Transfer to the fast disjoint residual

Include both new gain measures in the previous supported measure, assigning priority to previous recent/initial tests, then elapsed-weighted anchors, then sub-P excursions. All measures are on full original completed events. Their union G_total still satisfies
    G_total <= O(NT ell/u^1/256)+O(N(Jmax+B))
                +O(NT ell/u^(7/128))+O(NT ell/u^1/16).
In particular G_total/theta=o(NT). The incremental new measures alone contribute at most
    O(NT ell/u^(27/512))
after division by theta=u^-1/512 (7/128-1/512=27/512). This is a bound on the newly marked gain measure divided by theta, NOT a claim that the newly covered quota cost relative to the old density threshold is bounded by just the new gain measure divided by theta: old support might have been arbitrarily close to theta h. Use the union bound for the actual expanded edge test.

In the upper medium least-factor band P_r>=Q/u^1/24, both original segments of a time-disjoint far pair have duration <=2h/u^1/32 and h>=p(E)-1 eventually. At most 2h/u^1/64 gain comes from non-short-wait events. As before mark every full sparse long quota edge whose segment is fast and whose enlarged supported gain in [C,E) is >=theta h. Greedy longest-first disjoint covering of the extended intervals [C,E+p(E)-1) gives union length <=6G_total(M)/theta. The distinct later hit gain intervals are disjoint in this union and the actual clock+LOW allocation at each later hit sums to its cost. Therefore the full allocated fast-supported quota cost is O(G_total/theta)=o(NT), with the dominant previous term O(NT ell/u^1/512). This remains valid if a witness excursion or anchor lies outside the repeat segment: only the current supported event gain within the segment is counted by the measure.

The original normalized small-pool allocation of 8fd0a10 is preserved. If either focal or partner sparse edge has the expanded support, pay its associated far-disjoint charge; summing the incoming charges at a supported partner within its full pool costs at most w_r/k_P=O(a_partner(E)/k_P), as in d8dea6f. Thus the total covered charge is o(NT). The new test includes the old test; disjoint incremental coverage is a subset of the proved total. No change to original trajectories, phase cells, or partner selection.

On BOTH original segments of a remaining upper-band far-disjoint pair, gain fraction at least 1-O(u^-1/64)-theta consists of short waits with all of these properties:
- not initial-near; no light qualifying recent q>=q0(p) anchor within J(p);
- no light elapsed-weighted anchor at any e<=p-4 satisfying q>=R(e,l);
- sub-P excursion gain less than u^1/16 log(2P)(p-1), using P of selected p.
In the no-recent-eligible-anchor case at p>=B^delta, the last eligible q has the additional bracket from section 3 (or the analogous root-to-current distance if absent). If a recent eligible anchor exists, all such anchors are heavy, as before.

The remaining medium clock sum (large physical formation, lower-band far, overlapping far, and upper-band disjoint with these strengthened restrictions) still needs o(NT). The previous high residual E_phys,admitbad+E_async,bad=o(T²Bu) is independent and OPEN. No proof of either full remaining bound, twin primes, or Lean formal verification. A next arithmetic target is the remaining intermediate-length subthreshold excursions; alternatively use actual prior slow gain to bound heavy anchor formation. The new unconditional exclusions do not prove that all fast disjoint segments are rare.

## 5. Audit

Standalone ECMAScript research/min_prime_root_elapsed_anchor_gain_audit.mjs, exact remote readback at 94e222a76d7bdec236a50eabd507a7a175f30f57, blob ca75b09e3eeb32ffdd44b2a5b441e1495eb838f9. Run:
    node research/min_prime_root_elapsed_anchor_gain_audit.mjs 256 1024 4096 16384 65536 262144
Executed its audit function in the available ECMAScript runtime, not a separate Node process. All 42 runs (seven modes x six X) passed. Inherited canonical SPF/literal parity-GCD, original LOW and sparse quota, gap and bilateral phase, physical transfer/potential and immediate-merger oracle, direct and recent anchor CRT, interval cover and normalized partner checks. New checks positive/zero elapsed-anchor offsets and actual time, q threshold and distinct primes, both congruences and CRT slab/progression, uniqueness of anchor tag and mass, per-observed-tuple capacity, exact gain sum, per-source per-selected-prime-band disjoint preceding excursion intervals and gain/length inequality, nested previous/new support and actual focal/partner costs. The analytic finite settings exercise both new gain measures, but still have no retained fast quota charges. Arithmetic support sum and asymptotic constants are proved in the note, not inferred from enumeration. No full growing source ladder or cumulative optional marks.

Analytic mode uses stated thresholds, finite y3,L6 as previous, Jmax1 at tested sizes. The new elapsed anchor test has nonzero offset even there. Diagnostic modes inherit 86f67c8 with eps and theta and earlier Jmax24 (relative J<=p-4); new threshold max(5,ceil(z/64)), excursion factor .25 log(2P), deliberately relaxed to exercise the accounting. In particular these diagnostic factors need not exceed one, and do not imply small gain in the limiting regime. Analytic old first-merger cutoffs still inherited; no analytic retained residual.

Largest X262144:
- Analytic: new elapsed gain952 on37 tags, 33 beyond old J, 4 with q below old q0(p) (may overlap); max gap2, max elapsed10, 37 observed tuple/anchor states,36 tuples. New excursion gain5442 on220 tags, preceding interval length28624 summed over bands, max preceding gap476. No new full fast quota edge; residual empty. This gives nonvacuous finite checks of the two new gain measures in the analytic parameter setting, not limiting evidence.
- Short: elapsed gain4440 on50 tags, all beyond old J; max gap68/max elapsed89; new excursion gain452882 on11454 tags, summed lengths885590. Extra297 full supported quota edges/cost3684, previous1833/cost23019. No incremental retained far-disjoint cost.
- Wide/phase/stress/broad: elapsed gain5236 on60 tags, all beyond old J, max gap68, max elapsed89, 13 observed tuple/anchor states in13 tuples; new excursion gain1216754 on21113 tags, summed lengths2647596, max gap4068. Phase/stress/broad extra1574 full quota edges/cost3787.3333, previous2043/cost5018. Broad retained disjoint previous paid8.1667, incremental0. Total broad residual7653.0703 unchanged; stress7478.2740 unchanged.
- Relaxed: elapsed gain5758 on69 tags, all beyond old J, max gap68/max elapsed112, 15 observed tuple/anchor states in15 tuples. New excursion gain1726024 on39090 tags, summed lengths3718032, max gap4068. Extra2877 full quota edges/cost6968.6667, previous5109/cost12553.3333. Prior disjoint payment133.4444, incremental0, unclassified4.3333; total residual7527.7925 unchanged. At X16384 relaxed new197 full supported quota edges/cost538.3333, incremental retained payment0, unsupported fast residual9.3333. No positive incremental retained far charge at the tested windows. This checkpoint strengthens the full quota sufficient criteria and gain support; it does not demonstrate an additional reduction of the final retained finite residual.

Main and other branches unchanged.
