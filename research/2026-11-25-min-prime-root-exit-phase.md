# MIN exit phases: lag rounding, immediate synchronization and close-time absorption

2026-11-25 JST. Continuation of b8fea4846ebb14434fe77d8e7f6931317856a939 on research/min-prime-root-repeat-energy-2026-11-25. Uses the cubic-log least-factor support f8d81fc and the full original MIN dynamics to analyze asynchronous shared high horizons, including both young and old frozen band-chain hits. Gives a new linear-cost exit-group core, an absolute close-time pair-energy deletion and a relative energy absorption of imbalanced exit groups. Time lag is NOT monotonically decreasing; explicit actual examples below. No bound on all recurrent births, all physical-suffix energy, or the medium moment. Paper deductions and finite audits, no Lean compilation or novelty assertion.

## 1. Exact lag update at one common projected horizon

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^(1/4)), N=Theta(X/u) prime starts in [X,2X). Original gain-stopped prefixes include final vertices, each gain G_M<T+B. At even C, odd prime p<=B is eligible if p divides C-1 or C+1; the two cases are disjoint. Its admissible times are 0 mod 2p in the first case and p+2 mod 2p in the second. The next event is the lexicographic minimum (s,p) with s>t, over all eligible primes. For an actual selection wait 1<=s-t<=2r(C), r the least eligible prime. The next physical vertex is (s,C+p-1).

At a common C with actual next events from both t<=t', let their selected times be s,s', primes p,p', input lag d=t'-t, output lag d'=s'-s. The next-event time is monotone in input t, since the admissible future tick set shrinks. Thus d'>=0, and
    |d'-d|<2r(C).                                     (1)
If s=s', the same lexicographically minimal eligible prime is chosen, so p=p' and the trajectories physically synchronize at their next vertex. If t<t' and s>t', the earlier next tick is also available to the later path and they necessarily synchronize at that event. In particular asynchronous distinct exits require s<=t'.

If p=p', then both selected ticks are the first ticks of the SAME periodic progression after their respective input times. Hence
    d' in {2p floor(d/(2p)), 2p ceil(d/(2p))}.          (2)
This includes d'=0. If d is a multiple of 2p it is unchanged. If d<2p, the only possibilities are zero or 2p. Equations (1)-(2) are valid for two actual MIN events even if one or both outgoing events are not retained. They do not imply nonexpansiveness of d. A shared horizon with different outgoing labels need not have a common next projected horizon, so one cannot iterate (2) through intervening different histories without proving additional control.

Actual counterexamples at X262144 on original prime-root paths:
- M=262151,M'=262153, C=524304, p=5. Input times 262158,262155, output 262167,262157: lag 3 becomes 10 (both remain distinct).
- M=262151,M'=262187, C=524398, p=3. Input times 262207,262217, output 262212,262218: lag 10 becomes 6.
- Same latter roots at C=524394,p=5: input 262200,262210, output 262207,262217, lag 10 unchanged.
These are full-event examples, not counterexamples to a specialized high-band contraction conjecture; no general contraction of high-band lag is asserted.

## 2. Exit groups, a new linear-cost core

Freeze natural high I as in b8fea48: p>=Q=ceil(B/u), r(C)>p/sqrt(log p). Write H={even C in [2X-2,7X]: B/u^(3/2)<=r(C)<=B}. Every I incidence has C in H. By f8d81fc,
    |H| << X(1+ell)/u³, S_* << XB/u³.
All prime factors of each odd C±1 are at least r (factors>B also satisfy this); for large X, r³>7X+1. Hence C-1 and C+1 each have at most two prime factors with multiplicity, and there are at most FOUR distinct eligible odd primes in total. This is a pointwise fact at H, independent of the selected label or the distribution of roots.

For ANY retained subset J of I, at each C partition its original tags by actual next event key (s,p). Denote a group's mass a(C;s,p). The key determines a unique actual next physical state (s,C+p-1). There cannot be two different selected labels at the same s and C, by the fixed MIN tie rule. All roots in a group share the next physical state but need not share the current time or have identical past histories.

The elapsed time bound t-(M+2)<=3G_so_far and initial C0=2M-2 yield 0<=2t-C<=6+5(T+B). Since s-t<=2B, possible s lie in a common interval of length O(T) at fixed C (T>>B). For each eligible p they belong to one progression of spacing 2p. Thus the number of possible nonempty exit groups at C is O(1+T/r)=O(T/r), using the four-prime bound.

Delete all occupied exit groups of mass <=m, with
    m=max(1,floor(u^(7/4)/(1+ell))).
The linear clock cost satisfies
    R_exit,thin << m T |H|
                << X T/u^(5/4) = O(NT/u^(1/4))=o(NT).
This also applies to a subset of an already thinned incidence set. As in fdec6e9, if the earlier source-cell and frozen-lag thickness conditions are desired simultaneously, include this exit partition as one additional family in the joint peel at each C. Every initial exit group disappears at most once and has <=m tags at deletion, so its total charge has the same bound even with cascades. Whole-horizon dispersion and mass gates are then applied last. This preserves the new exit thickness and earlier thickness conditions on the surviving central horizons. Extra LOW attachment O(LNT/Q)=o(NT) follows from the count of high incidences. No claim that the deleted quadratic energy is negligible. The independent audit below isolates exit thinning only.

## 3. Asynchronous same-exit energy is negligible, including old chain hits

At any retained C consider distinct roots with different current times but the SAME exit key. They physically synchronize at the next vertex (which exists in both original prefixes even if it is terminal). This is their FIRST common physical vertex: had they already shared one, all subsequent original vertices until either cutoff would coincide. A fixed root pair can be charged at most once, across all C, bands and ages. The candidate pair bound P_*=O(NT/u) of b8fea48 applies because both roots visit the current high horizon.

Consequently the whole CURRENT ordered overlap energy of all these asynchronous same-exit hits is at most
    E_immediate <= 2B P_* = O(F/u^(11/4))=o(F),
where F=T² B u. This is stronger than a birth-only exclusion: even a very old shared band chain can have one such last asynchronous hit and it is included. It does not exclude the common physical suffix's future energy. No assumption on the incoming times, ancestry masses, labels of preceding hits or first projected contact is needed.

## 4. Arithmetic count of close DISTINCT exits

For two different exit groups at one C, both output times differ. Let D>=1 and count unordered pairs of arithmetic exit keys at a common C in H, with 0<|s-s'|<=D and both outgoing primes >=Q. Ignore actual occurrence and multiplicity for this arithmetic upper bound. Both output times lie in the O(T) strip of section 2. We will take D=floor(4B).

Different labels p!=q: for fixed p,q and two divisibility sides, p|C±1, q|C±1 constrain C by CRT to one class mod pq. Since pq<=B²=Theta(X), there are O(X/(pq)) candidate C in the full interval, with the additive one absorbed. For fixed signed time difference h (1<=|h|<=D), output clock congruences constrain s modulo lcm(2p,2q)=2pq or are incompatible. Thus the number of s in the strip at each C is O(1+T/(pq)). Summing both signs, sides, and p,q>=Q gives the envelope
    K_dist(D) << X (D+1) [(sum_{p>=Q} 1/p)^2
                            + T (sum_{p>=Q} 1/p²)^2]
              << X(D+1)/u^(1/4).                    (3)
All prime sums have upper limit B. Here sum 1/p=O((1+ell)/u), sum 1/p²=O(1/(Q log Q))=O(1/B), and T/B²=O(u^-1/4). Counting incompatible or tied output events as candidates only overcounts; no independent distribution of C and s is assumed.

Same label p: the signs at fixed C must coincide, and s,s' are distinct ticks of one progression. The number of horizons C in H where p is eligible is
    O(X/(p u²)).
Indeed fix the side and write C=p(2n+1)-sigma, with O(X/p+1) consecutive n; both C±1 avoid odd primes <=z=floor(B^(1/16)), z<p and z<r(C). Use the uniform two-form Selberg bound of 32d4185, with error z^6<=B^(3/8) absorbed by X/(p u²), and sum both signs. For each such C there are O(1+T/p) choices of one tick and O(D/p) of its distinct neighbor (the integer floor is zero if D<2p). Therefore
    K_same(D) << (XD/u²)[sum_{p>=Q}1/p² + T sum_{p>=Q}1/p³]
              << XD/u^(5/4).                        (4)
The last step uses sum 1/p³=O(1/(Q² log Q)) and T/(Q² log Q)=O(u^.75). Both envelopes count key pairs including their horizon and times, not just pairs of selected labels or root pairs. Unlike the old projected-anchor bound, these are outgoing keys at the SAME current horizon.

## 5. Absolute capped energy and relative imbalance absorption

Fix D=floor(4B). Let a,b be the actual two retained group masses at a close distinct exit pair, and define caps
    c_dist = X sqrt(u)/(D+1),
    c_same = X u^(3/2)/(D+1).
For differing labels use c_dist, for the same label use c_same. The entire CURRENT ordered energy of those key pairs with ab<=their cap is <=2B times the sum of the capped products. By (3)-(4),
    E_close,capped << X² B u^(1/4) = O(F/u^(1/4))=o(F). (5)
In particular these caps are order B sqrt(u) and B u^1.5, respectively, with D~B. They permit both group masses of polynomial size in B. They require an actual product bound; none is asserted for every key. There is no factor for the age of a shared band chain or number of earlier births, because (5) bounds current overlap directly over all horizons.

At fixed C construct a graph of nonempty exit keys with edges when their output times differ by at most D. Each eligible label provides at most O(1+D/p) ticks in the window of width 2D about a given tick. With at most four eligible primes and p>=Q, the maximum degree is
    Delta = O(1+D/Q)=O(u).
Take I_bal=u². If min(a,b) I_bal<=max(a,b), then 2ab<=2 max(a,b)²/I_bal. Charge to the larger endpoint. The total ordered energy of ALL such imbalanced edges at every C is bounded by
    E_imb <= (2 Delta/I_bal) sum_C r(C) sum_exit a²
          <= O(E_J/u),                               (6)
because sum_exit a²<=W_J(C)². In particular no bound on total E_J has been assumed. This is an absorbable error, not an independent o(F) estimate. It remains valid if we count only the edges not already covered by (5), or restrict the pairs in an edge to any subset; use full J masses to define the tests.

Define E_rest to include the ordered current energy of:
1. pairs already physically synchronous at the current C;
2. asynchronous pairs with close distinct exits that exceed their cap AND satisfy min(a,b) u²>max(a,b);
3. asynchronous pairs with |s-s'|>D.
All prior proved whole-pair or frozen young-chain exclusions can also be removed from E_rest, by their own absolute bounds. Then the disjoint decomposition, diagonal O(NT)=o(F), sections 3,5 and (6) give
    E_J <= E_rest + o(F) + O(E_J/u),
    E_J <= (1+O(1/u)) E_rest + o(F).                  (7)
This is a valid sufficient reduction even if E_J/F is unbounded, by moving the relative term to the left. It is not equality up to o(F) without an independent bound on E_J.

By (1), any asynchronous current pair with d<=2B must have d'<4B (or zero). Thus after these exclusions the far-exit class necessarily has input lag >2B. The close remaining class has large, relatively balanced physical exit group masses. This narrows the asynchronous part of both the young and old frozen chain criteria, but the already-synchronous class can still dominate. No upper bound on the number of recurrent asynchronous births, no contraction of all time lags and no control of the synchronous suffix energy follows from (7).

## 6. Hybrid implication

Take previous whole-root and linear accounting marks, optionally joint peel including exit groups, then the final whole-horizon gates. Apply the earlier pair/young-chain exclusions and (7) to the actual final J. If E_rest=o(F), then E_J=o(F), and the unchanged joint medium condition Z_m=O(N B u³) implies R=o(NT) by f8d81fc and the gain-prefix contradiction. Equivalently retain the recurrent/old split within E_rest using the frozen I ages. Neither the synchronous contribution nor all balanced large close-time edges or far-time edges have been bounded. The remaining medium condition is also OPEN. Main and other branches unchanged.

## 7. Reproducible audit

Standalone ECMAScript research/min_prime_root_exit_phase_audit.mjs, exact remote readback at e5f6814f0691d8dcad4ecab700a66e7f16860b53, blob c788113ea36ff2dccfac779ae6d5d6ee5ac49094. Run:
    node research/min_prime_root_exit_phase_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node invocation. All 18 runs (three modes x six windows) passed. Exact original SPF MIN paths and independent literal parity-GCD comparisons on smallest two windows (short1183, wide1707, analytic1719). Full shared-horizon pair sweep verifies monotonic next times, strict lag variation, exact same-label rounding, lex tie uniqueness, unique immediate synchronization, physical common suffix; includes terminal vertices in synchronization checks. At actual high horizons verifies four-prime bound whenever r³>C+1, exact exit group counts versus progression envelope, exit group thinning and energy decomposition, close graph degree and same-label period/distinct-label congruences, capped products and imbalance bound. Independently recomputes total E from horizon squares. The code checks finite arithmetic memberships and progression counts, not the asymptotic sums (3)-(4) themselves. It does not apply all earlier accounting deletions, joint peeling or frozen band age classification, so finite ledgers are independent diagnostics.

Modes: analytic T=X/u^.25,Q=B/u, relative r>p/sqrt(log p), D=4B, m=floor(u^1.75/(1+ell)) min1, I_bal=u², analytic caps. Wide T=4B,Q7,r>p/2,D4B,m1,I_bal3,c_dist=c_same16. Short T=B,Q=ceil(B/8) min5,r>p/2,D=floor(B/4), same diagnostic m,I_bal,caps. Wide at finite B can have >4 eligible primes (the four-prime condition is conditional on r³>C+1, not imposed on this diagnostic).

At largest X262144, B1355,N20390, wide T5420: 612685 events,633075 vertices, high I224748 tags, R_I14658404,E_I311130640. 5,563,458 actual common pre-event pair checks, 5,114,586 same-label rounding checks. Among positive input and output same-label lags, increases670296, decreases564548, unchanged223723 (all labels and shared full events, not just high). 114069 distinct pairs have a first physical synchronization at the next vertex after a shared pre-horizon with distinct times, of which97826 retained high pair hits after thinning. 55648 exit groups over35125 occupied high horizons, remove24198 singleton tags of cost844382. Retained E305116786. Close same-label edges10364 (4635 capped), distinct-label1624 (757 capped), graph max degree6. 4348 imbalanced edges before cap priority. All 685623 retained asynchronous pair hits with input lag<=D-2B satisfy d'<=D. Far class empty in wide diagnostic, not an asymptotic estimate.

| X262144 wide retained high energy | Value |
|--|--:|
| diagonal |13814022|
| already physically synchronous |174040038|
| immediate synchronization |50449876|
| close same-label capped |2283828|
| close distinct-label capped |427340|
| close imbalance (after cap priority) |26614062|
| close balanced above cap |37487620|
| far |0|
| total |305116786|

Short largest: 17772 high input tags, thin1056, E87599870->86203406; immediate28579374, distinct capped45602, imbalance225142, balanced369240, far9252820; close same-label edges zero by D<2Q. Analytic largest: high I23150 tags, thin9731 (m10), E218152748->175232493; immediate39634800, same-label capped11436744, distinct capped0, close balanced7433422, far0, synchronous110944856. Analytic finite all roots terminate before T; no limiting inference from removal fractions. In particular (6) is a relative bound and finite I_bal=3 does not imply a small contraction coefficient in wide mode. No Lean compilation.
