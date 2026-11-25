# Scale-resolved recovery: injective level matching and label-weighted slab allocation

Continuation of [9ee544b](https://github.com/tara-sooo/A166944-Lean/commit/9ee544bd1ef5eecc3a0aee9becbae0b2a71e1e0f). Rather than estimating only the total ordinary-deficit decrease, this note assigns subsequent recovery events (and disjoint portions of their actual decrease) to individual A1 events. The scale of each matched label is controlled. Under the existing root-sparse/high-B-sparse hypothesis, almost every large A1 requires low-label ordinary recovery proportional to its OWN prime, not merely to the common threshold R. No twin-prime contradiction or Lean kernel verification.

## 1. Two elementary crossing facts

Use adaptive MIN: ordinary pre/post deficits d,d', gain g=p-1, wait w>=1, side indicator I=0 even/1 odd, adjusted D=d'-6I. Write x=d+3 and x'=d'+3. A1 means p>=47, p>=5d+15, D=2p. Then
    x<=p/5, x'>2p.
At a decreasing nonreset with label s, s>=5 (3 never decreases), D=2hs for some integer h>=1, x'=2hs+6I+3>=2s+3, and
    x/x' < 3/2.
Indeed d-d'<=s-3 and x'>2s, so x/x'<=1+(s-3)/x'<3/2. At a decreasing reset q the prior result gives q>=7, x<=q+6, and a distinct canonical reentry in <=7 ticks before the next p>=7 event (or terminal normalization for the last finite prefix). Thus in a finite contiguous canonical event block, if N counts actual canonical visits in (start,end], there are at most N+1 decreasing resets. All statements concern the sequence of event-plateau states; ordinary d increases between nonunit events, so downward crossings of d cannot occur at unit ticks.

Let C=floor sqrt(Y+1) when pre-horizons in the block are <=Y. Fix R>=47 and mark any subset of A1 with labels p>R, count m (usually all). If m=0 all budgets are trivial. We use geometric levels only up to 2C, and count their number by L. Boundary convention for crossing up is x<y<=x'; down is x'<y<=x. This convention ensures alternating crossings at each fixed level, including exact equalities.

## 2. Injective recovery-event matching

Put beta=3/2 and choose any phase a in [1,beta). Use levels
    y_j=(R/5)*a*beta^j, j>=0, y_j<=2C.
Each mark p has either five or six levels in (p/5,2p], since the logarithmic interval length is log_beta(10)=5.67887... . All these levels are crossed upward at the marked event. Order them by rank k from smallest to largest. The rank-k level obeys
    beta^(k-1)*p/5 < y <= beta^k*p/5.
At each level assign every marked upward crossing to the FIRST subsequent downward crossing of the same level, if it exists in the block. Distinct marked crossings at the same level have distinct assigned downward crossings, by alternation; each assignment is to a later event. A nonreset downward crossing can cross at most one level, by x/x'<beta, so these assignments are globally injective across all levels when restricted to nonreset events. Remove assignments to decreasing resets and those still pending at the block endpoint. There are at most (N+1)L reset assignments and at most L pending assignments, for a total
    E=(N+2)L,
    L<=1+log_beta(10C/R).
In particular at most E marked events lack a full set of assigned nonreset recovery events. Any complete mark has at least five distinct assigned events; their chronological order is from the largest crossed level to the smallest. This follows because x is above every assigned level immediately after the mark; to get below the lowest it must first get below each higher level, possibly at the same event only in a reset. For complete marks all assignments are distinct.

For the assigned rank-k recovery label s and its post x', we have
    s < y/2 <= beta^k*p/10,
    y/beta < x' < y.
The first inequality follows from x'>=2s+3, and the lower bound from x>=y and x/x'<beta. Thus for the first five slots the successive upper bounds on s/p are
    0.15, 0.225, 0.3375, 0.50625, 0.759375.
Every assigned event, including a possible sixth slot, has s<p, since y<=2p. Moreover
    hs > beta^(k-2)*p/10 - 9/2
by x'=2hs+6I+3>y/beta. A tiny recovery label therefore requires a large adjusted-deficit multiplier. These bounds do not imply the five or six recovery events are adjacent.

The same matching gives simultaneous cumulative constraints: for any U>R let m(R,U) be the count of marked labels <=U, and D(V) the count of all actual ordinary-decreasing nonresets in the block with label s<V. For k=1,...,5,
    D(beta^k U/10) >= k*m(R,U)-E.                  (1)
Because the assignment is injective, (1) concerns occurrences on a single trajectory, not merely the number of distinct prime labels. It is a transport bound from A1 occurrences to strictly smaller recovery labels.

A phase can be chosen so that the total number of slots is at least m*log_beta(10). Indeed take log_beta(a) uniform in [0,1); the expected number of grid levels in each logarithmic interval of length log_beta(10) is exactly that length. No probability model on the trajectory is used. Since each mark has five or six slots, at least (log_beta(10)-5)m marks have six slots for some phase. After removing the E exceptions, at least m-E marks have all five mandatory slots, and at least (log_beta(10)-5)m-E have all six when using that phase. Total assigned ordinary-decreasing events >=m log_beta(10)-E, with all labels strictly below their own matched A1. This is stronger in localization than the previous aggregate logarithmic count.

## 3. Slab allocation: weighted actual decreases per mark

The preceding point matching does not control how much ordinary deficit decreases at each assigned event. To allocate actual lengths, now choose any real 1<beta<=3/2 and use levels y_j=(R/5)*beta^j, 0<=j, y_j<=2C. The elementary number bound L<=1+log_beta(10C/R) still holds. A slab is an interval [y_j,y_(j+1)] between consecutive levels; endpoints have zero length and can be shared. For every marked p, select every complete slab with
    p/5 < y_j < y_(j+1) <= 2p.
The selected slabs are consecutive, their union has length at least
    c_beta*p, c_beta=2/beta-beta/5 >0.              (2)
Indeed the first level strictly above p/5 is <=beta*p/5, and the last at most2p is >=2p/beta. This also proves existence of at least one complete slab. The mark moves from below every selected slab to above it.

For each mark and selected slab [a,b], follow the trajectory from immediately after the mark to the first later state x<=a, or to the block endpoint if no such state occurs. For every downward event x->x' during this recovery interval assign the length
    length([x',x] intersect [a,b])
to the mark/slab. The sum assigned to a completed slab is at least b-a: use the clamped linear function min(b,max(a,x)); it starts at b, ends at a, and its positive decreases must pay its net fall. (Positive increases can make the sum larger.) For a given slab, the recovery intervals of distinct marks are disjoint: a later mark crossing that whole slab begins below a, which requires the earlier interval to have ended. Consequently at any event at most one mark owns a slab, and the distinct slabs have disjoint interiors. The total length assigned from an event across all marks/slabs is <=d-d'. This is a deterministic capacity statement even when different recovery intervals overlap in time at different scales.

Fix an optional recovery-label cap V>=5. Call a mark bad if any of its slabs is incomplete, or any positive length assigned to it comes from a reset, or any assigned nonreset decrease has label s>V. Without a cap omit the last condition. Every other mark is good. An incomplete slab can spoil at most one mark per slab at the endpoint; a decreasing reset can spoil at most L marks. A decreasing nonreset intersects at most kappa=ceil(log_beta(3/2))+2 slab interiors because its logarithmic decrease is <log(3/2). It can thus spoil at most kappa marks. Write H_V for the number of ordinary-decreasing nonresets with s>V in the full block (zero if no cap). Then
    #bad <= (N+2)L+kappa*H_V.                     (3)
We can even replace H_V by the number actually intersecting an active marked slab, but use the simpler upper bound.

For any subset of good marks, all assigned positive lengths come from ordinary-decreasing nonresets with 5<=s<=V (if capped). Every such assigned event with positive intersection with a slab of mark p has x'<b<=2p, x>a>p/5. Hence
    s<p,  hs>p/15-9/2.                           (4)
This property holds for each positive length, not just for point-crossing events. Combining (2) with disjoint allocation gives, SIMULTANEOUSLY for all R<U and W>=R,
    sum_{dec nonreset, s<=V, s<U} (d-d')
       >= c_beta * sum_{good marks p<=U} p,        (5)
    sum_{dec nonreset, s<=V, hs>W/15-9/2} (d-d')
       >= c_beta * sum_{good marks p>=W} p.        (6)
Omit s<=V if uncapped. One can apply both restrictions jointly to any subset of marks p in [W,U]. These are actual ordinary reductions, no cut-correction or low-run error. The factor h=D/(2s) refers to each recovery event. The selected length is not necessarily the entire decrease of a contributing event; events can share disjoint length portions across slabs but never supply the same portion twice. In particular (5) cannot be interpreted as an injective match of whole events to individual marks; that distinct-event assertion is section2.

For the uncapped case (3) has no high-nonreset term. Thus when (N+2)L=o(m), all but o(m) marked occurrences receive weighted recovery from strictly smaller labels, even if high B events are abundant. This yields scale-resolved ordinary-gain lower bounds, not a frequency upper bound. If one considers only marks p<=V, the cap V never spoils a slab, by (4).

## 4. Consequence for macroscopic windows with sparse roots and high B

Take crossed [X,lambda X], lambda>1 fixed, on a canonical infinite ray. Set R=floor(c log X), 0<c<1/(8log2), and P=P_R, C=floor sqrt(lambda X+1). Assume along a sequence of windows N=o(sqrt X) and far B events p>R have count o(sqrt X), with the earlier fixed square-band cutoff. Let m be ALL A1 with p>R. Previous gain-share/barrier argument gives
    m>=((lambda-1)/14-o(1))*X/P.
Here P<=X^delta, delta=4c log2<1/2, so m dominates sqrt X times any fixed power of log X. All ordinary-decreasing nonresets s>R are B (A1 increases, A0 resets; low-deficit test exhausted), and the near event count is O(sqrt X); hence H_R=O(sqrt X). Choose V=R, beta=1+1/log X. Then L=O((log X)^2), kappa=O(log X), c_beta=9/5-O(1/log X). By (3) only O(sqrt X*(log X)^2)=o(m) marks are bad. Consequently a subset A_good of all but o(m) marks admits disjoint length allocation with
    sum_{dec nonreset, 5<=s<=R} (d-d')
         >= (9/5-o(1))*sum_{p in A_good} p,       (7)
where sums over labels count event occurrences. In particular the number of such low-label decreasing events is >= (9/5-o(1))*sum_good p/(R-3). This strengthens the previous uniform (9/5-o(1))*R*m bound: each good A1 supplies its actual label p, not R. It does NOT replace sum_good p with sum of all marked labels; the exceptional o(m) large labels can carry substantial weight.

For any W>=R sufficiently large (possibly growing), (6) with V=R shows that good marks p>=W must be paid for by low-label ordinary decreases with
    h > (W/15-9/2)/R
since hs>W/15-9/2 and s<=R. More precisely (6) bounds total reductions of that population by the sum of labels of such good marks. For W=L0 R with L0->infinity, this forces h->infinity on every charged event of those marks. If many good marks use p/R->infinity, their recovery cannot be accomplished by uniformly bounded adjusted multiples. This is a conditional tail result, not an assertion that many marks must use p/R->infinity.

Using section2 with fixed beta=3/2 and the maximizing phase, at most O((N+2)log X)=o(m) slots are lost to resets/boundary, and at most H_R=O(sqrt X)=o(m) distinct assignments can have s>R. Thus all but o(m) A1 marks receive at least five distinct subsequent low-label nonreset decreases and at least (log_beta(10)-5-o(1))*m marks receive six. The earlier count bound 5.678... is recovered with a per-mark injection and scale restriction.

An optional moderate-label corollary: choose c still smaller so delta<1/4. Since total marked gain <=G=O(X), at least half the marks have p<=U=1+2G/m=O(P). The total weight of bad marks in this range is <=U*O(sqrt X log^2 X)=o(Rm), because P^2 log X=o(sqrt X). Therefore (7) for just the moderate-label marks can equivalently use their entire weight with an additive o(Rm) loss. This avoids claiming control of the unbounded tail's exceptional weight.

None of these conclusions bounds the maximum possible population of low-label nonreset recoveries. The modulus barrier alone supplies no such upper bound, and a ray can in principle have many recoveries with large h. Finite twins forces infinite rays but not either sparsity hypothesis. The uncapped and injective finite theorems do not require sparsity.

## 5. Reproducible diagnostics and persistence

[Point matching audit f7c19fa](https://github.com/tara-sooo/A166944-Lean/blob/f7c19fa9af0bb3b0f9a93de80e59e34997aee7f2/research/min_direct_level_matching_audit.mjs), blob 5b07bb3c6383cbda17ca5f564b4a67bc9aa7cfd3. Run node research/min_direct_level_matching_audit.mjs 100000 180. Actual ECMAScript execution in tool runtime. 49,998 canonical roots,1,020,339 events,9,591 A1,49,989 stopped before cap,9 cap-unresolved. R47/71/101/151, phases1,5/4,7/5, full and suffix blocks. 1,098,819 block/cutoff incidences including witness,100,266 nonempty marked blocks,100,932 marked incidences,570,273 slots,65,613 six-slot incidences,7,829 injective nonreset matches,31,423 reset slots,531,021 endpoint slots,1,503,990 cumulative inequalities,385,473 nonreset ratio checks,7,829 scale checks,100,266 root bounds. All exact comparisons passed; only three complete-mark incidences, all from the constructed witness. These are overlapping finite-prefix diagnostics, not an empirical claim that the asymptotic hypotheses occur. Many finite scans terminate without ordinary-deficit recovery.

[Slab audit e9b5113](https://github.com/tara-sooo/A166944-Lean/blob/e9b5113fb100f8978643fe1101a38be2dccf56fa/research/min_direct_slab_recovery_audit.mjs), blob dc45f3fad503521ed796a2aa3af6d5533d6bd220. Run node research/min_direct_slab_recovery_audit.mjs 50000 180. 24,998 roots,452,868 events,3,929 A1,all stopped within cap. R47/71/101, beta3/2,5/4,11/10. 407,200 block/cutoff incidences including witness,33,412 nonempty blocks,33,493 marked incidences,412,800 slabs,20,845 completed,391,955 incomplete,25,847 positive intersection checks,161,226 disjoint-allocation checks,33,412 weighted inequalities,100,236 tail inequalities. Four good-mark incidences, all from constructed witness. Every inequality checked using common-denominator exact BigInt arithmetic. First version displayed null for some witness ratios after converting very large numerator and denominator to Number (exact assertions had passed); updated decimal rendering via integer division and reran all checks, all passed. Both audit sources independently fetched and exact remote readback confirmed.

Both audits reconstructed the earlier 9,962-digit canonical word7687/5233/3541/2389/1621/1093/733/7369, each with22,195 literal GCD ticks and20,600 stage-residue checks. R7500 leaves only 7687 marked. At phase5/4 all six point matches are assigned, in rank order 733/1093/1621/2389/3541/5233, no resets or pending slots. With slab beta3/2,5/4,11/10,101/100, the single good mark obtains exact assigned lengths (decimal display truncated) 9140.625,12094.838619,13124.599013,13694.070682, respectively, within total available ordinary decrease13908. No inferred empirical macroscopic crossing, no Lean kernel verification, no external novelty claim. Main and sibling branches unchanged.

Next: exploit (4)-(7) for upper bounds on repeated low-label nonresets with large h or on scale-specific recovery gain. Level matching and slab allocation provide the needed localization and non-double-counting, but do not themselves cap the supply of recovery events or prove a stopping invariant.
