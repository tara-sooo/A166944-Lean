# Ordinary recovery with a linear-log potential and mod-3 short-string constraints

Continuation of [8362e33](https://github.com/tara-sooo/A166944-Lean/commit/8362e339e6090dd82947095164a5a53f6d667a9d). We separate a genuinely ordinary-deficit recovery theorem (including small labels) from the previous cut-corrected potential theorem. A piecewise linear/logarithmic potential improves the necessary ordinary decrease per marked A1 to 9R/5, without assuming that the number of recovering events is O(m). Independently, the exact clock of prime 3 imposes a short-word restriction on adjacent D=2p strings beginning at an A1. These are new necessary conditions, not a contradiction to finite twins. No Lean kernel verification.

## 1. Ordinary-deficit potential

Use adaptive MIN, ordinary pre/post deficits d,d' and adjusted D=d'-6I, side I=0 even/1 odd. For an event label p and wait w>=1, d'=d+2w-(p-1). A1 means p>=47,p>=5d+15,D=2p. A0 is the same test with D0; for p>=47 the other events are B. Recall from 1924deb: every nonreset p>=5 has d'>=2p and (d+3)/(d'+3)<=3/2 when d decreases; p=3 cannot decrease d. A decreasing reset necessarily has p>=7 on a canonical ray (ordinary post deficits2,4,8 are impossible, and the initial d=6). Each decreasing reset q has d+3<=q+6 and associates to a distinct canonical reentry within7 ticks, before another p>=7 event, or termination.

Fix real R>=47. Write x=d+3 and define
    f_R(x)=0                        (x<=R/5),
           x-R/5                    (R/5<=x<=2R),
           9R/5+2R log(x/(2R))     (x>=2R).
It is nondecreasing, 1-Lipschitz, with derivative between0 and min(1,2R/x) wherever defined. Unlike using only a logarithm, its full linear slope persists through the relevant low-deficit recovery scale. Mark every A1 with p>R. Its increase satisfies
    Delta f_R >= f_R(2p)-f_R(p/5) = M_R(p) >=9R/5.
For R<=p<=10R this minimum gain is
    M_R(p)=9R/5+2R log(p/R)-(p-R)/5,
increasing with p. For p>=10R it equals 2R log10. (The actual post x>=2p+3 only improves the bound.) Every smaller A1 p<=R has pre f_R=0 and can be removed as a separator. A decreasing nonreset contributes loss at most
    min(d-d', 2R log(3/2)),
from the Lipschitz bound and integration of 2R/x. A decreasing reset q contributes at most f_R(q+6).

In a contiguous canonical event block with all pre-horizons <=Y, let C=floor sqrt(Y+1), m=#marks, N=#actual canonical visits in (t_start,t_end]. Remove the smaller A1, keep the maximal consecutive segments containing marks, and trim the segment ending at the full block endpoint immediately after its last mark. Every kept segment ending at a separator has nonpositive potential difference. The one possible positive endpoint difference is bounded by f_R(2C+9). Let J be the set of unmarked nonreset events in these segments that strictly decrease f_R, and Z the set of decreasing reset events there. Then the exact finite budget is
    sum_marked M_R(p)
       <= f_R(2C+9) + sum_{q in Z} f_R(q+6)
            + sum_{v in J} min(d-d',2R log(3/2)).           (1)
Here #Z<=N+1 (on infinite rays, or finite canonical prefixes allowing the last reset to terminate). In particular (1) controls actual positive ordinary deficit reductions, with no additive K_S*j correction. It includes low-label nonresets p>=5; it is not a bound restricted to dense-cut crossers or to p>S. We can discard any chosen subset of J by paying at most 2R log(3/2) times its count. The previous log-only budget also holds with the same segmentation and all p>=5 ordinary-decreasing nonresets: replace f_R by log(max(R/5,x)/(R/5)), each marked gain>=log10, loss per nonreset<=log(3/2), and endpoint/reset bounds O(log(C+R)) when R<=C. No low-run term is needed because low-label reductions are now included.

## 2. Macroscopic root-sparse and high-B-sparse windows

Fix lambda>1, a canonical infinite ray crossing [X,lambda X], and R=floor(c log X), 0<c<1/(8log2). Retain the earlier far/near square-band definition, with fixed epsilon0. Let S=floor(a log R), 0<a<1/(4log2). The primorial K_S=2P_S is o(R), P_R log X=o(sqrt X). One useful simplification of the earlier hypotheses: for sufficiently large X every jump with p>R has gain g=p-1>=R>K_S, so it crosses a multiple of K_S, and therefore a dense S-barrier. Thus at these asymptotic cutoffs the high-far B sparsity condition restricted to S-barrier crossers, to multiple-K_S crossers, or to all high-far B is the SAME condition. The earlier note 8362e33 described the first of these as stronger than the multiples-only condition; that distinction can hold at arbitrary finite cutoffs but disappears in the chosen asymptotic regime. Lower-label crossing populations remain different.

Suppose along a sequence of crossed windows N=o(sqrt X) and the count of far B with p>R is o(sqrt X). The preceding gain-share and barrier result gives
    m >= ((lambda-1)/14-o(1))*X/P_R
for ALL marked A1 p>R, so m/(sqrt X log X)->infinity. Every nonreset ordinary decrease with p>R is a B event: A1 increases, A0 resets, and the deterministic test exhausts both. There are at most O(sqrt X) near events of any class and o(sqrt X) high-far B. Their combined contribution to (1) is O(R sqrt X)=o(Rm). Endpoint loss is O(R log X); the reset contribution is O((N+1)R log X)=o(Rm). Thus after removing those events, let J_low be the remaining ordinary-decreasing nonresets in J, all with 5<=p<=R. Then
    sum_{J_low} (d-d') >= (9/5-o(1))*R*m,                     (2)
    sum_{J_low} (p-3) >= (9/5-o(1))*R*m.                     (3)
The second uses d-d'<=p-3. More precisely the sum of min(d-d',2R log1.5) is at least sum_marked M_R(p)-o(Rm). All p<=R events in these high windows are far because q=(H-e)/p is much larger than p. Those with p>=47 are B; smaller labels are not called B in this note.

The log-only version, with the same omission of above-R losses, implies a possibly different selected set of ordinary-decreasing nonresets with 5<=p<=R of count >=(log10/log1.5-o(1))*m. Both the count and sum conclusions can be stated for the entire population of such events in the full block; no need to identify the selected sets. In particular the unconditional ordinary decrease in (2) strengthens the earlier conditional Dnet+K_S*j bound in the following sense: it guarantees true decrease without assuming j=O(m), and the coefficient 9/5 replaces log10/5, BUT the allowed recovery population now includes small labels and does not require crossing S-barriers. It does not improve the previous more restrictive narrow-band cut-crossing gain theorem directly.

For any cutoff 5<=U<R, partition J_low into p<=U and p>U. From (2), for each fixed 0<theta<9/5, either the small-label group has >=(theta-o(1))*Rm/(U-3) events, or the larger-label group has total positive ordinary reduction >=(9/5-theta-o(1))*Rm. The latter is an actual gain lower bound at U<p<=R, not necessarily cut-crossing. This gives a tradeoff for every scale U (including growing U) without assuming a bounded j/m. Also if all ordinary-decreasing nonresets in the block with p<=R have drop <=delta*(p-1), 0<delta<=1 fixed, then their total gain must be >=(9/(5delta)-o(1))*Rm. In general the drop-weighted efficiency must be paid by more gain if individual reductions are small. The finite total gain is O(X), so this only yields the corresponding weak upper bound on m; it does not exclude m=Omega(X/P_R).

## 3. Exact mod-3 competition between adjacent D=2-label events

Let two ADJACENT actual nonunit events have labels a,b>=5, adjusted deficits D_a=2a,D_b=2b, sides I,J, with wait v of the second. Write H for the horizon immediately after the first, n for its tick. Substitution into the ordinary update gives
    3b=2a+1+2v+6(I-J).                                     (4)
Thus if a=1mod3 then v=0mod3; if a=2mod3 then v=2mod3. Wait1 is impossible. If H!=0mod3, prime3 divides exactly one neighbor and is eligible at all H>=8. It supplies a competing clock: even tick residue0mod6 when H=1mod3, odd tick residue5mod6 when H=2mod3. At the preceding event n=I mod2 and 2n=H+2a mod3 (the 6I term disappears). These equations give the next p3 wait uniquely. Since 3<b, the chosen v must be strictly smaller than that wait, even at a tie. The following table gives the only remaining possibilities from (4) and the 3 clock. A dash means impossible; a listed wait is necessary, not sufficient.

|H mod3|a mod3|I|wait of 3|possible v|J|
|---:|---:|---:|---:|---:|---:|
|1|1|0|6|3|1|
|1|1|1|3|--|--|
|1|2|0|2|--|--|
|1|2|1|5|2|1|
|2|1|0|3|--|--|
|2|1|1|6|3|0|
|2|2|0|5|2|0|
|2|2|1|2|--|--|

In particular when H=1mod3 any possible next D=2b event is odd (J=1), at wait2 or3. Its post-horizon H+b-1 has residue1 if b=1mod3, residue2 if b=2mod3. In both cases the table's next row is impossible (Hnew1,b1,I1 or Hnew2,b2,I1). Thus from a D=2a event whose post H=1mod3 at most ONE further consecutive D=2-label event with label>=5 can follow. H=2mod3 can return to H=0mod3 through b=2 in the listed even next event; no corresponding unconditional one-step terminal claim for that case.

An A1 initial event has pre H=0mod3: its wait w>6 follows directly from d<= (p-15)/5 and d'>=2p, and if pre H!=0mod3 the eligible3 clock would win within6. In ANY contiguous string of D=2p events with labels>=5 starting at an A1, therefore, all labels except possibly the last two are 1mod3. Indeed until the first label 2mod3 the horizon stays0mod3, then that label takes it to1mod3 and at most one further D=2-label event is possible. This includes arbitrary other waits and does not assume monotone labels. The statement concerns a string with no intervening nonunit events; intervening p3, other adjusted deficits or resets invalidate its adjacency hypothesis.

## 4. Short-word arithmetic scarcity

Consider a string as in section3 of at least k+2 events, starting with label a_0 and side I_0. Suppose the FIRST k inter-event waits are <=8. All their source labels are among the string's nonfinal-two labels, hence each is 1mod3. By (4) the k waits must belong to {3,6}. For a fixed side and fixed word v_1,...,v_k in {3,6}, sides are determined by I_i=(I_(i-1)+v_i) mod2. Iterating (4) gives
    3^k a_k=2^k a_0+sum_{i=1..k} 2^(k-i)*3^(i-1)
                               *(1+2v_i+6(I_(i-1)-I_i)).
As gcd(2,3)=1, integrality forces exactly one possible starting residue a_0 mod 3^k per side/word. Consequently at most 2^(k+1) residue classes mod3^k contain possible starting labels for such an actual string. Among integers a_0 in an interval [A,A+L] the number of candidate starting labels is at most
    2^(k+1)*(L/3^k+1).
For fixed k this is a relative upper bound 2*(2/3)^k in long intervals. It is a necessary arithmetic upper bound on the DISTINCT possible starting labels, not on their repeated occurrences along a ray, and not a proof these prime chains exist. Additional primality, adaptive eligibility and clock competition can only reduce it.

For the special word consisting entirely of wait3, the two-step recurrences are particularly simple: from an even side a to next even side c, 9c=4a+41; from an odd side a to next odd side c, 9c=4a+29. After j pairs the starting a must satisfy 9^j | (5a-41) for even start or 9^j | (5a-29) for odd start. Thus a bounded starting label imposes a logarithmic upper bound on such a run even before primality checks. These restrictions sharpen the earlier six-decrease rigidity only when recovery events are adjacent with D=2p and very short absolute waits. The known six-decrease construction allows waits proportional to arbitrarily small fixed fractions of large labels and is not ruled out. The ordinary recovery theorem of section2 does not force these adjacency or absolute-wait hypotheses, so the distinct-label bound cannot be applied to all of its recovered events.

## 5. Diagnostics and persistence

[Audit 528ac21](https://github.com/tara-sooo/A166944-Lean/blob/528ac21e6cd2a8f208dd012563fc31c8cb3274fc/research/min_direct_ordinary_recovery_short_strings_audit.mjs), blob 4be42cd7e5c5e4faa31f03edb6de2bf98579d5ef, exact remote readback. Run node research/min_direct_ordinary_recovery_short_strings_audit.mjs 100000 180. Actual ECMAScript executed in tool runtime, not separate Node process. 49,998 odd canonical M5..100000, 1,020,339 events,9,591 A1,49,989 stopped before cap,9 cap-unresolved. 457,843 linear-log budgets including witness (full/suffix intervals, R47/71/101/151/1009),33,424 retained segments,28,358 separator checks,33,648 marked gains,13,797 nonreset loss and25,173 reset loss checks. Float comparisons of analytic potentials use tolerance. 7,400 adjacent D=2-label transitions incl witness checked by integer recurrence, 289 with nonzero mod3 post-horizon checked by the competitor table. 9,593 A1-start strings incl witness,9,706 label incidences, one short interior check. These counts overlap when intervals or starting positions overlap. Enumerated 2,044 side/short-word residue conditions k1..9 and 16,388 integrality recurrence checks. All assertions passed.

Rebuilt prior 9,962-digit canonical word 7687/5233/3541/2389/1621/1093/733/7369;22,195 literal BigInt gcd ticks,20,600 stage-residue checks, all passed. At R7500 the first A1 alone is marked, the last A1 is a separator. Exact ordinary decreases total13908, potential loss13872.340..., mark lower13832.013..., endpoint difference0, reset0. At R7000 two marks and six decreasing nonresets; the finite endpoint term is nonnegligible. These are diagnostics, not macroscopic window observations or a proof of the asymptotic theorem. The previous cutoff-sparsity wording corrected in section2. No Lean kernel verification, external novelty claim or twin-prime contradiction. Main and sibling branches untouched.

Next: obtain a genuine multiplicity/frequency upper bound on the unrestricted ordinary recovery events of section2 (or find a different invariant). The very short adjacent strings admit residue scarcity but are only a restricted subclass, and the total gain lower bound still leaves room for abundant smaller labels.
