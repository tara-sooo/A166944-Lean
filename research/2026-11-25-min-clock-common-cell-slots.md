# Common-cell ancestry, later-arrival clock slots and old shared anchors

2026-11-25 JST. Continues 4087e2cad3a4730ec693c0220d3d9b883e18a760. New paper deductions: two common-cutoff local source partitions permit arbitrary orientation of each same-clock-slot pair; the entire overlapping-wait part of the old NOT-YET class can be eliminated by exact reorientation, not by deleting its energy. Different-slot energy has unconditional adaptive thin-slot and relative imbalance bounds. OLD low-r products require an actual shared nonLOW anchor within the stable clock window; thin anchor products are absolutely payable. No complete remaining energy bound, no Lean compilation.

## 1. Two local common-cutoff references

Keep dyadic X,N=X/2 odd roots M in [X,2X), B=ceil(sqrt(7X)), s=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B, u=log B. We use the exact deterministic MIN histories; the natural late occupation is [a,H) in relative time. Full positive-drift reference weights use completed positive-drift waits starting before relative H (including the crossing wait). Each such wait finishes before relative H+2B. The actual prime cap B is unchanged.

At any supported horizon C, both original roots satisfy 0<=C-(2M-2)<=2H+6, hence their separation is <=H+3<5B for sufficiently large B. Partition the original root coordinates M-X into half-open cells of width 10B, and a second partition shifted by 5B. Every supported pair is in a common cell of at least one partition (a pair crossing a boundary in both partitions would have separation at least 5B). Assign it to partition 0 if possible, otherwise 1.

In each cell take a COMMON ABSOLUTE reference cutoff c=max_(M in cell)(s_M)+H+2B. All its roots have c<=K(M) eventually since their start times differ by <10B and K-s=3M/4+O(1), whereas c-s<=16B. Reference trajectories run from their own starts to c or earlier twin terminal. This is an extension only within each original time gate and is NOT additional charged natural occupation. All reference horizons remain O(X), and total gain and reference clock are O(B) per root.

For each root M and partition j let n_(M,j)(t) count ALL active tags in its cell sharing the same true tick state at t, including itself. Since all cell members now have the same absolute cutoff, once they meet neither can expire earlier while the other continues; twins stop together. Thus n_(M,j) is nondecreasing along M's active reference, including companions on BOTH sides of M. Initial n can exceed one, unlike the ordered count in 4087e2c. Define n=1 before the root starts, so the initial increase is counted in the telescoping logarithmic budget.

Let A_j(C) be the count of reference tags visiting C in partition j, summed over cells, and A(C)=max(A_0(C),A_1(C)). The reference linear r cost sum_C r A=O(XB): for each j each root's completed r costs are bounded by 1.5 times its horizon gain, and one last incomplete wait costs at most B. No source multiplicity bound is assumed. For every n_(M,j)(t) at C, n<=A_j(C)<=A(C).

## 2. Arbitrary orientation and exact elimination of overlapping NOT-YET

Put D=max(1,floor(B/u^2)), eps=u^(-1/4), zeta=u^(-1/8). Mark any retained tick for which log[n_(M,j)(t)/n_(M,j)(t-D)]>eps in either partition. Counting the initial logarithmic jump, Fubini bounds the total across both partitions by
    #marked <= 2ND log N/eps = O(XB/u^(3/4)) = o(XB).
After any previous holes, delete marked ticks, then remove horizons with U(C)<zeta A(C). As before, U=sum_M w_M, w_M=retained tick mass/(2r), E=sum r U^2, R=sum r U. The added linear loss is <=(1/2)#marked + zeta sum r A=o(XB). Apply density gate last or reapply against the frozen reference. No small quadratic loss is inferred.

A CLOCK SLOT at a horizon C is the absolute next event time v of its original completed wait [t_M,v). Determinism gives:
* Two such waits overlap in actual time iff their next event time is the same. Indeed if they overlap they share a true tick state and must have the same next event; the converse follows since both waits end at v and have positive length.
* Same-slot events have the same selected prime. Distinct slots have disjoint actual waiting intervals.
This uses unmasked waits, not clipped weights; natural weights may occupy disjoint portions of a common original wait.

For any unordered same-slot pair, expand its ordered energy 2r w_i w_j over the retained ticks of the LATER ARRIVING tag (tie by smaller root). Each unit tick contributes the other tag's weight w<=1. The focal tag and its partner share every such tick in their common-cell reference. This exact reorientation removes ALL precontact NOT-YET products for overlapping waits from the classification. It does not subtract their energy from E. Pair orientation may choose the larger root, which the previous single ordered-companion proof did not allow.

Define RECENT if the pair did not yet share the true physical state at focal t-D, OLD otherwise. Use its assigned partition to count recent partners. For each focal tick in each partition there are at most (1-exp(-eps)) n_(M,j)(t) new companions by stability. Across the two assigned partition classes their summed weights are <=2(1-exp(-eps)) A(C). Hence, exactly as a finite sum over focal ticks,
    E_recent(C) <= 4(1-exp(-eps)) r U A
                <= beta r U^2,
    beta=4(1-exp(-eps))/zeta=O(u^(-1/8)).
So E=E_diag+E_recent+E_old+E_cross with E_recent<=beta E. CROSS now consists ONLY of disjoint original waiting slots, not near-future overlapping meetings or clipping artifacts. No assumption that old pairs shared a recorded pre-event state is required. E_diag<=R. This partition works for arbitrary retained fractional tick weights in [0,1], and both occupations in section 1. As before, LOW-destination amplification prevents an unqualified application to natural MED.

## 3. Adaptive disjoint-clock-slot estimates

For each active C, write W_v(C)=sum of w_M(C) over waits with next event time v. Then the same-slot energy including diagonal is exactly r sum_v W_v^2; CROSS is 2r sum_(v<v') W_v W_v'. The latter is still a source-weighted quantity, not the number of clock slots.

All next event times of natural supported waits satisfy C/2<=v<=C/2+3+H+2B by the original canonical start inequality and the clock bound. For each odd eligible prime p<=B dividing C-1 or C+1, one absolute progression of modulus 2p contains its possible event times. Thus the following explicitly arithmetic envelope bounds the number k(C) of occupied slots:
    K_C=sum_(eligible p<=B) (1+floor((6B+6)/(2p))).
In particular K_C=O((1+B/r(C)) log X/log r(C)), using the product of the distinct prime divisors of (C-1)(C+1)=O(X^2). For r>=B/u^alpha with fixed alpha>0, K_C=O(u^alpha); for r>=D/4, K_C=O(u^2). The finite K_C can be much larger than actual k(C); k(C) itself is also a valid upper envelope for the next two elementary bounds, with different residual definitions. We use K_C in the audit.

Take m=u^(5/2), b=u^(1/4). For each unordered distinct slot pair first pay all products with min(W_v,W_v')<=m/K_C. Orient each toward its larger slot. At most K_C partners can be attached to any slot, giving
    E_cross,thin <= 2m sum_C r U = O(XB u^(5/2))=o(XB u^3).
Next pay all remaining products with min(W_v,W_v')<=max(W_v,W_v')/(K_C b). Again orient to larger slot, so
    E_cross,imb <= (2/b) sum_C r sum_v W_v^2 <= (2/b) E.
The estimates require no regularity of source masses, and apply to any holes or clipped weights. They are disjoint by priority. Hence the remaining disjoint-slot term consists of genuinely heavy AND relatively balanced slot pairs:
    both weights >m/K_C, and ratio <K_C b.
In the near-maximal-r band r>=B/u^alpha with alpha<5/2, both weights grow at least on scale u^(5/2-alpha). This is a restriction on actual aggregate slot weight. It is NOT a bound on the mass of each slot or on the remaining products. No relative contraction is claimed from simply bounding the number of clock slots.

## 4. OLD shared anchors and a low-r reduction

For OLD pair-tick products the actual histories coincide throughout [t-D,t] in the common reference cell. For sufficiently large B let L be the largest even primorial <=D/12, with largest prime y; y=Theta(log B) by Chebyshev estimates. If ALL actual events ending in (t-D,t] have p<=y, their total horizon gain is <L by the even-primorial barrier. Their elapsed clock time from t-D through the last event is at most 3L, since the first wait may be partial and every completed wait length <=2p<=3(p-1). The final current wait has age <2r(C). If there are no events, the whole interval is within the current wait and the same upper estimate applies. Consequently
    D <= 3L+2r(C).
In particular if r(C)<D/4, this is impossible. Thus every such OLD low-r product has a common actual selected p>y event at a physical post-state alpha=(t_alpha,C_alpha), t-D<t_alpha<=t. Choose the latest such event. It is a deterministic physical anchor shared by the focal and its partner. This includes events jumping directly into the current horizon. It does not claim that the earlier root had a large selected prime at the start of the wait.

Also if the shared history is stationary (C(t-D)=C(t)), necessarily 2r(C)>D: a full wait is longer than D. This stationary subset belongs to the rough sector r>=D/4. Thus OLD can be divided into r>=D/4 (rough) and low-r with an actual recent nonLOW anchor. The two-form upper sieve implies O(X/u^2) horizons with r>=D/4 for the asymptotic D choice; it is a support count only.

For each low-r OLD product whose anchor has n_(M,j)(t_alpha)<=m in the assigned cell, pay its entire pair-tick contribution. For a fixed focal tick and partition all such partners are present at the same chosen alpha and have weights <=1. Their sum is <=m. Summing over both partitions and all focal ticks gives
    E_old,anchor-thin <= 4m R=o(XB u^3).
Likewise for any eta>0, the separate class with n_(M,j)(t_alpha)<=eta U(C) has contribution <=4eta E by the same count. This second bound is a paper deduction and not separately measured in the audit. It is relative, not absolute. If both classes are applied, use priority to avoid double subtraction.

These estimates leave OLD rough products and genuinely thick shared anchors at low r. The rough class includes long stationary waits (the previous OLD condition did not force any earlier event). The actual shared-anchor mass is still not controlled. The improved reduction must not be interpreted as excluding large ancestor groups.

## 5. Combined sufficient residual

For retained HIGH, using m=u^2.5 and any eta=o(1), after the actual linear masks of section 2 and nonoverlapping quadratic payments,
    E <= E_old,rough + E_old,anchor-heavy + E_cross,heavy-balanced
         + O(XB u^2.5) + [beta+2/b+4eta] E.
Eventually the bracket tends to zero. If the three residual terms sum to o(XB u^3) on unbounded dyadic windows, retained HIGH satisfies the previous sufficient bound. This still needs natural MED o(XB^(13/8)u^3) (or compatible masked destination bound). The same algebra applies to a trimmed full-positive occupation, but no transfer to natural L_shared+K_paid follows solely from the linear loss.

## 6. Finite checks

Standalone ECMAScript research/min_clock_common_cell_slot_audit.mjs, commit 292ceacc4acdb18c9eea98a51d94d41c623e0b78, exact readback blob 6023729f7ed0834dd7dfd83dccd87000de9734d8. Run:
    node research/min_clock_common_cell_slot_audit.mjs 4096 16384

Executed actual audit function in available JS runtime (not a separate Node run): two X, analytic and stress, both occupation types (8 combinations). Both references replay literal per-tick parity GCD, independently compare shared original trajectory prefixes, check common cutoff gate, exact all-companion monotonicity including nontrivial initial masses, Fubini, two-cell cover, exact same-slot/cross-slot identity, actual later-arrival expansion, sampled first common tick by independent linear scan, per-horizon recent bound, arithmetic slot envelope, thin and imbalance bounds, and actual old rough/anchor/anchor-thin partitions. Log and fractional energies use floating-point tolerances. Stress uses D=floor(B/4), eps=.12,zeta=.22 and deterministic seventh-tick holes, not the asymptotic thresholds; the analytic finite D does not satisfy the primorial scale gate and no low-r anchor claim is made there. The current finite beta is >1 in all modes.

Largest X16384,B339:
| mode | retained E | recent | old rough | old low-r anchor | anchor-thin (part of preceding) | cross |
|---|---:|---:|---:|---:|---:|---:|
| late HIGH analytic |41160.52|0|39166.54|0|0|0|
| full positive analytic |4351546.04|5905.40|3387996.46|0|0|891846.80|
| late HIGH stress |632183.11|0|524011.06|93445.58|93445.58|0|
| full positive stress |7664767.47|16828.50|3236810.69|2825973.20|1780568.37|1436444.24|

Diagonal is omitted from the table but verified in the exact partition. In largest stress D=84,L=6,y=3, full-positive cross thin=82198.59, imbalance=0, heavy-balanced=1354245.65; stationary OLD=1340735.58 (subset of rough); old anchor remaining after thin=1045404.83. Reorientation selected the larger-root later arrival for pair energy 36219.86 (not all of it was previously NOT-YET). 57085 of 1058043 pair-horizon terms assigned shifted cell, 128 independent literal meeting scans in that mode. Maximum occupied slots 6, largest relaxed K_C 945. At X4096 late-HIGH stress cross=25360.63 with thin=8392.03, low-r anchors=19909.50 all thin, nonvacuous disjoint-slot case. All finite imbalance contributions zero after thin priority. Across both partitions largest reference initial-heavy root incidences=5498, showing initial injection of smaller roots matters. Largest stress instability count=2006199 reference tick incidences, full-positive raw ticks=1489385, after stability/holes=631191, after gate=496449; not empirical negligible-loss evidence. These are isolated ledgers, not cumulative masks with all base research. No numerical inference about infinite windows or Lean verification.

## 7. Remaining work

Next target rough OLD (especially stationary long waits with thick shared earlier ancestry) and low-r OLD with thick actual anchors, using deficit levels and the source-tagged true-tick inverse. For cross-slot residual seek a bound for comparable heavy weights at distinct absolute clock slots of the same rough horizon, exploiting the actual incoming phases rather than only K_C. The new reorientation and anchor classification identify precise residuals but do not prove the general energy bound or twin infinitude. Main and other branches untouched.
