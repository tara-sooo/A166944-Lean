# Scale-local smoothed cluster recovery and enlarged lower prime cutoff

Continuation of [f763c6b](https://github.com/tara-sooo/A166944-Lean/commit/f763c6b2fe277f735a828a9f488f37872cda81d0). The previous recovery clusters required every low-label run to have gain <=T/200. Instead permit exceptional long low runs and bound their aggregate gain by the 4/11-power mean-square smoothing theorem. Also restrict the allocation to marks in one multiplicative band and pay the reset, high-B and endpoint exceptions in that band's own deficit range, rather than the full sqrt(X) scale. This yields finite count and weighted inequalities for ALL marks in the band, not just completed good slabs. It enlarges the usable lower prime cutoff from log T to as much as (11/4)log T, subject to an explicit long-run error. No contradiction with finite twins.

## 1. Finite model and allocation

Use the established adaptive MIN model, ordinary deficit d=2t-H, x=d+3, event label p, gain p-1, adjusted D=d'-6I. Every ordinary decrease is at most p-1. For a nonreset label p>=5, D=2ph with integer h>=1, x'=2ph+6I+3, and x/x'<3/2. A1 means p>=47, x<=p/5, D=2p, A0 the corresponding reset, B other events at p>=47. Near/far as in 850c00f; assume all pre-horizons in the finite contiguous block are >=6250001, so every near label s at or after a marked A1 p satisfies s>=.96p. Let N count actual canonical visits in (start,end], G the total gain, C bound all labels.

Fix 47<=S<=R and 48<=T<=U (U can be replaced by min(U,C)). Mark any subset of A1 events with p>R and T<=p<=U; m is the count and W=sum of their labels, with multiplicity. Choose an integer K>=0 with 200K<=T. Partition the block into clusters: an event s>S and the immediately following maximal run of labels <=S, plus the initial low run if any. A cluster is long if its low run has gain g_low>K, short otherwise. Write M_long for the number of long low runs (including the initial one if long), G_long for their total gain. In particular M_long<=G_long/(K+1). No upper bound on individual low-run lengths is assumed.

For every marked p allocate the real interval (p/5,19p/10] to its first subsequent downward crossings, leaving unvisited levels pending at the endpoint. The pre-state satisfies x<=p/5 and post-state x'>2p, so the mark crosses the interval upwards. At each level a new allocation is impossible until the old one is paid, because a new upcross requires pre x<level. The pending intervals are disjoint and each pending level is <=current x. At a downward event pay just the pending portions in (x',x]; aggregate payment is <=actual ordinary drop. Demand is 17W/10, and all levels belong to the common interval
    (T/5,19U/10], width Delta=19U/10-T/5.                (1)
Thus total endpoint loss <=Delta, not the former full-scale 2C. This uses disjoint pending levels, not disjoint deficit trajectories.

For a short cluster the precursor exclusion of f763c6b applies without change: its high event, if the mark itself, has post x'>2p; if a later A1 s it has post x'>=10y+3 at an old pending level y; if a later near nonreset s it has post x'>=1.92p+3. In every case the following low run cannot reach an assigned y<=1.9p because it can lower x by at most K<=T/200<=p/200. No such high event itself pays any level either. For a long cluster, direct payment by the high event still cannot come from an A1 or a near nonreset; only payments in its low run are exempt from the exclusion. The initial low run cannot pay any mark. All other high precursors of eligible payments are resets or far nonreset B. High resets s>S>=47 have distinct canonical visits associated by the normalization theorem (123bbd4), except at most one pending at the endpoint, so their count is <=N+1. Let B_R count all far B events with s>R (it is enough to count only nonresets here).

## 2. New scale-local weighted supply inequality

Assign all payments in long low runs to a separate account, of total <=G_long. For the remaining payments (direct high-event payments in ANY cluster, or low-run payments in SHORT clusters), the preceding exclusion holds. If the high precursor is nonreset far B with S<s<=R, assign the payment to its band cluster. Let J count the distinct band clusters that pay a positive length in this account. Each such cluster pays at most
    (s-1)+g_low*1_{short},
using the individual drop bound. One may use the actual positive ordinary drop of the high event instead of s-1.

For any such payment to the allocation of mark p, choose a paid level y. Let X0,X1 be precursor pre/post x. The level was pending before the precursor (no new mark in a B cluster), so y<=X0. For a direct payment X1<y; for a payment in a short low run X1<y+K. Also X1>(2/3)X0. Consequently
    S<s<(y+K-3)/2<p,
    s*h>y/3-9/2>p/15-9/2,                              (2)
where h=D/(2s). In particular each J precursor satisfies s<U and sh>T/15-9/2. Direct payments in long clusters are included in this conclusion; the low-run payments in long clusters are NOT.

All remaining payments outside the long-low account are assigned to high reset or far high-B clusters with s>R. There are <=N+1+B_R such clusters. No new mark can occur anywhere in any of them: their precursor is not A1 and all subsequent labels <=S. Each cluster can therefore pay at most Delta across all marks, regardless of repeated traversals of deficit levels. This accounts for direct reset/high-B payments as well as any short-run payments following them. The bound also applies to the direct-only portion of a long exceptional cluster. Together with the endpoint account we obtain the finite theorem
    (17/10) W <= sum_{J band clusters}[(s-1)+g_low*1_{short}]
                         + G_long + Delta*(N+B_R+2)
               <= (R-1+K)*J+G_long+Delta*(N+B_R+2).    (3)
All marks are used, and there is no completed-slab exception-count or weight loss. In particular the relative bound can be useful even if W=o(X), provided the two explicit error terms are smaller than W. This is stronger in that regime than an additive o(X) estimate. The same high event is counted at most once in J. There is no assumption that a precursor itself decreases, or that the assigned low runs are monotone in deficit.

## 3. Local geometric count, including long-run exceptions

Take geometric levels y_j=(T/5)*phase*(31/20)^j with 1<=phase<31/20 and j>=0 through 19U/10, total L. Every marked p crosses at least five such levels in its allocation interval, since (31/20)^5<9.5. Use first downward crossings for these discrete slots. For U<=2T, L<=1+floor(log(19)/log(31/20))=7, an absolute constant independent of the window size.

A short nonreset band cluster can pay at most one slot globally, as in f763c6b: all paid levels <=X0<(3/2)X1 and X1<y_min+K, so y_max<1.5(1+1/40)y_min<1.55 y_min. No new mark occurs in such a cluster, so it cannot pay two slots at the same level. A short exceptional reset/high-B cluster pays at most L slots.

A long cluster also pays at most L slots, EVEN IF its high precursor is itself a new mark: any previously pending level is <=the pre-state, whereas the new mark allocates only levels strictly above the pre-state. Thus at each level there is at most one slot available during this cluster; no further mark can occur inside its low run. This is why the long-cluster count is sufficient and no extra factor2 is needed. Endpoint slots <=L. All short band cluster slot payers are counted in J in (3): at the first downcross of a level y>p/5, a positive interval of levels immediately below y from the same allocation is still pending and paid, since no earlier downward event after that mark could cross a level below y without first crossing y. (Equivalently one can use all band precursors satisfying (2), without the positive-length refinement.) Therefore
    5m <= J+L*(N+B_R+2+M_long).                         (4)
This discards even the direct high-event slots of long clusters, which is harmless for an upper bound on the right. In a dyadic band, combining (3)-(4) yields simultaneously
    J >= 5m-7*(N+B_R+2+G_long/(K+1)),
    J >= [(17/10)W-G_long-(18/5)T*(N+B_R+2)]/(R-1+K).  (5)
The second inequality uses Delta<=3.6T. These are scale-local lower bounds on distinct band precursor occurrences, not distinct primes. All J satisfy (2); one may replace J on the right sides of (3)-(4) by the full eligible precursor population in order to obtain a necessary condition directly on that population.

## 4. Aggregate long-run bound and new cutoff

Write P=P_S, normalized horizon barrier moving average f_l, variance sigma_l^2. Each low-label run has a half-open horizon interval in coordinate H/2 with no S-barrier; all these intervals are disjoint. For K>=4 choose l=min(P,floor(K/4)). If l=P, then every low run has integer-coordinate length <P and absolute gain <2P<=K, so G_long=0. Otherwise every long run has integer-coordinate length >=2l and at least half as many starting positions at which f_l vanishes. The positions are disjoint, and on each |f_l-1|^2=1. Over the whole block's coordinate interval, periodicity bounds the number of zeros by (G/2+P)*sigma_l^2. Thus as in 4777ea7,
    G_long <=4*(G/2+P_S)*sigma_l^2.                      (6)
For K>=8, if P_S<=(K/8)^(11/4), then floor(K/4)>=ceil(P_S^(4/11)); the case l=P is already trivial. Apply the refined theorem of f763c6b to the other case. For S sufficiently large and P_S=o(X) on a crossed [X,lambda X] window,
    G_long=O_lambda(X exp(-.001*pi(S))).                (7)
The bound is aggregate, not a pointwise maximum length. When an elementary bound 2P_S<=K is available, one can take G_long=0 exactly instead; choose whichever estimate helps.

For fixed rho in(0,1), take R largest odd prime with P_R<=X^rho, R~rho log X (the near-X cutoff of f763c6b works with rho=1 in this asymptotic description). Let T=X^a, U<=2T, a>0 fixed and <=1/2, choose K=floor(T/200). Choose S<=R largest odd prime satisfying P_S<=(K/8)^(11/4). By PNT and next-prime bound,
    S~min(rho,11a/4)*log X.
All conditions hold eventually, including S>=47. Unlike the earlier S~a log X cutoff, this can approach 11/4 times that scale before clipping at R. Equations (4)-(7) imply
    J >= 5m-O_lambda(N+B_R+1+(X/T)exp(-.001*pi(S))).    (8)
Thus whenever m dominates the displayed error, J>=(5-o(1))*m. This includes any dyadic band carrying positive macroscopic weight under N,B_R=o(sqrt X): then m=Omega(X/T), and N+B_R=o(X/T) since T<=O(sqrt X). More generally it can include sublinear band weight if it dominates X exp(-.001*pi(S))+T(N+B_R+1). The increased cutoff is conditional on the error being small compared with the target count/weight; it is NOT a uniform upper bound on every low-run length. If S=R the band is empty, so (8) becomes an upper bound on the mark count, not a claim of available precursors.

For a weighted supply bound choose 0<b<a and K=floor(X^b), eventually <=T/200. Take S<=R largest prime with P_S<=(K/8)^(11/4), so S~min(rho,11b/4)log X. Then (3),(7) imply
    (R-1+K)J >=1.7 W
          -O_lambda(X exp(-.001*pi(S))+T(N+B_R+1)).    (9)
If W dominates that error, J>=(1.7-o(1))*W/(R-1+K)=Omega(X^(a-b)*m). Unlike the former good-slab estimate, there is no need to assume m>>sqrt X log^2 X; the error condition in (9) is the actual requirement. For the new larger S the long-run error may dominate a sublinear W; it must not be discarded. When W is a positive fraction of X and N,B_R=o(sqrt X), it is negligible. For smaller S with no long runs, (5) already works when m>>N+B_R+1, even if W is sublinear and T is small. All these are necessary conditions only.

## 5. A dyadic band consequence not requiring polynomial-size marks

At the balanced cutoff P_R<=sqrt X, under N,B_R=o(sqrt X), the f763c6b count gives m_f=Omega(X^(9/11)). Partition these far marks p>R into O(log X) multiplicative bands [T,2T] starting T=R+1, disjoint by taking half-open upper endpoints where necessary. At least one band contains
    m=Omega(X^(9/11)/log X).
No assumption that T grows as a positive power of X is required. In that band choose K=min(R,floor(T/200)) and S largest odd prime with 2P_S<=K. As T>=R+1, K=Theta(R)=Theta(log X) (constants may differ), S~loglog X by PNT; eventually S>=47. There are no long runs by the elementary primorial bound. Since m>>sqrt X and the band width is <=3.6T, (5) gives
    J >= (5-o(1))*m,
    J >= (1.7-o(1))*W/(R-1+K)
        =Omega((T/R)*m).
In particular this gives a band of at least Omega(X^(9/11)/log X) distinct high far nonreset B precursor occurrences, with label S<s<=R and s*h>T/15-9/2, without a polynomial-size mark hypothesis. If T/R diverges, the second bound requires a diverging number of precursor events per mark. If T=Theta(R), h need not diverge. It does not prove the selected band is at polynomial scale. The straightforward same-label H-congruence supply ceiling (two residues mod2s, horizon monotone) remains of order X/s per fixed label and is not enough to rule out this population; no stronger useful time/phase ceiling was obtained this turn.

## 6. Diagnostics and persistence

[Cluster audit 32de2b6](https://github.com/tara-sooo/A166944-Lean/blob/32de2b6d63d8f597f2add2f3135b51548c64fa53/research/min_direct_smoothed_cluster_audit.mjs), blob e3db7457db7070d833c818c8076ce0b871584a2e, exact remote readback. Run node research/min_direct_smoothed_cluster_audit.mjs 30000. Actual ECMAScript execution in tool runtime. 14998 odd canonical roots,243497 actual events,13837 marked block controls,13841 marks,69205 slots (149 band,1350 long,514 exceptional,67192 pending),42174 clusters,2030 positive interval intersections,1222 positive band-cluster incidences,59 positive-paying long-run incidences. All13837 finite count/weight conservation and capacity checks passed. Exact BigInt geometric slots and real allocation lengths using a common rational denominator. Diagnostic S3/5/7/11, R47, K=floor(T/200); for low S, count other nonreset far non-A1 as exceptions where needed for geometry. Directly check the later-near inequality at finite horizons rather than applying the asymptotic pre-horizon lower bound. Use actual high reset count in diagnostics rather than infer canonical visits. No small diagnostic block reached K>=4 with period tables, so the periodTests counter is zero; the separate capacity audit below supplies those checks.

Reconstructed the earlier9962-digit CRT canonical root with first word7687/5233/3541/2389/1621/1093/733/7369:22195 literal BigInt GCD ticks and20600 residue checks, adaptive eligibility and actual deficits verified. At R7500,T7000,U14000,K35, varying S47/750/1700/3600/6000 gives respectively J6/5/3/1/0, long gain0/732/3444/9372/14604, band slots5/4/2/0/0, long slots0/1/3/5/5. Full demand13067.9 paid in every control; at S47 all by band clusters, at S6000 all by the long low run. This demonstrates why the long-run error is necessary, not a removable endpoint term. Prior root reconstructed, not a newly discovered initial value.

[Long-run capacity audit e8bfeb2](https://github.com/tara-sooo/A166944-Lean/blob/e8bfeb2a8ab6b851542c589668d8d4b027763869/research/min_direct_long_cluster_capacity_audit.mjs), blob e5dcae8b9823e6b7528148d83f618891f4030ec3, exact remote readback. Run node research/min_direct_long_cluster_capacity_audit.mjs. Actual ECMAScript, five complete H-barrier periods R5/7/11/13/17, seven K choices incl power-scale and l=P cases,1900815 moving-average position calculations,3500 synthetic disjoint gap-family tests,560238 long barrier-free subintervals and31771023 zero-start incidences,2019 nonzero-gain tests. All passed. Counts exact; numerical variance comparison uses floating-point tolerance. These synthetic families are not simulated MIN trajectories, and the asymptotic bound is the previous theorem, not inferred from finite variances.

No new Fourier exponent, no observed infinite ray, no historical novelty claim or Lean kernel verification. Main and sibling branches unchanged. Neither sparsity follows from finite twins, and neither the new high-multiplier supply lower bounds nor the dyadic existence theorem exclude the supply. Next pursue an upper bound on that population (or a different route that forces stopping), especially using actual phase-clock constraints on repeated band labels. The long-run error is a quantified tradeoff, not a pointwise barrier improvement.
