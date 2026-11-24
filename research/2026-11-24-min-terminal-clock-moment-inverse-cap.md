# Terminal clock capped-mass moment and inverse-prime stop thresholds

2026-11-24 JST. Continues 8f11404fc0d294e0102c04232a1b5ee069fbff80 on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary deductions using the previously established MIN arithmetic budget, plus exact integer diagnostics and floating-point variance checks. Not Lean-checked. No complete stopping deficit or twin-prime proof.

## 1. Terminal clock dispersion is bounded by capped mass, not minority mass

Keep canonical MIN, odd sources M in [X,2X), N=X/2, B=ceil(sqrt(7X)), individual cutoffs, fixed LOW7 L=210. Use the clock-refined forest of the preceding note. Let v=(p,C) be a projected stop, A_v its original stopped tags, m_v their number. Partition A_v into actual event-clock classes A_(v,n), masses m_(v,n). The event is proposed and not executed. Its hypothetical post-height h(n)=2n-(C+p-1)>=0 is well defined. At a fixed key the divisibility side is unique, so all actual proposed event times lie in one residue class modulo 2p. Hence successive distinct h differ by at least 4p. Define H_v=sum_n m_(v,n) h(n), the source-weighted hypothetical height, not the unweighted sum of distinct heights.

For the previous smooth hat kernel K_D at an integer scale D>=1, let F_D(A)=(1/|A|) sum_{i<j} K_D(|M_i-M_j|). It has K_D(t)=1 for t>=2D and 0<=K_D<=1. For any nonempty A of size m, distinct origins are odd with spacing 2. Therefore
    m/2 - F_D(A)
      = 1/2 + (1/m) sum_{i<j}(1-K_D(|M_i-M_j|))
      <= 1/2 + (D-1) <= D.
Indeed for each left endpoint at most D-1 larger odd origins are at distance strictly below 2D. Also m/2-F_D(A)<=m/2. Thus for the virtual terminal variance of v,
    G_virt,D(v)=F_D(A_v)-sum_n F_D(A_(v,n))
      <= (1/2) sum_n min(m_(v,n),2D).
This is different from the preceding minority-mass bound: several large distinct clock classes need not produce significant virtual variance at a scale smaller than their individual source masses. Define a=2D and U_v(a)=sum_n min(m_(v,n),a). Both the capped mass and this new virtual upper bound are valid with any number of clocks and arbitrary projected overshoot.

## 2. A sharp elementary clock moment inequality

Write the increasing possible clock heights as h_min+4p j, j>=0 integer, omitting unoccupied classes; put c_j=min(m_j,a) for occupied classes and c_j=0 otherwise. Then
    H_v >=4p sum_j j c_j.
For nonnegative integers c_j<=a and U=sum c_j, the weighted moment sum_j j c_j is minimized by filling a at each smallest index before advancing. Writing U=a k+b, 0<=b<a, its minimum is a k(k-1)/2+k b, which is at least U^2/(2a)-U/2 (the difference is b(a-b)/(2a)). Thus
    H_v >= 2p(U_v^2/a-U_v),
    U_v <= a+sqrt(a H_v/(2p)).
Consequently for ANY chosen set E of terminal projected keys, with J_E=|E|, S_E=sum m_v, H_E=sum H_v and I_E=sum 1/p over E,
    G_virt,D(E) <= (1/2) sum U_v
                 <= D J_E + (1/2) sqrt(D H_E I_E).
Use Cauchy-Schwarz in the second inequality. Also
    sum_(v in E,n) F_D(A_(v,n))
        >= S_E/2 - D J_E - G_virt,D(E)
        >= S_E/2 - 2D J_E - (1/2)sqrt(D H_E I_E).
These are exact finite inequalities (apart from the harmless weak inequality for the square-root expression). They do not use a bound on a single clock class, a lag cutoff, or a minimum number of classes. They give a direct upper bound on virtual variance, rather than an upper bound on the entire terminal minority mass.

The number of original tags at stops in E whose own clock class has <=a tags is at most sum U_v <= 2D J_E+sqrt(D H_E I_E). Also the number of clock classes of mass >a is <=sum U_v/a. These statements concern original source mass, not merely the number of nonempty clock classes. For arbitrary fixed a>=1 one may apply the same moment argument without choosing a=2D.

For each stopped root, hypothetical post-height <=6+4R_i+4r(C), where R_i is its executed prefix cost and r(C)<=B. Hence H_E<=6N+4R_pre+4BN for every E. The unexecuted current wait is included explicitly. All formulas retain the original source-specific cutoffs and do not charge stopped proposals as executed cost.

## 3. Consequence for the old uniform B stopping rule

Let E be stops with p>=P, uniform threshold T=B. Then J_E<=N/B and I_E<=N/(BP). The prior budget R_pre=O(XB^2/log^3 B) and X asymp B^2 give H_E=O(XB^2/log^3 B). Therefore
    G_virt,D(E) = O_L(X D/B + X sqrt(D B/(P log^3 B))).
The same bound up to a factor two holds for sum U_v(2D).
For fixed 0<=alpha<3, 0<beta<3-alpha, P=B/log^alpha B, D=floor(log^beta B), this is o(X). In particular, with alpha=1, beta=1, the virtual contribution of all stops at p>=B/log B is O(X/sqrt(log B)). The within-clock terminal variance of these stops is at least S_E/2-o(X). This is not an estimate on all terminal stops or on their minority mass. It changes the distance scale from the preceding D=B to a smaller growing scale D; the new bound does not assert virtual cancellation at D=B.

The clock-refined forest restricted to tags whose final stop is in E remains a non-splitting forest. Sum of physical merge increments is exactly the within-clock terminal variance. By the preceding harmonic near bound, taking d=floor(D/(log(2D))^(1/2+epsilon)) with fixed epsilon>0 removes o(X) near physical proxy flux. Thus
    P_phys,far(E;D,d) >= S_E/2-o(X).
If a positive fraction of stopped roots belong to E, a positive fraction of X must be provided by actual physical coalescence on this scale. No estimate on the remaining physical far proxy is claimed.

## 4. Inverse-prime cap makes the same result work down to any growing prime cutoff

Choose any real Y=Y(B) tending to infinity, 11<=Y<=B, and keep fixed LOW7 (do NOT move the LOW cutoff to Y). Set projected stopping thresholds
    tau_p = B                 for 7<p<Y,
          = ceil(B^2/p)      for Y<=p<=B.
These are a new accounting rule on actual trajectories, not a replacement of the MIN clock rule. In particular all executed high keys are bounded by tau_p-1 and every proposed stop at p has mass>=tau_p. All minimum thresholds are at least B. For every high key with p>=Y, the executed mass is <= B^2/p, even with the ceiling. For smaller high labels it is <=B. No altered source path is executed beyond its first stop.

Reuse the earlier uniform S_p=O(X/log^2 p) estimate for r-cost of all eligible horizons at a prime p. Also the number of eligible horizons is O(X/p) (p<=B). LOW blocks have cost O_L(1) per root or executed high event. Therefore
    R_pre <= O_L(X
         + B X sum_(7<p<Y prime) [1/log^2 p + 1/p]
         + B^2 X sum_(Y<=p<=B prime) [1/(p log^2 p) + 1/p^2]).
The elementary upper bounds by partial summation of pi(t)=O(t/log t) are
    sum_(p<Y) 1/log^2 p=O(Y/log^3 Y),
    sum_(p<Y) 1/p=O(log log(3Y)),
    sum_(p>=Y) 1/(p log^2 p)=O(1/log^2 Y),
    sum_(p>=Y) 1/p^2=O(1/(Y log Y)).
All terms are O_L(X B^2/log^2 Y), because Y<=B and Y tends to infinity. Thus
    R_pre=O_L(X^2/log^2 Y)=o(X^2).
The original non-twin unstopped terminal cost lower bound Omega(X) applies unchanged; if no twins, S=N-o(X). This is an actual prefix-budget proof for the new cap. The low labels 7<p<Y are still subjected to their own stopping test, while only p<=7 are free LOW events; the latter distinction avoids an exponential L_Y charge.

Now take E to be ALL stops at p>=Y. By the chosen cap, p m_v>=B^2 at each such stop, so
    I_E=sum 1/p <= S_E/B^2 <= N/B^2,
    J_E<=N/B.
Apply section2, H_E=O(X B^2/log^2 Y), to get
    G_virt,D(E) = O_L(X D/B + X sqrt(D)/log Y).
Thus for ANY diverging integer D=o(log^2 Y), virtual variance at all those stops is o(X), as is sum U_v(2D). For instance D=floor(log Y) gives O_L(X/sqrt(log Y)). This remains valid if Y=log B (then D approximately log log B), or Y=B^theta for any fixed positive theta<1 (then D approximately theta log B). No power lower bound on p beyond p>=Y is required. Likewise almost all tags of E belong to physical clock classes larger than 2D, in the absolute sense that the number in smaller classes is o(X). For any growing a=o(log^2 Y), the general capped-mass moment shows that the mass of tags in classes of size<=a is o(X).

In the forest restricted to E, the within-clock variance lower bound is
    sum F_D(A_(v,n)) >= S_E/2-o(X).
With d=D/log^(1/2+epsilon)(2D) as in section3, P_phys,far >= S_E/2-o(X). This is a rigorous reduction of the virtual obstruction for E to physical far coalescence at a smaller growing scale. It is NOT a proof that S_E is large, nor that physical coalescence on that scale is sparse.

In a no-twin window one therefore has the alternative: most stops can be at small labels p<Y, or a substantial large-label stopped mass requires substantial physical far variance; the quantitative inequality is
    S_<Y + 2 P_phys,far(E;D,d) >= N-o(X).
This does not remove the low-label term. In fact the finite diagnostics below show that the inverse cap tends to transfer much of the stopped population to lower labels. No claim of an overall improvement in stopping deficit over the uniform rule follows from this theorem.

## 5. Exact finite checks

Saved research/min_terminal_clock_moment_inverse_cap_audit.mjs and its results JSON, executed at X=256,1024,4096,16384,65536,262144. Three diagnostic modes: uniform T=floor(B/4) (at least2), inverse with that same T and cap ceil(T B/p) for p>=Y, inverseSmall with T=floor(B/32) (at least2). All three use Y=max(11,ceil(sqrt B)), LOW7 unchanged and original individual cutoffs. These are finite cap analogues; the analytic choice in section4 is T=B. Replay every actual stopped source to its original stop, recover exact clock classes and hypothetical heights. Verify source conservation, every terminal cap, actual executed prefix height inequality, clock period, capped integer moment and global virtual and physical bounds at all tested scales and prime thresholds. The smooth hat kernel numerator is integer, and ratios and sums are compared with explicit floating-point tolerances. Each run also includes 80 direct kernel checks and for X<=1024 literal GCD clock checks. For inverse modes, at all tested P>=Y verify sum_{p>=P stops}1/p<=S_{p>=P}/(TB). Exact readback of script and data at 88d61966abbd311d6c1ed7f8fcbf68a73feb8d69.

At X262144,B1355,Y37, N131072:
- Uniform T338: S11112, 30 stops, 5192 tags at p>=37 (14 stops), 5920 below37. D4 virtual variance for p>=37 is37.9614, within-clock variance2539.8225, capped mass U352, moment bound on virtual989.5635. No stop at p>=678. Total R98554147.
- Inverse T338: S8775,24 stops, all at p<37; R100971457, 122297 twin terminals, no non-twin terminals. Thus the new bound for p>=Y is empty in this particular large window. It would be misleading to call that evidence of physical concentration at large labels.
- InverseSmall T42: S74459,1305 stops,1564 tags at p>=37 (20 stops),72895 below37; R44248884. At D4 the high-label total terminal variance757.215110 = within-clock754.983932 + virtual2.231178; U176 and square-root upper bound182.379782. At p>=678, 1444 tags in19 stops, virtual1.077421 and within-clock697.278575. These tests are nonempty but neither their relative frequencies nor the looseness of the upper bound constitute asymptotic proof. At the smallest X256 inverse run there are five non-twin terminals with the restrictive cutoff; all counts are retained. No need to extrapolate them.

## 6. Remaining issue

The new estimate controls the virtual terminal term on all sufficiently large current-label stops of an inverse-prime cap, with no lag or clock-number assumptions. It also provides a general terminal bound in terms of the actual weighted height and reciprocal stop-label sum, usable without adopting that cap. The reduction changes the distance scale to D=o(log^2 Y); it does not strengthen the D=B far-merge bound at the same scale. The remaining no-twin alternative requires controlling the low-label stopped source mass and the physical far coalescence of the large-label population. One possible next move is to control low-label stops by tracing their physical incoming classes back to the last event with p>=Y; if there is no such event, the growing LOW barrier restricts the original-root span, but a general bound on those mixed ancestral populations is still missing. No main edit, no new branch, no Lean compilation.
