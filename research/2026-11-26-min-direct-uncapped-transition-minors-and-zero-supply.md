# Uncapped close-transition minors and zero-minor variation supply

Continuation of [c4ef87a](https://github.com/tara-sooo/A166944-Lean/blob/c4ef87a5974a684f88c9675c44017e056f2a7a2a/research/2026-11-26-min-direct-growing-multiplier-and-zero-stratum-chains.md). Remove the multiplier cap in a new arithmetic subcase of nonzero adjusted displacement. The three minors of a two-row integer matrix connect horizon and deficit displacements; the zero cofactor-multiplier minor has exactly two possible positive integer slopes on a canonical ray. Its gain is charged to positive ordinary deficit variation without a support-size or multiplier factor. Nonzero minors remain; the result is a refinement of the close-transition alternative, not a proof of twin infinitude. No Lean kernel verification.

## 1. Exact minors, with arbitrary positive multipliers

Retain the MIN notation: event label p, pre H, gain g=p-1, wait w, side I, e=1-2I, ordinary d=2t-H, post d'=d+2w-g, adjusted D=d'-6I=2hp with positive integer h for a nonreset p>=5. Let the physical block have pre-horizons in [X,Y], Y=lambda X with fixed lambda>1, gain G=O_lambda(X), cap C=floor sqrt(Y+1). Choose any subset of high nonresets p>=T, in order, with NO upper bound on h. For successive selected events write p,q,h,I,e,H,d'_1 and r,s,k,J,f,H2,d'_2, with H-e=pq and H2-f=rs. Cofactors q,s are odd, q>=p,s>=r. Write E=H2-H-(p-1) for intervening gain, even and nonnegative; v=d'_2-d'_1, c=v/2-3(J-I), and
    a=E+e-1-f,
    L=p(q+1)=H+p-1+2I,
    x=hp=D1/2.
Then a is an odd nonzero integer, |a|<=E+3, and
    rs-p(q+1)=a,   kr-hp=c.                               (1)
Define the integer minor
    j=hs-k(q+1).
The three exact identities are
    rj=ah-c(q+1),   pj=ak-cs,   prj=ax-cL.                (2)
These follow by eliminating p and r in (1), and are valid for every actual such pair. In particular j=h mod2. They require no bound on the multipliers, no first-hit certificate of primality, no absence of twins. If c=0 then j!=0 since a and h are nonzero, and the earlier equal-D product constraint pr|x holds. This separates the new zero-minor case from the previous zero-displacement case.

Assume from here that T>=11, close relay E<=B with B+3<T, |v|<=A, and successor cofactor s is prime. For example at the previous cube threshold T=T_3=max(256ell+1,1+ceil(9(Y+1)^(1/3))), select all-long events (4w>=p-1). Or select arbitrary high nonresets with A+5B<=(T-1)/2: every close successor is automatically long by the relay drift argument and hence has prime s at T_3. The first cofactor need not be prime for the zero-minor theorem below. Distinct labels p!=r follow from E<T-1, as before. All results concern actual selected visits on one physical monotone ray, not candidate starts drawn from an ensemble.

## 2. Zero minor: exactly two possible slopes and no consecutive zero edges

If j=0, (2) gives
    h=c(q+1)/a,   k=cs/a.
Since s is prime, s>=r>=T>|a|, gcd(a,s)=1. Hence a divides c, and the ratio m=c/a is an integer. Since h,k>0, m>=1. Thus
    h=m(q+1), k=ms, x=mL,
    d'_1=2m(H+p-1+2I)+6I,
    d'_2=2m(H2-f)+6J.                                   (3)
For canonical start (H_root,t_root) with ordinary d_root=6, the elementary envelope is d'<=6+5(H_post-H_root), from |d'-d|<=5g on every physical event. In particular, at Z1=H+p-1,
    2m L<=6+5 Z1,
so m<=2 for sufficiently large X (in fact Z1>=8 suffices). Consequently
    m in {1,2},   h>=q+1>=p+1,   k>=s>=r.               (4)
This is a genuinely large-multiplier subcase. It lies outside the earlier growing-cap sieve M<T. It needs neither equal adjusted D nor a bound on how many different labels are used. The conclusion m<=2 also holds for abstract states satisfying the same upper envelope at the first endpoint, though canonical reachability of such a state is separate.

No two successive edges of the selected list can both have j=0 under the stated hypotheses. Indeed if the first has integer slope m and its successor label r, cofactor s, multiplier k=ms, the next zero-minor edge starting at that same event must have k=m'(s+1). This would give (m-m')s=m' with m,m' in {1,2} and s>=T>=11, impossible. This exclusion holds for different a,c at each edge and any intervening physical events satisfying the relay bounds. In particular in a factor-two selected band [U,2U) each zero-minor edge forms a disjoint two-vertex component; its ending gain fraction is at most (2U-1)/(3U-2) of its two-vertex gain. The stronger supply bound below does not need a band or a fixed ratio of p,r.

The nonzero minor cannot be assumed to be large merely because h,k are large. From (2), universally
    |j| pr <= |a| x + |c| L.
For |v|<=A and E<=B, |c|<=A/2+3, x<=2.5(Y+C)+3 and L<=Y+C+2 give
    |j| <= O_lambda((A+B+1) X/(pr)).                    (5)
Thus when p,r>=eta sqrt X for fixed eta>0, j belongs to an integer range of size O_(lambda,eta)(A+B+1), without a multiplier cap. Also, if 0<|j|<s then gcd(q+1,s)=1, since a common factor of q+1 and prime s must divide j. In that case for a fixed q,s,j, the equation hs-k(q+1)=j puts h in ONE residue class modulo q+1, and the envelope gives h<=2.5(q+1)+3/p. There are at most three positive such h, each determining k. These are necessary arithmetic restrictions, not a global bound on the number of distinct q,s pairs along a ray. Formula (5) gives |j|<s, for example, if p,r>=X^(1/3+epsilon) and A+B=log^O(1) X. The nonzero-minor class is not covered by the zero-minor supply bound.

## 3. Zero-minor gain charged to positive variation

Let P_plus=sum_physical max(d'-d,0) on the whole block. Let Z_0 be total ENDING-event gain over all close j=0 edges in the filtered selected list. Separate those edges into their two possible slopes m=1,2. For consecutive edges in a fixed slope list, let the earlier ending event have pre-horizon H2, label r, post Z2=H2+r-1, side J and sign f, and ordinary post deficit d'_2=2m(H2-f)+6J. Let the later starting event have post Z3>=Z2 and side I3; by (3) its ordinary post deficit is d'_3=2m(Z3+2I3)+6I3. Therefore
    d'_3-d'_2 >= 2m(r-2)-6
                = 2m(r-1)-(2m+6).                     (6)
The physical intervals from the earlier ending POST state to the later starting POST state are disjoint within each slope list. Indeed zero edges cannot be adjacent, and they are ordered in the same physical ray. Their positive variations have total <=P_plus. Each such interval supplies (6), irrespective of the intermediate signs, labels, resets or total variation. Since r-1>=T-1, summing over the slope list except its final edge gives
    Z_(0,m) <= C+P_plus/[2m-(2m+6)/(T-1)].
Here C is needed only when the corresponding list is nonempty. Summing the two slope bounds gives the main new uncapped estimate
    Z_0 <= 2C + [1/(2-8/(T-1))+1/(4-10/(T-1))] P_plus
         = 2C+(3/4+O(1/T)) P_plus.                     (7)
The variation intervals for different slopes may overlap; we used a separate P_plus bound for each, which is why the coefficient is a sum. No erroneous claim of disjointness across slopes is needed. This is a gain-weighted estimate on actual zero-minor ending events. It uses positive variation only, not the total variation, and is independent of the number of labels and the sizes of the multipliers. In particular on macroscopic windows with P_plus=o(X), Z_0=o(X). Alternatively a macroscopic Z_0 forces macroscopic positive ordinary variation, even if the change on each individual close edge is small. This does not bound P_plus itself.

There is a further cumulative restriction on slope m=2. At its first post horizon Z, equation (3) gives d'>=4Z. For any earlier canonical prefix ending there, choose a threshold R0>=7 and let U_low be gain of all its events p<R0. The other events have d'-d<= (3+4/(R0-1))*g, while low ones have d'-d<=5g. Put epsilon0=4/(R0-1). The clock envelope gives
    4Z <= 6+(3+epsilon0)(Z-H_root)+(2-epsilon0)U_low,
hence
    U_low >= [(1-epsilon0)Z+(3+epsilon0)H_root-6]
                    /(2-epsilon0).                    (8)
With fixed canonical root and R0 tending to infinity, this requires at least (1/2-o(1))Z gain in that prefix from labels below R0. This is a cumulative gain necessity for slope2; it does not follow merely from a local small-crossing-mass condition on one window. Slope1 has no such conclusion from this calculation. The previous all-high gain dominance on a single large window does not by itself exclude slope2, because the starting deficit may be large.

## 4. Combining the uncapped split with the earlier growing-cap sieve

Take a chosen all-long high nonreset population in one factor-two band [U,2U), U>=T_3, in a macroscopic physical window. Let F be its gain, U_out=G-F, V_d total ordinary variation, P_plus<=V_d. For its consecutive filtered edges define close by E<=B, |v|<=A, with B+3<T and A/2+3<=T/2. Choose integer M>=6 within the preceding growing-cap range M<=X^(a-epsilon) (for T>=X^a, a>1/14); below we only use M polylogarithmic. Every close edge with ending multiplier k<=M/3 also has h<=M: from hp=kr-c, r/p<2, |c|<=p/2, obtain h<=2k+1/2<=M. Both endpoints belong to the sublist of selected events with multiplier <=M, and consecutive in the original selected list implies consecutive in that sublist. Thus all these ending gains are bounded by the earlier growing-cap double sieve
    F_small-h,close << X M log(2M)(A+1)(B+1)/log^2 X.    (9)
The same inclusion holds if the starting multiplier h<=M/3, using p/r<2 and |c|<=r/2. Consequently any remaining close pair with neither endpoint charged in (9) has both h,k>M/3.

The close gain with c=0 is bounded by (2/3+O(1/U))F in the absence of a direct twin witness: use the previous equal-D two-label chain theorem on this same selected band. Imposing |v|<=A can only reduce that charge. The disjointness of zero-minor and zero-displacement classes follows from (2). Let F_res be the total close ending gain with c!=0, j!=0, and both h,k>M/3. All selected events after the first either have large relay E>B, large ordinary post difference |v|>A, or are close; hence
    F_res >= (1/3-O(1/U))F -3C
             - C U_out/(B+1) - C V_d/(A+1)
             - O(X M log(2M)(A+1)(B+1)/log^2 X)
             - (3/4+O(1/T))P_plus.                     (10)
This is a necessary alternative under absence of the certified twin witness, in particular under finite twins at sufficiently large T_3. All subtractions are upper bounds; overlap in discarded categories is harmless. We do not claim the selected gain has macroscopic size or that its complement gain is small unconditionally.

For example, fix 0<delta<2, take M=floor(log^(2-delta) X), A=B=floor(log^(delta/4) X). If F>=rho X for fixed rho>0 and
    U_out+V_d=o((X/C) log^(delta/4) X),
then the error terms in (10) are o(X). Indeed M log(2M)(A+1)(B+1)/log^2 X=O(log^(-delta/2) X loglog X), and the stated budget gives P_plus=o(X). Absent a twin witness, at least (1/3-o(1))F must be supplied by close transitions with nonzero c,j and BOTH multipliers exceeding M/3. This is a precise remaining class even for a near-consecutive, nearly flat, large-event ray. The hypotheses on relay/variation budgets are much stronger than the o(X) outside-high-crosser gain given by the previous smoothing argument; they have not been shown to be forced. For p,r comparable to sqrt X, the remaining j has size O(log^(delta/4) X) by (5), and is nonzero. This identifies a small integer determinant range in which future uncapped analysis can focus, rather than summing over all possible multipliers. It does not yet give a supply upper bound for that range.

## 5. Finite diagnostics and preservation

[Final audit 4c7117d](https://github.com/tara-sooo/A166944-Lean/blob/4c7117db3ebb8c0ac305fb1062272a6efec09fac/research/min_direct_uncapped_transition_minors_audit.mjs), blob 1e995783f013ba9bc86ea84bba2ca6ef50c73ad6. Exact remote readback. Run node research/min_direct_uncapped_transition_minors_audit.mjs 60000. Actual ECMAScript execution in tool runtime, not separate Node. 29998 odd canonical roots through60000,549085 actual MIN events,0 unresolved cap180. 72517 nonempty block/cutoff controls including 20 abstract two-event controls,80806 filtered pair comparisons,1760 close exact minor identities,1740 nonzero minor incidences,48 zero-displacement incidences (24 in factor-two band). All minor absolute bounds and 1740 nonzero-minor coprimality checks passed; 30173 band controls restricted to finite analog D/2<T^3 for the support condition, with no band twin triple in these controls. 72517 exact gain partition and positive-budget checks. Small finite thresholds17/31/61 and direct SPF prime cofactors, not asymptotic cube thresholds. Counts overlap across cutoffs and roots.

No j=0 pair was observed on the canonical-root scan. To exercise nonempty zero-minor cases, searched actual MIN from abstract high-deficit plateaus chosen using (3), without claiming canonical reachability. 164 candidate first-event starts,20 actual consecutive zero-minor pairs (9 slope1,11 slope2), all replayed by literal raw parity-GCD clock over628 ticks. Example m=1, initial H9642,t14500,p31,q311,r19,s509, E0,a=-1,c=-1, post d19344/19342, waits8/8. Example m=2, H3318,t8362,p31,q107,r17,s197,E0,a1,c2, post13392/13402, waits8/13. Both satisfy the upper envelope used in the theorem, but are NOT examples starting from canonical roots or cube-certified pairs. No multiple-zero-edge actual block was found in these controls (zeroSpacingChecks=0); the positive-supply proof for repeated edges is algebraic, with 144 synthetic endpoint and 144 weighted inequality controls exercising (6). The aggregate tests with actual abstract pairs only exercise single-edge endpoint charges. The combined asymptotic inequality (10) uses earlier analytic double-sieve and chain results, not an empirical test of their constants. All final assertions passed. No Lean kernel verification or external novelty claim. Main and sibling branches not modified.
