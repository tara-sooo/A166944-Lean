# Future-minimum canonical target certificate and terminal persistent record slots

2026-11-26 JST. Continues [0a64b1c8d36d](https://github.com/tara-sooo/A166944-Lean/blob/0a64b1c8d36de0fc36243d2cae633c169f6ceca1/research/2026-11-26-min-unified-canonical-overshoot.md) and [ac0460216f5f](https://github.com/tara-sooo/A166944-Lean/blob/ac0460216f5f4478b17e051af01debada1d4d565/research/2026-11-26-min-unified-canonical-target-certificate.md). Integrates actual canonical return geometry, the older deficit-record level method, and exact departure-slot arithmetic. Independent heads checked unchanged: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New: a third clock correction based on observed future states, exact elimination of positive excess above half-gain from all completed canonical gaps, unique last-upcross charge decomposition, and a thin *persistent-charge* sieve applicable to ALL odd selected labels. Under no twins its remaining heavy slots force a long common forward high-deficit suffix, not merely old common ancestry. No new bound on their total charge and no twin-prime proof or Lean compilation.

## 1. Original paths and future-minimum correction

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u), the original prime-root gain-stopped MIN prefixes and terminal snapshots. Every completed jump with selected odd prime p has gain p-1<=B and actual wait 1<=w<=2r<=3(p-1), nonnegative deficit d=2t-C. The root deficit is 6. Under the no-twin hypothesis all original tags reach T for large X. No trajectory is changed by the accounting.

Use the previous selected target set I_a in the latter halves of canonical gain gaps of length >=a>12, including the artificial endpoint T and its possibly unreached trailing gap. Write J_a=|I_a|, R=x-g_c>a/2, W=t_x-t_c, where c is the last actual canonical point strictly below the target gain x. The canonical point may be virtual inside a wait. For reached x, let g<x<=G be the crossing jump, t its actual pre-time, v its exit, t*=max(t,t_c), d*=2t*-(C_origin+g), d_i=2v-(C_origin+G), theta=(x-g)/(G-g). The previous hybrid overshoot correction was
    2 W_H=R-6+min(d_i,(1-theta)d*+theta d_i).
Index recorded completed poststates by i=1,...,n, including the actual terminal poststate, and d_0=6 at the root. Let
    m_i=min_(j>=i, j<=n) d_j.
It is a minimum on the original observed future only. The minimum over all true states after that exit is the same: between jumps the deficit increases by 2 at each tick.

For any recorded poststate j>=i, its elapsed time since c minus half its gain beyond x is exactly (R-6+d_j)/2. Hence each such *observed* future endpoint gives a further upper-accounting candidate at least (R-6)/2. Take the minimum with the previous two candidates. Define for a reached x
    D_*(x)=min(m_i,(1-theta)d*+theta d_i),
    W_*(x)=(R-6+D_*(x))/2.                                (1)
For unreached x leave W_*=W_H=W unchanged; use D_*(x)=d_n and M_x=x-G_n>0. For reached x put M_x=0. Then for every selected target
    2W_*=R-6+D_*(x)-M_x.
In particular for reached targets 0<(R-6)/2<=W_*<=W_H<=W. This is an accounting correction based on actual observed states; no artificial continuation or a fabricated physical state at gain x is used.

To implement on the original ticks, multiply the previous hybrid target-specific nonnegative weights by W_*/W_H on reached targets. The denominator is positive. Unreached targets retain the old weights even when W=0. The sums of weights equal W_*/R; every new weight is bounded by the old corresponding target weight. Hence the total new load on every original tag tick satisfies
    0<=omega_*<=omega_H<=omega_old<=1.
For any frozen union of earlier original linear masks, both paid and remaining weighted clocks are nonnegative and dominated pointwise. This holds also for partial-tick masks and the earlier relative strip masks. Do not recompute a trajectory, canonical gap, target, future minimum or load after deleting an accounting incidence.

Thus the new sufficient condition, under the same exposure and payment hypotheses as ac04602 (a->infinity, P(a)+B=o(T), beta_X(P(a)+a)/a->0 for the verified absolute payment rate beta_X), is
    liminf V_*,rem/J_a < 1/2
on an unbounded dyadic sequence with J_a>0. Alternatively J_a=0 infinitely often already contradicts the primorial exposure bound under no twins. At fixed a>12 use the exact lower budget B_a=sum_(I_a)(1/2-3/R) or threshold 1/2-6/a. The previous hybrid residual condition implies the new one for the same frozen masks and targets. We have not shown strict implication on actual MIN paths, nor proved the new inequality.

## 2. Completed canonical gaps no longer have positive excess

For any target in a canonical gap with an actual subsequent canonical endpoint at gain h>=x, the crossing poststate occurs no later than that endpoint's time. If the endpoint is virtual within a wait, the recorded arrival at its horizon has deficit <=6. If it is a recorded poststate, its deficit is 6. Consequently m_i<=6, and (1) gives
    (R-6)/2 <= W_* <= R/2.                                (2)
This includes a target exactly equal to the next canonical gain (c was defined strictly below x), and a canonical endpoint at the artificial partition boundary T or beyond it if observed. No need that the crossing event itself is RESET. In particular all positive excess above 1/2 of normalized reached clock is now confined to the trailing canonical-free part with no subsequent canonical point in the actual prefix. This is stronger than the preceding correction which only eliminated the excess at RESET crossing events. Equation (2) does NOT delete the baseline half-gain from one side of a sufficient inequality. It does not prove a lower bound on the number of trailing targets; the old exposure uses all selected gaps.

## 3. Exact terminal last-upcross layer decomposition

For any reached target define positive normalized excess in deficit units as (D_*(x)-6)_+/R (the clock excess is half this). For event i, define the half-open level interval
    I_i=(max(6,d_(i-1)), m_i] if m_i>max(6,d_(i-1)), empty otherwise,
    l_i=|I_i|.
The recorded d_(i-1) is the pre-deficit of event i; d_i its post-deficit. Because m_(i-1)=min(d_(i-1),m_i), we have
    l_i=(m_i-6)_+-(m_(i-1)-6)_+.
Here m_0=min(d_0,...,d_n)<=6. Thus the I_i are disjoint up to endpoints, their union is (6,d_n] if d_n>6, and they assign each such level to its LAST recorded upcross, after which it is never lost before the actual terminal. In particular
    0<=l_i<= (d_i-d_(i-1))_+ = (2w_i-(p_i-1))_+.
No first-upcross or common-birth assumption is used.

For a reached target crossing event j, D_*(x)>=m_(j-1) since both interpolated endpoints are >=m_(j-1), even if t* is a later virtual canonical start. Therefore
    (D_*(x)-6)_+ = sum_(i<j) l_i
                      + (D_*(x)-max(6,d_(j-1)))_+.        (3)
The last term is a partial interval of I_j. The lower endpoint remains the ORIGINAL pre-deficit, not the shortened-wait pre-deficit d*. This matters for virtual starts; (3) remains valid.

For every original tag and event i charge
    C_i=l_i sum_(selected reached x crossing a later event) 1/R_x
        + sum_(selected reached x crossing i)
                    (D_*(x)-max(6,d_(i-1)))_+/R_x.        (4)
The sum of C_i is EXACTLY the reached positive excess in deficit units, by finite Fubini. If l_i>0, all later true states from its departure have deficit>6 (m_i>6), so no actual subsequent canonical point is possible. Every target contributing to (4) belongs to one canonical gap: its c lies at or before the prehorizon of i, and there is no subsequent canonical endpoint. A virtual point before the jump in the same wait does not change that conclusion. The selected latter-half harmonic sum in this gap is <=1. Thus
    0<=C_i<=l_i<= (2w_i-(p_i-1))_+ <=2w_i.               (5)
This bound is per original tag-event, not per ordered pair or level count; it does not depend on how many targets are selected. It applies to all labels. If C_i>0, then d_i>6 and r(C)>(p_i-1)/4 by w_i<=2r. Therefore RESET endings and high events with r<=(p-1)/4 cannot create any such positive record charge. In the earlier full clock criterion those latter high events could still contribute substantial waiting time. Also C_i<=(4r-p+1)_+<=3p+1<=4p.

For a threshold lambda_0>=6, replace each level interval by its part above lambda_0, and the partial term in (4) accordingly. Call the new charge C_i(lambda_0). The omitted total reached excess is <=(lambda_0-6) sum_(I_a)1/R<=2(lambda_0-6)J_a/a. This permits lambda_0->infinity with lambda_0=o(a), at relative cost o(J_a), while every tag with positive charge keeps deficit>lambda_0 from that event's departure to its actual terminal. The audit tests lambda_0=6 only; the higher threshold statement follows by interval intersection.

If desired the charge of each event may be allocated at constant density C_i/w_i on its original waiting ticks, at most 2 by (5). This gives a nonnegative original tick accounting of the reached positive excess. Under this particular allocation any fixed previous partial linear mask can cover at most twice its absolute paid waiting clock. The charge is not the original waiting clock; its smallness cannot justify deleting the half-gain baseline. The exact signed identity for the new full objective is
    2V_* = J_a + E_+ - E_- +
                   sum_(unreached x) (d_n-6-M_x)/R_x,
where E_+=sum C_i and E_-=sum_(reached x)(6-D_*(x))_+/R_x. This identity explains what the record estimate controls. It does not independently estimate missing gain or prove the sufficient inequality.

## 4. Uniform positive-record support for all odd labels

Fix a selected prime p and initial eligibility sign sigma with p|(C+sigma). Positive charge implies r>(p-1)/4. Uniformly in 3<=p<=B, the number of possible initial horizons C in the original O(X) domain is
    S_p << X/[p log²(2+p)].                               (6)
Proof for sufficiently large p: write C=p(2b+1)-sigma. The quotient and other neighbor, 2b+1 and p(2b+1)-2sigma, avoid every odd prime <=z=floor(p^(1/40)) by the least eligible factor condition. The two forms have distinct roots at each odd sieving prime since p>z and the determinant is nonzero mod every odd prime. The dimension-two Selberg upper sieve with the explicit quadratic weights used in the previous unified four-form note gives O(X/(p log² p)+z^8); log z is comparable to log p. The error p^.2 is uniformly absorbed since X/p>>B and p<=B. For bounded p use the trivial single congruence count and enlarge the constant. Sum over the two signs. This does not use the natural HIGH predicate; positive drift itself forces the roughness needed by the sieve. We use the previous selected-prime support proof, not any lower bound for prime tuples.

For every positive-charge event its parity s is determined by the eligibility side, and its departure has the exact form
    d_i=6s+2p k,   v=(C+p-1+6s+2p k)/2.
Since d_i>6, k>=1 even for p=3. For fixed (C,p,k) there is at most one physical departure v. Group all original tag-event charges C_i(lambda_0) for the same departure slot, and set
    A_slot=sum C_i(lambda_0), n_eff=A_slot/(4p).
By (5), n_eff <= n_persist <= n_full: the number of tags contributing positive charge, and the full original slot mass, respectively. These may be very different; they are not pair multiplicities. The actual future from a common departure is deterministic, and each member may have a different original stop. Freeze all charges and membership before any payment.

## 5. A new thin persistent-charge budget

Let f(k)=1/[(k+1)(1+log(k+1))²], k>=1, so sum f(k)<infinity. Put
    m_all(p,k)=H log²(2+p) f(k)/(p u ell²),
    m_high(p,k)=H u² f(k)/(p ell²),   for p>=Q.
Use m=max(m_all,m_high) when both are defined, m_all otherwise. Pay the entire POSITIVE RECORD CHARGE of a slot when n_eff<=m. This is a charge-ledger payment, not a whole-event deletion or an estimate of projected pair energy. There is no condition on the full slot mass. From (6), sum_(p<=B)1/p=O(ell), and the summable phase index weight,
    sum_(n_eff<=m_all) A_slot
      << sum_(p,k) X/[p log²(2+p)] * 4p m_all(p,k)
       = O(XH/(u ell))=O(NT/ell).
Similarly for p>=Q, log p=Theta(u) and sum_(Q<=p<=B)1/p=O(ell/u), so
    sum_(n_eff<=m_high) A_slot = O(NT/ell).
Their union costs O(NT/ell). This includes all low and medium labels through m_all, and a stronger high cap through m_high. The formulas count actual charge, not the number of full occupied ticks. For slow a satisfying (P(a)+a)/(a ell)->0 and P+B=o(T), the budget is o(J_a) under no twins by the previous primorial exposure estimate. One may additionally pay prior actual-clock deletions in the charge ledger using (5) and avoid double counting. The result isolates large effective persistent charges; it is not a proof that their total is o(J_a).

## 6. Heavy charge forces a long common FORWARD high-deficit suffix

On a scale on which all original tags reach T (in particular under no twins for sufficiently large X), each contributing tag in a heavy slot has a distinct prime root M, whose target horizon is C_M+T=2M-2+T. Since its record event is completed, its prehorizon C<C_M+T, and its original terminal horizon is in [C_M+T,C_M+T+B]. For any z->infinity, the number of such target horizons in (C,C+z] is O(z/log z) by the uniform upper bound for primes in an interval, applied to the original roots. This is a bound on nearby END targets, not on the initial root age.

If n_eff>m and m is sufficiently large, choose z=c m log(2+m) with a fixed small absolute c so that this number is <=m/2. At most 2p m units of charge can come from those near endpoints, since each individual charge<=4p. The full slot charge is >4p m. Thus MORE THAN HALF of the charge, and more than m/2 distinct contributing tags, have target horizon>C+z. They all complete the same recorded jump, and the deterministic continuation from its poststate is identical until their respective actual stops. Each of them has min future deficit>lambda_0 by its positive charge. Therefore there is a common actual canonical-free suffix from the departure through a strict crossing of C+z if z>=p, with gain length at least z-(p-1), and deficit>lambda_0 throughout. At least m/2 original tags share that suffix; the gain-stop at their individual targets does not truncate it earlier. No claim about tags that stopped before T, or arbitrary continuation beyond any original stop. This is a no-twin structural consequence, not an unconditional reachability assertion.

For p>=Q and any fixed positive k, the high cap gives uniformly
    m >> B u^(7/4)/ell²,
    z >> B u^(11/4)/ell².
Uniformly for 1<=k<=sqrt(u) it gives
    m >> B u^(5/4)/ell^4,
    z >> B u^(9/4)/ell^4.
Thus for all such indices the required common future gain span eventually exceeds B u², even after subtracting the initial jump. This is a different obstruction from the previous lower bound on *backward* common ancestry of huge RESET cohorts: these are nonRESET positive-record events whose generated deficit level must persist through an extended future segment. We have no estimate bounding the total charge of these segments. For very large k the cap may be small and the forward lower bound correspondingly weak. The high statement uses p>=Q, regardless of the finite diagnostic high definition.

## 7. Audits and limitations

Source [min_unified_future_record_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/b06513471747c3bb6357d6220b3f0db6d6323a5c/research/min_unified_future_record_audit.mjs), commit b06513471747c3bb6357d6220b3f0db6d6323a5c, exact remote content readback. Executed the remotely obtained function after the tie-rule and focus-cap changes in the available ECMAScript runtime (not a separate Node process). Reproduce:
    node research/min_unified_future_record_audit.mjs 256 1024 4096 16384 65536

Eight final runs passed: five normal T=min(8B,floor(X/2)), a=max(13,ceil(B/2)), and three reach-focused T=max(16,floor(B/2)), a=max(13,ceil(B/8)) at X4096,16384,65536. Finite high p>=max(5,ceil(B/10)), r>3 and 2r>p, sample old clock mark w<=.2(p-1) or high RESET age>2p. Diagnostic record caps 2B/[p(k+1)] (normal) and .02B/[p(k+1)] (focus); NOT the analytic caps, and do not compare normal and focus as a single increasing mask. Checks original clock and phase, virtual canonical starts, exact future-min correction and hybrid lower bound, completed-gap ceiling, disjoint last-upcross partition, per-target level identity, exact record transpose, roughness/positive drift condition, dominated tick weights and paid/remaining transpose via difference arrays, common deterministic recorded suffix across persistent contributors and full slot mass inclusion. Focus uses reached-T members for the elementary root spacing and actual far terminal check. The original no-twin asymptotic prime-interval bound, lambda_0>6, and analytic sieve/caps are paper estimates, not finite tests. Literal gcd oracle and cumulative previous masks are not repeated.

| X/mode | hybrid remaining | future remaining | reached positive excess (deficit units) | persistent slots |
|---:|---:|---:|---:|---:|
|256|1250.618508|1236.080991|553.729992|66|
|1024|3857.836163|3831.528728|0|0|
|4096|36875.087398|36796.827312|1334.685013|86|
|16384|213516.354903|212605.373154|5889.743209|205|
|65536|1297511.942734|1294243.826278|10217.435883|314|
|4096 focus|11768.012174|11402.221330|7901.761717|584|
|16384 focus|75130.100425|73354.496647|50007.601072|2143|
|65536 focus|483497.740120|471370.018860|297924.393848|7009|

Largest normal: 5709 roots, 140255 completed events, 15078958 selected targets including 336572 reached and 315770 completed-gap targets, 2395330 tick checks, raw hybrid 1318438.598984 -> raw future 1315099.872269. Completed-gap correction credit2931.454788. Positive excess10217.435883 exactly equals record sum. 1392 positive tag-event contributions including133 diagnostic high,314 slots,137 with persistent count strictly below full slot mass. 310 thin and4 heavy at diagnostic cap; no root reaches T at this scale, so no forward all-reached test here. 92482 common suffix event comparisons. Maximum tick load .693055.

Largest focus: 2886 of5709 roots reach T, 75256 completed events,854818 targets,483514 reached,144256 complete-gap targets. 207735 positive targets,14906 positive tag-event contributions including1749 diagnostic high,7009 slots including1016 partial-membership slots. 3529 thin,3480 heavy,3048 heavy with at least one reached-T contributor. Max observed actual forward terminal distance802 gain among those heavy groups (not the analytic z lower bound). 65916 common suffix comparisons and1238683 tick checks. Future correction is nontrivial in both modes. Finite ratios with many unreached targets do not verify the asymptotic sufficient condition.

The new certificate removes complete-gap positive excess, not all reached baseline clock. A small positive-record total alone would not prove twin infinitude. The remaining open task is a genuine arithmetic/occupation estimate on heavy persistent record slots and the residual baseline/tail clock sufficient inequality; not merely the equivalent missing-gain identity. Main and independent branches untouched; no external novelty claim or Lean verification.
