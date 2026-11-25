# Overshoot-corrected canonical target certificate

2026-11-26 JST. Continues ac0460216f5f4478b17e051af01debada1d4d565 (canonical target certificate). Original ensemble, selected latter-half targets I_a, target count J_a, canonical c_x strictly below x, R=x-g_c>a/2>6, target-prefix elapsed W=t_x-t_c, and original bounded tick loads are unchanged. Independent heads checked unchanged: 1a4005f2f336 and e1ad9e2b434c. No Lean verification or twin-prime proof.

## 1. Two valid corrections

For a reached target x let g<x<=G be its crossing event's pre- and postgain, v its actual exit, t its actual arrival. Put t*=max(t,t_c), w*=v-t*, lambda=(x-g)/(G-g). If t_c>t then its canonical point is inside this same wait at gain g. Let d*=2t*-(C_origin+g) and d+=2v-(C_origin+G); both nonnegative. For all reached targets define
    W_I=W-(1-lambda)w*,
    W_A=W-(G-x)/2.
The first is fractional clock accounting on the last event, not an actual intermediate MIN state. The second is the gain overshoot subtraction. Exactly
    2 W_I=R-6+(1-lambda)d*+lambda d+,
    2 W_A=R-6+d+.
Both are >=(R-6)/2>0 and <=W. Set W_H=min(W_I,W_A). For unreached targets leave W_H=W_I=W_A=W, with G the original final gain and d+ the original terminal deficit. Never extrapolate a path. Thus define
    D_eff=min(d+, (1-lambda)d*+lambda d+) for reached targets,
    D_eff=d+ for unreached targets,
    M_x=max(0,x-G).
Then for ALL selected targets
    2W_H=R-6+D_eff-M_x.
In particular on reached targets whose crossing event is an even RESET, W_H=(R-6)/2 exactly; for odd RESET its excess over (R-6)/2 is <=3. For a single canonical-to-canonical event with both adjusted endpoints of deficit 6, W_H=R/2 exactly (including virtual initial points if applicable; the condition on the final endpoint is explicit).

## 2. Nonnegative dominated tick accounting

Freeze the chosen scheme for every target on original paths. In interpolation mode weight all actual tail ticks by 1/R except those of the crossing event from t* through v-1, weighted lambda/R. In arithmetic mode weight every actual tail tick by W_A/(W R); this factor is in [0,1/R]. For unreached targets use the original weight 1/R on the actual tail. Sum over targets to obtain omega_H on original actual ticks. Pointwise 0<=omega_H<=omega_old<=1. The total V_H=sum omega_H=sum W_H/R. For ANY fixed earlier union of original linear masks the new paid and remaining sums are nonnegative and no larger than their corresponding old sums, even for partial ticks. Old paid absolute bound beta_X NT transfers without modification via the preceding primorial exposure lemma, under P(a)+B=o(T), beta_X(P(a)+a)/a->0, a->infinity. On all-reached scales V_H>=(1/2-6/a)J_a. Consequently liminf V_H,rem/J_a<1/2 along an unbounded dyadic sequence (J_a>0, or zero infinitely often) implies infinitely many twins. At fixed a>12 use exact budget B_a=sum(1/2-3/R) or threshold 1/2-6/a. This criterion is implied by the old normalized residual criterion for identical masks/targets, without a claim of strict implication on actual MIN paths. The earlier relative terminal-strip budget still holds since its weights are dominated pointwise. One can also choose the scheme minimizing the remaining clock separately per target after a fixed mask, rather than minimizing the full clock, preserving the lower bound and domination. That optional version was not audited.

## 3. Exact excess/missing-gain balance and RESET targets

Put D=sum D_eff/R, M=sum M_x/R, H_a=sum 1/R, all over selected targets. Exact 2V_H=J_a-6H_a+D-M. Under no twins all targets reached for sufficiently large X, so M=0 and D>=0. Thus the sufficient condition is equivalently a positive normalized gap between missing gain and effective deficit, up to the known paid and harmonic errors. This is an identity, not an independent estimate of M or D. Reached RESET targets contribute at most 6/R to D and hence at most 12/a per target. They can have very large unweighted original waiting time and arbitrary full original cohort size. Their baseline half-gain contribution cannot simply be deleted from only the numerator. Removing them from BOTH sides would require a new exposure bound on the complementary target set; no such bound is claimed.

## 4. Quantitative overshoot improvement on few-event gaps

Consider a fully reached selected canonical gain gap of length L>=a, m=ceil(L/2) selected targets. Suppose their crossing events number at most k; partition the m targets by crossing event, counts m_i. In each event the integer target gains are consecutive, so the sum of G-x over those targets is >=m_i(m_i-1)/2, even if G exceeds the gap boundary. Since R<=L, the arithmetic correction in the normalized clock is at least sum_i m_i(m_i-1)/(4L). Cauchy gives
    V_old(gap)-V_H(gap) >= m^2/(4L k)-m/(4L)
                         >= m/(8k)-m/(4a).
Sum over such gaps; if a->infinity and a fixed k sector has a positive fraction of all selected targets, its overshoot credit is a positive fraction of J_a. This estimate is on raw clocks; for residual improvement subtract at most the old paid normalized clock, o(J_a) under the old budget transfer hypothesis. No lower bound on the fraction of such gaps is asserted. The formula removes a specific discretization cost even when the corresponding physical cohorts are huge. The one-event neutral case illustrates the exact cancellation; it is not claimed that a positive fraction of actual MIN trajectories has this form asymptotically.

## 5. Finite tests

Executed six ECMAScript diagnostic runs in tool runtime (not separate Node). Same target selection and sample masks as the parent audit (T=min(8B,X/2), a=max(13,ceil(B/2)) or stress ceil(B/8), Q=max(5,ceil(B/10)), high r>3,2r>p, mark actual w<=.2(p-1) or high RESET age>2p). All assertions passed: literal gcd on small X; virtual canonical points; two deficit identities and hybrid reached lower bound, unreached deficit; nonnegative original tick weights dominated by old weights; direct target sum and transposed tick sums including sample paid subset; exact global effective-deficit/missing-gain identity; residual domination. At X65536 normal: 15078958 targets,336572 reached,14742386 unreached; 9331 strict interpolation wins,287620 strict arithmetic wins,39621 ties. 308792 reached RESET targets (125100 even RESET equality checks),6440 partial virtual starts. Old full normalized 1376729.084627, interpolated 1344969.227814, arithmetic 1318559.339191, hybrid 1318438.598984. Old remaining 1353449.487179, hybrid remaining 1297511.942734. Reached old 233271.482481 -> hybrid 174980.996838. 2395330 tick checks; max load .693055. Stress: 15340138 targets,597752 reached, old remaining 1524218.263451 -> hybrid remaining 1421354.219669. Earlier X256/1024/4096/16384 passed. The six runs use finite substitutes; most targets are unreached, so ratios do not verify the required asymptotic inequality. The optional per-target residual-minimum scheme and quantitative few-event improvement are paper deductions, not included in those runs. Audit source remote persistence failed in two attempts at time of writing; this note does not claim source readback. Full sufficient inequality remains open.