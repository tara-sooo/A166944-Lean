# Hypothetical infinite MIN worlds VIII: gain-charged inverse graph and unit-return source cost

2026-11-26 JST. Independent continuation of [1ca1058](https://github.com/tara-sooo/A166944-Lean/commit/1ca1058926f239104c7961d31d67d224fcef139e). Sources: [III exact clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), [IV low-only transducer](https://github.com/tara-sooo/A166944-Lean/blob/73a01303cbc6c0bc73fa053a1e4e3a6e3525f21a/research/infinite-orbit/low_relay.md), [V first-unit entry](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md), [VI signed recovery](https://github.com/tara-sooo/A166944-Lean/blob/00f533d998b0cc87f48850b95476e41583e68539/research/infinite-orbit/recovery_budget.md), [VII inverse graph](https://github.com/tara-sooo/A166944-Lean/blob/1ca1058926f239104c7961d31d67d224fcef139e/research/infinite-orbit/deep_inverse.md). Sibling preflight direct [26ada2c height-localized flux](https://github.com/tara-sooo/A166944-Lean/blob/26ada2c8c9c572aefa93941460ff1625e785f7e8/research/2026-11-26-min-direct-height-localized-flux-and-sparse-support.md), unified [a0eb99b reset reverse support](https://github.com/tara-sooo/A166944-Lean/blob/a0eb99b0cdf6faf86902ebe4679adac0a7063ee4/research/2026-11-26-min-unified-reset-reverse-support.md). The new reverse graph includes arbitrary medium, short-high and out-of-band high events between designated long highs, charging actual gained horizon length. Paper deductions plus finite actual MIN diagnostics, not Lean verification or external novelty claims.

## 1. Setting

Fix [X,lambda X), lambda>1, and a selected band [T,B], T>=eta sqrt X (fixed eta>0), B<=floor sqrt(lambda X+1). A good event is ANY actual complete adaptive MIN event with T<=p<=B and w>=p-2. Retain every good event in the list, not a further subset. All physical states obey H/2<=t<=3H+3 (canonical necessary envelope). Other initial states in that envelope are also admissible for the local inverse calculation. Good events have positive adjusted multiplier h=(d'-6s)/(2p)>=1 for T>=11; d'=2t'-H', s=t' mod2.

Fix integer R>=3, R<T and H+1>=R². Low labels p<=R have exact maximum contiguous gain M=M_R as in IV; elapsed time of any event <=3g, g=p-1. Write r_R for the least odd prime >R. For non-good events, define medium R<p<T, bad high p>=T (including p>B and short clocks). Their actual gains are U_m,U_h. Set
    c_m=1+M/(r_R-1), c_h=1+M/(T-1), c=max(c_m,c_h).
Every pair of consecutive good events in the selected list has a unique intervening relay (all non-good events, possibly none), with physical gain E, elapsed ticks b. The low parts are at most 1+n_m+n_h runs, each gain<=M, so
    E<=M+c_m U_m+c_h U_h,     0<=b<=3E.                 (1)
This is an upper bound on a specific physical relay; the actual list and all competition remain unchanged.

## 2. Reverse enumeration for arbitrary relay gain

Given target good POST state (J,n), use VII's exact inverse:
    s=n mod2; p | gcd(J+2s,n-2s);
    H=J-p+1; p eligible on side s at H;
    l=max(p-2,n-(3H+3)), u=min(W_n,n-H/2),
where W_n is the minimum of the previous strict clock gaps, including 2p, and a smaller tied label at n invalidates the candidate. The condition l<=u is necessary and sufficient for some admissible start t=n-w, w in [l,u]. The previous good post-state must have J0=H-E. Since its own arrival is on a clock, for each possible prior side s0 its good label r divides J0+2s0 and its time n0 is a side-s0 clock modulo 2r.

For a FIXED even E>=0, b may vary with all medium, low and bad-high events. Instead of enumerating their words, use the interval
    n-u-3E <= n0 <= n-l.                               (2)
It has length at most 2B+3E. Enumerate possible n0 on each candidate prior clock. Verify (i) the prior post-state has at least one exact feasible incoming good event by VII, (ii) from (J0,n0) run actual deterministic MIN until H, with no intervening good event, rejecting an overshoot, stop or incorrect time, (iii) the actual next good event arrives precisely at (J,n). This test is necessary and sufficient for an edge of the compressed good-state graph with relay gain E. Each endpoint is a feasible intermediate physical state; no claim about ancestry unless separately verified. Deduplicate prior states for each E and target.

For sufficiently large X, each of J+2s and J0+2s0 is O_lambda(X), hence has at most two distinct prime divisors >=T since T³>>X. Thus at most two current labels, two prior sides and two prior labels per side. Each clock contributes at most 1+floor((2B+3E)/(2T)) candidate times. The number of actual reverse edges at any target with this particular E is therefore at most
    8(1+B/T+3E/(2T)) <= C(1+E/T), C=8(1+B/T).         (3)
Here B/T>=1, and C is uniformly bounded in X. This counts exact physical predecessor states, not the O(B) possible starting times of the last event, and not the number of relay words. Since E is even, all relay gains <=A give at most
    C (floor(A/2)+1)(1+A/T)
predecessors. This bound remains valid if the band has B<=2T and if no cap on the adjusted multiplier is imposed. The cost-sensitive enumeration is exact for any finite A and contains VII's fixed-low-only case. Equation (3) is an overestimate on degree, not an asymptotic count of actual reverse states.

## 3. Depth and total interruption budget

Consider j reverse edges from a fixed target, with summed medium and bad-high gains at most U_m,U_h. Summing (1) gives
    sum E_i <= S_j = M j+c_m U_m+c_h U_h.
The number of nonnegative even j-tuples with sum <=S_j is binom(floor(S_j/2)+j,j). For each such tuple, (3) gives at most C^j prod_i(1+E_i/T) possible reverse paths. AM-GM bounds the product by (1+S_j/(jT))^j. Consequently the number of reverse paths (and hence distinct possible earlier vertices) at depth j>=1 is bounded by
    A_j(S_j)=C^j binom(floor(S_j/2)+j,j)
                   (1+S_j/(jT))^j.                    (4)
For j=0 use A_0=1. Different paths reaching the same earlier vertex may be overcounted, which is harmless for an upper bound. No independence of residues or phases is needed. An equivalent budget uses U=U_m+U_h and S_j=M j+c U.

Take original canonical odd roots H0=2M0-2, H0=0 mod4, initial d=6. Restrict to those whose FIRST designated good event has pre-displacement E0<=D0 and adjusted multiplier 1. For D0=o(T), all such shallow first entries automatically have h=1 by V, with no restriction on earlier labels. More generally explicitly requiring first h=1 suffices even for large finite D0. At a unit post-state d'-6s=2p identifies its label, hence its pre-H, and at most m0=floor(D0/4)+1 original roots can have their first good event there. Every root has a unique deterministic path. Counting at most k good events including the first, the number of original sources reaching one target within total interruption budget U AFTER first good is at most
    m0 [1+sum_(j=1)^(k-1) A_j(M j+cU)].                (5)
Separate U_m,U_h budgets may instead be used. This generalizes VII's pure low relay degree estimate; no requirement that later good states have bounded multipliers. It does not bound all canonical histories with large first-entry displacement or unlimited numbers of good events.

For fixed R,lambda,eta, (4), binom(n,j)<=(e n/j)^j and monotonicity of j log(1+u/j) yield the coarser convenient estimate
    log(number/m0) <= log k
       + O_(R,lambda,eta)(k)
       + k log(1+U/k) + k log(1+U/(kT)),              (6)
for k>=1 (if number=0 interpret the bound as trivial). Constants may be absorbed in the O(k) term; for example the factors c,M from S_j are bounded. Thus for D0=X^o(1), U=O(k), k=o(log X), the source count is X^o(1). With U polylogarithmic, the same conclusion holds for k=o(log X/loglog X). The more precise sufficient condition is k[1+log(1+U/k)+log(1+U/(kT))]=o(log X). A polynomial-sized cohort cannot be produced in this history class without either more good events, larger paid relay gain, or greater first-entry displacement. This is only a submacroscopic information bound; it does not force an NT-scale loss.

## 4. Narrow-band unit return requires paid gain

There is a stronger conclusion for unit target states, without using the reverse-path enumeration. Take any consecutive sublist of k>=2 good events in the band, with actual relays including arbitrary interruptions, from just AFTER the first good to just AFTER the last. Denote their labels p_i, post-deficits d_i'=2h_i p_i+6s_i. On this interval the low gain is <=M[(k-1)+n_m+n_h]. Good event increments are >=p_i-3 and non-good increments >=-g. Summing with the ACTUAL endpoints gives
    c_m U_m+c_h U_h >= d_1'-d_k'+sum_(i=2)^k(p_i-3-M). (7)
No leading/trailing low part outside the displayed interval is charged. This is the signed ledger from VI with exact endpoints, but sharper for relative multiplier return. If h_k<=a for an integer a>=1, use d_1'>=2h_1 p_1 and d_k'<=2a p_k+6:
    c_m U_m+c_h U_h
       >=2h_1 p_1-(2a-1)p_k-(M+9)
                 +(k-2)(T-3-M).                       (8)
In particular assume T>3+M and B<2T-M-9. Then for a=1 (a unit target) and h_1>=1, the lower bound is at least
    tau = 2T-B-M-9 > 0.                               (9)
For fixed R and B<=(2-eps)T with fixed eps>0, tau>=eps T-O_R(1). Thus ANY unit good state which is not the first good in this band requires Omega_R,eps(T) intervening medium or bad-high gain since the first good. No assumption of bounded h in between, no small complement assumption, no ancestry requirement. With U=0, two unit good visits are impossible in this band for large T. A short or out-of-band high itself can pay this cost; the result does not exclude such events.

Sum (9) over consecutive UNIT good visits on a single actual path, allowing any number of nonunit goods between them. The intervals are disjoint (shared endpoint states, no shared events). If N_1 is the unit good count, F_1 their gain, then
    c_m U_m+c_h U_h >= tau (N_1-1)_+
                      >= tau (F_1/(B-1)-1)_+.          (10)
For fixed R, B/T<=2-eps and T~sqrt X this gives a proportional physical bad-gain cost for macroscopic unit good supply. It also applies over complete original tag paths by summing once per tag and keeping the one boundary term per tag. It is not a separate extra cost to add to the same signed ledger of VI. The proof uses w>=p-2, not the weaker positive excess 4w>=g in unified. No conclusion is asserted for arbitrary medium labels that may not have strong positive ordinary drift.

## 5. A target-specific cohort inequality

Let v be one unit good post-state. Consider m distinct canonical source tags reaching v at a good event, with each tag's FIRST designated good event in this window starting at displacement E0<=D0 from its original root. For the first-entry condition here no assumption that first h=1 is necessary: every good has h>=1, so (8) applies regardless. At most m0=floor(D0/4)+1 of these tags can reach v as their first good, by the exact unit post-state inverse (even for D0 not o(T)). Every other tag has a preceding good and pays at least tau in (9) from its first good post-state to v. Therefore
    sum_over_tags(c_m U_m(tag)+c_h U_h(tag))
         >= tau (m-m0)_+.                              (11)
In particular the mean bad gain per source is >=(tau/c)(1-m0/m)_+. This bound is independent of the number of good events in their prefixes, including deep states, and is positive for a cohort of size much larger than its direct first-entry fan. For example with B<=1.5T, fixed R=3,M=4,r_R=5, tau>=T/2-13 and c_m=2, c_h=1+4/(T-1). A polynomial-sized unit cohort with polylogarithmic first-entry displacement pays Omega(T) bad gain per tag even if its good depth is arbitrarily large. This is stronger in this specific unit/narrow-band case than inferring a bad-gain requirement from (6).

This is a per-TARGET tagged statement, not a bound on distinct physical gain: if six tags already share a physical relay, all six pay its tagged cost. That is the actual multiplicity convention in unified. Do not sum (11) over arbitrary target states without verifying disjoint charged intervals along each tag. Equation (10) is one disjoint way to aggregate. The cost could be submacroscopic compared with the short lifetime X/polylog, and shallow first-entry fans, deep target states and weak/short high populations still leave alternatives. Neither (5) nor (11) bounds the entire original ensemble's omitted waiting measure or proves an NT-scale gap.

## 6. Reproducible finite diagnostics

[Final audit e57d676](https://github.com/tara-sooo/A166944-Lean/blob/e57d6768d1dd410abdd39005cefb98522071f4f2/research/infinite-orbit/charged_reverse_audit.mjs), blob932a723f165c7f062e8e5f4921653fe2d025b335, exact remote readback. Run node research/infinite-orbit/charged_reverse_audit.mjs. Actual ECMAScript function executed in available tool runtime, not separate Node. Final assertions passed. Windows X=4096,16384,65536, pre H in [X,4X), T=ceil(sqrt X/2), B=floor(1.5T) or floor sqrt(4X+1), R=3 or7 (skip R7 at X4096 since T<=M+3); no endpoint safety restriction. All 64512 canonical roots H0=0 mod4 in those windows, plus 4608 targeted actual long first-clock states with prescribed h in {1,2,4,8} in the envelope (arbitrary intermediate states, not established canonical ancestry). 1,503,465 event incidences, no unresolved 3000-event cap.

- 20,391 good-pair controls and 900 unit-return incidences, including 188 positive pointwise lower demands in (8); 900 disjoint consecutive unit-return checks. Counts overlap across R and bands, not distinct paths.
- 283 sampled exact reverse enumerations with physical relay gain <=128 and actual forward predecessor inclusion, 384 returned predecessor incidences. 18,395 per-fixed-E degree checks (including empty E layers). On 20 sampled targets, independently enumerate all prior integer times in (2) and compare full sets, exact agreement. Largest observed reverse set size 4. This is an exact finite bound on each tested target's bounded-relay predecessors, not an exhaustive global maximum.
- 3398 canonical physical-state/configuration group controls with first entry <=32 and first multiplier1 for the source-capacity test. 46,948 nonempty budget/depth capacity checks (U=0,16,64,256; k<=1,2,4,8), 2755 unit target cost checks. The capacity uses analytic upper bound (4), not a tight estimate of actual multiplicity.

Selected results for R=3:
| X | band | max tested reverse set (E<=128) | max source mult. (first entry<=32, first h=1) | max unit mult. | unit returns (all starts) |
|---:|---|---:|---:|---:|---:|
|4096|[32,48]|2|8|8|0|
|4096|[32,128]|4|14|9|0|
|16384|[64,96]|2|15|15|12|
|16384|[64,256]|3|17|15|57|
|65536|[128,192]|2|13|9|0|
|65536|[128,512]|2|32|21|381|

Actual canonical example X=16384, T=64,B=96,R=3,M=4,D0=32,m0=9,tau=19. Unit target v=(53466,26800), side0,p=67,d'=134. Fifteen distinct canonical starting horizons in the audited restricted history class reach v. Nine have first good at pre-H=53400 (roots 53368,53372,...,53400, i.e. every fourth horizon). Six earlier roots 53044,53048,53052,53060,53064,53068 have first good post-state (53142,26647), p=73,h=1, then the same actual relay to target. Each of those six has medium gain112 and bad-high gain138, total250; weighted cost per tag 2*112+(1+4/63)*138=370.7619..., aggregate2224.5714... for those six (the other nine have zero post-entry cost). Inequality (11) demands at least 19*(15-9)=114, and the exact pair endpoint lower (8) demands >=66 per returning tag. This is a genuine example from canonical roots, not just an admissible intermediate-state collision. It also exhibits why initial-root multiplicity and physical reverse degree differ. No inference that every other cohort has the same cost, or that a finite sampled minimum is a uniform theorem.

## 7. Residual world

Arbitrary interruptions now have an exact reverse-graph cost, and a shallow unit cohort in a narrow high-label band cannot form solely by cheap repeated good entries. The model still permits a deep multiplier population with large cumulative gain, many weak/short high events, or long/expensive precursor histories. Future work: connect the gain-charged graph to actual first-large cohort weights in unified, use label-band changes and signed flux to prevent low-cost repeated large-cohort creation, and study high-deficit paths without unit targets. No full all-constraint infinite model, uniform uncapped mixed-run bound, Lean verification, or finite-twin contradiction. Main and sibling branches not modified.
