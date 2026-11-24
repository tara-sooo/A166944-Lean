# Height-adaptive physical stopping and a local-band passage budget

2026-11-25 JST. Continues 53fad303653461b032fb04877b83645cffc661a4 on the SAME research/min-cycle-forest-2026-11-24 branch. New optional accounting rule and paper-level conditional global cost reduction, using the previously established per-prime sieve and finite-time averaged clipped potential. Also an independent exact characterization of universal LOW barriers. Exact finite diagnostics. No Lean compilation; neither the LOW potential coefficient nor the global physical far-coalescence upper bound is proved. No new external literature search.

## 1. Use a height-adaptive cap only at actual physical states

Canonical MIN as before: N=X/2 odd original sources M in [X,2X), initial h=2t-C=6, B=ceil(sqrt(7X)), individual K(M)=floor((7M-1)/4). Executed p<=B, wait w<=2r(C), r<=p<=1.5(p-1), h'=h+2w-(p-1)>=0. All actual times and horizons have range O(X); in particular h+1<=8X in the canonical window for large X. Each source executes total gain O(X), hence its entire r-cost is O(X) uniformly, even after arbitrary truncation.

Let H0>=6 be an integer growing slowly, T0=ceil(B log^2 B), and integer a>=1 with a<=T0. Define
    T(h)=T0, h<=H0;
    T(h)=min(T0,ceil(a sqrt(8X/(h+1)))), h>H0.
At every attained physical V(t,C), stop ALL active tags there if their total mass is >=T(h). Process by increasing horizon, so all arrivals and root injections are included in each test. No other stops are necessary for this new route. It can also be combined with a group-wide stop of mass >=T0 at an anchor arrival, but this is not needed or used below. This REPLACES the preceding optional low/anchor-only rule by a stronger height-adaptive physical cap; it is not an estimate under the unchanged cap. Original individual cutoffs and MIN choices are unchanged. Every stopped group is a single actual state, and every stop has mass >=a. Denote total stopped mass by S_stop, executed cost by R.

At every event landing at a group that continues (including a natural terminal if its mass was below the cap), the event incidence count is <T(h'). A final event landing at an accounting stop may have much larger mass, but every source has at most one such event, so their TOTAL cost R_stopedge<=B S_stop<=BN. Exclude these last events in all subsequent continued-landing counts. This argument avoids assuming a cap on the final incoming event itself, or on the projected key after summing over clocks.

## 2. Unconditional cost below a macroscopic height threshold

Use the established uniform per-prime sieve cost S_p=sum_(eligible even C in the O(X) window) r(C)=O(X/log^2 p), including p=3,5,7 with adjusted absolute constant. At fixed projected (p,C), the actual event time n belongs to one residue class modulo 2p, and h'=2n-(C+p-1) increases by 4p on that clock progression. For an arrival-height interval of width u, there are O(1+u/p) possible n. The unweighted r-cost sum over such candidate physical event keys is therefore
    O(X sum_(p<=B prime)(1+u/p)/log^2 p)
     = O(X [B/log^3 B + u+1]).
This uses sum_(p>=3)1/(p log^2 p)<infinity. The estimate holds at arbitrary band position; no distribution of actual arrival heights is assumed.

Let Q=floor(epsilon X) with 0<epsilon<=1, Q>H0+1. The cost of all continued arrivals with h'<=H0 is
    O(T0 X [B/log^3 B + H0+1]).
For H0<h'<Q partition h'+1 into dyadic bands [u,2u). The width is <=u, and the cap on a continuing landing in this band is <=O(a sqrt(X/u)); the ceiling is harmless because the actual band lies in [1,8X] and a>=1. Multiply the preceding count by this cap and sum over dyadic u<=Q+1. Geometric series give
    sum u^(-1/2)=O(1), sum u^(1/2)=O(sqrt Q)
(the former can be further reduced to O(1/sqrt(H0+1)), not needed). Hence
    R_cont,<Q <= O(T0 X [B/log^3 B + H0+1]
                 + a X sqrt(X)[B/log^3 B + sqrt Q]).
Dividing by X^2 and using X asymp B^2 gives
    R_cont,<Q/X^2 <= O(1/log B + (H0+1)log^2 B/B
                        + a/log^3 B + a sqrt(epsilon)).
All labels are included, not only small-relative p<h/D. In particular this removes the earlier residual at low and intermediate attained heights under the new physical cap. No LOW probability convergence, no cell or projected-key stopping, no assumption about root weights or their phase distribution. This is an unconditional estimate only for the cost of continuing arrivals below Q, not for all cost.

## 3. Local-band first passage instead of tracking full low-to-high ascent

Take the same finite-time averaged clipped correction F(C,t)=(1/(S_time+1)) sum_(T=S_time..2S_time) min(K,D_(Y,T)(C,t)) from research/2026-11-25-min-ghost-finite-time-averaged-clipped-potential.md. Here Y>=P>=11, 2P<=S_time, 0<=K<=S_time, L=2 product_(3<=p<Y prime)p, and 0<=F<=K. Let Phi=h+F and
    eta=P[mu+K/(S_time+1)] + 1/log^2 P
          + sum_(q>=Y prime)(K-q+1)_+/q^2,
    mu=Pr_uniform phase rectangle(D_(Y,2S_time)>K).
The previously proved pointwise positive leakage for p<P is <=4P 1{D_(Y,2S_time)>K}+2P K/(S_time+1); for P<=p<Y it is <=6r; for p>=Y it is <=4r+(K-p+1)_+. We use those paper deductions, not a claim that eta tends to zero.

Suppose Q>=max(32B,8(K+6),L,4(H0+1)). Let Z_Q count distinct original tags which attain a height >=Q at a CONTINUING group (i.e. not stopped at that state), before their natural cutoff or accounting stop. Their first such passage cannot have an earlier stopped state. Since positive height jumps are <=4B, for each such tag take the last entry into height >=Q/2 before its first attainment >=Q. The entry height is in [Q/2,Q/2+4B], and is strictly below Q. From that entry through the hitting step all pre-heights lie in [Q/2,Q), every landing continues and has height in [Q/2,Q+4B]. (Using last entry avoids excursions below Q/2.) All these pre-states and physical event incidences therefore have cap O(a/sqrt(epsilon)), including the hitting step, irrespective of the mass at earlier lower heights. Initial Phi on this segment <=Q/2+4B+K, final Phi>=Q. Thus each segment requires at least Q/4 total positive corrected increment by the stipulated Q inequalities. No per-source cost prior to the band is charged here.

For p<P count ALL candidate pre-states in the height band, O(XQ/L^2) per phase pair because Q>=L and X>=L. Multiply the pointwise clipped leakage by their incidence cap O(a/sqrt(epsilon)), then sum over phase pairs. For p>=P count candidate matching clocks from the pre-height band and wait<=2p: O(1+Q/p)=O(Q/p), since Q>=32B>=p. The incidence cap may be applied at the continuing landing. Per-prime sieve bounds then give r-cost O((a/sqrt(epsilon))XQ/log^2 P). The high correction excess is O((a/sqrt(epsilon))XQ sum_(q>=Y)(K-q+1)_+/q^2) using O(X/q) eligible prehorizons. Sum the three bounds and divide by Q/4:
    Z_Q <= O(a X eta/sqrt(epsilon)).
This is a local-band version of the prior small-incidence first-passage theorem: no uniform cap on the whole root-to-passage history is required. In particular the potentially very large cap T0 at low heights does NOT multiply eta. The Q-scale height requirement is essential for this proof; do not use it with Q of order B or smaller.

Every continued arrival with height >=Q belongs to one of these Z_Q tags. Each tag has total executed r-cost O(X), so the entire high-arrival cost is <=O(X Z_Q). Together with sections1-2,
    R/X^2 <= O(1/log B + (H0+1)log^2 B/B + a/log^3 B
                 + a sqrt(epsilon) + a eta/sqrt(epsilon) + 1/B).
This is an unconditional parameter-dependent inequality, not an unconditional o(X^2) conclusion. It applies under the NEW cap and does not imply the corresponding high-remainder bound under the previous low/anchor cap. It is the main new result: use raw arrival counting for small heights, and positive corrected-height counting only in a macroscopic band. No need to split the high remainder into every possible giant/long/small-relative event.

## 4. Conditional physical-only route and a larger far-distance scale at stops

Suppose the unresolved finite-time infinite-CRT signed-peak condition gives eta->0 along a diverging sequence, as in the earlier diagonal argument. Choose Y(B) slowly along it with L<=log^(1/4) B and K<=Y-1 (using the earlier coupling construction), H0=floor((log log B)^(1/4)) eventually >=6, a->infinity sufficiently slowly that a<=log^(1/4) B and a^3 eta->0. Set epsilon=a^-4 and Q=floor(X/a^4). Then Q satisfies all section3 inequalities eventually. We get
    Z_Q=o(X), R=o(X^2).
On a no-twin canonical window the existing uniform cX cost lower bound per naturally unstopped original root gives
    S_stop=N-o(X).
This uses only actual physical stopping groups, not cell admissions, projected prime stops, or virtual terminal unions. Conditional eta is still required. A simpler small fixed physical mass cap would also give a conditional cost reduction; the adaptive profile here additionally retains the old T0 at low heights and makes most stopped groups much larger than a.

In fact every tag stopping at h>Q+4B must have attained a continuing h>=Q earlier, because the last positive height jump is <=4B, and root height is6. Thus their total mass is <=Z_Q=o(X). All other stop groups have T(h)>=min(T0, a sqrt(8X/(Q+4B+1))) for h>H0, or T0 below H0, hence mass >=c1 a^3 eventually for an absolute c1>0. In particular the number of such groups is O(X/a^3), and all but o(X) stopped mass lies in them. This is a stronger terminal size statement than the mere universal minimum a. It does not bound the total mass of stops, only how concentrated their actual physical groups are under eta.

Retain only tags ending in an accounting stop. Their full V/A event graph is non-splitting because identical physical states imply identical actual continuation for all such retained tags, and group-wide stopping cannot split them; source-specific natural cutoffs cannot intervene on their retained suffixes. Keep source injections as singleton donors. At each first physical merge v of m_v retained tags, count pairs from distinct incoming donor groups with origin distance |M-M'|>d, weighted by 1/m_v. Denote their total P_far^physical(d). This is a direct far-pair proxy on the full actual forest, not the earlier hat-kernel proxy on a compressed graph. Every pair in the same terminal physical group has a unique first common vertex with m_v<=m_terminal. Hence P_far dominates the sum over terminal groups of the number of their far pairs divided by terminal group mass. Distinct odd roots have spacing2, so each group of mass m has at most O(md) near pairs (distance <=d). The full unordered pair count divided by m is (m-1)/2. Restrict to groups with h<=Q+4B, whose mass is >=c1 a^3, and choose d=floor(a^2). The loss from near pairs and the -1/2 per group is O((d+1) X/a^3)=o(X). Therefore on no-twin windows, conditionally on eta,
    P_far^physical(floor(a^2)) >= N/2-o(X) = X/4-o(X).
A strictly smaller upper bound on this full-physical proxy along the same windows would suffice for contradiction. An upper bound on the weighted color or compressed hat proxy must not be substituted without a comparison proof. The advantage is that all stopped groups are already physical and almost all have a larger size than the basic representative cap a; no small cell-terminal-clock-class deletion is required. The principal unresolved mass/far-merger upper bound remains. The new rule may stop more mass than the preceding rule and it is not claimed to make the final anti-concentration estimate automatically easier.

## 5. Exact dense universal LOW barriers (independent deterministic observation)

For an odd prime p, on even horizons, the two eligible starts modulo 2p are C=p-1 and C=p+1. The p-jump has gain p-1. An even boundary J can be crossed (C<=J<C+p-1) from one of those starts precisely when J mod2p is in the even set {p-1,p+1,...,2p-2}. More explicitly the start p-1 crosses boundary residues p-1 through 2p-4, and the start p+1 crosses p+1 through 2p-2, both in steps of2. The union includes both endpoints and has (p+1)/2 residues. The SAFE residues are {0,2,...,p-3}, with (p-1)/2 elements. This is a characterization for the permissive graph of all eligible p-jumps, hence also a sufficient barrier for the actual MIN rule at any clock.

For all odd primes p<Y, L=2 product p, a universal LOW barrier J is exactly an even J satisfying those safe residues at every p<Y. By CRT the number per L-period is
    b_Y=product_(3<=p<Y)(p-1)/2.
Its density among even horizons is product (p-1)/(2p), and the mean distance between consecutive universal barriers is
    L/b_Y = 2 product_(3<=p<Y) 2p/(p-1).
By Mertens this is Theta(2^(# odd primes <Y) log Y), far smaller than L. If a new prime q>=Y is allowed, at a boundary J the number of projected q-crossing keys is exactly 0,1,2 with counts (q-1)/2,2,(q-3)/2 respectively among the q even residues mod2q; this is independent of the LOW-safe conditions over a common period Lq. The maximum barrier gap is at most L, but no asymptotic short-gap bound strong enough for the LOW probability condition is established. A run consisting only of labels <Y lies between consecutive universal barriers (right-closed cells) and has gain at most the corresponding gap and elapsed <=3 times that gap. This remains true at arbitrary height and with arbitrary mass. It improves the exact barrier geometry, but the mean gap over cells is NOT the mean gap seen by a source or by an adaptive arrival. In particular this observation is NOT used to prove the cost bounds in sections2-4 and does not prove eta->0. Using irregular universal cells instead of primorial-multiple cells is available for future work if arrival-weighted gap estimates can be obtained.

## 6. Finite replay and persistence

Saved research/min_height_adaptive_physical_cap_audit.mjs and research/min_height_adaptive_physical_cap_results.json with exact remote readback at f8e5d0cd646477faec9d790f8750d52c9a7bc516. X=4096,16384,65536,262144, H0=24, diagnostic T0=max(8,floor(B/4)), mode0 a4,Q=max(48,floor(B/2)); mode1 a8,Q=max(48,floor(1.5B)). Stop only at physical V by the profile above (no anchor or cell stop; optional diagnostic count of anchor witnesses). These finite parameters do NOT satisfy the Q>=32B hypothesis or asymptotic cap. Exact SPF and individual canonical cutoffs. Check every attained group cap and partition every executed cost by stop-edge, continued low arrival, continued middle arrival and continued high arrival. Check actual arrival event incidences and per-key dyadic-height clock counts, stop/natural mass conservation, stop-edge cost<=B S_stop, continued high cost <= total cost of tags with continuing hit, and per-tag cost<=11X. Use an exact small finite DP at Y7,L30,K8,S_time16 to compute F, and check local corrected-height passage identity on actual paths that enter the middle band before first continuing hit (large overshoots can skip the band in these diagnostic choices; such paths are not claimed to satisfy section3 lower Q/4). The recorded nontrivial passages satisfy positive lower Q-entryH-K. No evaluation of eta or of the asymptotic passage bound; no actual forest far proxy calculation this turn.

At X262144,N131072,B1355, mode0 Q677:11808 stopped tags, total cost97585966, stop-edge3534820, continued low40457700, middle25659008, high27934438. 30082 continuing hit tags;11697 local band passage checks of which11289 have strictly positive lower bound;357664 per-key/band clock checks. Mode1 Q2032:4436 stops, total104058378, stop-edge967569, low40842641, middle55738713, high6509455;6797 continuing hits,6057 local passage checks all with positive lower bound,358506 clock checks. Maximum attained height6150 in both modes. These are finite ledger checks only and the two modes change both cap and Q; no comparison of their asymptotic efficiency is inferred.

Separately enumerate every even J in the full L-period for Y5,7,11,13,17; for each p<Y count all eligible prehorizons crossing J, including negative prehorizons for residues near0, and compare with exact local gateway count. Verify CRT barrier counts and calculate gaps. At Y17 L30030,180 universal barriers, mean gap166.8333333333, min18,max438;75075 local checks. At Y13 L2310,30 barriers, mean77,max198. These complete-period computations do not establish a general max-gap or source-weighted mean-gap asymptotic. No Lean compilation.

## 7. Remaining work

The new physical-only cost route replaces the previous complicated small-relative remainder by the local-band positive-height coefficient eta, with a concrete unconditional low/middle-height cost saving and an adaptive cap independent of the LOW ghost. It conditionally concentrates stopped mass at large actual physical groups, but does not supply an upper bound on their far coalescence. Future work needs an actual estimate of eta or a direct bound on the local-band positive leakage, and a global far-pair upper bound at the new physical stops. The dense universal barrier identity by itself does not give either. No main edit, no new branch, no twin-prime proof.
