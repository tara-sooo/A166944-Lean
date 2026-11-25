# Truncated reset mass potential, first rank attainment, and unique thick ancestry near a prime start

2026-11-25 JST. Continuation of 9c62b7fbc0e4cb298f0cdbf7fa44f27be8e878f5 on the selected prime-root branch. Derive an absolute upper bound on the number of thick reset merger states and on the actual small incoming source memberships, with an exact first-attainment interpretation of the truncated potential. A new dyadic first-attainment age exclusion applies at the older crossing landing of EVERY first projected contact for high, and at shallow landings or nearby resets for actual medium. The two estimates combine to remove all thick branching in a polylogarithmic reset strip traversed by surviving thick high focal tags. This is a restriction on formation of large old fibres, not a general upper bound on their mass or the energy of arbitrarily long nonreset paths.

## 1. Original transport and a threshold potential

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) prime roots M in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, m_g=u^(19/4)/ell^4. Original gain-stopped physical histories and all prior ledgers unchanged. The genuine reset DAG of 9c62b7 has actual reset fibres A_v of size n_v, their continuing source suffix B_v of size m_v, and a unique successor of v when m_v>0. The sources in each B_v are the largest m_v sources in A_v. Original prime injection is a singleton with no incoming arc. All noninitial fibres partition into their actual incoming continuation sets. Sum_v(n_v-m_v)=N. Define n_M(e)=1+# larger actual original companions at physical vertex e of M. This is its descending source rank in the original physical fibre and is nondecreasing along its entire original path, by original stop order. In particular n_M(root)=1.

For an integer threshold m>=1 (distinct from the continuation count m_v) put f_m(n)=(n-m)_+. At a reset v define
    Delta_m(v)=f_m(n_v)-sum_{w: successor(w)=v} f_m(m_w),
    L_m(v)=f_m(n_v)-f_m(m_v).
Both are nonnegative: f_m is superadditive on nonnegative integers, and the original injection has f_m(1)=0. If v is not an injection,
    Delta_m(v)=sum_{w->v} min(m,m_w)-min(m,n_v).
Summing the actual arcs once gives
    sum_v Delta_m(v)=sum_v L_m(v)<=sum_v(n_v-m_v)=N.       (1)
This is uniform in the threshold, the number of actual reset visits and lengths of renewal intervals.

There is a stronger exact interpretation. Since B_w is a descending-rank prefix (in the largest-first order) of A_w, every continuing source keeps precisely its rank within B_w from A_w. Hence f_m(m_w) counts the incoming sources whose rank already exceeded m at their previous reset. At v ranks can only increase. Therefore Delta_m(v) is exactly the number of original tags for which v is their FIRST genuine reset with n_M(v)>m. L_m(v) is exactly the number of exiting tags with n_M(v)>m at their last reset. Each such tag is counted once on each side. A physical rank may have exceeded the threshold earlier at a nonreset vertex; (1) uses the first RESET attainment, not first physical attainment. This gives an independent source-by-source verification of the transport identity.

## 2. Actual thick merger and small-inflow bounds

At a reset with n_v>=2m call an actual incoming continuation cohort thick when m_w>=m. Define:
- A: no thick incoming cohort;
- B: at least two thick incoming cohorts;
- C: exactly one thick incoming cohort.

For type A all incoming masses are below m, and Delta_m=n_v-m>=n_v/2>=m. Thus #A<=N/m and sum_{A} n_v<=2N. In particular arbitrarily large A fibres cannot occur at many reset states, regardless of their previous renewal spans.

For type B with k_v>=2 thick parents, Delta_m(v)>=(k_v-1)m. More precisely if at least one thick parent is present and n_v>=2m, Delta_m(v)=(k_v-1)m+sum_{small incoming}m_w. Consequently
    #A + sum_{B}(k_v-1) <= N/m,
    sum_{n_v>=2m} sum_{small incoming} m_w <=2N.           (2)
The second bound counts actual incoming tag memberships, including all tags of type A. For a fibre with a thick incoming parent, the sum of the small incoming masses is paid directly by Delta_m, and for A it is at most 2 Delta_m. These estimates do not require a small upper bound on any individual thick parent. They are bounds on actual branching keys and tag inflows, not counts of relaxed arithmetic states. Even a source that visits many resets cannot defeat the fixed-threshold budget.

In particular, there are <=N/m large-fibre reset states with either no thick predecessor or multiple thick predecessors; and total original membership of all-small births is <=2N. At every other large fibre, its actual input is one thick branch plus small inflows. The sum of the latter over all such fibres is <=N. This is an upper bound on creation complexity, not a claim that the old dominant branch is small.

## 3. First dyadic rank attainment: absolute whole-pair exclusions

Use the uniform whole unordered pair envelopes U_H=3H, U_M=C_med H/m_g, including both actual directed medium charges, arbitrary previously retained holes or fractional payments. Set L_H=B u^1.5, L_M=m_g/u^.25; N U_H L_H=O(F/u^.25), N U_M L_M=O(NT/u^.25).

For any M<M' with first common projected horizon, let C0'=2M'-2 and D be the unique older crossing landing of x=C0'-1. Then 0<=D-C0'=2i<=B, with i the landing offset. At older physical vertex e at D put j=floor(log2 n_M(e)). Let a be the FIRST original physical vertex on M with n_M>=2^j. Monotonicity ensures a exists and is unique. As j varies each source has O(log N)=O(u) distinct such vertices, including the original root (j=0). A rank jump crossing multiple powers can share its activation vertex; count it once or overcount by levels. Likewise define a^R at the latest genuine reset r at/before D by taking the current dyadic rank at r and the first genuine reset attaining that rank. This gives at most O(u) reset activations per source. They are frozen from original fibres, not retained cohorts.

A HIGH pair is fresh if D-C(a)<=R_H=ceil(B u^1.25), with no restriction on contact age or nearness of a reset. For a fixed activation of an old source, every younger root of this class has
    C(a)-B<=C0'<=C(a)+R_H.
Uniform prime interval upper bound O(R/log R) for length R (standard upper sieve, equivalently Brun-Titchmarsh for modulus 1) shows that the possible younger primes per activation are O((R_H+B)/log(R_H+B))=O(B u^.25). The total number of such unordered pairs is O(N B u^1.25), so the whole remaining high energy of this class is
    O(N U_H B u^1.25)=O(F/u^.5)=o(F).                    (3)
This covers arbitrary projected first contacts, including those with no earlier genuine reset close to the younger origin. No physical meeting is required. It is stronger in scope than the preceding reset-index-window instability exclusion; even a stable rank can have been attained recently in gain.

For MEDIUM use R_M=ceil(u³). Pay a pair if either:
(a) i<=R_M and D-C(a)<=R_M (shallow older landing);
(b) |C(r)-C0'|<=2A with A=ceil(8u^(2/3)) from 9c62b7, and C(r)-C(a^R)<=R_M (nearby latest genuine reset).
For (a), C0' lies in [C(a)-2R_M,C(a)+R_M]. For (b), it lies in [C(a^R)-2A,C(a^R)+R_M+2A]. Each is an interval of length O(R_M) in the source coordinate up to a factor 2. Again use the uniform prime upper bound O(R_M/log R_M), not a distribution lower bound. At most O(Nu R_M/log R_M)=O(N u^4/ell) pairs across both families. Their entire actual medium costs (both directions) satisfy
    O(N U_M u^4/ell)=O(NT ell³/u^.75)=o(NT/u^.25).        (4)
No analogous fresh-physical-rank estimate for ALL medium landings is claimed, since their offset can be of order B.

For any surviving HIGH pair, a precedes its older landing by more than R_H in gain. At a there are at least 2^j-1 actual larger companions, and all of them persist on the identical physical suffix to D. In particular if the current rank is large then at least half that rank (including the focal source) is inherited from a long earlier physical history, not just the previous k resets. This is valid for arbitrary high and medium pair holes; it is a structural assertion on the original reference fibre. The earlier finite masks need not imply an equal rank condition on retained tags.

## 4. Removing thick reset branching in a whole strip (HIGH only)

Choose the threshold
    m=max(1,floor(m_near/8)),
    m_near=floor(L_H/(2A+3)),
asymptotically m=Theta(B u^(5/6)). Use strip half-width A'=ceil(u²) in source-half-horizon units. Pay all remaining HIGH pairs whose older actual path, at or before D, visits ANY genuine reset v with |C(v)-C0'|<=2A', n_v>=2m, and type A or B of section 2. No particular incoming label or older reset proximity is required. A marked v admits at most 2A'+1 possible younger integer roots M' and at most N original old source tags. By (2) the total candidate pairs are O(N² A'/m). Therefore
    E_branch <= O(U_H N² A'/m)
              = O(N U_H L_H u^(-4/3))
              = o(F/u^.25).                              (5)
Here N=O(B²/u), A'=O(u²), m=Theta(B u^(5/6)), L_H=B u^1.5. The deliberately crude bound N on each entire fibre suffices. In particular this pays thick merger states of ANY actual mass inside the strip, not merely tags with small recent rank.

Also pay all remaining HIGH pairs whose older path, at or before D, visits a reset in this strip with n_v>=2m and is a member of a small incoming cohort (type C). The total such actual tag memberships over all reset states is <=2N from (2), hence at most O(N A') candidate pairs and cost O(N U_H A')=o(F/u^.25). Multiple visited marked keys for one pair only overcount this budget. For a numerical implementation choose a deterministic priority: fresh rank first, then a marked A/B state in the strip, then a small input at C. No additional medium branch mask is proved, because (5) at the corresponding polylogarithmic medium threshold is not small.

Combine this with (3). Suppose a surviving high pair has n_M(D)>=4m. Its dyadic threshold 2^j>=2m and its first activation a is earlier than C0'-2A', since D-C(a)>R_H, D-C0'<=B, and R_H>B+2A' eventually. At every genuine reset of its old path in the strip up to D, the original focal rank is therefore >=2m, hence the full fibre has n_v>=2m. No such state can have type A/B, and the focal tag cannot belong to a small incoming cohort at C. Thus each visited reset has EXACTLY ONE thick incoming continuation cohort, and the focal source comes from it.

This gives a unique thick backward reset ancestry through the strip for these focal tags: whenever the previous reset of the tag is also inside the strip, it is that unique thick predecessor. In particular it applies to the previously surviving near-reset high class with rank at the latest reset >m_near, for which rank at D is at least that. If a path has no resets in the strip the condition is vacuous. The thick predecessor can be outside the strip, and arbitrarily long nonreset arcs are not ruled out. No claim of a unique physical incoming transition or a bound on all earlier fibres is made. This genuinely limits the actual large-fibre branching keys and small-branch arrivals, as opposed to just assigning further arithmetic key quotas.

The total high absolute payment of sections 3-4 is O(F/u^.5), since (5) and small inflow are smaller. The medium added payment is o(NT/u^.25). All payments concern actual remaining pair weights. No new linear root deletion or density gate. Retain earlier relative absorption and joint sufficient conditions unchanged. The full natural renewal energy identity of 9c62b7 is still exact, but (1)-(5) do NOT bound its entire mass-squared integral: a very large fibre can be inherited from outside the strip and persist over many renewal arcs.

## 5. Reproducible finite verification

Standalone research/min_prime_root_reset_threshold_audit.mjs, final source commit e9e1a875366207dfed508f43c380032ce4500dfb, blob 324a2c78b9661fae63ff3810e92ee795ed0179cd, exact remote readback.
    node research/min_prime_root_reset_threshold_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_reset_threshold_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress --grid-stress --star-stress --prefix-stress --reset-stress --threshold-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in the available ECMAScript runtime, not a separate Node process. Initial14 successful runs; final18 successful runs (analytic, concurrent, combined fourteen stress flags at six X). Other modes not rerun. All previous assertions retained. Final version independently scans every original root's reset sequence for first threshold attainment and last-reset rank; checks their counts at every reset against Delta and L for all tested thresholds (1,2,4,8,16,32,64 and chosen threshold). Direct dyadic first attainment checks at every original physical vertex, actual older landing and reset activation intervals, fixed original source multiplicity, actual marked strip memberships, inherited actual larger companion sets on survivors, exact unpaid-only deletion and reoptimization. Natural mass/count arithmetic integer; floating residual flow uses tolerances. No Lean compilation.

Finite normal chosen m=2,A'=ceil(B/4), R_H=ceil(B/8), R_M=ceil(B/32) min2. Stress m=3,A'=ceil(B/2), R_H=ceil(B/2), R_M=ceil(B/8); analytic settings as above (m min2 in finite auditor). These are diagnostic scales, not asymptotic thresholds. All tested analytic prior residuals empty, but potential/activation checks nonempty. The high ledger is the inherited isolated natural high diagnostic, NOT a cumulative full retained hybrid. Both medium masks implemented, no additional positive medium deletion at tested scales.

|X|prior normal medium|final normal medium|prior isolated normal high|final isolated normal high|
|--:|--:|--:|--:|--:|
|4096|0|0|0|0|
|16384|0|0|0|0|
|65536|1.272782|1.272782|14631.632804|14151.916041|
|262144|0|0|208795.455315|62161.837452|

Largest normal X262144: 238 positive unpaid pair weights before new stage,93 whole high pair unpaid fractions paid,145 survive. Actual paid146633.617863: 19 fresh physical rank pairs17243.786954 and74 thick branch strip pairs129389.830909, small-inflow incremental payment0. Never/async0, medium remains0 to rounding (-6.39e-14). All145 survivors verified inherited actual companion sets,655 strip reset visit occurrences among pre-deletion queries (619 large-fibre,475 unique thick input,144 marked A/B visits;2 small-member occurrences in unique branch). Under finite choices,93 survivors met the activation-age and rank preconditions for corridor verification, but NONE of these93 had any actual reset in the finite strip, so the final corridor checks were vacuous on those pairs. Do not claim a nonempty surviving thick reset corridor from this finite example. Full original potential and incoming cohort controls are nonempty and exact.

Largest normal potential: N20390,48725 physical reset states,341075 independent reset/threshold identity comparisons,142730 root/threshold scans,633075 physical rank checks;50931 distinct physical dyadic activation visits and39262 reset activation visits. At m=2 total Delta=L=8189,207 all-small births with949 total source memberships,711 thick branching states with848 excess thick-parent counts,5717 small-incoming memberships including A; all (1)-(2) checked. At m=8 Delta=3205,17 all-small births (315 tags),23 branching states (24 excess thick-parent counts),1889 small tags. At m=16 Delta=1422,1 all-small birth (32 tags),1 branching state (one excess),573 small tags. At m=32 Delta=407,no A,1 B (86 fibre tags),66 small tags. At m=64 Delta=73,no A/B,0 small tags. All are finite actual source counts, not asymptotic prevalence. X65536 paid479.716763 on one fresh high pair, no branch increment; medium unchanged. Combined stress already zero before this stage, stays zero to floating precision; no new stress reduction claimed. No external novelty claim.

## 6. Remaining task

The preceding thick stable reset class is now restricted by actual threshold creation and long inheritance, with all near-origin thick branch states removed for high at negligible absolute cost. The key next issue is mass inherited through the unique thick branch from OUTSIDE the strip, and large fibres on nonreset arcs that traverse it without a reset (prominent in the finite surviving corridor-precondition sample). Use the actual age of first rank attainment and the full gain/clock budget of the inherited suffix, rather than presuming the branch itself has bounded mass. Both joint residual little-o estimates on a common unbounded sequence remain OPEN. Main and independent branches unchanged.
