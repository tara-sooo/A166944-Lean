# Progress-weighted record capacity: a polynomial-depth barrier and hard-budget cutoff transfer

2026-11-28 JST, Issue #10. Base f6c1a1ce9472ab21a76171cefdc28c585404912a. User requests continued multistage research toward M85 and eventual unconditional twin infinitude. This checkpoint replaces the previous COUNT of large record keys by their logarithmic height-progress WEIGHT. It strengthens the short-record upper from sqrt(k) to log(1+k), hence the dynamic M85 depth requirement from logarithmic squared to a fixed positive polynomial (times a logarithm). Then uses the new bound in (i) an early macroscopic height-growth restriction, (ii) a hard-budget trial/true cutoff transfer without any gain discount, and (iii) a broader record-discounted twin criterion. These are analytic reductions and finite verification, not a new density lower at H=.4, M85, an unconditional twin proof, new Lean compilation or independent specialist review.

Write L=log R. All logarithms natural. M85 remains H=floor(R^.4), Omega(R/L²) DISTINCT actual first-H sites of canonical births A in [R,2R], 6|A, with gain A-x<=4H. The exact age is H-3+G/2. For the upper bounds we allow any common hard gain budget B_gain=O(sqrt R), including a prefix of a path whose budget is much larger than the current height. This is important for the cutoff transfer below. All visited centers stay in [R-B_gain,2R], of scale R. Fixed constants can depend on fixed polynomial exponent margins, the bound on B_gain/sqrt R, and, for conditional density conclusions, the supplied positive density constant.

## 1. Include the bottom crossing in the logarithmic record ledger

Let R^theta0<=H<=C sqrt R for fixed theta0>0 and C>0, H an integer. Reuse the previous exact deficit identities and calendar:
    d_j=H-h_j,  d_0=H-3,
    p_j<=2d_j+1,  d_(j-1)-d_j<=2p_j,
    d_(j-1)<=4d_j+2<=6d_j.                                  (1)
Here h_j is the POSTevent height of completed moving event j before first H, p_j its prime. The running deficit minimum mu_j=min(d_0,...,d_j) decreases precisely at strict postevent-height RECORDS. k is the number of these records, not all physical first-record heights and not all moving events. On any record event w>(p-1)/2, since it increases height even relative to its immediate preceding arrival. The full next-wait bound w<=2 qmin(source) then implies qmin(source)>=p/5 for p>=5. These are properties of an actual realization of the event; the arithmetic key upper needs only one such realization.

Fix a real lower deficit b with b>=R^eta, eta>0 fixed, and b<d_0. Write ell=log(d_0/b). We will use ell>=c_ell>0 fixed (not necessarily >=8). Consider a path on which mu eventually reaches <=b. Stop the record ledger at its FIRST such crossing. If a record lands below b, its preceding deficit d_(j-1)>=mu_(j-1)>b, hence d_j>b/6 by (1). Thus EVERY record included in the ledger, INCLUDING its final crossing, lands at d>=b/6. Cover [b/6,d_0] by dyadic bands [D,2D), D=(b/6)2^i for nonnegative integer i, including the last partial band. The number J is O(1+ell).

For each included record define its clipped log progress
    Delta=log(mu_before/max(b,d)).
These nonnegative quantities telescope EXACTLY to ell. Since mu_before<=d_prev and log(1+u)<=u for u>=0,
    Delta<=log(d_prev/d)<=log 6,
    Delta<=2p/d<=2p/D                                      (2)
in its landing band. The disjoint progress intervals in the log coordinate belonging to a single band lie within [log D,log(2D)+log6]; total progress in that band <=log12. The previous argument left the possible last crossing as a separate O(1) term; including its landing band allows a constant-size progress interval, such as b=d_0/2, to be studied by the same method.

For m>=1, distinguish major records p>=D/m and minor records p<D/m in each band. A minor record contributes <=2/m log progress. No winner rule is modified by this distinction.

## 2. Weight each physical key by its maximum possible progress

Assume m<=R^(eta/2), so p>=D/m >= R^(eta/2)/6 is polynomial for every major record. In any band the landing h=H-d lies in an interval of length D and p<=4D+1 by (1). At a moving arrival of sign s=+1 for even absolute firing clock and -1 for odd, the exact pins are
    y=1-s mod p,  h=b_s mod p,  b_+=0, b_-=3,
    n=h-y/2.
Write the source neighbor as x_source+s=pv. Because a record has positive net height, both v and pv-2s are p/5-rough, with v>1 for sufficiently large R (source ~R, p=O(sqrt R)). For fixed p,s, the possible v lie in a containing interval of length O(R/p). The uniform elementary two-form upper sieve used in f6c1a1ce, with a small fixed polynomial sifting support below p/5, gives O(R/(p L²)) candidates. This is uniform because p has a fixed positive polynomial lower and the parameter length is polynomially large. The two forms have distinct roots outside 2 and p, the latter omitted by the cutoff. For each p,s, O(D/p+1)=O(D/p) landing heights satisfy the pin, since p<=4D+1. Therefore the total possible physical major record keys with fixed p is
    O(R D/(p² L²)).
Unlike the previous unweighted counting proof, charge each such key at most its progress weight 2p/D from (2). The summed possible progress weight in ONE band is bounded by
    C R/L² * sum_(D/m<=p<=4D+1) 1/p
       <= C' R (1+log m)/L³.                               (3)
The reciprocal prime estimate follows by summing the elementary O(1/log t) bound in dyadic prime intervals [t,2t], all t of fixed polynomial size. The key weight is independent of the previous trajectory. The factor p/D cancels a factor D/p from the raw key count; this is the essential improvement. The constants are uniform in b,m under the fixed exponent margins above. Counting a superset of possible keys is permitted for this upper.

For any selected set of distinct first-H sinks, choose one actual budgeted witness per sink. Two selected witnesses cannot pass through the same physical state before first H: identical deterministic continuation would give the same sink. Thus in (3) each physical record key can be charged at most once over these witnesses. If the assertion is that SOME witness has a given large progress property, choose such a witness for that sink. The same argument works and does not assume a common ancestor selection rule. The upper is on DISTINCT sinks, not all root incidences; it relies on actual deterministic continuation.

Sum (3) over J=O(1+ell) bands. For any fixed rho>0, the number of distinct first-H sinks admitting ANY budgeted witness which reaches mu<=b and contributes at least rho ell major log progress to this ledger is
    <= C_rho R (1+log m)/L³,                               (4)
because ell>=c_ell. No extra factor ell remains. This also holds for any restricted selection of such actual witnesses. No independent residue model, distribution theorem beyond elementary upper sieve, or bound on basin multiplicity is used.

## 3. Short-record upper improves to logarithmic in the depth

If a budgeted witness reaches mu<=b with at most k records, its minor log progress is <=2k/m. Take
    m=max(1,ceil(4k/ell)).
Provided m<=R^(eta/2) the major progress is at least ell/2. By (4),
    N_reaches(H,b,k) << R/L³ * [1+log(1+k/ell)].             (5)
For k=0 the set reaching mu<=b<d_0 is empty, so the same upper holds. The earlier unweighted argument instead gave O(R/L³(1+k/ell)), followed by a sqrt(k) optimization. Here even a fixed log span suffices.

At a terminal x the final idle I=H-h_last<2 qmin(x), so qmin<=Q implies mu_last<2Q. Choose Q=floor((H-3)/4), b=2Q, so ell=log2+o(1). This Q is polynomial, e.g. >=R^(theta0/2) for all large R. Choose a fixed epsilon0>0 sufficiently small in terms of theta0, e.g. theta0/8. For 0<=k<=R^epsilon0, m=O(1+k) is within the required power margin for eta=theta0/2. Equation (5) bounds the sinks with qmin<=Q.

For Q<qmin<=U with U<=O(sqrt R), the previous uniform intermediate roughness upper remains
    # centers << R[1+log(U/Q)]/L³.                          (6)
Indeed pick the least factor p of one neighbor, p in (Q,U], write that neighbor pv, and sift v,pv±2 at a small fixed polynomial cutoff below Q. The resulting O(R/(p L²)) count is summed over p using the same reciprocal bound. This counts actual centers, regardless of reachability.

Apply (6) to U=4H. We obtain the NEW uniform upper
    N(qmin<4H, some witness <=k postevent records)
         << R/L³ * [1+log(1+k)],  0<=k<=R^epsilon0.          (7)
The allowed gain budget is any fixed O(sqrt R), not necessarily O(H); the proof only used the slab of visited positions of scale R and first-H height restriction. Constants uniform in H in the specified fixed polynomial-to-square-root range. In particular every subpolynomial k=R^o(1) gives o(R/L²). A density-scale family of short-record endpoints would have to yield density-scale rough pairs already.

For near-square H=floor(4 sqrt R/L^B0), fixed B0>=0, a non-twin center has qmin<=sqrt(2R+1); apply (6) with this upper U (if U<Q, there is no intermediate set). Then
    N_nontwin(H,k) <<_B0 R/L³ * [1+log L+log(1+k)].          (8)
For B0=0 the log L term can be omitted. This strengthens the previous sqrt(k) term and extends the admissible record bound to a small fixed polynomial. It immediately implies the new sufficient twin criterion: for unbounded R, a density-scale set of distinct first-H sites with gain<=4H and a witness of subpolynomial postevent record count k=R^o(1) suffices for infinitely many twins (indeed a density-scale set of actual twin centers). This still does not prove such a lower.

## 4. Conditional polynomial complexity of the genuinely dynamic M85 branch

Fix H=floor(R^.4). Suppose a density-scale M85 lower is supplied, N>=c_* R/L². If stationary centers with qmin>=4H already make up a fixed positive fraction, they provide the static branch (ignoring O(H) boundary sites). Otherwise retain a density-scale nonstationary family with qmin<4H. Denote its positive lower constant by c1.

Use (6) with Q=floor(H R^-delta), where delta>0 is a sufficiently small FIXED number, delta<.1. Uniformity is available with the common fixed polynomial lower Q>=R^.25 for large R. The intermediate band Q<qmin<4H contains at most C(delta+O(1/L)) R/L² centers. Choose delta small relative to c1 and the common constant C. Delete this band. Retain a density-scale family with
    qmin<=Q = H R^-delta (up to rounding).                 (9)
This strengthens the old shrinking logarithmic cutoff H/L^6 in the conditional dynamic branch. It is NOT a lower for such a family without the assumed nonstationary M85 lower.

Use b=2Q and ell=log(d_0/b)=delta L+O(1). Set m=R^epsilon for a sufficiently small FIXED epsilon>0, epsilon<.1 (reduce to ensure the fixed exponent condition of section 2). By (4) the sinks admitting ANY witness with major progress >=ell/4 number at most C'(epsilon+O(1/L)) R/L². Choose epsilon small relative to the retained density constant. Delete them. For each remaining sink EVERY successful budgeted witness has at least 3ell/4 minor progress in the ledger, and each minor event contributes <=2/m. Thus EVERY such witness has
    k >= (3/8) m ell >> R^epsilon log R                     (10)
strict postevent records, with the lower supplied by labels p<D/m<=H R^-epsilon, not merely a count of all events. Moreover, since there are J=O(ell) bands and any band contributes at most log12, at least c2 ell distinct landing-deficit bands carry >=c3 minor progress for fixed positive c2,c3. In each of those bands the number of minor records is >=c3 m/2 and their gain sum >=c3 D/3, by (2) and p-1>=2p/3. This distributes the required polynomial record complexity over Omega(log R) scales of remaining deficit.

There is an additional macroscopic gain restriction earlier in the SAME witnesses. Apply (4) separately to b0=d_0/2, ell0=log2, with the same m (if necessary reduce epsilon once more). Every witness of (9) crosses mu<=b0, and the sinks admitting >=ell0/4 major progress in this shorter ledger are again at most C'' epsilon R/L²+o(R/L²). Delete these too. All records before this crossing lie in bands D>=b0/6=(H-3)/12. The minor records supply >=3ell0/4 progress, so their total gain is at least
    sum_minor(p-1) >= (H-3) ell0/48
                   = Omega(H).                             (11)
For clarity: each gain >=Delta*D/3>=Delta*(H-3)/36, and sum Delta>=3ell0/4, giving the constant ell0/48. Each label is <=H R^-epsilon. Thus even the rise of the postevent record from 3 to at least (H+3)/2 requires a positive macroscopic amount of gain contributed by primes polynomially smaller than H on every retained dynamic witness. This is not just an asymptotic requirement that many very late events have small label. The actual first-H has not yet occurred at this crossing.

Combining the above deletions and the earlier global-top pruning (1d7517b4) gives an equivalent M85 disjunction, with the same original gain and first-height budget: a density-scale stationary lower qmin>=4H, OR a density-scale dynamic lower with (9)-(11), the distributed deficit-band progress, and the previous fast-top/long-intervening-relay restrictions. In the forward implication the fixed delta,epsilon are chosen depending on the given positive M85 lower constant. If only an unbounded subsequence lower is assumed, the branch split can be made on an unbounded subsequence. Reverse implication is immediate inclusion in the original M85. The old additional top deletions are o(R/L²) and compatible with these fixed-small-fraction deletions. There is NO assertion that M85 requires polynomial depth on arbitrary isolated sinks or on stationary paths, nor that either branch has been established. The new theorem supersedes the earlier conditional quadratic-log depth barrier, while retaining its exact Pareto recursion.

## 5. Hard-budget short-record transfer through a common lower section

Use the same canonical births and the same hard gain budget B_gain=O(sqrt R) in both actual and trial graph. The trial retains only odd labels <=z, with no modification of the priority among them. Let z be an integer, polynomial in R with fixed positive lower, z<2H+1. Put
    h0=floor((z-1)/2).
For all large R, 3<h0<H, 2h0+1<=z and 4h0>z. The two rules agree on EVERY physical transition before first h0, because the height bound limits all eligible primes there to <=2h0+1. Consequently both the physical first-h0 state and its attained postevent-record count are the same for a given root, unless both fail the common budget before reaching it. A path attaining first H must pass first h0 since upward tick increment <=1. No assumption of a common later suffix until H is made. At h0 the running postevent maximum and the record count can be continued exactly as in the earlier Pareto transport. A first-h0 idle edge does not add a record.

Let A_H(k), T_H(z,k) be the sets of DISTINCT first-H sinks in actual and trial graphs, respectively, that have SOME canonical witness of gain<=B_gain and record count<=k. Let P be the common first-h0 states with some witness satisfying these same bounds. Decompose P:
    P_low: qmin<4h0;
    P_mid: 4h0<=qmin<=2H+1;
    P_high: qmin>=4h0 and qmin>2H+1.
Empty ranges allowed. For any prefix in P_high neither graph ever moves before H, since the largest possible label before H is <=2H+1. It gives the same terminal x in both graphs with unchanged gain and record count. For P_mid the trial stays at x since 4h0>z; the actual suffix may or may not move. For P_low both may evolve differently.

Every actual-only sink and every trial-only sink has a witnessing lower prefix in P_low or P_mid: choose a witness with the required budget and depth. Its prefix satisfies them by monotonicity. Determinism from any common physical first-h0 state means at most one physical first-H sink per graph, regardless of which prefix ancestor ultimately satisfies the gain and depth cap. Hence
    |A_H(k) symmetric_difference T_H(z,k)|
       <= 2(|P_low|+|P_mid|).                              (12)
The first-h0 proof of (7) applies even though the budget is the FINAL B_gain and can be much larger than h0. This is why section 3 was formulated with an arbitrary O(sqrt R) budget. For z>=R^alpha fixed alpha>0, use (7) at h0 with some common epsilon0 depending on alpha. Then |P_low|<<R(1+log(1+k))/L³. Equation (6) gives |P_mid|<<R[1+log^+(H/z)]/L³. Consequently
    |A_H(k) symmetric_difference T_H(z,k)|
       << R/L³ [1+log(1+k)+log^+(H/z)],  k<=R^epsilon0.     (13)
Here log^+(u)=max(0,log u). This is a HARD-BUDGET, set-valued two-way transfer, not a difference of sums of heavily gain-discounted scores. No mod2310 potential needed for (13). In particular z=H exp(-L^gamma) rounded down, fixed 0<gamma<1, is permitted, and k=R^o(1) makes the error o(R/L²). For fixed powers H=R^theta,z=R^alpha with alpha<theta, the term log(H/z) is order L; then the estimate is only O(R/L²), not negligible relative to the target density. This is an explicit remaining obstruction, not an extension across a fixed exponent gap.

## 6. Identify exactly what a short-record trial lower would achieve

The same first-h0 argument gives a stronger diagnostic of the trial itself. Write S_z={x in [R,2R] even: qmin(x)>z}. These are all canonical births (z>=3) and are stationary throughout the trial, so S_z is contained in T_H(z,k) for every nonnegative budget and record cap. For any trial sink with witness coming from P with qmin>=4h0, the trial suffix is stationary at that very center, which is z-rough. If it lies outside the original slab, the total number of such boundary centers is O(B_gain)=O(sqrt R). Every other trial sink can be charged to P_low by deterministic continuation. Thus
    0 <= |T_H(z,k)|-|S_z|
        << R/L³ [1+log(1+k)] + B_gain.                    (14)
The symmetric-difference version also holds because S_z is a subset of the trial set. The large H/z ratio causes no additional term in (14), as long as z has the fixed polynomial lower and h0<H. The trial's stationary rough frontier therefore already accounts for the leading-order short-record count. This is a restriction of what the new hard-budget transfer can achieve, not a proof of the required trial lower.

At H near sqrt R as in section 3, the number of NON-TWIN trial sinks of record count<=k is bounded directly by (14) and the same rough interval sieve at qmin in (z,sqrt(2R+1)], even if the actual graph later moves:
    # non-twin trial sinks
      << R/L³ [1+log(1+k)+log^+(sqrt(2R+1)/z)] + B_gain.    (15)
A lower larger in order than this bound at unbounded R forces actual twin centers among the trial's endpoints, since the arithmetic qmin test does not depend on the dynamical model. For instance z=H exp(-L^gamma), k<=exp(L^kappa), 0<gamma,kappa<1, B_gain<=4H, the upper is O(R/L^(3-max(gamma,kappa))) (log L is smaller), which is o(R/L²). This is a sufficient condition permitting a much longer subpolynomial record budget and a smaller retained prime alphabet than before, not an established lower. Equation (14) explains why proving it only with short-record trial paths is tantamount at that precision to breaking the corresponding static roughness barrier. A z far below sqrt R with fixed exponent gap does not give a negligible non-twin upper.

For the actual graph, stationary qmin>=4H centers similarly supply all but O(R(1+log(1+k))/L³) of the short-record sinks by (7). Therefore counting short-record paths alone cannot generate a new density-scale leading term beyond static survivors. The polynomial-depth dynamic alternative of section 4 is a genuinely different unweighted lower target.

## 7. Reuse the previous projected max-flow transfer with a much broader record discount

The previous f6c1a1ce theorem transfers max scores L^(-13G/H) exp(-k/K) between the actual graph and the trial with z=floor(2H/3), with total error O(R/L³) uniformly for K>0. That theorem uses the inherited mod2310 wait certificate and projected physical residual (not needed for sections 1-6). For a sink let k_x be its minimum record count among gain<=4H actual witnesses, infinity if none. Its max score is <=exp(-k_x/K)+L^-52 by separating excessive gain witnesses. Integrate the new counting bound (7) or (8) up to k0=floor(R^epsilon0); the tail contributes O(R exp(-k0/K)). For an exponential random variable of mean K, Jensen gives E log(1+t)<=log(1+K). Hence
    sum_(qmin<4H) C_H(x) << R/L³ [1+log(1+K)]
                           + O(R exp(-k0/K)+R L^-52),
    sum_(non-twin x) C_H(x) <<_B0 R/L³ [1+log L+log(1+K)]
                           + O(R exp(-k0/K)+R L^-52).       (16)
For B0=0 the log L term in the second line is unnecessary. The k0 tail is negligible whenever K=R^o(1). This replaces the previous sqrt(K) by log(1+K).

In particular with K=L^A for ANY fixed A>0, or with K=exp(L^gamma) for a fixed 0<gamma<1, the criterion accepts substantially longer histories than the previous K=(log L)^2. At near-square height H=floor(4 sqrt R/L^B0), a trial total max score of order omega(R[1+log L+log(1+K)]/L³) would suffice for infinitely many twins. If K=R^o(1), a lower Omega(R/L²) suffices. The score of every twin birth in the original slab is exactly1, since it stays at its initial center with gain0 and record count0. Thus more precisely the trial weighted mass equals the number of twin centers in the original slab plus an error bounded by (16), the O(R/L³) transfer and the boundary O(H). For H=.4 the analogous statement holds with static qmin>=4H centers instead of twins and the first line of (16). These are asymptotic equivalences with arithmetic counts at the stated precision, not new lower estimates.

## 8. Executed audit

research/lean/negative_min_weighted_record_capacity_and_hard_transfer_audit.mjs @2fb2772534ea3ca1ecab9505228d14fd60904e6e, blob efa3616ca1b53f0633dc35dcdeb11c6caa2e2aab. Executed ECMAScript, pinned and branch readback exactly compared to executed source. First component: R=12000,48000,192000,768000, H=floor(R^.4), gain<=4H, actual finite proxy Q=floor((H-3)/8). 170004 roots,163476 successful first-H paths,809099 strict postevent-record incidences on these successful paths (not failures). 2242 clipped log-progress profiles,2170 crossings below target b,2260 local major-key pin/roughness checks,2242 minor-gain inequalities,24 aggregate major-key weight inequalities, with independent per-profile record reconstruction from exact event calendar. Select distinct sinks and verify that their charged actual keys never overlap. All passed. Logs are double precision with tolerances, not certified interval arithmetic; calendar and pin checks integer exact. Finite thresholds and finite counts do not prove (3)'s asymptotic estimate.

Second component: R=12000,48000,192000, gain<=4H, cutoff z=floor(2H/3),floor(H/3),max(9,floor(H/6)); h0=floor((z-1)/2), record caps 0,1,2,4,8,16,32. 126009 root/cutoff cases,126009 exact common lower section comparisons,252018 exact resumed continuation comparisons (including running record maximum),63 distinct-sink set comparisons,50817 stationary trial-prefix checks,31537 unchanged high-rough prefix checks,606 true-only and75008 trial-only sink incidences charged across caps/cutoffs. All passed. The test of (12) includes nonempty true-only and trial-only sets. Largest proxy R192000,H129,z86,k8: 3293 true sinks,4092 trial sinks,2 true-only,801 trial-only,3420 low and549 intermediate lower-prefix states. These coarse finite capacities are not asymptotic estimates. No actual density proof extrapolated. No separate Node or Lean invocation; ECMAScript research runtime used.

## 9. Source ledger and precise remaining gap

- Reopened f6c1a1ce9472ab21a76171cefdc28c585404912a, research/2026-11-28-min-negative-deficit-record-depth-and-weighted-transfer.md §§1-5,7-9. The previous deficit inequalities, record source roughness, two-form sieve and exact physical pins are reused, with the new weighting (3) and the included bottom-crossing ledger. Previous near-square weighted transfer used only in section 7.
- Reopened at pinned base the earlier static-frontier/missed-clock note (research/2026-11-27-min-local-negative-static-frontier-equivalence-and-missed-clocks.md), dyadic-insertion, small-descent, and global-top-relay pruning notes. The old static-frontier equivalence required a small fixed G/H; the present short-record equivalence permits arbitrary fixed O(sqrt R) gain budget at all polynomial H. No fresh high-level distribution theorem used. No claim of mathematical literature priority.
- Core b0e26798535b2c997f1383c1dc37bbe560aac938 not edited; main/sibling branches untouched. No new Lean compile, independent specialist review, M85 or unconditional twin proof. The required lower is still missing: either a static roughness breakthrough, or the density-scale active M85 branch with polynomial postevent record depth and macroscopic gain from polynomially subtop labels. The latter is a stronger necessary structural reduction, not a supplied active cohort. The hard transfer can reduce the cutoff by a subpower factor at negligible density loss but not yet by a fixed exponent gap; its short-record trial lower is equivalent at leading order to static roughness. The broadened twin criterion is genuinely more permissive on record depth, but does not circumvent the arithmetic lower-bound obstacle by itself.
