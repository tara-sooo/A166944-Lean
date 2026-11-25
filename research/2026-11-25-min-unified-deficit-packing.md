# Deficit-adaptive actual-clock packing and long nonRESET local diversity

2026-11-25 JST. Continuation of the unified stable-strand reduction [3fe50cf63782](https://github.com/tara-sooo/A166944-Lean/blob/3fe50cf6378294cdaa25cacc0e9f9cda16a2174c/research/2026-11-25-min-unified-stable-strand-clock.md). Combines its true-tick packing and entropy windows with the least-factor buckets of [minfactor-support](https://github.com/tara-sooo/A166944-Lean/blob/1ccfb6af1957dcada4ee3286d01206288664e135/research/2026-11-25-min-prime-root-minfactor-support.md), the newer local sparse-interval mask [9db807e00aba](https://github.com/tara-sooo/A166944-Lean/blob/9db807e00aba8bfc0f59aa818d5698e871024f09/research/2026-11-25-min-prime-root-persistent-density.md), and the adjusted arrival-phase identity [44187d1ede5f](https://github.com/tara-sooo/A166944-Lean/blob/44187d1ede5ffbf73319bba9c82775a3a7fef4f7/research/2026-11-25-min-clock-record-birth-geometry.md). New result: a deficit-dependent mass threshold for actual clock simultaneously across ALL least factors, a much stronger mass threshold near RESET for HIGH, and a long nonRESET witness alternative with local label and phase diversity. These are unconditional linear deletions and necessary constraints, not a general tail bound or a twin-prime proof. No Lean compilation.

## 1. Direct tick-state packing, no pair energy

Keep the long prime-root ensemble, dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^(1/4)), H=T+B. All original gain-stopped completed paths and their cutoff remain unchanged. At a completed wait a tag occupies (j,C) for integer j in [t,v). The mass b(C,j) counts original tags occupying this state in completed waits, excluding terminal snapshots. All these tags have the same next actual exit tick and selected label (the next tick-state evolution is deterministic). At each even C let r(C) be the least eligible odd prime <=B, or zero at twins. Only r>0 has completed waiting occupation. The common deficit at a tick is d=2j-C, in [0,6+5H]. As j varies the deficits are distinct (and even). Thus at fixed C each allowed d has at most ONE physical tick state. All synchronous and asynchronous occupation is included automatically: we sum tag-clock units b(C,j), not pair masses. Partial deletion of a wait is legitimate for the actual-clock objective; no trajectory is rerun.

Every tag present at C started at C_origin=2M-2 in [C-H,C]. By the uniform upper bound for primes in an interval of length H/2, used also in the source-locality estimates of the prime-root branch,
    b(C,j) <= # original prime origins in that interval << H/u.        (1)
This is a uniform upper bound, not a statistical assumption on the root distribution.

Let q_r=# even C in the original O(X) horizon domain with least factor exactly r. From minfactor-support,
    q_r << X/[r log^2(2+r)] for all odd primes 3<=r<=B,
    sum_(r>=R_h) q_r << X ell/u^3, R_h=B/(2 u^(3/2)).                 (2)
The second bound follows by reciprocal-prime summation in the top polylogarithmic range, not by summing over all primes with a crude count. A natural HIGH event, p>=ceil(B/u) and r>p/sqrt(log p), satisfies r>=R_h for sufficiently large X. All constants here and below are absolute unless explicitly specified.

Define the finite nonnegative envelope
    f_H(d)=max{1, sqrt(H/(d+1)), H/[u(d+1)]}, 0<=d<=6+5H.
Then
    sum_(d=0)^(6+5H) f_H(d) = O(H).                                 (3)
Indeed max<=sum of the three terms. The constant term contributes O(H), the square-root term contributes O(sqrt(H)*sqrt(H)), and the harmonic term contributes O(H log(2+H)/u)=O(H). Restricting to even deficits only improves the bound. The two nonconstant terms are complementary: square-root for moderate deficits, harmonic for very low ones.

## 2. New simultaneous factorwise and high-factor masks

For every least factor r put
    m_r = log^2(2+r)/(u ell^2),     l_r = log^2(2+r)/ell^2.
Delete an actual tick's clock contribution when either
    b(C,j) <= m_r f_H(d)  OR  d+1 <= l_r.                             (4)
Use priority when both hold. This works even when m_r<1: there is no floor up to 1 and therefore no spurious budget for low factors. In the second test the number of possible deficits is <=l_r, even if l_r<1.

For fixed r and C the first deletion costs at most m_r sum_d f_H(d). The second costs O(H/u) l_r by (1). Summing over the least-factor buckets, using (2), (3) and sum_(r<=B) 1/r=O(ell), gives
    W_factor << XH/(u ell^2) sum_(r<=B) 1/r
             = O(NT/ell) = o(NT).                                    (5)
This is one absolute budget covering LOW, MED and HIGH simultaneously. It is not a sum of separately chosen full budgets for every factor.

Independently strengthen the test at ALL horizons r>=R_h by setting
    m_h=u^2/ell^2,     l_h=u^3/ell^2,
and deleting when
    b(C,j) <= m_h f_H(d)  OR  d+1 <= l_h.                             (6)
The union is paid after (4), without double-counting. The upper bound by all possible (6) contributions is
    W_top << (sum_(r>=R_h) q_r) [m_h H + (H/u) l_h]
          << (X ell/u^3) (H u^2/ell^2)
           = O(NT/ell) = o(NT).                                      (7)
In particular ALL high-factor clock at deficits d+1<=u^3/ell^2 is paid, without an assumption on cohort mass. The separate low-deficit test is useful because prime-origin locality gives a uniform cap (1); it is not necessary to force the mass test alone to imply it. Formula (7) also improves the former uniform thin mass u^(7/4)/ell to u^2/ell^2 (asymptotically larger).

These are tick-level linear bounds, not bounds on discarded r-weight, event count or quadratic energy. They are valid on any subledger obtained by earlier masks. The original least-factor support (2) is inherited; no additional analytic sieve theorem is required for (5)-(7).

## 3. Consequences for stable cohorts and actual RESET geometry

For a retained HIGH tick (j,C) in a surviving stable strand g=(K,e) of the parent, write n_g for the full original through-cohort mass, epsilon=1/ell, delta=exp(epsilon)epsilon=o(1). The parent's entropy property applies throughout the extended shared span, not just at the event's recorded input state. Thus n_g >= (1-delta) b(C,j) (the full mass including terminal snapshots is at least b). Applying (6),
    n_g > (1-delta) m_h,
    d+1 > l_h,
    n_g > (1-delta) m_h sqrt(H/(d+1)),
    n_g > (1-delta) m_h H/[u(d+1)].                                  (8)
Equivalently,
    d+1 > max{ l_h, H[(1-delta)m_h/n_g]^2,
               (1-delta)m_h H/(u n_g)}.                              (9)
The stable mass and the actual clock are coupled: low deficit now requires much more than a polylogarithmically large cohort.

For any fixed beta>=0, at d=O(B u^beta),
    n_g >> B u^(3/4-beta)/ell^2.                                      (10)
Use H=Theta(B^2/u^(1/4)) in the harmonic term. In particular a high wait near the short-clock deficit scale B can survive only in an actual shared cohort of size Omega(B u^(3/4)/ell^2). This is a SYNCHRONOUS mass bound, not a projected horizon mass bound. It is not a bound on all possible cohorts.

For any two ordered true states on one original path, with gain difference a=C_2-C_1>=0, one has
    -a <= d_2-d_1 <=5a+4B.                                          (11)
The lower bound is exact from d=2j-C. For the upper bound, the part from the first true state until entry at C_2 has elapsed time at most 3a by the full completed-edge wait bound (shortening the first wait cannot increase it); the remaining partial wait at C_2 is <=2B. The same-horizon case has time difference <=2B. Thus (11) also holds across virtual canonical states inside waits. If a retained tick has deficit d, any preceding actual state of deficit <=6 is at gain distance at least max(0,(d-6-4B)/5), and any later such state is at gain distance at least d-6. This includes root, RESET and all low-stock states, and is independent of which tags meet before or after the tick.

In particular, for a fixed A>=0, if n_g<=B/u^A then (9) requires d >> B u^(A+3/4)/ell^2. Such a retained HIGH tick lies far from ANY low-stock state in either direction when such a state exists, by (11). This is a new long excursion alternative even for masses of order B. For the more moderate cohorts
    n_g <= m_h u^(1/3),                                               (12)
the square-root term of (9) requires d >> H/u^(2/3). The entire extended stable-strand span has gain diameter O(S+B), S~H/(4u ell^2), so (11) implies every true and recorded state of that span has deficit >> H/u^(2/3). This is asymptotically much larger than S, and no RESET or canonical point occurs anywhere in the entire span. The inference uses actual shared states, not a model of average drift.

For an actual completed event with selected p and post-state (J,v), put s=v mod 2 and d_post=2v-J. The exact arrival phase is
    D_phase=d_post-6s,       2p | D_phase.                            (13)
Phase zero is precisely RESET (d_post=0 at even arrival, 6 at odd arrival). As noted in the independent stable-heavy result, odd p=3,d_post=0 can have negative nonzero phase; no blanket nonnegative phase assumption is used. On an event ending at RESET, all occupied pre-jump ticks satisfy d<=B+6, since d just before exit is d_post+(p-1)-2 and deficit increases by two per waiting tick. Thus every retained HIGH clock unit of such an event belongs to a cohort satisfying (10) with beta=0. The true-tick result treats asynchronous entry times correctly.

## 4. Sparse interval mask at a genuinely long scale

The newest independent persistent-density result uses sparse actual-clock intervals on the shorter primorial blocks. On our stable superblocks, a larger minimum length allows the stronger log-B saving.

Use the parent's central block length S=P floor(D/(4P)) with D=floor(T/(u ell^2)) and P the largest even primorial <=B u^(3/2). Eventually S~H/(4u ell^2), so choose
    s_min=ceil(B^(3/2)),    eta=u^(-1/4),    s_min=o(S).
Partition EACH original path's events by K=S floor((C-1)/S), using the prehorizon C. The event gain intervals in each nonempty block form one contiguous interval of length <=S+B; the intervals of different blocks partition the full original completed gain. In an extended stable cohort the complete central block is identical across all members.

Freeze a natural HIGH measure on these gain intervals after (4),(6) and optionally the absolute actual-cheap test w<=eta(p-1), but BEFORE sparse deletion and any tag-specific masks. Give each event its remaining count of actual HIGH ticks uniformly over its own gain interval. This is only an accounting measure; all interval endpoints below are actual recorded vertices, so its mass is exactly the sum of remaining actual wait units. The tick mass tests depend only on the original global tick state and hence agree on shared events, even if different tags have different earlier histories. The optional cheap test costs at most eta NH and is not used in the new audit.

Inside each source block let U be the union of ALL vertex-endpoint intervals I with |I|>=s_min and frozen mu(I)<=eta |I|. Delete the remaining actual HIGH ticks of every event lying in U. By the finite interval same-union depth-two cover lemma used in 9db807e00aba, mu(U)<=2 eta |U|. The exact sum across all original blocks costs
    W_sparse <=2 eta NH=o(NT).                                      (14)
No multiplicative penalty for the number of interval scales, and no pair energy. Every surviving HIGH event now has, in EVERY eligible interval containing its full gain interval in its block,
    mu(I)>eta |I|.                                                   (15)
Witnesses use the frozen pre-sparse measure, NOT the final surviving measure. An entire shared central block is eligible for large X, and there are also much shorter intervals of length about B^(3/2) around interior events. Prefix and terminal blocks lacking such intervals impose no condition.

Use the uniform short-quotient two-form sieve already established in the gain-prefix/quotient-blocks notes, as cited and applied in 9db807e00aba: on a high selected-p list inside a horizon interval of length L, the number is
    O(H_q/log^2(2+min(p,H_q))), H_q=ceil(L/(2p))+O(1).
For L>=s_min, p>=B/u and p<=B, log(2+min(p,H_q)) >> u uniformly and H_q=O(L/p). Each wait <=2p, hence the entire HIGH clock for any fixed selected p in the interval is O(L/u^2). This is valid for partial tick deletion since it is an upper bound on the original full waits. In (15), every witness interval therefore contains Omega(eta u^2)=Omega(u^(7/4)) distinct actual HIGH selected primes with positive frozen weight. This is a local condition in all sufficiently long actual vertex intervals, not merely a global count in the whole superblock. It lifts the previous log-log label diversity to log-B diversity at the new minimum length.

## 5. Adjusted-phase diversity and a second possible rank mask

If a retained HIGH tick belongs to a moderate mass strand (12), no state of its central block is RESET by section 3. Every contributing HIGH witness event in (15) has nonzero adjusted post-phase (13). Each nonzero D_phase of size O(H) has at most TWO distinct prime divisors >=B/u eventually: (B/u)^3 >> H. In particular, distinct labels in the interval require at least half as many distinct nonzero adjusted phase values. For every eligible witness interval containing a retained event of a moderate-mass strand,
    # distinct nonzero adjusted post-phases with positive frozen mass
        = Omega(u^(7/4)).                                           (16)
This couples the local high-prime diversity to an actual nonRESET deficit excursion, rather than simply to a possible list of arithmetic labels.

Optional additional rank deletion on any original central block: remove the first k=floor(u^(7/4)) nonzero adjusted phase values ranked by their natural remaining HIGH weight (ties by integer phase); if there are fewer, remove all nonzero values. Each nonzero phase has <=2 possible HIGH labels and their entire block wait is O((S+B)/u^2) per label by the same sieve. Thus the removed actual clock over N original paths is O(N(H/S+1) k(S+B)/u^2)=O(NT/u^(1/4))=o(NT). The zero phase is NOT covered by this argument. This mask is optional; it can precede the frozen sparse measure and preserves every estimate above. Neither the rank deletion nor (16) bounds the mass of a strand that repeatedly occupies many phases. This optional mask is a paper deduction, not part of the finite audit below.

## 6. Updated sufficient condition and exact remaining alternatives

Apply all previous valid linear deletions, the new absolute masks (4),(6),(14) and optional rank/cheap masks by priority. Retain the entropy-window and endpoint-gain trims of the parent, and its absolute low-occupation group exclusion if desired (natural original V_g<=u^(-1/4)S). The new masks are evaluated on full original paths and states, then intersected with the surviving ledger. Do NOT add old quadratic pair payments to this actual-clock sum.

Let L_new be the remaining actual natural HIGH clock on thick slow stable strands and A_new the actual remaining non-HIGH clock (also reduced by (4),(6)). The all-clock inequality is
    W_all <= A_new + L_new + o(NT).
Thus the same no-twin contradiction follows from
    liminf_(dyadic X -> infinity) (A_new+L_new)/(NT) < 1/2.             (17)
On every sufficiently large no-twin window, every original prime tag crosses T before the original cutoff, so W_all>=N(T-6)/2 by the exact deficit identity. The new ledger is a subset of the previous ledger on the same paths; there is no new quadratic/asynchronous condition.

For HIGH, split surviving clock into moderate n_g<=m_h u^(1/3) and larger n_g. The moderate sector lies in long high-deficit nonRESET excursions (9),(12),(16) and every eligible local interval is dense in the frozen measure (15). The larger sector also obeys (8)-(11),(15), but can still contain RESET; the portion near deficit O(B) requires the much larger synchronous mass (10). This is a genuine additional absolute exclusion and structural narrowing. Neither sector's full linear clock nor the full non-HIGH residual has been bounded here. In particular no proof of (17), no claim of a full proof of twin infinitude, and no external novelty claim.

## 7. Exact finite tick audit

Source [min_unified_deficit_packing_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/77ce513815412a6e5005fa45e03a902ad8c32c97/research/min_unified_deficit_packing_audit.mjs), source checkpoint 77ce513815412a6e5005fa45e03a902ad8c32c97, exact remote readback. The audit function was executed in the available ECMAScript tool runtime, not an independent Node process; the saved version replaces the adjusted-phase trial-factor count by direct trial division to avoid indexing beyond the SPF array at other scales. On the seven executed windows those arguments were within the array; this replacement does not affect masks or results. No Lean verification.

    node research/min_unified_deficit_packing_audit.mjs diagnostic 256 1024 4096 16384
    node research/min_unified_deficit_packing_audit.mjs analytic 1024 4096 16384

Independent original prime-root MIN path generation using SPF and literal per-tick gcd at X256/1024 (431 and 1239 comparisons in diagnostic, 1239 in analytic X1024). Counts all completed true tick states, exact synchronous mass, common next selected event at each tick, all least-factor horizon buckets independently over the full horizon domain, exact finite factorwise mass and low-deficit capacity sums, disjoint tick partition, inverse deficit bounds, actual previous and next low-stock separation, adjusted phase divisibility and full RESET wait within d<=B+6. The sparse union is computed by literal enumeration of all actual vertex intervals in each source block, with complete paid-clock partition and the depth-two upper budget and every surviving interval's dense witness checked. The full stable-cohort reconstruction is the parent's separate audit, not repeated here. The optional phase-rank mask is not tested. These finite comparisons test the exact geometry, not the implied constants in the asymptotic prime sieve.

Diagnostic parameters deliberately do not match asymptotic scaling: T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), HIGH r>p/2, R_h=Q/2, m_h=1.5, l_h=8, m_r=.1*(log(2+r)/u)^2, l_r=2*(log(2+r)/u)^2, S=2B, s_min=max(4,floor(B/2)), eta=.2. Analytic mode uses the asymptotic mask parameters, T=floor(X/u^.25), and S=max(1,floor(H/(4u ell^2))) (not rounded to a primorial multiple). At these finite X, s_min>S+B, so the analytic sparse test is vacuous; diagnostic supplies nonzero interval tests. The independent low-deficit masks pay zero after mass-mask priority at these finite X, so the test of their disjoint contribution is vacuous. No observed reduction fraction is an asymptotic conclusion.

| X/mode | original clock | raw HIGH | after factor/deficit HIGH | after sparse HIGH |
|---:|---:|---:|---:|---:|
|256 diag|2426|1765|670|502|
|1024 diag|7377|3908|799|450|
|4096 diag|67027|37458|16492|13690|
|16384 diag|385422|195474|99486|78067|
|1024 analytic|7377|2198|0|0|
|4096 analytic|67027|27685|790|790|
|16384 analytic|385422|161263|7002|7002|

At X16384 diagnostic, 1612 prime roots, 32866 completed events, 113577 occupied true tick states, max synchronous mass28. All-label general mass deletion6506, top-factor mass deletion124461, remaining all clock254455. HIGH priority paid3128 and 92860, remaining99486; remaining low-deficit d<=B HIGH47836, minimum mass5 there, retained RESET HIGH8281 (all meet finite mass threshold). Sparse removes21419, retains78067. 128313 literal interval checks, 38584 dense witness checks, 99486 prior/future low-stock separation checks. At X16384 analytic all-clock retained83484, HIGH retained7002, minimum live high mass15, no live HIGH d<=B and no live RESET HIGH. These are exact original-tick diagnostics without the earlier entropy/endpoint/low-occupation masks. No nonzero asymptotic local phase-diversity test is claimed.

Both new files remain on the unified branch. Main and the two independent research branches were not modified.
