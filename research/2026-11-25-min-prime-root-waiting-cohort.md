# Stationary entry cohorts and band-adaptive local ranks in the waiting forest

2026-11-25 JST. Continuation of e8c9304692ff0c4d5dccabce62098c114832547c on research/min-prime-root-repeat-energy-2026-11-25. Two new actual-clock exclusions: use the previously available factor-band decay in the endpoint density to enlarge formation caps, and use two-sided local ranks at stationary/arrival first waiting mergers, including a subdivision of the stationary branch into original entry cohorts. The latter has a truncated-potential bound even if the two branches and the total visiting mass are very large. Arithmetic bounds the number of eligible entry cohorts and yields a sufficient rank threshold inside a single cohort. No bound on the whole residual or twin prime infinitude. No Lean compilation.

## 1. Inherited ledger and band-adaptive density

Retain X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts, Q=ceil(B/u). Original gain-stopped MIN prefixes, completed waiting intervals, terminal snapshot, disjoint fixed finest original source cells, sparse medium quotas and gap-adaptive phase/small-pool allocation are unchanged. The target is actual completed time W_all=o(NT). The high proxy sufficient condition is still independent.

For a fixed ordered source pair and a later medium event E, let c(M,M',E) be the charge from any subset of the existing ledger and b_M(E) its actual E-plus-LOW time block length. The gap-adaptive cap estimate in 8fd0a10 and actual-relative transfer in 3ec0b49 give the stronger band-specific inequality
    c(M,M',E)/b_M(E) <= (C0/m_g) (P/Q)^(1/8),
    m_g=u^(19/4)/ell^4, P<=r(E)<2P.                  (1)
Indeed the original full pool denominator is >=m_{P,S}/(2 max(K_P,U)), the focal has <=k_P predecessor choices in all gap bands together, and
    m_{P,S}/((1+L/P)max(K_P,U)) >> m_g (Q/P)^(1/8).
The constant in (1) is uniform. Give each charge constant density across its actual E-plus-LOW block. Blocks for different E on a fixed ordered pair are disjoint. No comparability of b_M(E) and b_M'(E) is required. All previous paid classes, including the waiting mass/rank exclusion of e8c9304, remain paid by priority.

Set H0=ceil(4H)+2 and m0=max(1,floor(m_g/u^.25)). For x=|j-j_*|<H0 at a charged unit j of a pair with first waiting meeting j_*, use the band-adaptive integer threshold
    m_P(x)=max(1,floor(m0 (Q/P)^(1/16) sqrt(H0/(x+1)))).
It is at least the old m(x). At every threshold m, the previous mass and chronological rank tests each count at most mN unordered first waiting pairs in the original disjoint cells. For fixed P,x at most two times and two directions per pair are charged. Hence their enlarged union costs
    << (N/m_g) sum_P (P/Q)^(1/8) sum_{x<H0} m_P(x)
    << (N m0 H/m_g) sum_P (P/Q)^(1/16)
    = O(NT/u^.25)=o(NT).                             (2)
The dyadic sum is a convergent geometric budget (P ranges from 2 to Q). This preserves the low-band gain instead of replacing (1) with its uniform bound. In particular no extra O(u) band count appears. The cap depends on the later focal least-factor band, NOT on the first merger's incoming primes.

## 2. Original stationary entry cohorts

At first waiting vertex v=(j,J) in a fixed original source cell, let S denote its stationary branch (tags already at J at j-1), s=|S|. The other immediate branches A_i have masses a_i, and consist of jumps from J-q+1 with actual incoming q (one branch per q) or singleton injected roots. All are original visiting masses before expiry at v. If s>0, every member of S has a completed outgoing wait still ongoing at j, with next tick >j; its original entry time j0 is strictly earlier than j. Write q' for its incoming selected prime on that visit, or 0 for a root injection. Refine S into cohorts indexed by (j0,q'). These are subsets of the currently stationary branch, not all tags ever entering a state, since expired tags are absent.

Let r_v be the least eligible prime at J. It exists since S is nonempty. The original wait at J is <=2r_v. Therefore every cohort has
    0<j-j0<2r_v.                                     (3)
For q'>0 the incoming congruences are
    q'|J+2(j0 mod2),
    j0=0 mod 2q' if even, q'+2 mod 2q' if odd.
As J is even, an odd q' divides at most one of J,J+2. Thus its parity and single progression of possible entry times are determined by J. The number omega_v of possible positive incoming prime labels is <=omega(J(J+2))=O(u/ell), from the product of k distinct primes being >=(k+1)! and J=O(X). At most one root entry cohort exists for J because original root horizon 2M-2 determines M. An arriving jump branch with label q satisfies the same incoming congruences at j; for a root arrival put q=0.

Choose Z=max(1,floor(u^(1/8))). For each arriving branch A_i define the eligible earlier cohorts in S by the union of:
    (R) q'>0 and q'>=r_v/Z;
    (N) j-j0<=2Z (includes a root cohort);
    (L) q'=q>0 and j-j0<=2Z q.
Let K_i be the exact number of distinct eligible cohorts. In R each q' has at most Z+1 entry times by (3) and period 2q'. In N each label has at most 2Z possible integer entry times. In L the same parity/progression as the arriving branch gives at most Z earlier entry times. The possible root contributes at most one. Consequently
    K_i <= (3Z+2) omega_v+Z+1 = O(Z u/ell).          (4)
No sieve or independence of arrival histories is assumed. These are restrictions on the number of actual stationary entry groups, not bounds on their masses. The incoming label of the arriving branch can be small. A later terminal arrival is allowed; the earlier stationary tags must have actual ongoing waits as above. If S is empty this paper's new local-rank test is not applied.

## 3. Local rank score (with or without arithmetic cohorts)

For a finite nonempty tag group G sorted by increasing original prime start, put
    R_G(M)=min(position_G(M), |G|+1-position_G(M)).
Then at most min(|G|,2m) tags have R_G<=m for every positive integer m. This differs from the chronological rank among all partners first met in e8c9304. It uses no history beyond this actual branch's current tags.

Consider an unordered first pair consisting of M_a in an arriving A_i and M_s in the stationary S. Let G_s be the entry cohort of M_s inside S. Define
    R_i^S(M_s) = min(R_S(M_s), K_i R_{G_s}(M_s))
                        if G_s eligible for A_i,
                 R_S(M_s) otherwise.
When K_i=0 no cohort is eligible. Define local score
    L_v(M_a,M_s)=max(R_{A_i}(M_a), R_i^S(M_s)).
The raw local score omits the cohort term: max(R_Ai,R_S). Both permit large groups and large chronological partner ranks. The cohort option means, for example, that an arriving tag of local rank <=m may pair with a stationary tag of eligible cohort rank <=floor(m/K_i) even when that tag lies deep inside the whole stationary branch. By (4) the stronger sufficient condition R_Gs<= floor(m/(C Z u/ell)) is uniform over qualifying cohorts, with a suitable absolute C, but the actual test uses the exact K_i. This rank is measured among the tags still stationary at the merger, not among tags that have already expired.

For a fixed m and branch i, the selected arriving tags number at most min(a_i,2m). The selected stationary tags number at most min(s,4m): the raw rank option contributes <=2m, and the cohort option sums <=2 floor(m/K_i) per eligible cohort, hence <=2m in total. Their union counts a tag once. The number of first pairs of score<=m at v therefore satisfies
    B_v^local(m) <= 8 min(s,m) sum_i min(a_i,m).       (5)
This is not the square of the total first-meeting mass; (5) is useful for an arbitrarily large total stationary branch and arbitrarily large arriving branches.

## 4. Capped cross-branch potential

For the same convex truncated quadratic f_m(n)=n² up to m and 2mn-m² beyond m, one has for a,b>=0
    f_m(a+b)-f_m(a)-f_m(b) >= min(a,m) min(b,m).      (6)
For a,b<=m and a+b<=m the left side is 2ab. If a,b<=m but a+b>m it equals 2ab-(a+b-m)^2>=ab since a+b-m<=min(a,b). If a>=m and b<=m it is 2mb-b²>=mb, symmetrically for b>=m and a<=m. If both >=m it is m². These cases also cover zero.

Sequentially merge the stationary branch S with all arriving branches, in any order. The accumulated mass is always >=s, so telescoping (6) gives
    D_v(m)=f_m(s+sum a_i)-f_m(s)-sum f_m(a_i)
            >= min(s,m) sum_i min(a_i,m).
Combining with (5) yields B_v^local(m)<=8D_v(m). Sum over the full original waiting forest and disjoint source cells. Every nonexpired tag group moves intact; singleton injected roots and terminal expiry give the established sum D_v(m)<=2mN. Thus
    # unordered first waiting pairs with stationary/arrival
       formation and local score <=m  <=16mN.       (7)
The sum counts each pair at its unique first waiting meeting. This is a global bound at every m, independent of the number of entry cohorts, labels, events, or waiting-time layers. It is also independent of the old global first-mass and chronological rank criteria. No claim that large stationary mass itself is rare.

For the density (1) use the same band-adaptive m_P(x). Pay each previously unpaid charged unit if the pair has a stationary/arrival first meeting and L_v<=m_P(|j-j_*|). This works for both focal orientations, whether the merger is in the past or the future, including blocks straddling the first meeting. For fixed band and distance, (7) counts <=16 m_P(x)N unordered pairs and each has at most two clock times and two focal directions. By exactly the geometric summation in (2),
    W_local << (N/m_g) sum_P (P/Q)^(1/8) sum_x m_P(x)
              = O(NT/u^.25)=o(NT).                  (8)
No need to change the previous actual-cost allocation or count an entire E block as paid when only part meets the test. The raw rank and cohort-only subsets each obey the same bound. The cohort-only subset is not asserted to contribute a positive fraction in the analytic regime.

## 5. Residual and relation to earlier proofs

Keep all prior paid classes by priority, then the enlarged mass/chronological-rank test (2), then the local test (8). Each remaining charged unit of a pair with a waiting meeting now has both first local mass and chronological rank >m_P(x). If its first merger has a stationary branch, its local score also exceeds m_P(x). In particular, if the arriving tag's local rank is <=m_P(x), the stationary partner lies beyond the first/last m_P(x) tags of the whole stationary group and, in an eligible cohort, beyond the first/last floor(m_P(x)/K_i) tags of that cohort. This is a genuine restriction on pairs even when the stationary group is large. Jump/jump first mergers without a stationary member in the pair and never-meeting pairs receive no new local-rank exclusion. The latter have no formation time. The first-mass/rank band improvement can also cover jump/jump pairs.

The joint OPEN sufficient conditions remain all residual actual medium costs summing to o(NT) and the earlier high proxy residual E_phys,admitbad+E_async,bad=o(T²Bu) on the same unbounded dyadic windows. Next targets: use actual source ordering and entry cohort rank to control pairs deep in both groups, or derive arithmetic control of never-meeting concurrent pairs. The new potential counts selected local ranks, not all cross-branch products. No twin-prime proof or formal verification.

## 6. Finite audit

Standalone ECMAScript research/min_prime_root_waiting_cohort_audit.mjs, final exact remote readback at 51f03934d5fc67dbae7fc106135e50ccc68e5990, blob 0b4160ccea2736ad67cc17c6c8bf7534bfec63af (initial 952f2e18952d0fcda599f16a2c9cd03d900d7fc8). Run:
    node research/min_prime_root_waiting_cohort_audit.mjs 256 1024 4096 16384 65536 262144
All final 42 runs (seven modes x six X) passed by executing the audit function in the available ECMAScript runtime. Inherited original canonical paths, literal comparison, LOW/actual quota/phase, previous paid occupation, full event-compressed waiting forest and small-window independent chronological rank oracle. New exact current stationary entry metadata, entry congruences and wait windows, eligible-cohort count, local scores for ALL original stationary/arrival first pairs (including root arrivals), per-vertex potential inequality for four tested caps and global score histogram cumulative bound (7) at every observed score, band-adaptive and local unit-time charge partitions and integrated layer counts. Independent root-stationary pair total check. The finite ledger uses the inherited finite actual-relative coefficient, not a numeric test of asymptotic (1) or the geometric weighted budget. No cumulative optional masks. Analytic finite y3,L6 and m0 as before, Z=max(1,floor(u^.125)); analytic residual empty before new tests, but formation tests nonvacuous. Diagnostics m0=2,Z=2 and inherited altered gap/phase/fast parameters are not asymptotic evidence.

Largest X262144, N20390:
- Analytic formation 114187 stationary/arrival pairs =111021 stationary/jump+3166 stationary/root. 38869 original incoming-label checks,13022 eligible-cohort degree checks,51624 local-potential checks, max7 observed cohorts and max3 eligible for a branch; 1676 pair scores strictly improved by the arithmetic cohort term over the raw whole-stationary score. No actual retained ledger to pay.
- Common wide/phase/stress/broad/concurrent paths: 87301 stationary/arrival pairs=84951 stationary/jump+2350 stationary/root,32262 entry congruence checks,12706 degree checks,50404 local potential checks, max7/3 total/eligible cohorts;1454 pair scores improved. Short 59037 pairs,866 improved. The score histogram is independent of the ledger.
- Concurrent diagnostic: previous residual1438.8716758 after e8c9304 mass/rank exclusion; enlarged band cap additionally pays516.9448637, local raw rank pays671.4161394, cohort-only extra0, remaining250.5106727 (never-meeting cost185.2592593). 2360 directed pairs with band-paid units,4352 with local-paid units. At X16384 previous69.8712121 ->65.1212121 (band3.75, raw local1), all remaining never-meeting; X65536 prior234.9135161 ->68.9333333 (band85.8104858, raw local80.1696970), never cost16.
- Stress largest prior703.8253680 ->21.6106494, band276.9538170, raw local405.2609017, never cost2. Short prior94.4444444 ->0, band50.6666667, raw local43.7777778. Broad prior69.8719212 ->0, band28.4170772, raw local41.4548440. Zero values within floating roundoff. Wide/phase prior empty. No additional retained far charge in these reported diagnostic partitions. The arithmetic cohort subdivision genuinely lowers many original first-pair scores, but does not pay extra retained charge beyond the raw stationary local rank in any of the tested modes/windows. No claim of observed arithmetic-cohort-only cost saving.

Main and other branches unchanged by this checkpoint.
