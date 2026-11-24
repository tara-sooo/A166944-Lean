# Parity-corrected height lattice and disjoint signed record erasure

2026-11-25 JST. Continues 653ee71a07727583c38632a3cab0eec5925c3447 on the SAME research/min-cycle-forest-2026-11-24 branch. New exact clock-and-horizon lattice, deterministic backward interval erasure and signed credit inequality, compatible with the earlier probabilistic surplus deletions. This addresses the overlap issue by avoiding separate per-band resource charges: it does not give a global sum of those band inequalities. Exact finite common-CRT path audits. No external search or Lean compilation. The remaining record surplus (or signed net record surplus) is not proved sublinear, and the physical far-coalescence upper bound remains open.

## 1. Exact clock correction

Use the common CRT ghost, finite initial prime segment or infinite alphabet. Initial common time parity epsilon, independent coordinates c_p,b_p mod p. At an event of label p at relative tick s, let g_- and g_+=g_-+p-1 be its pre/post-gains, and chi=(epsilon+s) mod 2. The exact selected clock/eligibility conditions are
    c_p+g_- == 1-2chi mod p,
    b_p+s == 2chi mod p.
The event's absolute clock phase mod 2p is 0 when chi=0 and p+2 when chi=1. Let h=2s-g_+ at attained states, and put
    J=h-6chi.
At time zero g=0,h=0, J_0=-6epsilon. At every event p,
    J == c_p-2b_p mod p, and J is even.
Thus all attained post-event J values for this label lie in a single even residue class modulo 2p. This holds also at p=3. It requires no nonnegative-height restriction and no bounds on intermediate labels or LOW runs.

For two occurrences of p, earlier and later, let delta_s>0, delta_g>0 denote the differences in their elapsed times and POST-gains, and e=chi_later-chi_earlier in {-1,0,1}. The gain difference equals the pre-gain difference for these equal labels. From the clock and eligibility conditions,
    delta_s=2lp+(p+2)e,
    delta_g=2mp-2e,
    delta_J=2p(2l+e-m)
for integers l,m. Since the earlier event adds p-1 and subsequent gains are nonnegative, delta_g>=p-1. For p>=5 this implies m>=1, including e=-1. If delta_J>0, then 2l+e>=m+1>=2. It follows that
    delta_s>=2p if e=0,
    delta_s>=3p+2 if e=1,
    delta_s>=3p-2 if e=-1.
In particular any pair of repeated p occurrences with delta_s<2p has nonpositive corrected change, even if some of the intervening individual steps have positive signed drift. These sharper elapsed lower bounds concern time BETWEEN occurrences, not the completed wait immediately preceding the later event. The m>=1 argument is not used for p=3. Every positive corrected change between equal labels is >=2p, for all odd p. Every strictly negative one is <=-2p.

## 2. Exact nonoverlapping backward erasure on a peak prefix

For an arbitrary finite observed trajectory up to elapsed U, choose a first attained maximizer of h (including time zero) and truncate at it. If h peak D(U)>0, its total gain is <=2U and every earlier gain is <=2U, by monotonicity. Number the event poststates, with sentinel index 0 at initial time. For any label p at index i, call i a strict record if its J_i is strictly larger than EVERY earlier J at that same label; the first occurrence is fresh and handled separately. For a nonfresh index i define j(i) to be an earlier occurrence of p with maximal J (latest in case of ties).

Scan BACKWARDS from the peak index:
    if i is nonfresh and J_i<=J_j(i), jump to j(i) (erasure);
    otherwise move to i-1 (ordinary step).
An erasure interval is the segment of actual events with indices (j(i),i], including its ending repeated event, not its starting event. Every such interval has net J change J_i-J_j(i)<=0, an integer multiple of 2p. Every ordinary step ends at a fresh event or strict same-label record. Index strictly decreases, so the scan terminates at 0; the erased intervals and ordinary steps partition the truncated original event sequence exactly, with no repeated time or gain charge. Their signed changes telescope. This is an accounting operation on the original trajectory, not a claim that deleting events would give another legal trajectory with the same clocks.

Let R be the sum of positive J increments on retained ordinary REPEATED steps. Let C be minus the sum of signed J changes on all erasure intervals, and Nminus the sum of negative magnitudes on all ordinary steps (including ordinary fresh ones). All three quantities are nonnegative. Let P_f be the sum of positive J increments on retained ordinary fresh steps. Then the exact identity on the all-event scan is
    J_peak-J_0=P_f+R-C-Nminus.
In particular
    D(U)<=6+P_f+[R-C-Nminus]_+.
Each fresh ordinary change is <=2w+6<=8w because its wait w>=1. Use the previous theorem E F_wait(U)=O(U/log(2U)) for all fresh completed waits. Then
    D(U)<=6+8 F_wait(U)+[R-C-Nminus]_+.
All nonrecord repeat steps encountered in the backward scan, including those with large individual positive change, are removed together with their preceding compensating interval. A repeated record step may itself be inside a removed interval, so the retained ordinary record set can be strictly smaller than the full record set. No summation of overlapping arbitrary return intervals is required.

For p>=17, any positive ordinary corrected step has w>p/4: its change is at most 2w-(p-1)+6, which is negative if 4w<=p. Thus a retained positive repeated step at such p requires simultaneously a strict same-label J record (increase >=2p over all previous occurrences), the elapsed constraints in section1 relative to the immediately preceding same-label occurrence, and the local long-wait condition. Unlike a per-label weight budget, the erasure also retains a NONNEGATIVE credit C that can absorb positive changes at unrelated labels. The credit is not a new probabilistic estimate; its value depends on the actual trajectory.

## 3. LOW grouping with the same exact erasure ledger

Choose A>=5 and L=2 product_(3<=p<A)p as before. Scan only the HIGH event poststates (labels >=A), plus the sentinel at time zero. Every omitted consecutive LOW run has gain <L and maximum signed height increment <=5L by the established LOW-only barrier and elapsed/gain lemma. If the attained peak falls in a LOW tail, take the last preceding high event (or sentinel) as the scan endpoint. Its corrected difference to the peak is <=5L+6. Including h-J<=6 and J_0<=0 gives an additive upper-bound constant 5L+12; this is conservative and valid even with no high event.

For high index i and its previous HIGH index i-1 (or sentinel), define a_i to be the EXACT corrected height difference J_i-J_(i-1). This represents the intervening LOW run followed by the high event i; the low run precedes the high event rather than follows it. Thus
    a_i <= 2w_i-(p_i-1)+5L+6.
Use the identical erasure rule between high indices, with all previous occurrences of the same high p still present in the high sequence. The erased interval and ordinary steps again partition the ORIGINAL event sequence through the last high event (all intervening LOW events are included exactly once). The last LOW tail is separately bounded. The same exact identity between sentinel and last high endpoint holds for P_f,R,C,Nminus defined using a_i. Consequently
    D(U) <= 5L+12+2F_wait(U)+(5L+6) K_U + [R-C-Nminus]_+,
where K_U is the number of distinct globally selected labels by U. Indeed each ordinary fresh high step has a_i^+<=2w_i+5L+6, and no fresh label is counted twice. The previous unconditional first-selection count E K_U=O(sqrt U/log(2U)) follows by splitting at sqrt(2U) and using the fresh hazard <=2/p^2 above it. For L<=U^(1/4), the expectation of all additive/fresh terms is O(U/log(2U)). Thus
    E[(D(U)-[R-C-Nminus]_+)_+] = O(U/log(2U)).
This is an upper reduction, NOT an equivalence: the right-hand residual can exceed the actual peak. The earlier exact signed bank equivalence remains available.

Each erased interval of high label p spans >=p-2 elapsed time by its clock classes. Since intervals are disjoint, their count n_E<=U/(A-2). Write T_E,G_E for their total actual elapsed time and gain. Their original (uncorrected) signed changes telescope separately over intervals, with parity changes at most 1 each. We obtain
    C=G_E-2T_E+6 sum_(erasures) (chi_end-chi_start),
    G_E >=2T_E-6 n_E >=2T_E-6U/(A-2).
In particular the selected erased intervals contribute no net positive corrected height, and their actual total gain pays at least twice their elapsed time up to a sublinear error as A->infinity. The strict negative intervals contribute integer multiples >=2p to C. This gives a nonoverlapping time/gain resource inequality, rather than charging the same off-band gain separately for many label bands. It is not a global bound on the band's required off-band gains from the previous note.

## 4. Compatibility with earlier weighted estimates

For p>=10L+14, if w<=p/4 then a_i<=0; otherwise a_i^+<=2w<=4p, since p>=5L+7. For all p>=A, a_i^+<= (4+(5L+6)/A)p. These are the same quantitative bounds (up to harmless additive constants) used to delete the earlier following-LOW block positive surpluses. We may apply the previous event-based classifications to a_i^+ at retained ordinary repeated high events, even though the grouping is now preceding-LOW. In particular use:
* the weighted long-repeat sieve for p>=z=ceil(U/log^(5/2) U), and for p>=z0=ceil(sqrt(2U)) with first-to-return stride m<=floor(log^(3/2) U) in its first-gain relation (the old m convention, NOT the clock lattice m above);
* first k0=floor(sqrt(log U)) repeat occurrences at each p<z0 (or the same first-long-wait rank condition);
* comparable fresh-anchored runs marked by the previous F^r chain bound;
* bounded-support short consecutive-return exclusions at Q=ceil(U^(k/(k+1))) for each fixed k and allowed growing index bound from the earlier relation theorem.
All these classifications depend on the original, unmodified path, not the path after accounting erasure. We use their p-weight, completed wait, or exceptional-event bounds, not an equality with the earlier following-LOW surpluses. For the short-return exclusion, sum a_i^+<=2 sum w_i<=2U on the exceptional event, for p>=5L+7. Choose L<=log^(1/8) U and previous F,r etc. The earlier upper bounds show that the sum R_del of retained positive repeated increments belonging to the union of these deleted classes has expectation o(U). The cap pre-gain<=2U is satisfied on the positive-peak prefix. With R_res=R-R_del>=0, the inequality [x+y]_+<=[x]_++y for y>=0 gives
    E[(D(U)-[R_res-C-Nminus]_+)_+]=o(U).
Credits C,Nminus refer to the actual scan; they are NOT also removed from the ledger when dropping R_del. No double-counting of credits. This strengthens the preceding nonnegative positive-surplus reductions by retaining only strict-record events visited by the backward scan AND subtracting disjoint negative credits. The new residual remains unproved sublinear. In particular neither this inequality nor the deterministic narrow-band theorem establishes eta->0. The full signed-bank convergence and global physical far-coalescence estimate remain independently necessary in the current route.

## 5. Finite diagnostics and persistence

Saved research/min_ghost_corrected_height_record_erasure_audit.mjs and research/min_ghost_corrected_height_record_erasure_results.json; exact remote readback at 53a74dd2be8fe0fc16908e8f04c08c6552b364b7. Run node research/min_ghost_corrected_height_record_erasure_audit.mjs 256 1024 4096 16384 65536. Independent pseudorandom CRT coordinates, fixed seeds, finite initial alphabet of odd primes <=4U. 256 paths per window except 128 at U65536. All-event scan and HIGH scans with A=5,7,11 (L=6,30,210). These are finite diagnostic cutoffs, not the slowly growing analytic choices. The finite-to-infinite O(1/log U) coupling error is an asymptotic estimate, not calibrated finite-sample error.

For every executed event check actual clock/eligibility and parity-corrected residue; for repeated labels check both exact lattice identities, record lattice gap, and for p>=5 the positive-return time lower bounds and nonpositive short opposite-clock returns. For each scan through the first original attained peak, verify disjoint coverage of original events, exact time/gain/height telescoping, nonpositive erasure changes, ordinary endpoint type and local increment upper bound, the LOW-tail bound, and positive-record long-wait necessity. Check per-path peak upper bound including C and Nminus, and for A>=5 the nonoverlapping elapsed and gain resource bounds. No earlier weighted-sieve deletion is applied in the numerical residual; the combined deletion in section4 is a paper deduction.

At U65536,128 paths: 7642 executed events, 5682 repeats (3193 nonrecords, 2489 strict same-label records), 207 short opposite-clock repeats with p>=5 and delta_s<2p, 2030 positive consecutive-p corrected-change checks. All-event scan: 289 erasure intervals (153 strict negative) covering 2366 events and 47784 elapsed ticks with total gain134194, exact credit38878. All positive repeated ordinary-step increments before scanning sum30994, retained sum19378, sum over paths of [R-C]_+ equals10084, sum of [R-C-Nminus]_+ equals7720. Note that positive parts are computed PER PATH before aggregation; comparing total credits directly to total positive increments would be invalid. A5: before scan23214, retained15976, credits30912, per-path residual after credits5626; A7:19836,14744,30960,4920; A11:15654,11912,28426,3630. At A11,68 disjoint intervals cover1273 actual events;41 intervals strictly negative;32 of128 paths have positive net residual after both credits. Different A values change the grouping, so do not compare absolute before-scan values as if they were the same quantity. Full-path count and scan counts have different ranges (scan truncates at first peak). These are finite pathwise structural checks and empirical reductions, not an asymptotic upper bound on residual or a numerical estimate of the implied constant. No Lean compilation.

## 6. Next target

Use the strict per-label record condition and the exact positive-return clock lattice to estimate the net residual R_res-C-Nminus, rather than charging each arbitrary repeated interval separately. In particular the remaining high record repeats require a large enough corrected-height increase AND elapsed gap, as well as the earlier rank/span/run failures. A direct probabilistic or deterministic bound on that signed residual is still needed. The global physical far-coalescence upper bound also remains open. No main edit, no new branch, no twin-prime proof.
