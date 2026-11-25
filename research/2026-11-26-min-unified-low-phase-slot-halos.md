# Low-index high departure slots, RESET halos, and entropy transfer of mass thresholds

2026-11-26 JST. Continues [8ea2abc61a82](https://github.com/tara-sooo/A166944-Lean/blob/8ea2abc61a8210be51c6b75261ba2e16c30e7108/research/2026-11-26-min-unified-rational-band-phase.md), [09559cdebe9d](https://github.com/tara-sooo/A166944-Lean/blob/09559cdebe9d44a0a2b5f6a64299e49eeaa1453a/research/2026-11-25-min-unified-deficit-packing.md), and [3fe50cf63782](https://github.com/tara-sooo/A166944-Lean/blob/3fe50cf6378294cdaa25cacc0e9f9cda16a2174c/research/2026-11-25-min-unified-stable-strand-clock.md). Independent heads verified unchanged, prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. Read the stable-heavy [canonical renewal map](https://github.com/tara-sooo/A166944-Lean/blob/e1ad9e2b434c652699e1bc9a0797887631e0ea6d/research/2026-11-25-min-clock-canonical-renewal.md) again; it treats thin canonical departures at a shorter clock scale. Here use the long prime-root ensemble, actual full exit-slot mass, weighted selected-prime sieve, and all-event halos. No bound on the entire canonical renewal basin, no Lean compilation or twin-prime proof.

## 1. Exact low-phase departure slots

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN gain-stopped prefixes and original terminal snapshots are unchanged. Natural HIGH means p>=Q, r(C)>p/sqrt(log p). Actual wait w<=2r<=3(p-1), gain p-1. A true occupied tick (j,C) counts b(C,j) original tags in completed waits (terminal snapshots alone not counted). All tags at this tick share the same deterministic next actual exit and selected p.

An actual HIGH event with prehorizon C, departure v, selected p and parity s=v mod2 has posthorizon D=C+p-1 and adjusted phase
    phi=2v-D-6s=2p k,     k>=0 integer.
This identity is inherited from the stable-heavy arrival geometry. The sign of eligibility of p is unique at C, and determines parity s: p|C-1 implies s=0, p|C+1 implies s=1. Consequently for each fixed (C,p,k) there is AT MOST ONE actual departure time, namely
    v=(C+p-1+6s+2p k)/2.                                 (1)
Some such triples are impossible by the parity condition, or not selected by MIN; count them anyway in upper bounds. In particular k=0 RESET has one possible time per (C,p), not O(H/p) possible times. This is true even if many original tags arrive into this exit from different recorded prevertices.

Define an exit slot (C,p,v) by the full original set of tags that complete this exact event. Its mass n(C,p,v) is exactly b(C,v-1): all completed waits have positive integer length, every member occupies that last tick, and every tag occupying it in a completed wait has the same exit by determinism. This is not the mass of only tags entering at one recorded time or surviving an earlier accounting mask.

The parent uniform selected-prime quotient sieve gives
    # { C: p is eligible and r(C)>p/sqrt(log p)} << X/(p u²)       (2)
uniformly for Q<=p<=B. Indeed write C=p(2j+1)-sigma and sieve the quotient and other neighbor by odd primes below B^(1/8); the dimension-two bound applies, and log p=Theta(u). Include both signs. This is the selected-p version of the high least-factor support, not an estimate of number of actual slots or roots. The sum of reciprocal p on [Q,B] is O(ell/u).

## 2. All-event gain halos around low-index slots

Take K=floor(u²), kappa=max(2,floor(u^.25)). Use the caps
    m(p,0) = H u²/(kappa p ell²),
    m(p,k) = H u²/(kappa p (k+1) ell³),     1<=k<=K.           (3)
Do not round them up to 1. Mark each ORIGINAL high centre on an original tag whose complete exit slot has k<=K and n(C,p,v)<=m(p,k). On that same tag mark every completed event whose entire selected gain interval is contained in
    [C-kappa p, D+kappa p], D=C+p-1.                         (4)
This includes the central event, previous and following LOW, MED and HIGH events, and short RESET-to-RESET sublists when they fit. Each centre is determined using full original slot mass; do not re-evaluate after removing tags. The centre may be an original terminal-crossing event, but (4) never invents a continuation beyond a tag's stop. A marked event is paid once in the union, by priority after earlier masks.

On each tag its gain intervals are disjoint; total gain of marked events is at most the length of the union of its halos, hence at most sum over its centres of (2 kappa+1)p. Actual wait is <=3 times that gain. Therefore the absolute total cost of the union is bounded by
    W_halo << kappa sum_(eligible original slots) p n(C,p,v)
            <= C0 kappa sum_(p,k) p m(p,k) * X/(p u²)
            = C0 kappa X/u² sum_(p,k) m(p,k).
Use (2), (1), sum_p1/p=O(ell/u), and sum_(1<=k<=K)1/(k+1)=O(ell). Separately the RESET and positive-index parts have the same bound:
    W_RESET << (X/u²) H u²/ell² * ell/u = O(NT/ell),
    W_pos   << (X/u²) H u²/ell³ * ell/u * ell = O(NT/ell).
Hence
    W_halo=O(NT/ell)=o(NT).                                 (5)
This is one LINEAR actual-clock payment over the entire original population, including the waits of other labels in (4); no assumption of small cohort size globally and no quadratic energy estimate. Actual tag multiplicities enter ONLY through the exact slot cap. Overlaps of halos are not counted twice in the residual. If kappa is chosen to be 1 instead, the same cap formula gives a stronger centre mass threshold and a smaller halo; the present choice trades a factor u^.25 of the cap for a growing gain neighborhood.

In particular a surviving actual high RESET event must have full exit mass
    n(C,p,v)>H u²/(kappa p ell²).
For p~B this is Omega(B u^(3/2)/ell²); for smaller high p the threshold is even larger in proportion to B/p. A surviving positive-index high event with 1<=k<=u² requires
    n(C,p,v)>H u²/(kappa p(k+1)ell³).
These are original exit-slot masses, not a lower bound on all recorded-arrival group sizes. The next section transfers the thresholds to true tick mass.

Optional all-index form: replace the positive-index harmonic cap by H u²/[kappa p ell² (k+1)(1+log(k+1))²] for every integer k>=1. The sum of the k-weights converges, so (5) holds without any upper cutoff on k. The resulting cap is stronger at very small k and weaker at large k than (3); one can use both at constant-factor cost. This is a paper extension, not tested in the finite audit.

## 3. Transfer to early tick mass using the true-tick entropy budget

Use the original true-tick state forest of 3fe50cf63782. At a state V with original mass n_V and continuing mass c_V, each continuing tag's transition to U carries nonnegative token
    e_M(V)=log(n_V/c_V)+log(n_U/c_V).
The global sum over all original tag transitions is <=N(2+log N), by the merge-entropy telescoping and expiry loss argument in that note. This is a statement about the full original forest; no rank recomputed after an accounting deletion.

Within a completed wait at C, all ticks from the recorded arrival through v-1 are present on the tag's original path. The transition token dominates log(n_U/n_V) (subtracting gives 2 log(n_V/c_V)>=0). Thus the sum of tokens on this wait, from its first occupied tick through its last, is >=log(n_slot/b(C,t)). The mass b(C,j) is nondecreasing in j within this slot: existing tags continue to the common exit, and new tags may join. This property concerns completed waits only; incomplete/terminal snapshots are excluded. Therefore if any occupied tick of a tag's completed wait has b(C,j)<exp(-delta)n_slot, its first tick does as well and the internal token sum is >delta. The internal transition segments of distinct completed waits on one tag are disjoint, even if they share a postvertex; the final jump transition is not used.

Choose delta=1/u. Mark the WHOLE actual wait of every such tag/event. Since each wait is <=2B, their total actual-clock cost satisfies
    W_growth <= 2B N(2+log N)/delta=O(NB u²)=o(NT).           (6)
Here log N=O(u), B u²/T ->0. This applies to all labels, not just HIGH, and also covers arbitrary initial tag masks. Empty internal segment for a one-tick wait cannot have the indicated mass change. The exact entropy budget is inherited; the new application is from first to last tick within an original completed event.

After (5),(6), for EVERY surviving original low-phase HIGH tick (not only a stable-strand focal tick),
    b(C,j) >= exp(-1/u)n_slot > exp(-1/u)m(p,k).              (7)
The first inequality uses the full growth mask and the second the centre mask. In particular the RESET threshold is Omega(B u^1.5/ell²) uniformly, including early arrivals at the same departure. This avoids interpreting a large last-tick mass as evidence of a large early cohort without payment.

At an original stable-strand retained focal event the parent entropy-window comparability also gives n_g >=(1-delta_old)b(C,j), delta_old=exp(1/ell)/ell. Hence the same threshold up to 1-o(1) transfers to its common through-cohort. If a retained focal event's full gain interval lies in the halo (4) of an actual low-index HIGH centre on its own original path, that centre must have n_slot>m(p,k). If the original entropy window covers the entire interval from the focal tick to the centre's last tick, the token sum <=1/ell gives b(focal)>=exp(-1/ell)n_slot. For the inherited stable focal window this holds for all such centres eventually: the gain distance is O(kappa B)=o(D_window), where D_window=floor(T/(u ell²)), and both true states have prehorizon distance bounded by that amount. Thus low-mass stable strands cannot merely pass close to a RESET on the same original path without triggering an absolute halo payment. This local comparison does not assert that every neighbouring centre survives other masks. The original window and membership are used without recomputation.

## 4. Consequence for short RESET-to-RESET segments

Suppose consecutive original natural HIGH events on a tag both end in RESET, with intervening completed gain e<=L=floor(u^.75) as in 8ea2abc. Their labels p,q may be arbitrary distinct high primes (the zero-zero case excluded from that rational-band phase test). The full interval from the first prehorizon through the second posthorizon is contained in the first centre halo (4) whenever e+q-1<=kappa p. This condition is automatic eventually if p and q are comparable, or q<=kappa p/2; e=o(p). For p near the bottom Q it need not hold for all q, so keep the exact condition. The same reasoning using the second centre's backward halo holds if p-1+e<=kappa q. At least one of these two containment conditions always holds for large X since min(p,q)<=max(p,q) and e=o(min(p,q)); the halo of the larger label contains the whole interval. Therefore, if the larger-label endpoint's full RESET slot mass is <= its cap, the ENTIRE short RESET-to-RESET segment is unconditionally paid by (5), including all intermediate waits, without a relation between p and q. If either endpoint survives, that larger-label endpoint has original slot mass >m(max(p,q),0). If the smaller endpoint survives and has its inherited stable entropy window, its focal mass is also >=exp(-1/ell) times this large-slot mass, by section 3. If both endpoint waits survive, each must pass its own cap (7).

This directly addresses the both-RESET branch of the preceding phase-drift dichotomy, not all RESET renewal arcs. Long intervening excursions or very thick endpoint slots are not bounded by this statement. In particular no claim of a uniform upper bound on canonical basin sizes.

## 5. Relation to previous sufficient condition

Apply these fixed new masks by priority to the earlier actual linear clock ledger. Under the no-twin assumption the original W_all>=N(T-6)/2 lower bound is unchanged. The sufficient condition liminf (A_rem+L_rem)/(NT)<1/2 remains valid on the smaller residual. Relative to the previous generic harmonic deficit cap H u/[ell²(d+1)], at a high RESET the pre-wait deficit is at most p+5; at its p-scale deficit the new RESET slot threshold is larger by order u/kappa. The improvement is at the p-scale; for very tiny d the earlier envelope can still be stronger, and the masks are combined by union, not by replacing that envelope globally. The new positive-index cap likewise gains order u/(kappa ell) at d~p(k+1). These are threshold comparisons, not an asserted asymptotic strict separation on realized paths. The remaining very heavy RESET slots and high-index nonRESET strands, longer renewal excursions and remaining non-HIGH clock are open. No external novelty claim, no Lean kernel verification, no twin-prime proof. Main and independent branches unchanged.

## 6. Numerical audit

Source [min_unified_low_phase_slot_halo_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/5a2e3208b525d4429bc8f9d198d0562dcaec2f5a/research/min_unified_low_phase_slot_halo_audit.mjs), exact remote readback at 5a2e3208b525d4429bc8f9d198d0562dcaec2f5a. Ran its audit function in the available ECMAScript runtime, not a separate Node process:
    node research/min_unified_low_phase_slot_halo_audit.mjs 256 1024 4096 16384 65536

Five normal diagnostics and one stress at X65536 passed. Finite T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), high r>3 and 2r>p. Normal K4,kappa2, m=12B/[p(k+1)]; stress K8,kappa3,m=24B/[p(k+1)]. These are diagnostic substitutes for (3), not analytic scales. Checks actual MIN against literal per-tick gcd on X256/1024 (431/1239), exact adjusted phase for every completed event, one actual slot per (C,p,k), direct time reconstruction and parity, full exit-slot mass equal to last occupied tick mass, exact mass eligibility, halo centre coverage and every full contained gain interval, RESET-halo subset, per-tag union gain bound and whole actual-clock budget. The script does NOT implement the entropy-growth deletion (6), all-index optional cap, stable-strand window or explicit both-RESET segment classification. Those are paper deductions using the previously proved entropy budget and interval geometry. No numerical verification of sieve constants.

| X/mode | raw HIGH | raw RESET | low-index slots | eligible slots | all marked clock | marked HIGH | remaining HIGH |
|---:|---:|---:|---:|---:|---:|---:|---:|
|256|1753|108|80|79|2111|1570|183|
|1024|3908|985|101|101|6540|3908|0|
|4096|37458|6328|322|319|58275|34935|2523|
|16384|195474|34427|623|609|296875|165560|29914|
|65536|1380549|257778|1628|1566|1692774|1019490|361059|
|65536 stress|1380549|257778|1687|1662|2062589|1276582|103967|

Largest normal: 5709 prime roots,140255 completed events, original all clock2395330. 1628 exact slot formula, uniqueness and last-tick mass checks; maximum slot mass43. Eligible slots1566 of which741 RESET; 6663 actual centre incidences, own wait913680, full halo marked1692774 including1019490 HIGH and673284 nonHIGH. RESET-only halo marked749958 (subset of full union), marked RESET-ending high241916 of257778. 37543 forward RESET-neighborhood checks, 97738 marked events. Exact union gain2169732 <= sum halo lengths6010612, actual cost <=3 times that sum. Stress marks2062589 including1276582 HIGH, all257778 RESET-ending high, 45871 forward checks. Finite percentages are not asymptotic rates, and the audit does not apply earlier masks cumulatively.
