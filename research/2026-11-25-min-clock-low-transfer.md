# LOW-block clock compression, polynomially relaxed small-event energy, and two-sided clock cells

2026-11-25 JST. Continues 99aa9dbc13e44b2949ece78b4177177f7fb6573b (physical next-event groups), a16e49ac73e59de5b649b03bbb260723dbd212ba (cubic-log short-clock target), and prior LOW primorial barrier. The main new result is a rigorous reduction of the LOW clock budget to small non-LOW events, with a much weaker sufficient energy bound at that small scale. Also gives exact full-budget compression and a pointwise/same-physical/local-projected energy transfer, and optional growing two-sided small-event cores with frozen projected and coarse-clock cell thickness. This is NOT an unconditional negligible LOW-budget theorem. Full twin-prime proof remains open; paper proof, no Lean compilation.

## 1. Setup

Dyadic X, N=X/2 original odd roots M in [X,2X), B=ceil(sqrt(7X)), s=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B. Assume H+2B<=min(K-s), eventually. Keep actual canonical MIN prefixes up to first state at or beyond relative H (including its crossing event), or twin terminal. Strictly increasing even horizons and times; C<=2t; total gain <=G=2H+B+6; at selected p the wait<=2r(C)<=2p, with r(C) least eligible odd prime <=B dividing (C-1)(C+1). Hence full selected weight per root <=1.5G=O(B); elapsed over any completed subpath <=3 times its gain; deficit strip 0<=2t-C<=12B+6. For each occupied pre-event horizon C let w_M(C) be the wait duration clipped to relative [a,H), divided by 2r(C). Then R_M=sum r w<=B; R=sum R_M, E=sum_C r(C)(sum_M w_M(C))^2; 0<=w<=1. Under a no-twin window R=NB. Any o(X) whole-root deletion or o(XB) linear incidence deletion preserves the required lower bound R=(N-o(X))B. The least-factor support imported at a16e49a is

    S(Z)=sum_{0<r(C)<=Z} r(C)=O(X Z/log^3(2+Z)),
    S_*=S(B)=O(XB/log^3 B).                             (1)

Thus E=o(XB log^3 B) on unbounded windows suffices; all sums are over even horizons in [2X,7X). All bounds here hold for any frozen reference family of original roots; the audit uses all odd roots, not the previously pruned family.

Use u=log B, ell=log u, y=max(3,floor(sqrt(ell))), L=product_{p<=y}p, Z=L^2, k=max(1,floor(sqrt(y))). Eventually Z<B, L tends to infinity, and L,Z,k=u^{o(1)}. Indeed log L<=y log y=o(ell). Also L+1>y since otherwise any prime factor of L+1 would occur in L, contradiction; hence k/L=o(1). In finite analytic audit use min(B,L^2), equivalent eventually. Here LOW means selected p<=y; non-LOW means p>y. SMALL means y<p<=Z, LARGE means p>Z (this differs from near-B HIGH in earlier notes).

Every maximal consecutive LOW block has total gain <L by the established primorial barrier: at an even multiple of L no LOW prime divides C+-1; a LOW jump from below cannot jump strictly across that multiple (the divisibility condition forces the positive even distance to the multiple to be >=p-1). Landing on the multiple stops further LOW jumps. Thus a LOW block's full elapsed time <3L and its clipped cost <=b=3L/2. Root or final truncated blocks obey the same bound.

## 2. NEW exact compression of full clock budget onto non-LOW events

For each non-LOW event of a source at pre-horizon D, let b_M(D) be the clipped slab cost of its entire immediately preceding maximal LOW block (zero for empty). Include the final crossing event even if its own clipped cost is zero. Assign the LOW block to this event. Define

    r^#(D)=r(D)+b,
    w_M^#(D)=(r(D)w_M(D)+b_M(D))/(r(D)+b)

on non-LOW selections, zero otherwise. Then 0<=w^#<=1. In particular this does NOT assert equality of the original and compressed quadratic energies. With R^#=sum r^# w^# summed over original tags, and E^#=sum r^#(sum_M w_M^#)^2,

    R^#=R-R_terminalLOW, 0<=R_terminalLOW<=Nb=o(XB),
    S^#<=S_*+O(Xb)=O(XB/log^3 B).                       (2)

The only unassigned block is the trailing LOW block if it is not followed by a non-LOW selection in the full prefix. This includes twin termination. Thus the exact compressed non-LOW energy target E^#=o(XB log^3 B) is sufficient, by Cauchy R^#^2<=S^# E^#. A non-LOW event can carry positive compressed weight even if its own original slab occupancy is zero. No clipping or support shortcut that ignores this is allowed. This construction alone does not upper-bound E^#; the next section gives a stronger reduction using natural small-event energy.

## 3. NEW LOW budget controlled by small non-LOW event energy

Let R_LOW,R_s,R_l denote natural original slab costs on selected p<=y, y<p<=Z, p>Z, respectively. Define U_s(D) using original clipped weights of all small non-LOW selections, and E_s=sum r U_s^2. Analogously U_l,E_l for large selections. Full E includes cross terms, but linear costs sum exactly R=R_LOW+R_s+R_l. Since r<=p<=Z on small events, R_s^2<=S(Z) E_s.

Delete LOW blocks with no following non-LOW event (cost <=Nb), and those whose following selected p>Z (at most O(B/Z) such events per root, each receives at most one LOW block). The second cost is O(XB L/Z). Restrict LOW occupation only to relative [a,H-m), m=3L+2Z+2. This loses at most Nm/2. All losses together are

    epsilon_LOW=O(XL+XB L/Z+X(L+Z))=o(XB).              (3)

Every remaining occupied LOW tag at C has a subsequent small non-LOW event at D with 0<D-C<L. That small event's ENTIRE wait belongs to the original untrimmed slab [a,H): its pre-time is at or after the end of the low waiting interval that intersects the trimmed slab (so >=s+a), and its post-time is <=the low arrival time+3L+2Z<s+H. These bounds also show the event really belongs to the original full prefix, as assumed by the block classification. It has integer positive wait, hence cost>=1/2.

The entire retained LOW block has cost <=b. For every original source its different LOW blocks have distinct destination non-LOW events. Therefore

    R_LOW <= 2b R_s + epsilon_LOW = 3L R_s+o(XB).
    R_LOW+R_s <=(1+3L) sqrt(S(Z) E_s)+o(XB).             (4)

Unlike the earlier one-block absorption into count of HIGH events, this transfers LOW budget specifically into the ACTUAL clipped clock cost of the natural small non-LOW events. Full wait containment is essential. Even a cheap selected small event is included; it is not assumed relatively expensive.

Consequently the following JOINT sufficient condition for twin infinitude is valid on an unbounded sequence of dyadic windows:

    E_s = o( X B^2 log^3(2+Z)/(L^2 Z) ),                (5a)
    E_l,ret = o( X B log^3 B ).                         (5b)

Here E_s uses natural, not previously thinned, small-event weights of the reference roots. In (5b) one may remove any further LARGE-event incidences of total linear cost o(XB), preserving the original clock. Reference may already remove o(X) entire roots. Proof: (4),(1),(5a) imply R_LOW+R_s=o(XB); then (1),(5b) imply retained R_l=o(XB), contradicting R=(N-o(X))B under no twins. Each twin in these windows has smaller prime >=2X-1, hence infinitely many if both estimates hold. In particular bounding the FULL natural non-LOW energy by o(XB log^3 B) suffices without any independent LOW energy estimate. The separate small-energy threshold (5a) is B/u^{o(1)} times XB, much larger than XB log^3 B (the logarithmic factors are absorbed in u^{o(1)}). No upper bound at (5a) has been proved. Prior incidence removals that cost o(XB) selected weight cannot automatically be applied to the small-event side of (5a), because multiplying their loss by L can destroy the saving.

A useful contrapositive: if no twin and (5b) holds along windows, (4) forces E_s >= c X B^2 log^3(2+Z)/(L^2 Z) with an absolute positive c eventually. Thus any remaining obstruction confined to small labels must generate much larger concentration than merely exceeding the cubic-log target.

## 4. NEW direct energy transfer and physical/projected separation

Use the LOW incidences retained in section 3. For each destination horizon D let n_D count distinct original tags whose preceding retained LOW block has positive cost; this includes only small non-LOW destinations. Each tag occurs at most once per D. Let F_D(C) be the total retained LOW occupation at C of tags with destination D. It vanishes unless 0<D-C<L, and F_D(C)<=n_D, sum_C r(C) F_D(C)<=b n_D. Thus

    E_sameDest = sum_{C,D} r(C) F_D(C)^2 <= b sum_D n_D^2,
    E_LOW,ret <= (L/2) E_sameDest
               <=(b L/2) sum_D n_D^2.                 (6)

The extra L/2 counts the number of possible even destination horizons for a LOW pre-horizon. A second useful bound without lumping the destination counts is

    E_LOW,ret <= b sum_{D,D': |D-D'|<L} n_D n_D'.       (7)

Indeed expand the projected square, use F_D'(C)<=n_D' and sum the F_D clock costs; only overlapping destination intervals contribute. This is an upper bound including the diagonal, not an equality of all pair transfers. Distinct destination interactions are localized to a short horizon neighborhood. Since each destination wait is fully occupied with cost>=1/2, n_D<=2r(D)U_s(D), giving

    sum_D n_D^2<=4Z E_s,
    E_LOW,ret<=3 L^2 Z E_s.                            (8)

The multiplicative loss L^2 Z=u^{o(1)} is not an absorption coefficient <1. For sufficient conditions (4) is stronger because it only needs negligible LOW LINEAR budget; (8) also controls actual low-low pair energy if needed, at a small subpower-log cost. Cross LOW/non-LOW terms satisfy the usual Cauchy bound on fractional occupation and are not independently negligible by (8).

Refine to physical destination event keys alpha=(v,J,p) where J=D+p-1, v actual next clock. Let n_alpha count the corresponding destination tags. At any single physical LOW pre-state (t,C), all retained LOW tags have the SAME eventual destination physical event: deterministic continuation, with the terminal or cutoff-only blocks already excluded. Partition the same-physical-state LOW occupation by these keys. Its squared energy, including diagonal, satisfies

    E_LOW,sync <= b sum_alpha n_alpha^2.                (9)

For each key let U_s,alpha(D) sum the ORIGINAL small-event occupation of all natural tags selecting alpha (even if arriving from different pre-times), and E_s,event=sum_alpha r(D) U_s,alpha(D)^2 <=E_s. Then n_alpha<=2r(D) U_s,alpha(D), so

    E_LOW,sync <=4 b Z E_s,event =6 L Z E_s,event.       (10)

This has only one L factor, and no need to count nearby destination horizons: two tags in the same physical LOW state cannot have distinct next non-LOW keys if both retained. E_s,event is grouped by common POST-event physical key, not by same PRE-event physical state, which can differ. This handles the same-state low-low term and makes the remaining asynchronous term explicit in (6),(7). It is not an independent small bound on all asynchronous energy.

## 5. NEW optional two-sided small-event core with thick clock cells

The linear-budget reduction (4) can be supplemented by a structural restriction independent of either energy target. For each original root freeze its list of ALL non-LOW events in the full actual prefix. A maximal LOW block between list positions j-1 and j has k preceding and k following non-LOW events if the indices exist. Delete LOW blocks lacking either side, and blocks with ANY p>Z among these 2k neighbors. At most 2k blocks per source lack the required side; every large event can affect at most 2k blocks in its source. Cost removed

    O(N k L+NB k L/Z)=o(XB).                            (11)

All remaining neighboring non-LOW events are small. The gain span from the earliest neighbor pre-state to the latest neighbor post-state is <=D_k=2k Z+(2k+1)L=u^{o(1)}, including every intervening LOW block. This is o(B). Trim these LOW occupations only to [a+m_k,H-m_k) with m_k=3D_k+2=o(B). Extra cost <=Nm_k=o(XB). All 2k neighboring small events now have their full waits in the original slab, by elapsed<=3gain on the whole segment and the interior trim. This optional trim is independent of the earlier one-sided marks. In particular it gives a growing number of fully occupied small events on BOTH sides of a retained LOW block.

For the frozen full natural SMALL input define projected visit count A_s(D) = #original tags selecting small non-LOW p at D (not fractional weights). Let

    sigma=floor(B/(L^2 k^2)).
    d=ceil(u^4), w=B/u^(1/8), tau=floor(u^3).

At each D partition these tags by time bucket of width d in t-D/2, and source bucket of width w in M-X. These are COARSE CLOCK cells of actual PRE-event states, not physical anchor keys. All tags of a cell have the same D, their times differ by <d, their sources by <w; selected labels can differ. The deficit and root support strips imply O(1+B/d) time buckets and O(1+B/w) source buckets for fixed D. Across all horizons there are O(XB u^(1/8)/d) possible cells eventually.

Mark LOW blocks if ANY of their 2k small neighbors has A_s(D)<=sigma or belongs to a cell of mass <=tau. There are O(X sigma) thin projected incidences in the full reference, and O(XB u^(1/8) tau/d) thin cell incidences. One such incidence can charge at most 2k original LOW blocks, each costing <=b. Hence these extra marks cost at most

    O(X L k sigma + XB L k u^(1/8) tau/d)
       = O(XB/(Lk)+XB Lk/u^(7/8))=o(XB).                (12)

All counts frozen before marks, no recalculation or recursive retention claim. After (11),(12), boundary trim, remaining LOW budget must have the following structure at every one of its 2k neighboring non-LOW events:
- all small selections y<p<=Z, full gain span <=D_k=u^{o(1)}, all waits in original slab;
- projected small-tag mass >sigma=B/u^{o(1)};
- same-horizon, same coarse-clock and source-cell original mass >tau=u^(3+o(1)).
For a cell with mass >tau either one actual physical PRE-state has >sqrt(tau) tags inside the cell, OR it contains >sqrt(tau) distinct actual arrival times (otherwise product bounds the total by tau). This is a precise dichotomy between actual coalescence and asynchronous clock spread in a narrow time strip; no claim the latter is impossible. Companions in a cell need not share selected labels, subsequent trajectory, or even positive clipped occupation. It is a bound on actual frozen visit counts. Unlike the medium shared-physical-history theorem of 99aa9db, no common companion set across the neighbors is asserted here.

This structure is much more restrictive than simply A(C)>log^2.5 B at a LOW horizon: it forces polynomial-size projected visit mass at nearby SMALL non-LOW events and simultaneous thick time/source cells. Whether such configurations carry o(XB) clock remains open. The quantitative energy route (5) is independent of these optional structural marks.

## 6. Actual verification

Standalone research/min_clock_low_transfer_audit.mjs, exact remote readback at 62b8c3b636764f5d6c470168bdf0b2afa03edce5, blob 88ca7c680a0edfb702a9ff17a7b88254a0b82af6. Run:

    node research/min_clock_low_transfer_audit.mjs 1024 4096 16384 65536 262144

Actual JS function executed in available runtime on five X windows x three modes, 15 successful runs. Independent canonical MIN simulation, 4658 literal parity-GCD comparisons per X1024 mode. No prior root pruning or cumulative incidence marks; all odd roots. Verifies clock/deficit/gain and LOW barrier, exact linear compression and capacity, compressed Cauchy, one-sided original full destination waits, unique destination group for retained tags sharing a physical LOW state, actual linear transfer (4), independent projected/same-destination/same-physical/local energy bounds (6)-(10), and optional two-sided frozen cell/threshold deletion cost and actual full neighboring waits, span and dichotomy. Integer counts exact; fractional energies floating tolerances. The sieve asymptotics (1) are inherited, not validated by finite runs.

Analytic y=3,L=6,Z=36,k=1 throughout these windows, tau=u^3 (integer floor), coarse time width ceil(u^4), source width B/u^.125. This does not reach growing y,k; optional core empty at all tested analytic windows (thin cells). Diagnostic y3,L6,Z13,k1, sigma4,tau2,d16,w=B/4; wide y5,L30,Z31,k2,sigma6,tau4,d32,w=B/4. Wide has Z much smaller than L^2, purely finite nonempty diagnostic, not the asymptotic choice.

Largest X262144,B1355,N131072, all original events3941922, R2373997.5, E184229117.19. Analytic LOW cost78489, natural small cost273839, large2021669.5. Compressed R2369303, terminal loss4694.5, compressed E169526314.11 (not same as original E). One-sided LOW: 4694.5 terminal,20277.5 adjacent large,435 trim,53082 retained; 31385 positive blocks, their destination small cost162782. E_LOW,ret4248472.83, transferred cost energy1451164.61, same-physical low energy4239362, E_s20331209.47. Max actual destination mass293. E_sameDest equals E_LOW,ret in y3 runs, so distinct-destination interactions are not exercised there.

Wide at largest: LOW138029; small214299; large2021669.5; compressed R2365117.5 (tail8880), E148799216.23. One-sided basic retained89899.5, destination cost144805.5, E_LOW,ret7164165.02, E_sameDest7162405.32, E_LOW,sync7152915.92, E_s15412319.77. Thus both distinct projected destination and different-time low-low contributions are nonempty. Max actual D-C14. Local count sum5380585 vs sum n_D^2=3028605. These are checks of the inequalities, not an asymptotic energy comparison.

Largest diagnostic optional core: original LOW78489, end4694.5, adjacent-large neighborhood51727, projected thin49.5, coarse-cell thin267, trim2940, retained18811 at11238 positive LOW blocks. 22476 small-neighbor checks, max gain span26; min projected count5, min cell count3. Wide: original LOW138029, end18149.5, large neighborhood95191.5, projected thin69, cell thin770.5, trim14569, retained9279.5 at2775 blocks,11100 neighboring checks, max span94; min projected17, min cell5. All those finite surviving cells have a physical state exceeding sqrt(tau); the clock-spread alternative was not observed in the tested diagnostics. The analytic threshold prunes all cells at X262144, so no numerical claim of negligible deletion fraction or asymptotic contraction. No comparison with prior cumulative residuals (different family and marks).

## 7. Next question

The LOW term no longer requires its own cubic-log energy bound. The main new two-scale target is (5a),(5b): polynomially weaker small non-LOW energy estimate plus the original cubic-log target for large selections, with optional earlier linear deletions on large events. To obtain (5a) independently, need exclude near-maximal projected mass at small non-LOW events, potentially using actual clock spread and repeated small-event words, or a sharper transfer to their physical groups. The optional two-sided core identifies where to seek such a bound; it does not prove the bound. The exact compressed criterion (2) is a separate route that preserves almost the entire budget without first bounding LOW energy. Main unchanged; no Lean compilation or twin-prime proof.
