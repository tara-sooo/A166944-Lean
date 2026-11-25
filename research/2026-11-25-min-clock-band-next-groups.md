# Scale-sensitive physical next-event groups and two-sided common histories

2026-11-25 JST. Continues a16e49ac73e59de5b649b03bbb260723dbd212ba (moving ancestry / cubic-log short-clock criterion), f8d81fc374e78c1c2587de34890678957f0924f6 (least-factor quotient sieve), and the parallel fdec6e92519c8cb7d36cc3a7d918f66867c6b18c (two-sided high history). New linear-budget deletions over ALL growing selected-prime scales, using physical NEXT-event keys rather than just projected current mass. For medium labels, the same large group of actual original tags shares a growing two-sided sequence of band events within o(B) gain. This does not bound the remaining clock budget or energy independently. Paper proof; no Lean compilation; twin infinitude OPEN.

## 1. Setup and reference

Dyadic X, N=X/2 odd original roots M in [X,2X), B=ceil(sqrt(7X)), s=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B. Assume H+2B<=min(K-s), eventually. Use full actual MIN prefix through first post-event at or beyond relative H, or twin terminal. C strictly increases, t strictly increases, C<=2t. At occupied pre-state C, r(C) is the least eligible odd prime dividing (C-1)(C+1) with p<=B, wait<=2r(C), r<=selected p. Total gain <=G=2H+B+6. Thus per-root sum of all selected labels p<=1.5G=O(B), including crossing event and events outside slab. Time elapsed over any completed subpath <=3 times its gain. Post-event (v,J) deficit 0<=2v-J<=12B+6. For the relative slab [a,H), w_M(C)=clipped wait/(2r), R_M=sum r w<=B. R=sum R_M, E=sum r(sum w)^2. Under no twin R=NB. Earlier least-factor support S_*=O(XB/log^3 B) gives sufficient E=o(XB log^3 B) on unbounded windows after o(XB) linear deletion.

Take ANY frozen reference family of original roots (e.g. after previous o(X) whole-root pruning), preserving all their actual paths. Groups and band lists below are frozen BEFORE the new incidence marks. None of the results asserts that group members all survive the final incidence marks. No rerun or change of root cutoff.

Put u=log B, ell=log u. Let Y=2^floor(log2(max(4,ell))) and Q=2^floor(log2(B/u^(1/4))). Eventually 4<=Y<Q<=B, Y tends to infinity. For each dyadic band P<=p<2P with P>=Y define l_P=log(2+P), w_P=B/l_P^(1/8) (source-cell width), k_P=floor(l_P^(1/8)). Medium bands Y<=P<Q, high bands P>=Q (truncated at B). For selected p>=Y call the incidence relatively expensive if

    r(C) >= p/(log(2+p))^(1/8).

The other such incidences have total slab cost <=sum p/(log(2+Y))^(1/8)=o(XB), by the total selected gain bound. Their selected gain need NOT be negligible. Marks below concern the relatively expensive input, including unoccupied events so that neighbor transfers can be made in selected weight rather than clipped duration.

## 2. NEW arithmetic support of physical next-event groups per band

For relatively expensive selected p in [P,2P), p|C+sigma for unique sigma=+-1. Write (C+sigma)/p=2n+1. Both 2n+1 and p(2n+1)-2sigma avoid odd primes q<=floor(P^(1/8)), for sufficiently large P, because r>=P/(log(2+2P))^(1/8)>P^(1/8). Every such q<p excludes precisely two residues in n. The uniform two-form quotient sieve used in f8d81fc gives O(X/(p log^2 P)+P^(3/4))=O(X/(p log^2 P)) candidate C, uniformly P<=B: P^(7/4) log^2 P=o(X). Bounded P absorbed in absolute constants. Summing over p by Chebyshev's bound for a dyadic prime band, candidate (C,p) count is O(X/l_P^3).

For each such (C,p), the next physical vertex is (v,J=C+p-1). Its clock is v=0 mod 2p for sigma=-1, or v=p+2 mod 2p for sigma=+1. Deficit strip 0<=2v-J<=12B+6 allows O(1+B/p)=O(B/P) times. Thus the number of possible physical next-event keys (v,J,p) in the band is O(X B/(P l_P^3)). This counts arithmetic candidates even if no actual root selects them. Distinct tags having the same key have exactly the same post-event physical state; no assertion that their preceding times coincide.

At fixed C, all original roots satisfy 0<=C-(2M-2)<=G, so they belong to a source interval of width G/2=O(B). Partition the original source values M into half-open cells of width w_P, aligned at X. There are O(1+B/w_P)=O(l_P^(1/8)) possible cells at that C. Define a group by the key (v,J,p, source cell), including exactly the actual reference incidences with that key in the relatively expensive band input. The number of groups is at most

    K_P = O(X B/(P l_P^(23/8))).                     (1)

Each tag can occur at most once in a given group (strict growth of C). All members are distinct original roots, not representative trajectories. Their source spread is <w_P, and they have a shared post-event physical state even if their incoming times differed.

## 3. NEW scale-sensitive thin group removal

At medium bands put tau_P=floor(l_P^(3/2)); at high bands put tau_P=floor(u^(11/4)). Mark as SEEDS all relatively expensive input events whose group mass is <=tau_P. Full selected-prime weight of seeds in a band is at most

    W_seed(P)<=2P tau_P K_P
              =O(XB tau_P/l_P^(23/8)).                (2)

In particular their clock cost is no greater. This proof does not rely on arbitrary source masses being small: thinness is a test on actual groups, and all other groups can be huge.

At medium bands (2) is O(XB/l_P^(11/8)). At high bands l_P~u, so it is O(XB/u^(1/8)) per band; there are O(1+ell) high bands, giving o(XB) total selected weight. Hence except for o(XB) clock cost, high relative-expensive events have >u^(11/4) companions (count including themselves) at their next physical state in the SAME source cell of width O(B/u^(1/8)). This is a constraint on actual post-event physical ancestry, stronger than a lower bound on the mass of the projected pre-horizon. It includes final crossing events. The companions may have arrived from different physical predecessors.

## 4. NEW medium-band halo and end deletion at growing depth

For each original root and medium band freeze the list of its relatively expensive events in increasing horizon order. Mark the seed events and every event within k_P list positions on either side of a seed. Do not propagate again from newly marked events. Since selected p in the band differ by a factor <2, one seed can charge at most (2k_P+1) events of weight <=2 times its own label. Thus

    W_seed+halo(P)<=2(2k_P+1) W_seed(P)
                   =O(XB/l_P^(5/4)).

Sum over dyadic P>=Y; l_P is comparable to the integer band index, and sum_{j>=c log Y} j^(-5/4)=O((log Y)^(-1/4))=o(1). Consequently these marks remove o(XB) total selected weight. This is not a probabilistic independence estimate.

Mark first and last k_P events of each medium band list (if shorter, all). Per-root selected cost <=4 sum_{Y<=P<Q} P k_P =O(Q u^(1/8))=o(B). This end deletion is restricted to medium bands; imposing it at high bands would not have the same bound.

Every remaining medium event has k_P earlier and k_P later frozen same-band relative-expensive events, including all 2k_P+1 positions centered on it, whose actual physical next-event groups have >tau_P distinct members in their corresponding source cells. No marks are recomputed after deletion. At this step the groups could have different companions at different positions.

## 5. NEW bounded span and a single shared physical history

Let Delta=B/u^(1/16). For each remaining medium center indexed i in its band list let D_i be gain from the PRE-horizon of event i-k_P to POST-horizon of event i+k_P. For each original source, sum D_i over all centers with these neighbors is <=(2k_P+1)G: each completed gain step in the full trajectory belongs to at most 2k_P+1 of the spans. Mark centers with D_i>Delta. Their selected weight in band P is <=2P(2k_P+1)G/Delta per root. Summing bands and roots gives

    W_span=O(N B Q u^(1/8)/Delta)
           =O(XB/u^(1/16))=o(XB).                   (3)

Thus both neighbor sides now lie in o(B) total gain, not just in a bounded number of selected-event positions. k_P tends uniformly to infinity over P>=Y, albeit slowly at the smallest scales.

Set b0=ceil(max_{P>=Y} w_P)=O(B/(log Y)^(1/8))=o(B). For these medium centers only, restrict slab occupation further to relative

    [a+b0, H-b0-3Delta).

Integer rounding of boundaries harmless. For sufficiently large B interval nonempty, as b0,Delta=o(B). Total extra clock loss <=N(2b0+3Delta+O(1))/2=o(XB), irrespective of group counts.

Take a positive-occupation center after these marks. Let G0 be the actual reference group at its earliest band neighbor i-k_P. It has >tau_P roots and all source differences from the central M <w_P<=b0. All those roots select that earliest event and share the exact post-event physical state. The deterministic MIN continuation then forces ALL of them to share every later physical vertex through the post-event of i+k_P, unless a root-specific cutoff ends the prefix sooner. This exception cannot occur here: the elapsed time from center pre-state to that final post-event <=3D_i<=3Delta. The center has a nonempty clipped interval before relative H-b0-3Delta, so its center pre-time is strictly earlier than s+H-b0-3Delta. The final post-time is <s+H-b0<=s'+H for every companion start s'=M'+2. Original K cutoffs are beyond the relative prefix gate, and a twin on the shared path before the final state would also have stopped the central path. Hence the companions really do have these later states in their original reference prefixes.

They share ALL of the intervening physical events from the first neighbor's POST-state onward, including the remaining 2k_P band events (not necessarily the first neighbor's PRE-state). The entire shared part has gain <=Delta. For the central trimmed waiting interval, each companion has exactly the same physical wait and its relative slab contains that interval because |s-s'|<b0. Thus each companion's original w_{M'}(C)>=w'_M(C), the trimmed central weight. In particular the actual reference occupation at this C is at least |G0| w'_M(C). This is a common COMPANION set, not a separate collection of roots at each event. The companions are in the frozen reference family, not asserted to satisfy the central incidence marks in their own histories.

This is a structural reduction of linear budget. It does not by itself give an upper bound on their multiplicity or on their total clock budget. Indeed it implies large shared history rather than ruling it out.

## 6. Consequence and unresolved terms

All new linear deletions total o(XB), uniformly for any frozen reference family. If the original reference removed only o(X) roots, under no twins the remaining cost is (N-o(X))B. The retained occupations have three types:
- selected p<Y, not controlled by the present marks;
- high p>=Q, relatively expensive, same-cell thick physical next-event group as in section 3;
- medium Y<=p<Q, relatively expensive, with a short two-sided history from section 5, shared by >log^(3/2)(2+P) actual reference tags in one source cell.

Earlier moving-light incidence marks may also be imposed on the centers; the statement about companions remains relative to the frozen input used to construct the groups. One may start with a previously pruned original-root family, but no recursive claim about final retained companion counts follows. Low selected labels p<Y can occupy a non-negligible budget; the LOW primorial barrier alone does not give an o(XB) bound for them at this cutoff. Need an upper bound on residual clock budget/energy or a contradiction to the forced common histories. Under (1) of a16e49a, E_rest=o(XB u^3) for all these retained types would suffice for infinitely many twins. No such full bound is proved here. The present argument concerns selected-prime bands with a least-factor relative-expense condition, not r bands independently. Main unchanged.

## 7. Actual verification

Standalone research/min_clock_band_next_group_audit.mjs, exact remote readback 8bd6f753437fdacadb43a2956b5957f3182172e6, blob bf3cea058a23d21d191b28d54d36476a582f55a7. Run:

    node research/min_clock_band_next_group_audit.mjs 1024 4096 16384 65536

Actual JS function executed in available runtime on four X windows x three modes, 12 final successful runs, not a separate Node invocation. Canonical full-prefix simulation inherited from previous audit, 4658 literal parity-GCD comparisons at X1024 per mode. Uses reference after shallow degree pruning ONLY, not previous moving-root pruning or cumulative prior incidence marks. Explicit relaxed candidate (C,p) enumeration over all horizons and exact allowed time count in deficit strip, source-cell capacity; actual group clock/residue/cell and post-state checks; full selected-weight and clipped clock partitions; seed bound, halo/end bound, per-band gain span sum, direct independent retained-energy oracle for marks through section 4. Direct companion replay and occupation check for middle centers after symmetric boundary trim; separate stronger span+future-trim core checks every companion at each of the 2k_P subsequent band events and post-state, including final endpoint before cutoff. All integer counts exact, fractional energies use tolerances. The stronger core's cost is computed independently; E2 in the output is for earlier seed/halo/end marks, not the stronger core.

Analytic thresholds at these small X have Y=4 and k_P=1, so no growing-depth regime reached; b0+3Delta is larger than the slab width, and the full two-sided core is empty in every analytic finite run. This is a finite limitation, not an asymptotic conclusion. Diagnostic Y4,Q=largest dyadic <=B/4, relative expense r>=p/2, width B/2, tau=2,k=1; wide Q<=B/8, width B/4,tau=3,k=2. Both diagnostics use Delta=B/8 for direct nonempty core checks; these thresholds are NOT the asymptotic ones.

Largest X65536,B678 standard reference31824 (944 previously shallow-pruned), R373244.5,E16529423.70. All actual prefix selected weight17828769. Standard diagnostic: 46543 groups,20097 thin, 26446 thick next-state checks; cheap clock7604, seed3407.5, halo463.5, end77431.5, retained R284338 (incl p<Y cost17818.5), E2=10377791.51. 4013 medium occupied centers after symmetric trim (prior-only companion validation), 111094 companion checks. Additional span removal clock55435.5, future trim7535, two-sided core R3783, 1102 occupied centers, 37223 companion checks, 74446 actual band-event/post-state checks, max gain span82, group sizes4..119.

Wide diagnostic same reference R,E; 53415 groups,27289 thin,26126 thick next-state checks; cheap7604, seed5663, halo1956.5, end60058, retained R297963 incl low17818.5, E2=12170719.52. Medium retained clock before stronger core34613.0; span marks remove32464, future trim742.5, core retains1406.5 at515 occupied centers. 12994 actual companion checks,51976 shared band-event/post-state checks (four per companion, k=2), max full span84, core group sizes4..60. In both diagnostics high/low retained occupation untouched by optional core trim; results are finite checks of membership and bounds, not numerical o(XB) proof.

Analytic largest R2=110106.5 incl low19493 on reference R402074 (no shallow deletion). Much clock budget removed at finite thresholds, core empty: no observed asymptotic saving. The asymptotic o(XB) assertions follow from (2),(3), summable band bound and the boundary widths, not from finite removal fractions.

## 8. Next proof problem

The new medium core forces actual many-source coalescence across a short but growing sequence of same-band relative-expensive events. To go further, need an independent bound on the formation or persistence of these groups, using common physical trajectory and actual preceding times, or a bound on the low-label clock term. Mere arithmetic counts of possible thick group keys without actual mass control do not finish the proof. No Lean compilation or twin-prime proof.
