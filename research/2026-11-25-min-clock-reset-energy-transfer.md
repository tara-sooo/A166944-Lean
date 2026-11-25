# Two-sided reset-cohort energy transfer, and a full-to-late bridge

2026-11-25 JST. Continues 842e743d7219abf6ad143288fe22ea3f321f36e4 (upward deficit cutsets/peeling), f3ebd2e8066c6674b360c1bd8a9f492825b098d7 (short reset excursions), and the natural MED/retained HIGH two-sector criterion in 2c5f5f0b1852ada0bc0837ab279a302e92981ff5. NEW actual earlier/later energy partitions by next and latest short reset, one-sided near-reset graph absorption, quantitative credit from a single shared upcrossing witness, and a two-window bridge using only a trivial full-prefix energy bound. No cap on total ancestor counts is needed for these estimates. Does not bound the remaining energy in general; no Lean compilation or twin-prime proof.

## 1. Setup and a correction about upcrossing cohorts

Use the original canonical all-odd MIN prefixes as in 842e743: X dyadic,N=X/2,B=ceil(sqrt(7X)),H=4B,a=2B,G=2H+B+6. Initial C0=2M-2,t0=M+2, K=floor((7M-1)/4); assume H+2B<=min(K-t0) eventually. Include first post-state at/beyond relative H or twin terminal. C and t strictly increase, total gain<=G, deficit delta=2t-C in [0,12B+6]. A selected q on D has wait w<=2r(D)<=2q, deficit change 2w-(q-1). A reset is any actual vertex with delta=6(t mod2), including original root; at an incoming q>=7, its labeled reset key v=(J,t,q) has J=0 mod4, t=J/2+3s, q|J+2s.

Put u=log B,P=ceil(B/u^1/8),V=floor(B^1/16). A short high reset selects p>=P, wait<=V, and enters a reset state. As before, every integer L in [ceil(p/4),floor(p/2)] eventually lies strictly above 6 and at/below the pre-reset deficit. On a root's excursion from previous reset to this reset, choose the last actual upward crossing of L before its reset-entry event. We can choose a single witness key alpha=(post horizon,post time,incoming q) from these last crossings by ANY deterministic rule, including earliest such event (audit). No changed path or cutoff.

**Correction/strengthening of 842e743, section 4:** assigned roots at the same labeled upward-crossing key DO share the same NEXT reset physical state and incoming reset label, whenever all reach that reset. After the crossing they follow the identical deterministic suffix, and there is no intervening reset before the reset for which they were assigned. A tag cutoff can terminate a path early but cannot change its continuation before cutoff. Thus the next-reset assignment is a function of the physical crossing state for these tags, even if they were assigned different levels. Their pre-crossing histories and previous reset can differ. The earlier note's sentence saying companions need not share the same later reset label is too weak and is corrected here. The earlier count/peeling and second moment proofs do not rely on that sentence.

## 2. Actual past and future partitions

Take ANY frozen set of eligible short-reset incidences (individual original tag entries), not necessarily every such entry. If a tag has several, its preceding excursions from immediately previous reset to pre-current-reset are disjoint. For each actual occupied horizon D and each label sector b, use arbitrary nonnegative weights w_i^a(D), w_i^f(D) bounded by the natural fractional weights for the chosen earlier/later time windows. Histories and eligibility stay frozen. Define

  P_v^b(D) = sum of w_i^a(D) for tags whose selected eligible reset v
             has D in its preceding excursion (from prior reset's
             post-state through just BEFORE the reset-entry wait),
  Q_v^b(D) = sum of w_i^f(D) for tags whose LATEST eligible short reset
             at or before D is v.

In P the excursion excludes the wait that enters v; in Q the occupied wait at the post-state v is included. If no such entry, the tag contributes to no corresponding bucket. Both assignments are unique PER TAG AT EACH D. In particular Q does not include a tag repeatedly for every earlier short reset. This latest-entry rule removes the O(B/P) multiplicity that would otherwise appear in the future ledger.

Let c_b>=0 fixed coefficients, and write
  E_a=sum_b c_b sum_D r(D)(sum_i w_i^a(D))²,
  E_f=sum_b c_b sum_D r(D)(sum_i w_i^f(D))²,
  A_v=sum_b c_b sum_D r(D) P_v^b(D)²,
  F_v=sum_b c_b sum_D r(D) Q_v^b(D)².
All masses are actual fractional occupation weights, NOT raw ancestors. Pointwise disjointness and positivity give
      sum_v A_v<=E_a,       sum_v F_v<=E_f.             (1)
We do not assert sum_v(A_v+F_v)<=one energy. The past and future intervals may overlap. This is true under arbitrary original-root deletions or incidence masks; no new LOW destination loss is introduced. It also applies when past and future use different windows or masks.

The normalized two-sector energy of interest is
    E_* = E_H + B^(-5/8) E_M,
with natural MED z<p<=T, z chosen by primorial L_z<=B^1/16, T=ceil B^1/4, and retained HIGH p>T, subject to the previous o(XB) HIGH linear loss condition. Then E_*=o(XB u³) is equivalent to both prior sufficient sector bounds. We may use this exact weighted sum for all the following estimates; no LOW energy included. One can also use a single sector or the full natural all-label energy (not the same criterion). Earlier natural MED/retained HIGH masks should match the energy on the appropriate side; the algebra is valid even when they differ, but a same-energy absorption requires the stated equality of the two energies.

## 3. One-sided graph absorption, including asynchronous overlap

Form a simple undirected graph on eligible labeled reset keys. For example connect distinct keys with |J-J'|<=A (A here is distance, not the energy A_v). A fixed horizon has at most O(1) labels >=P for each of two reset lines, by the product bound on distinct prime factors. Thus max degree Delta=O(A+1). The graph may include distinct labels at the same physical state, which are distinct buckets. No first physical meeting uniqueness or deterministic common suffix is needed for this particular bound: actual projected future weights suffice, and asynchronous pairs are included.

The ordered offdiagonal contribution of a same-key pair in Q is at most F_v. For two distinct keys v,w the full ordered projected cross contribution is
    E_vw=2 sum_b c_b sum_D r(D) Q_v^b(D) Q_w^b(D)
         <=2 sqrt(F_v F_w).                            (2)
Define good key by F_v<=kappa A_v. Pay same-key offdiagonal energy at good keys, and all edges with at least ONE good endpoint. Since each tag at a given D is in at most one future bucket, these same-key and edge classes are disjoint actual pair-incidences. (Other overlaps are not included; if prior exclusions applied to pairs, only pay their remaining fractions.) Equation (1) gives
    E_paid,self <= kappa E_a,
    E_paid,both-good-edges <= Delta kappa E_a,
    E_paid,one-or-both-good-edges <= 2 Delta sqrt(kappa E_a E_f).
The last follows by orienting towards a good endpoint, overcounting edges with two good endpoints if necessary, and Cauchy over directed incidences. Each endpoint participates in at most Delta edges. Consequently
    E_paid <= kappa E_a + 2 Delta sqrt(kappa E_a E_f).  (3)
Unlike a rare-state cap, no absolute upper bound on F_v or mass of either key is required. The other endpoint can have arbitrary F. If E_a=E_f=E_*, choose A=2 floor(u^1/8), kappa=1/u. Then (3) pays at most O(u^-3/8) E_*. This is an absorption inequality, not an unconditional o(target) bound on paid energy in isolation. It yields
    E_* <= (1+o(1)) E_*rest
where E_*rest includes all unpaid terms (and can have other known o(target) exclusions added in the usual manner). No new constraint on natural MED is imposed. Same-window absorption can fail to pay any positive contribution if the relevant earlier excursions occur outside that window.

## 4. A full-to-late bridge without requiring the full energy target

Take the past window [0,H) relative to each root, the future window [2B,H), both clipped to original waits, with the same coefficients c_M=B^-5/8,c_H=1. On the past side use natural sector weights (one could use masks); on the future side natural MED and any valid retained HIGH. Past is the full CLIPPED short prefix, not the untruncated final crossing wait. It includes earlier ages absent from the previous criterion.

There is a trivial bound E_a=O(XB²): every horizon D is visited only by sources with initial 2M-2 in [D-G,D], so at most G/4+O(1)=O(B) odd source tags. All weights<=1, and total full linear cost<=2BN. Since c_b<=1 for these two disjoint sectors,
    E_a <= O(B) sum_b sum_D r(D) U_b^a(D) = O(XB²).
This is substantially weaker than the desired late cubic-log scale and needs no new assumption. By Young's inequality, (3) gives for any eta>0
    E_paid <= eta E_f + (kappa+Delta² kappa/eta) E_a.   (4)
Set A=2 floor(u^1/8), eta=u^-1/4,
    kappa=u²/[B(1+A)²].
Then Delta=O(A+1), so the additive cost in (4) is O(XB u^9/4)=o(XB u³). Hence
    E_f <= (1+o(1)) E_f,rest + o(XB u³).              (5)
The criterion is still only the LATE two-sector target, not an assumed full-prefix target. The new class consists of reset keys whose actual LATE future energy is <=kappa times their actual FULL preceding excursion energy, and all close edges with at least one such endpoint. This is a small ratio (polynomially shrinking); no assertion that every reset or most actual pairs satisfy it. For same-key and both-good edges alone, one can use the more generous kappa=u²/[B(1+A)] by the direct bound (1+Delta)kappa E_a=O(XB u²), without an eta E_f term. This variant is a paper deduction, not an additional finite mask audit. Existing LOW transfer and high mask loss accounting remain unchanged; previous nonnegligible pair exclusions may not be silently treated as linear deletions.

## 5. Quantitative actual earlier credit from a single shared crossing

This supplies sufficient conditions for the good-key ratio rather than merely defining it. Fix reset v with incoming p, and partition its eligible entries by a chosen witness alpha from section 1 (use earliest among last crossings, for example). For a given group g, let n_g be number of entries whose ENTIRE interval from pre-witness time to reset time lies inside the past natural evaluation window. This can be checked per tag even when the pre-witness arrival times differ. All these tags have the same witness label q and predecessor horizon D0, and the same deterministic suffix from its post-state up to pre-reset. Denote by d_g^b the sum of positive deficit increments on this common suffix, restricted to selected labels in sector b, excluding the reset-entry event. The witness's pre-event itself is not in that sum.

At the positive-drift witness, each full wait weight w/(2r(D0))>=1/6; thus the projected earlier occupation of those n_g roots contributes >=r(D0)n_g²/36 in the sector containing q, even if their incoming predecessor times differ. Every subsequent shared positive-drift full wait has energy per unit squared root mass
    r(D) (w/(2r(D)))² = w²/(4r(D)) >= w/12 >= positive drift/24.
Therefore define
    K_g=sum_b c_b [1_{q in b} r(D0)/36+d_g^b/24].
For natural past occupation,
    A_v >= sum_g K_g n_g².                            (6)
At every earlier horizon the group weights from different witnesses are subsets of the disjoint root entries in that v's actual P bucket; their squared masses sum to at most that bucket's square. Thus there is no extra factor for #groups, levels or excursion length. For arbitrary masks one may instead use their actual group quadratic costs in (6); the natural lower bound is not valid if prior credit has been masked away.

For the ALL-label natural past energy, K_g>=c p for some absolute c>0 eventually. Indeed if q>=p/16, then r(D0)>(q-1)/4 and the witness term alone suffices. If q<p/16, post-witness deficit <p/2+4q<=3p/4, whereas the pre-reset deficit>=p-1-2V>=7p/8 eventually. The common suffix therefore has positive drift sum>=p/8 and yields credit. In HIGH alone the first case works since p/16>T eventually; the second works if the sum of HIGH positive drift on the common suffix >=p/16. Otherwise the all-label conclusion does not justify a HIGH credit of order p. In the normalized E_* the MED contribution is discounted; use actual K_g, not an unweighted p credit. The code checks (6), not a full-sector lower bound cp when the necessary condition fails.

A direct good-key test: let n_v be all entries at v (including those without fully contained witnesses), b_i the future assigned linear cost of entry i in the chosen sector/weighted sum (using latest-entry partition), tau_v=max b_i. At each horizon Q_v<=n_v, so
    F_v <= n_v sum_i b_i <= tau_v n_v².
Using (6), sufficient is tau_v n_v²<=kappa sum_g K_g n_g². For example if every entry has full witness, K_g>=c p in the energy being used, and dispersion D_v=n_v²/sum_g n_g²<=D, it suffices tau_v D<=c kappa p. In same-window theorem with p>=P,kappa=1/u, tau_v<=P/u² and D<=u^1/2 suffice eventually. This permits unbounded root counts, provided the actual witness groups account for sufficiently much earlier occupation relative to later tails. This is a sufficient test of the same ratio, not a general upper bound on dispersion, and not a claim that the full-to-late polynomial ratio usually follows from a single witness.

## 6. Verification

Standalone research/min_clock_reset_energy_transfer_audit.mjs, final exact remote readback 6b8cecefd195f34d86ff55f5df8fcd27276422dd, blob bb335c57fe379859c70e3878dab8a48f73a2a991. Run
    node research/min_clock_reset_energy_transfer_audit.mjs 1024 4096 16384 65536
Final JS function executed in available runtime for 20 successful runs, four X windows x five modes (not a separate Node invocation). Inherited independent canonical MIN and literal parity-GCD comparison (4658 checks per X1024 mode), original cutoff, full actual excursions, exact earliest chosen last crossing, actual witness-key -> unique next labeled reset, no intervening reset, disjoint past/latest future assignments. Independent direct pair oracle for same-key/close graph energy, both sync and async, exact pointwise and global partitions, actual natural witness lower credit, tail test, one-sided graph and Young bounds, weighted two-window bridge. Floating tolerances used. All original roots, no previous peeling/other masks; no cumulative earlier energy residual. Smaller windows explicitly exclude short entries when p/4..p/2 level band fails the >6/predeficit condition. Mode analytic uses asymptotic formulas at finite sizes; diagnostics use fixed thresholds, not extrapolated limiting ratios.

Largest X65536,B678,N32768,794415 selected events. Analytic P537,V1,A2,16 entries at one reset key, no positive late future weight. Standard P170,V8,A12,1073 entries,54 reset keys,111 distinct witnesses. Stress P85,V7,A24,2332 entries,134 keys,276 witnesses,24655 intermediate no-reset checks,3 close edges,max degree1. All [2B,H) runs have ZERO past energy in the assigned pre-reset excursions at tested windows, so same-window ratio has no nonzero paid contribution. This is a real obstruction to directly reusing the late window; do not report a finite improvement there from the same-window theorem alone.

The added early and full diagnostic modes use same stress P,V, same original trajectories but weights on [B,H) and [0,H), graph A=2B and kappa=1 (NOT analytic scale). At largest full, all 2332 entries have full witness containment; 167 graph edges, degree6. For HIGH natural full clipped E265354704.75, sum A_v2859860.64, sum F_v4327186.30, quantitative lower credit174268.17; same-key offdiag4188689.64, close-edge198459.11; paid same294143.90 and edges57203.88. Of all target same/edge energy82437.89 is asynchronous. MED full same/edge1549819.55/138322.17, paid246697.81/33048.13. All-label full witness credit345788.44 vs actual sum A5153056.50. These use earlier weights, not previous late-energy estimates.

The FULL-to-LATE bridge is computed in EVERY mode independently of the displayed single-window diagnostic. Its E_a/E_f are normalized MED+HIGH with coeff B^-5/8/1, full clipped versus original late. Largest standard E_a266534028.08, E_f15359786.70, sum A2065013.83,sum F7275.32; finite diagnostic kappa=.25, positive good keys3. Eligible same-key weighted offdiag6551.73 -> paid5046.67 -> remaining1505.07, no close-edge contribution. Stress same normalized energies, sum A2890248.98,sum F29571.37, kappa1; positive good keys8; self27601.13 paid10243.85. In early/full broad adjacency A=1356, extra actual close-edge3835.73 all paid (at least one good endpoint), total eligible31436.86 -> paid14079.57 -> rest17357.29. Analytic ratio at largest .0069648, no eligible positive late energy, so nontrivial finite absorption occurs only at diagnostic ratios, not proof of asymptotic reduction. Max original tag support at any horizon408. The initial 12 runs exposed zero late past credit; added eight earlier-window diagnostics, then all 20 rerun with final weighted bridge. No code error in that zero result.

## 7. Remaining

This removes a specific class of reset-associated late overlaps by absorption, even when earlier witnesses lie outside the late window, with no full-prefix cubic-log assumption. Shared witness credit and unique next-reset geometry supply actual conditions for the ratio. It does not control keys with larger future/earlier ratios, pairs without two eligible latest reset keys, far edges, or unrelated formation terms. The late-only finite absence of upstream credit suggests a useful next route: analyze late suffixes of early-reset groups directly, possibly using the odd reset state as a new canonical original root (when J divisible by 4 and t=J/2+3, M'=J/2+1 is odd). The corresponding renewal/basin multiplicity estimate has NOT been proved here. Main untouched, no Lean compilation, twin-prime conjecture OPEN.
