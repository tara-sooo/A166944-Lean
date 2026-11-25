# Paired LOW entry compression and nearby canonical-pair reduction

2026-11-25 JST. Continues 64323f51c0aae638bca2e3d3c484b5dda8658166. New: compress both independent pre-contact LOW tails to their actual last nonLOW entry or root; large entry labels at low-contact merges must be RESET and cannot agree on both sides. When both entry phases are zero, route the entire pair weight to two actual canonical states in the same primorial block, without repeated weight transfer. Their deterministic future fixes the physical first meeting. Absolute quotas on nearby canonical-pair keys, with stronger rough support. No heavy residual bound or Lean compilation; twins OPEN.

## 1. Actual ensemble and two independent LOW tails

Use original all-odd roots M in [X,2X), fixed B=ceil(sqrt(7X)), u=log B, actual MIN original completed prefixes through crossing or earlier twin, clock <=6B, gain <=12B+6, d=2t-C>=0, w<=2r<=3(p-1). Same-outgoing-label recorded birth graph of 64323f5: actual pair first physical meeting at horizon C and later recorded arrival b1, earlier b0<b1, both complete same departure (v,p). Aggregate nonbirth record-routed donor weight over all levels/targets once per actual unordered original pair. Pair weight <=324B, O(XB) possible pairs. Restrict later deficit d1=2b1-C<=A (asymptotic A=u²). Earlier d0<d1. This includes both RESET and nonRESET outgoing, not just rough slots.

Choose even primorial L of primes <=Y (odd selected primes <=Y called LOW; Y>=3). For each of the two actual recorded arrivals (C,b_i), follow records backward across the maximal consecutive LOW suffix. Stop at actual root or last nonLOW poststate (J_i,a_i) of incoming label q_i>Y. Set q_i=0 for root. With K=L floor((C-1)/L), the primorial barrier (LOW cannot strictly cross multiple of L) implies
    K<J_i<=C, G_i=C-J_i<L,
    0<=b_i-a_i<=3G_i,
    d_i-5G_i<=d_i^entry<=d_i+G_i.
This includes zero-length LOW tail. C is allowed to equal the next block boundary K+L, which is why K uses C-1. No LOW suffix has been inferred from congruences alone. The two entry states are distinct: an identical physical entry would force the paths to coincide before b1, since a_0<=b0<b1. Every common horizon in the two tails has disjoint actual half-open wait intervals before physical first contact. Entry clock separation <=g+3(L-1) where g=b1-b0<=A/2, not necessarily the same chronological order as b0,b1. Actual entry deficit <=A+L.

For q_i>Y, side s_i=a_i mod2, exact phase
    q_i | J_i+2s_i, q_i | a_i-2s_i,
    d_i^entry-6s_i=2q_i k_i.
Since q_i>=5 the phase is nonnegative (odd negative phase would require q_i=3). A nonzero phase forces q_i<= (A+L)/2. Thus any label q_i>T=max(L+2,(A+L)/2) forces phase zero RESET. Moreover if both labels exceed T, they MUST differ. Proof: if equal q>T, congruences give J0+2s0=J1+2s1 because absolute difference <L+2<q. Both RESET post horizons are 0 mod4, so s0=s1, J0=J1 and a0=a1. This contradicts distinct actual entry states. Root entry already canonical. This gives a joint restriction on large entry labels not available for immediate LOW inputs. It does not bound ancestor multiplicity for either label.

## 2. Two actual canonical states in a common block

Suppose both entry phases are zero (including root). Use odd RESET immediately canonical and even RESET bridge from canonical-renewal.md, <=7 clocks and <=8 gain. Choose the first actual canonical point at or after each entry, including virtual canonical points in waits. These points exist no later than first physical contact b1. Indeed prior to the first canonical point of the bridge the true deficit is at most 4 (even reset sequence and final quiet segment); at a later distinct recorded arrival into a shared horizon the deficit is at least 6. This follows from recorded congruences (d=2,4 impossible, d=0 cannot be later than a nonnegative earlier arrival), or root d=6. Hence a bridge cannot still be before its canonical point at contact. The actual supporting prefix contains the bridge, not an extrapolation. Both canonical horizons are in (K,C], since they occur at/before contact and horizons increase monotonically.

Write canonical state as (C_c,t_c)=(2m-2,m+2), m odd. For the two indices m0,m1,
    |m0-m1|<L/2.
If equal, the common state must be exactly first physical contact, by uniqueness of earlier contact; assign to the canonical physical-contact class already considered in 64323f5, not a new independent weight. If distinct, assign whole pair mass to unordered canonical pair (min(m0,m1),max(m0,m1)), preserving actual endpoint assignment for incidence. All later charge of that original pair counted once. Actual source ancestry reaching each canonical point may be very large; this is a new reduced key, not a pair of original roots in general.

For fixed two canonical indices, future physical trajectories from those states are deterministic with fixed B in the original valid range. Because both canonical points occur before/equal first contact, the first common physical state after both points is the original pair's actual first contact. Thus any actual original pair assigned to this key has the SAME first contact (and same outgoing label/departure when completed). No multiplicity for possible later contact locations, departure phases, or LOW chains. This assertion uses only actual witnesses and their overlap; no unbounded extrapolation. Source-specific end times restrict but do not change that contact. A pair of close canonical indices can still support large cross-basin ancestry. In the special case an endpoint is a canonical root, its source is fixed there, but the other basin may be large. Root incidences are reported separately.

## 3. Absolute canonical-pair quotas

All canonical indices are in an O(X) interval, and separation <L/2. Thus there are O(XL) possible distinct unordered keys. Pay min(actual aggregate weight at key, B u^(11/4)/L) per key. Cost O(XB u^(11/4))=o(XB u³), with any positive residual implying >u^(11/4)/(324 L) distinct actual charged original pairs before payment. For L<=u^(1/16), this is Omega(u^(43/16)). This is independent of earlier quotas; use only residual weights if applying sequentially. Equal canonical points retain prior canonical-tail bound. Nonzero entry phase retains section1 label bound, but no canonical-pair assignment is asserted.

Sharper rough-contact variant, for both phase-zero distinct canonical points in the same block and r(C)>=R=cB/u². The established two-form sieve gives O(X log u/u³) possible rough horizons C in the O(X) interval: for each p in [R,B] dividing C±1 count O(X/(p u²)) by conditioning on p, then sum reciprocal primes O(log u/u). True rough horizon has at least one eligible p because an actual outgoing event exists. For each C both canonical horizons in (K,C], so at most O(L²) distinct canonical index pairs. This overcounts possible keys but suffices even without using unique contact. Thus rough canonical-pair support O(X L² log u/u³). Pay min(actual rough-subset aggregate mass, B u^(23/4)/L²) per key, total O(XB u^(11/4) log u)=o(XB u³). For L<=u^(1/16) this leaves only keys originally with >u^(45/8)/(324) distinct pairs (up to constants) in that sector. The rough variant does not require RESET departure, only r>=R and both phase-zero/root entries. This is a paper estimate using the earlier sieve; finite audit tests the general key quota only. No assumption of independence of two canonical basins, and no bound on their product. Key quotas do not prove raw mass small. Heavy nearby canonical pair keys are the next target.

## 4. Audit and concrete cohorts

Standalone research/min_clock_paired_low_entry_audit.mjs, initial d8ea1f3d18fa48af30844b7c10aa9e100051cc79, final 4f4df0bc071a595ff9e08cb14de9c7c6971ba08d, verified exact blob c1a63e2d1400bab2b870b2b2df51cbf02ce4e22f. Extends 64323f5 actual sampled record/arrival audit. Checks true LOW suffix, gain/clock/deficit bounds, entry phase congruence, distinct entry, large-label exclusion, actual disjoint tail physical occupancy (128 pairs per nonempty block ledger), actual canonical point including virtual, distinct/equal canonical pair partition, separation and absolute diagnostic quota. Original 48 record comparisons at X4096/16384/65536, two occupations, original L30/L6, four Q/bands; each now tests independent paired L6/Y3, L30/Y5, L210/Y7, 144 block ledgers. Same 12 sampled origin levels per X. Actual JS functions run in available runtime, not Node or Lean. All assertions passed. Finite A32, general key cap8B/L, earlier rough threshold ceil(B/16). No asymptotic inference from sample.

    node research/min_clock_paired_low_entry_audit.mjs 4096 16384 65536

X65536 upper band both original LOW choices identical. Same-outgoing pair raw1028228.90265; low d1<=32 sector668914.96165 (2422 pairs), high359313.94100. Independent paired blocks:
| L | both entry phases zero incl root | mixed | both nonzero | actual entry-pair groups |
|6|164881.18584|496853.02065|7180.75516|76|
|30|633839.73451|35075.22714|0|91|
|210|661734.20649|7180.75516|0|110|
Largest observed LOW gain4/10/26 and clock6/17/28, entry clock gap13/13/15 respectively. Both q>T large entry mass46951.09145 at L6 and L30, zero at L210 (T larger), both distinct labels421/79; no counterexample. Raw phase-zero fractions sample-dependent.

Largest p107 44x32 cohort (1408 pairs,388865.51032) prior q3 waits at C202120. L6 main subgroup40x32: early entry (J,t)=(202120,101060), q163 from201958, starting101059, d0 RESET, then q3; late entry (202120,101070), q5 from202116 at101061, d20, then q3. Mass353514.10029. L30 main subgroup40x31: late entry now (202116,101061), q7 from202110 at101058, d6 RESET, then q5,q3; early unchanged. Mass342466.78466. L210 main40x29: late entry (202096,101048), q17 from202080 at101040,d0 RESET, LOW chain5,3,3,5,3,7,5,3 gain26 clock28; early unchanged. Mass320372.15339. These are actual entry event subgroup incidences, not full source populations.

Canonical reduction:
| L | equal point | distinct pair | distinct keys | diagnostic paid | residual |
|6|148862.57817|16018.60767|15|8311.10914|7707.49853|
|30|109920.79056|523918.94395|31|5604.8|518314.14395|
|210|109092.24189|552641.96460|50|1291.42857|551350.53603|
L30 distinct nonroot441616.44248, root-containing82302.50147, max index separation4. L210 distinct nonroot417864.71386, root134777.25074, max gap8. Largest L30 key (101059,101061): all 44x32 pairs, weight388865.51032; actual canonical states (202116,101061) and (202120,101063), gap2, despite differences among immediate entry labels. This is a single canonical-pair key for entire dominant pair graph. L210 key (101053,101061) 30x44=1320 pairs mass364561.41593, canonical horizons202104 and202120, gap8. Distinct L30 second key (101133,101137), 3x82=246 pairs,67940.99115. All samples independent comparisons, no numerical contraction. Main and independent prime-root branch unchanged.

## 5. Next

The dominant L30 canonical pair consists of adjacent odd indices 101059 and101061; study the elementary renewal arcs from these two actual starts and their upstream ancestor populations. The deterministic contact identity allows studying a pair of canonical starts independently of its many original tags, but the two basin multiplicities remain the main issue. Examine nearby canonical pair support conditional on actual rough merge, and whether short separation admits a stronger transport via disjoint renewal arcs or a sieve on both source-start residue classes. Keep nonzero entry phases, equal canonical points, long tails and original cross-to-donor chi/recipient reuse separate. No twin infinitude proof.
