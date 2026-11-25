# Donor last-upcross partitions and gain-weighted upstream ascent transfer

2026-11-25 JST. Continues 24bfe41f766e37896aff332739c0fb0511bf7a39. New paper results: exact nested ancestry partitions of a nonreset donor cohort by last true upward crossing of each high deficit level; weighted common-minimum identity separates deficit created on shared donor histories from inherited high-deficit first meetings; gain-weighted upstream transfer to full positive-drift occupation WITHOUT an extra factor for the number of rough target slots. The diagonal of the new moment costs O(XB). An explicit cross-energy transfer condition is given, not a proof that every dense donor anchor satisfies it. All original masks and old terminal charges unchanged, no Lean compilation, twin infinitude OPEN.

## 1. Original pair ledger and long LOW donor anchors

Use the same dyadic X, N=X/2 odd sources M, B=ceil(sqrt(7X)), u=log B, s_M=M+2, C0=2M-2, H=4B, K(M)=floor((7M-1)/4). Complete original crossing waits, with e_M<=s_M+H+2B, stop at twins or first recorded event at/beyond relative H. In particular all original gains <=12B+6, all true deficits d=2t-C in [0,12B+6]. Aggregate actual remaining old terminal charge into W_ij<=U=6B+3 per distinct unordered original pair, after any frozen previous payments. No reference-created pairs.

Restrict to long-age LOW jump-stationary first contact at a completed rough recipient slot (J,v), r=r(J)>=R=cB/u^2, incoming donor p<=y, recipient age A>3L+3, even primorial L<=u^1/16 with largest prime y. The previous note proves unique last nonLOW donor anchor g=(J_a,t_a,q>y), with d_g=2t_a-J_a>=2A-5L>6; delta=J-J_a in [p-1,L), elapsed LOW suffix <=3delta. The anchor uniquely determines recipient slot and donor arrival t. All donors through this labeled anchor have identical true state at t_a, and identical predecessor at t_a-1 (same selected q). For each g form the actual cross-edge graph of these donor-recipient charges. Let W_g be its total weight, n_R(g) the number of distinct positive recipient vertices, and w_i the sum of its weights at donor i. Use actual normalization
    omega_g=max_i w_i>0,  x_i=w_i/omega_g in (0,1],
    m_g=sum_i x_i,  W_g=omega_g m_g,  omega_g<=U n_R(g).
All statements about the donor square moment also hold for arbitrary fixed x_i in [0,1], including x_i=1. Do not identify an effective row-normalized mass with an actual integer number of sources; both can be used but they are different quantities.

## 2. NEW last-upcross ancestry partition

For each donor i reaching g and each integer level lambda in [7,d_g], define L_i(lambda)=(z,C) to be the last actual stationary upward crossing of lambda before or at the anchor. The state is after tick z, d(z-1)<lambda<=d(z). At a stationary tick d increases by exactly 2, at an event tick its increment is 3-p<=0; initial d=6. Therefore every such level was crossed upward, and its last upward crossing exists, occurs at a stationary tick strictly before a subsequent completed event no later than t_a, and is not crossed downward afterward through the anchor. The upward key includes clock and horizon; projected equal horizons do not suffice.

Partition donors by equality of L_i(lambda) at each lambda. These partitions are nested: equality at a lower lambda implies equality at every higher lambda (through d_g). Indeed both donors share actual true state at the lower last upcross, hence their deterministic suffixes agree; the higher last upcross occurs at or after that tick, possibly at the same tick if both adjacent levels are crossed. This is a different hierarchy from primorial horizon cuts: it is indexed by surviving deficit height.

For two distinct donors i,j at g, let (tau,J_*) be their actual earliest common true state in their full original prefixes. Define
    mu_ij(g)=min_(tau<=t<=t_a) d(t)
along their shared suffix, including the first common true tick and the anchor. The minimum is computed by the deficit at tau and the actual subsequent recorded post-states, since stationary ticks only increase d. Then EXACTLY
    L_i(lambda)=L_j(lambda) iff lambda>mu_ij(g),       (1)
for 7<=lambda<=d_g. If lambda>mu, the common path dips below lambda and must cross upward again before anchor; the last crossing is common. Conversely a common stationary upcross requires both donors present at its preceding tick, since neither an event nor a root at high level is a stationary upcross. Its preceding deficit is below lambda, so the common minimum is <lambda. This also handles a jump-stationary internal first contact, where only one donor may cross upward at the first common tick; it cannot be a shared upward crossing for both at that tick. A root starts at d=6 and cannot supply a high level without a stationary crossing.

Put D_g=d_g-6>0, and define for each distinct internal donor pair
    s_ij(g)=d_g-max(6,mu_ij(g)),
    h_ij(g)=max(6,mu_ij(g))-6.
Both nonnegative, and s+h=D_g. Here h denotes inherited high levels, not an elapsed time. The s levels are created by a surviving last ascent on the shared donor history; the h levels have different last-upcross keys on the two histories. In particular h>0 means their actual first contact took place above 6. The minimum, not only the first-contact deficit, is essential: a later common drawdown can erase earlier inherited levels.

## 3. NEW weighted square identity and earlier high-contact reduction

Write
    S_g=sum_(i<j) x_i x_j s_ij(g),
    I_g=sum_(i<j) x_i x_j h_ij(g),
    Z_g=D_g sum_i x_i^2.
Then exactly
    D_g m_g^2 = Z_g+2 S_g+2 I_g.                     (2)
Alternatively S_g is sum over levels lambda of the weighted offdiagonal pairs within each actual last-upcross class, independent of computing pairwise first meetings. Define shared fraction sigma_g=2S_g/(D_g m_g^2), inherited fraction beta_g=2I_g/(D_g m_g^2), diagonal fraction Z_g/(D_g m_g^2). These three sum to 1. They are fractions of the normalized DONOR SQUARE moment, not fractions of the original cross-edge energy W_g.

If beta_g>=b>0, the weight sum of internal donor pairs satisfying mu>=6+b D_g/2 is at least b m_g^2/4. Proof: those below that threshold contribute <=(bD_g/2)*(m_g^2/2) to I_g, while I_g>=b D_g m_g^2/2; each remaining pair contributes at most D_g x_i x_j. Hence a large inherited fraction forces many weighted actual donor pairs with genuinely earlier first contacts at high deficit, staying above that height throughout the common suffix to g. Their internal meeting is strictly earlier than the anchor (they share the anchor's selected labeled predecessor at t_a-1), hence earlier than the original donor-recipient contact. This is a reduction to earlier high-deficit ancestry, not a bound on its size. No assumption that the two internal donors themselves had positive OLD terminal energy.

## 4. NEW transfer of shared last-upcrosses to full positive occupation

For each donor pair and common surviving last upcross in a completed original wait at horizon C, with outgoing selected p and minimal r_C, both donors' actual full waits of lengths w,w' have positive NET recorded drift. Indeed their respective arrivals precede the true upward tick (initial deficit there is below lambda), their common post-event deficit is >=lambda (last upcross survives to g), hence 2w>p-1 and 2w'>p-1. Both waits complete before or at the anchor. The number of shared levels assigned to this one wait for this anchor is at most 2 min(w,w'). Since r_C<=p and w,w'>(p-1)/2>=p/3, their full ordered offdiagonal occupation energy is
    e_+(i,j,C,v)=2 r_C (w/(2r_C))(w'/(2r_C))
                 =ww'/(2r_C)>=min(w,w')/6.
Thus assigned shared level count <=12 e_+. This is an actual full positive-drift occupation term, not merely selected-gain p times ancestor mass. No need to force that upstream wait to be rough or lie in the late HIGH slab. Summing at a single donor anchor yields
    s_ij(g)<=12 sum_(shared full-positive waits before g) e_+(i,j,C,v).

A naive sum of S_g across anchors would reuse an upstream donor pair/wait as many as O(B/R) times, because both donors complete every corresponding rough recipient target. Instead use r_g=r(J_g) and define
    S^sharp=sum_g (r_g/B) S_g,
    I^sharp=sum_g (r_g/B) I_g,
    Z^sharp=sum_g (r_g/B) Z_g,
    M^sharp=sum_g (r_g/B) D_g m_g^2.
For any FIXED internal donor pair, its anchors in this sum have DISTINCT rough target slots: each tag has only one last nonLOW anchor at a specified arrival into a given completed rough slot, and both are donors at g. Since each target is an actual original completed wait,
    sum_(g containing that donor pair) r_g
       <=1.5 min(total original gain of either tag)
       <=1.5(12B+6).
The same bound holds for any single donor tag. Therefore each fixed upstream pair/wait, even if its levels survive to many later g, is reused with TOTAL weight r_g/B bounded by an absolute constant. Since x_i x_j<=1, summing the preceding per-wait charge inequality gives
    S^sharp <= C E_+^full,                           (3)
where E_+^full is the full actual same-slot positive-drift offdiagonal occupation moment over ALL original sources and ALL their original completed positive-drift waits (no rough/late mask). Can take C=12*1.5*(12+6/B). If one sums over a bounded number of independent classifications, multiply by that constant; here one fixed L,y,R and one actual ledger. It is also valid with unweighted x_i=1. The proof bounds the total of reused counts on each physical donor pair/wait; it does not assume distinct high levels are disjoint across anchor targets.

The diagonal satisfies
    Z^sharp <= sum_(g,i in donors) (r_g/B) D_g
             <= O(B) per original tag summed over N
             =O(XB),                                (4)
because D_g<=12B and the same per-tag r_g gain bound applies. Thus the exact aggregate identity
    M^sharp=Z^sharp+2 S^sharp+2 I^sharp
gives the new unconditional comparison
    M^sharp <= O(XB)+C' E_+^full+2 I^sharp.           (5)
It has NO extra log factor for the number of reused rough targets. (3) is a conditional upstream transport, not an absolute small estimate for E_+^full. The full positive upstream moment is a different, still open energy sector; no self-absorption of the masked old terminal energy is inferred. The inherited component in (5) may be arbitrarily large unless earlier high-deficit donor births are controlled.

## 5. Explicit cross-weight transfer and its limits

For an anchor define the actual dimensionless cross-to-donor coefficient
    chi_g=B omega_g/(r_g D_g m_g).
Then exactly W_g=chi_g (r_g/B) D_g m_g^2. For any set of anchors satisfying chi_g<=kappa and sigma_g>=sigma>0, equations (2),(3) imply
    sum W_g <= (2 kappa/sigma) S^sharp
             <= O(kappa/sigma) E_+^full.             (6)
For example a vanishing kappa/sigma, together with an independently established E_+^full=O(XB u^3), would pay that cross sector by o(XB u^3). Neither hypothesis follows just from a large number of donors. This condition uses the actual row maximum, not an upper estimate based on all possible recipients. It permits selective transport without paying the entire original cross graph or changing the original masks.

Alternative local comparison: if all positive recipient partners of g have age at least a_g, their natural full occupation at recipient slot has energy E_R,g>=a_g^2 n_R(g)^2/(4r_g) (includes diagonal). Since W_g<=U n_R m_g, and if sigma_g>0 then m_g^2=2S_g/(D_g sigma_g), this yields
    W_g <= (2 U/a_g) sqrt(2 r_g S_g E_R,g/(D_g sigma_g)).
This is a local inequality only. Multiple different donor anchors can use the same recipient group, so a global sum would need a separate recipient reuse bound or allocation. The gain-weighted transport in (3) specifically solves reuse on the DONOR side, not on both sides of this latter comparison. Do not claim a global geometric-mean energy bound without that extra step.

The remaining sectors are high inherited fraction (earlier high-deficit first contacts), large chi or small shared fraction, short age and nonrough receivers, other first-contact types, and previous immediate/later, heavy distinct-slot, low-r and MED/full-positive residuals. Equations (3)-(6) are a new connection to earlier occupation and not a bound for all the remaining old terminal energy.

## 6. Reproducible diagnostics

Standalone research/min_clock_donor_ascent_partition_audit.mjs, initial source commit 669167c1f9630aeb44fe000c4a6836bab3e0df6d, final 4dbc2f25ae7cb6517fa148cf1d588da5ceb6c287, exact remote blob c9f4e1fe0dac4b486f1b18271e527754e95bf5a4. Retains the previous literal forward MIN and exact inverse original sampled-origin engine and its original pair-level masks; uses the actual aggregate sampled W_ij. New code builds last stationary upcross keys for every high level and compares the independent level-partition sums to the actual pairwise common-suffix minima; checks (1) at each pair-level, independently scans up to128 literal common true paths for minima in each nonempty mode, verifies both upstream waits are positive and complete before anchor, per-wait 12e_+ bound, actual row normalization, exact (2), per-pair r-target reuse against both original gains and scaled (3). The earlier source normalized rows by U n_R, final uses actual maximum row weight; fractions unchanged, moments now larger and meaningful. Both runs passed. The aggregate diagonal asymptotic (4), the inherited-threshold corollary, and the conditional transfer (6) are paper deductions (the corresponding identity, not an asymptotic bound for chi, is audited). No Lean compilation.

Run:
    node research/min_clock_donor_ascent_partition_audit.mjs 4096 16384 65536
Actual functions executed in available JS runtime, not separately under Node. Final 12 window/occupation/classification combinations: X4096/16384/65536, two occupations, usual stress L30,y5 and independent L6,y3 for the new anchor classification ONLY, preserving all old sampled pair weights and masks. Same 12 selected rough origin levels per X as prior notes. R=max(y+1,ceil B/16), original stress masks and recipient quota base8 unchanged. Sampled-only aggregate; no whole original energy estimate. Smaller L6 control is a separate classification and not added to L30. All final checks pass.

Largest X65536, L30,y5: 2 anchors, 4417 distinct internal donor pairs summed over anchors, 128 literal minimum oracles, 151601 distinct upstream internal donor pair/waits, actual full-positive pair moment restricted to these waits1856155.13575, max r-weighted reuse .40855457 (scaled by B). Shared/inherited/diagonal unweighted (row weights normalized to1 at these two uniform-row anchors) 2818270/80766/68792 respectively (offdiag s and h not doubled); scaled shared1139132.58112, inherited29949.97345, diagonal26645.10914, square2364810.21829. Identity exact. Do not confuse the magnitude of these internal donor moments with the original sampled cross charge8634.74845.

| anchor | donor/recipient vertices | d_g | max common minimum | shared fraction | inherited fraction | diagonal fraction |
|---|---:|---:|---:|---:|---:|---:|
|(203038,101860,q11)|92/143|682|116|96.5713%|2.3417%|1.0870%|
|(165478,82892,q17)|22/193|306|282|76.4821%|18.9725%|4.5455%|

For q11, actual common last-upcross level/pair count2762744, inherited66992, 3334 donor pairs with common minimum<=6, none with common minimum>=344 (half high strip). Positive upstream moment for the counted pair/waits1818708.00877. For q17, shared55526, inherited13774, 84 internal donor pairs with min<=6, 40 with min>=156, upstream37447.12698. Both cohorts' per-donor cross rows uniform in this sampled graph; maxima59.62635379 and143.14199550, normalized masses92 and22. Computed chi approximately .00234 and .1158, respectively, for these SINGLE-LEVEL sampled charges, not for their full cross weights over all origins and levels. Natural full recipient energies4558742.81679 and1466891.34646; no global reuse inference from these two values. Literal donor path inspection at q11 showed earlier large positive waits with selected q67,97,127 (e.g. q97 wait170 raises recorded d144 to388); at q17 several donor paths share q127 wait176 raising d28 to254; other donors have a q67 wait100 raising d6 to140. Not all donor paths use the same such wait; the exact partitions, not these example paths, determine the moments.

Independent L6,y3 control at X65536 full-positive: 10 anchors, old sampled cross charge11453.94366, 33330 internal pair-anchor incidences, 128 literal minimum checks, 254856 distinct upstream pair/waits, upstream moment2573340.75529. Actual pair reuse up to3 different target anchors, max sum r_g/B=1.02949853. Scaled shared1418163.73746, inherited93748.84661, diagonal31436.20944, square3055261.37758. This exercises the gain-weighted reuse bound nonvacuously. Shared fractions range .48 to .96571347; one 181-donor/12-recipient group at (165478,82790,q17) had .785872 shared/.208603 inherited. X4096 L6 control has one 31-donor/6-recipient group at q5, shared fraction .92826916, cross127.96463 late/213.00713 positive, max reused r/B=.18235294. L30 smaller windows and all X16384 samples have no long-LOW target under chosen finite conditions. X65536 late HIGH selected samples zero. These are diagnostic finite fractions, not a proof that shared fraction dominates for general windows. Main and other branches unchanged.

## 7. Next step

Use (5) to attack the inherited moment via earlier high-deficit first-contact keys and reverse reachability, and derive a uniform upper bound for E_+^full or the much more targeted upstream moment in (3). Also investigate the cross-to-donor coefficient chi using actual row mass and recipient-side time reuse. A productive alternative is to combine donor and recipient transports at earlier true upcross levels, but a global recipient reuse control is required. Do not claim twin infinitude from the conditional transport. Preserve all prior unresolved residuals and independent prime-root work.
