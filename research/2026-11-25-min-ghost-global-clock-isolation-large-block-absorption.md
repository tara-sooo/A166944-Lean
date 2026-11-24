# Global seen-clock isolation and large LOW-block absorption in the high-return ledger

2026-11-25 JST. Continues db7d27de7415e5551f3493efa0af0e09a2a13230 on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary conditional-probability and deterministic ledger deductions; finite shared-CRT audit. No Lean compilation. Neither the clipped-height tail criterion nor the physical far-coalescence upper bound is proved.

## 1. All-depth clock isolation, including repeated high events

Keep the infinite CRT ghost, with its uniform independent prime coordinates and common initial time parity. Fix an integer time U, and cutoffs 11<=P<=z<=U with P^2>=2U. A high label is >=z. Use the filtration revealing all p<P initially, common parity and selected tick labels including zero thereafter. For an unused q>=P the conditional probability of first selection at tick s<=U is at most 2/q^2. Once p is selected, its two possible time-clock classes modulo 2p are known, irrespective of horizon eligibility.

Let v be an integer with 1<=v<z-2. Define a bad pair to be two distinct labels p,q selected at least once by U, both >=P and at least one >=z, having possible clocks in [1,U] at distance <=v. These are possible clocks, not just actual selections, and the two close clocks may occur BEFORE either label is first selected. We count bad pairs without assuming the seen labels or their phases are independently sampled.

Consider an ordered pair with p first selected before q, and let s be the first-selection tick of q. The possible clock classes of q consist of s mod2q and one of s+(q+2) or s-(q+2) mod2q (the choice follows the selected side). Consequently any of its possible clocks in [1,U] is s+e for an offset e in a deterministic list depending only on q and U, of size O(1+U/q). This list includes both side alternatives, and offsets in [-U,U]. The number of possible p clocks in [1,U] is O(1+U/p). Thus for a fixed known p phase and candidate q, the number of s in [1,U] which could make the pair bad is at most
    O((v+1)(1+U/p)(1+U/q)).
This follows by summing over p clocks and q offsets, and allowing the entire integer interval of length 2v+1 for each difference. At tick s, whether p is previously seen and whether s lies in this candidate set are measurable BEFORE s. Multiply the indicator by the conditional unused-q selection bound 2/q^2, and sum over s. Pathwise the sum of the indicators is bounded by the displayed count times 1{p seen by U}, even if some possible s occur before p was seen. The deletion estimate P(p seen by U)<=U/p^2 therefore yields
    P(p seen before q, pair bad, q seen by U)
        <= O((v+1) U (1+U/p)(1+U/q)/(p^2 q^2)).
This argument bounds bad potential-clock pairs across the entire horizon, not merely close events immediately after a fresh high selection. No independence of known p and q is asserted.

Sum over both orders and both label-band assignments, counting high/high pairs at most a constant number of times. By prime-count upper bounds and partial summation,
    S(x)=sum_(p>=x prime) (1+U/p)/p^2
         =O(1/(x log x)+U/(x^2 log x)).
Hence
    P(any bad pair) <= O((v+1) U S(P) S(z))
                   = O((v+1) U^3/(P^2 z^2 log P log z)).
The last estimate uses P<=z<=U. It is uniform over finite upper alphabets and the infinite alphabet. The nonnegative pair sum is convergent. It does not require conditioning on the future absence of bad pairs.

For P=z=ceil(U/(log U)^b) with fixed b>1, take
    v=floor(U/(log U)^(4b-2+eta)), eta>0.
Then the probability bound is O((log U)^(-eta)), and v<z-2 for all sufficiently large U. Outside this exception, ANY two actual high events through U are separated by more than v: distinct labels by the pair exclusion, the same label by the exact own-clock spacing >=p-2. Thus the full path following EVERY high event (fresh or repeat) agrees with its <z deterministic continuation for the next min(v,U-s) ticks. The statement is about a capped prefix, not necessarily the whole lifetime. If P<z, the same conclusion holds with the <P continuation using the asymmetric pair exclusion, since every actual subsequent label >=P would have a close possible clock of a seen prime (or the same high label, already excluded by v<z-2). For example P=ceil(U^alpha), alpha>1/2, z as above, v=floor(U^(2alpha-1-epsilon)) for fixed 0<epsilon<2alpha-1 gives error o(1). Compared with the earlier fresh-only asymmetric guard, this result applies after repeated high starts as well, though its probability budget may require a smaller v for fixed power cutoffs.

This does not establish that LOW-only lifetimes are less than v. Nor does it prohibit a known high label from being eligible at a LOW terminal; it prohibits only close actual/potential clocks. It is an independent unconditional estimate, not a solution of the repeat or active-occupation residual.

## 2. Replace total LOW gain by a count of large-gain blocks

Use the previous bounded-coefficient relation exclusion, with 1<b<3/2, z=ceil(U/(log U)^b), K0=ceil(C_b (log U)^(b-1)), and either R=floor(U^(1-epsilon)) for fixed epsilon in (0,1), or the stronger explicit R_* from that note. Let Good be its event that the number of distinct high labels is <=K0, no selected high label is >=ceil(U), and EVERY consecutive return of a high label consumes intervening LOW gain >R. We know P(Good^c)=o(1). No new conditioning on Good is used in the probability calculations below.

Partition [0,U] by actual high events, including the initial interval and final truncated interval. Each block starts at zero or just after a high event and ends at the next high event or U. Put the LOW gain d_i equal to the sum of p-1 of LOW events in that block. A high event on its right boundary is not counted in d_i. All LOW events belong to exactly one block. The number of blocks is F_U+R_U+1, including a possible zero-length final block, where F_U is the number of distinct high labels seen, R_U is their total number of repeat selections. A return interval of a fixed label p (from its previous selected post-state to its next selected pre-state) is a union of COMPLETE blocks in this partition, with their boundary high jumps omitted in the LOW-gain sum. Each block belongs to at most one return interval for each fixed p, hence to at most F_U<=K0 return intervals in total.

Fix 0<epsilon0<1 and set D=epsilon0 R/K0. Call a block large if d_i>D, and let L_D count such blocks (one may omit the initial and incomplete final blocks, since they cannot be inside a completed return). At most K0 L_D returns contain any large block: charge to one such block, using the per-label disjointness. Every remaining return consumes >R from small blocks alone. Summed over all such returns the small-block contribution is at most K0 D(F_U+R_U+1). Thus, on Good,
    R_U <= K0 L_D + epsilon0 (F_U+R_U+1),
and consequently
    R_U <= [K0 L_D + epsilon0(F_U+1)]/(1-epsilon0).
For epsilon0=1/2 this gives
    R_U^term <= R_U <= 2 K0 L_D + F_U + 1,  D=R/(2K0).
This is a new deterministic absorption inequality. Unlike the previous R_U<=K0 G_low(U)/R, it does not require a bound on the magnitudes of individual large gains. A very large gain in a single block still charges at most K0 returns. In fact L_D<=G_low(U)/D, so the new bound need not be numerically stronger when all gains are small or near the threshold. Its advantage is permitting arbitrary gain on a few exceptional blocks. The inequality holds for arbitrary interleaving and repeated labels, without the clock isolation event of section1.

For T=floor(Y sqrt(log Y)), w=2Y, U=T+w, take fixed b in (1,3/2). Then K0=o(T/w), and D=U^(1-o(1)) for R=R_*. If
    L_D=o_prob((T/w)/K0),
then R_U^term=o_prob(T/w), since F_U<=K0 on Good. The required block count scale diverges as (log U)^(3/2-b). Combined with the earlier gap-or-repeat bound, for fixed delta in (0,1), m=floor(delta T/w), and integer k=o(m) with K0=o(k), we have
    P(sigma_Y>T)
      <= P(A_T>(1-delta)T)
         + P(L_D>(k-K0-1)/(2K0))
         + o(1) + 2^k(1-c/2)^m.
Here the last term tends to zero; choose k so that k>K0+1 eventually. Equivalently the sufficient conditions are A_T<=(1-delta)T with probability 1-o(1) and K0 L_D=o_prob(T/w). This is a replacement of the LOW-total-gain requirement, not a proof of the new count-tail bound. It may be useful if an upper bound on the number of long-gain continuations at high starts is easier than controlling their entire gain.

## 3. Exact signed active-height ledger and a joint duration/drop count

For each block i, let a_i be its LOW-active elapsed time (time during which at least one p<z is eligible). This is exactly the capped LOW-only lifetime within the interval, as established previously, and active time is a single initial portion of the block. Let A_U=sum_i a_i, Q_U=U-A_U. Define signed active contribution
    h_i=2a_i-d_i.
It measures the relative height change over the active portion, before the next high jump, including an active waiting segment truncated by a high event or by U. It is not in general the sum of signed increments at completed LOW event times alone, since that truncated waiting segment may be present. Let G_high=sum_(actual high events through U)(p-1). With g(U) the relative horizon gain after any events at U,
    2U-g(U) = 2Q_U + sum_i h_i - G_high.
This is exact at arbitrary integer U with the horizon frozen between events, not an assertion about the attained-event maximum D_Y at a nonevent time.

Every large block d_i>D has either
    a_i>=D/4  (slow active block),
or
    d_i-2a_i>D/2  (negative active-height block).
Indeed if a_i<D/4, d_i>D implies the second inequality. Let S_D and N_D count these two block types, respectively, over the same partition (including small blocks that satisfy either condition only increases the bound). Then
    L_D<=S_D+N_D,
    R_U<=2K0(S_D+N_D)+F_U+1
on Good. Since the blocks are disjoint in time,
    S_D <= 4 A_U/D.
And N_D<= 2 sum_i (d_i-2a_i)_+/D; using N_D directly avoids charging magnitude of a huge negative excursion. This gives a joint duration/signed-drop form of the new return bound. The large LOW gain needed for repeat cannot always be treated as a cost: a short block with a large gain necessarily decreases height on its active portion. A proof of a small count of such negative excursions, or a direct argument absorbing their losses when estimating positive first-passage heights, would be needed for further progress. No such cancellation inequality is established here.

On no-gap paths with many inactive tests, the previous test lower bound forces many repeat outcomes except with exponentially small probability. With Good and F_U<=K0=o(m), the absorption inequality then forces order m/K0 large blocks (or slow/drop blocks) unless the test count itself is small. This is a count of distinct blocks, not just existence of one long suffix. At near-top cutoff b=5/4 and R=R_*, the count scale is (log U)^1/4 and D=U^(1-o(1)). A few exceptional blocks are permitted. The new criterion still needs active-time and large-block probability estimates; it has not proved the required tail of D_Y. The physical far-coalescence upper bound remains independently unresolved.

## 4. Finite audit

Saved research/min_ghost_global_clock_block_absorption_audit.mjs and research/min_ghost_global_clock_block_absorption_results.json, exact remote readback at 1af336233a1e3761711105145d464f824ee0edc6. Run 512 fixed-seed shared CRT initial states per Y=53,199,797,1597,3203, finite upper alphabet V=8Y, T=floor(Y sqrt(log Y)), U=T+2Y. Diagnostic z=ceil(U/log^1.2 U) and ceil(T^.8), min11. Simulate all event records through U, including final truncated plateau in the signed ledger. Compute all possible clocks in [1,U] of seen high labels and seen medium labels >=ceil(U^.65) below z (min5). Count pairs within v for v=floor(U/log^3 U) and floor(sqrt U), with local clipping at z-3. Verify that actual close high events imply bad high-clock pairs, actual close medium/high events imply a bad asymmetric pair, and when no bad high pair exists the <z capped continuation exactly matches the full prefix after every high event, including repeat events. The diagnostic parameters do not purport to make the asymptotic probability bound small.

Compute all high-delimited LOW blocks with exact elapsed and active time and signed gain, verify conservation, full signed ledger, large/slow/drop dichotomy at R=floor(U^.5), floor(U^.75), floor(U^.9) and D=R/(2F_U) for F_U>0. On paths where EVERY actual return has intervening LOW gain >R, verify the two separate charge bounds and absorption inequality. This tests the deterministic implication, not the previous stronger full relation-set certificate. The code's fields certified and repeatCertified are unused zeros; relationGood and repeatGood report actual-return conditions, not all-coefficient certification. No original canonical source paths or Lean compilation in this turn.

At Y3203,U15506,z1022, across512 paths:473 fresh high selections, zero repeat, 985 blocks, LOW-active time552190, LOW gain670702, high gain2043608, total negative active contributions31280, total positive active contributions464958 (these are sums of magnitudes of signed block contributions, not the final signed height). At diagnostic v17, 26 paths have a bad high clock pair (31 pairs), two close actual high event pairs occur, and 382 guarded high starts pass exact prefix replay; 75 paths have bad asymmetric pairs including high/high. At v124 the corresponding high-pair bad count is82 paths and prefix replays222. This demonstrates that a conservative clock exclusion is not deterministic at the finite scales.

At Y1597,z545 there are450 fresh high selections and4 repeats (all from LOW-inactive plateaux); for R808,258 paths with at least one seen high satisfy the actual return-gain bound, including all4 repeats, and all4 returns touch a large block. Across paths with at least one high, there are334 large blocks,503 slow blocks,40 negative-drop blocks at the per-path D=R/(2F_U). At R3084 none of the repeat paths satisfy the assumed lower return bound. These finite checks are not asymptotic estimates of L_D, and the actual tests observed no repeats among the largest-Y sample. A zero repeat count in a finite sample is not a proof of their asymptotic absence.

## 5. Remaining work

The all-seen-clock estimate extends the no-high-interference prefix to repeated starts. The large-block absorption inequality replaces total LOW gain by a count of exceptional LOW blocks; the exact signed ledger splits those blocks into long active occupation or substantial negative height contribution. The remaining probabilistic task is to bound the number of those large blocks, or use signed losses directly in a first-passage argument. Active occupation also remains open. No complete twin-prime proof, no main edit, no new branch, no Lean compilation.
