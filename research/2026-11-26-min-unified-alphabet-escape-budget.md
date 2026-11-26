# Integration XXXII: adaptive alphabet escape and disjoint extra-relay gain

2026-11-26 JST. Parent 3d9c7b19f1e021bdd23f3335e9b3328b016f5356; direct preflight [568cfa4](https://github.com/tara-sooo/A166944-Lean/blob/568cfa484c91708e7e9196731f7a8566b9deda52/research/2026-11-26-min-direct-bounded-word-crt-and-repeat-supply.md) unchanged from XXXI. New: replace a count of interior events (which might already be consumers) by an upper count for words closed in an arbitrary actual alphabet containing BOTH source and consumer labels. Under quantitative small-low-gain and sparse-alphabet conditions this forces a macroscopic gain DISJOINT from both endpoints of the height transport. Also deep starting sources forbid every reset in their short physical relay, so a nonreset-only low-gain budget suffices there. The result is a strict conditional improvement to the height-transport saturation bound, not the final overlap loss.

## 1. Setup and exact disjoint budget

Use the actual extracted source-consumer population of XXIX, on original tags and original long bins L, after any filters. Denote retained matched mass M. Every source is upward, every consumer downward, labels of both comparable to Y (at least Y and at most K0 Y with fixed K0, enlarge K0 as needed). All pairs are local to the same original bin. Actual matched height units are not reused, including compulsory buffers. Let U,D be the sets of actual source and consumer events in a bin. These sets are disjoint by sign, even if their label supports overlap. The following inequalities hold over all original tags:
    M <= (3+4/(Y-1)) G_U,
    M <= G_D.
Indeed source positive ordinary change 2w-g<=3p+1=3g+4 and consumer down length <=g; each unit is charged only once. Neither G_U nor G_D is a new copy of the gain of a tag.

Assume near-minimal original source support as in XXX, with the actual retained source occurrences separated for each same label by at least 2a0 p log²Y-2. Such separation can be obtained after a small matched-mass discard using XXVIII, before source-preserving extraction. For a fixed tolerance one can work on the resulting population itself (all definitions of M, U,D refer to it). Assume M>=rho NH, L>=B Y^eps and L>=Y^(2+eps1), L<=H. Work first on bins with s=number of retained source labels <=C0 log²Y. As in XXX the high-support bins can be discarded at arbitrarily small normalized mass by increasing fixed C0, since the support sum is O((NH/L)log²Y) and each bin has mass O(L). Alternatively impose the per-bin bound directly.

In each retained bin choose ANY containing alphabet A_j of actual or hypothetical high labels (>=Y), including all labels of U and D; let |A_j|<=a(Y). The counting result below needs only that both source endpoint labels belong to A_j, but the inclusion of D makes the extra gain disjoint. The alphabet may depend on the entire actual bin. We choose a(Y)>=log²Y and a(Y)<=O(Y), not necessarily near-minimal. If all consumers have small local support, a=O(log²Y) is possible, but this does not follow from near-minimal SOURCE support alone.

Order U by actual prehorizon, take consecutive sources, and retain distinct-label short transitions D_gap<=A Y for fixed large A. First endpoint weight <=3K0Y+1 per bin, total o(NH); long gap weight <=O(NH/A) by the gap span; same-label short impossible by same-label separation. Use either ENDING or STARTING matched weight of the source (consistent within one ledger). Denote retained transition weight F. It is at least M-o(NH)-O(NH/A). Strict physical relay interiors are pairwise disjoint. A high word includes all actual events >=Y from one source through the other, length j<=J=2A+2, intermediate labels <=AY+1. Let E_low be strict interior gain on p<Y, and G_out be gain of actual high interior events whose label is not in A_j (count each event once). Every relay not closed in A_j has at least one such event of gain >=Y-1. Its transition weight <=3K0Y+1. Consequently if F_open is the weight on such words,
    G_out >= (Y-1)/(3K0Y+1) F_open.                 (1)
This does NOT follow for the older interior-high gain without alphabet restriction. Every counted outside event is distinct from U and D, because of its label and actual bin. Thus
    G_all >= G_U+G_D+G_out
          >= [1+1/(3+4/(Y-1))] M + (Y-1)/(3K0Y+1) F_open.     (2)
No event may be counted again as an extra relay for another word; disjointness holds on original tags, not necessarily on unweighted physical rays. A low label or an internal label already in U/D never receives this extra credit.

## 2. Closed alphabet capacity at the pair CRT scale

At a fixed ordered pair of distinct endpoint labels p,r, the shift D_gap is p-1 plus a sum of at most J-2 high interior gains from A_j and E_low. If E_low<=b, with 0<=b<Y-3, the number of distinct shifts satisfies
    t_pr <= (b+1) sum_(k=0)^(J-2) a(Y)^k.
No assumption on repetition, primality pattern, order, or how many LOW events make the same gain. Apply XXX's pair four-form estimate (two actual upward endpoints), valid already at L>=Y^(2+eps1), all endpoint labels comparable Y, and sum over s² ordered pairs. Uniformly in adaptively chosen alphabets:
    F_closed,small,j(b) << L s²/log^4Y
                     * min(1,sqrt((b+1) a^(J-2)/Y)).          (3)
Here min(1,...) follows from full shift range O_A(Y). If a^(J-2)=o(Y), choose b=floor(cY/a^(J-2)) for sufficiently small fixed c, with b<Y-3 (if J=2 use cY). On bins with s<=C0 log²Y the sum of (3) can be made arbitrarily small relative to NH. Transition weight with E_low>b is at most (3K0Y+1) G_low,all/(b+1), since the physical strict interiors do not overlap. Consequently when G_low,all=o(NH/a^(J-2)), almost all F (in the iterated fixed-c tolerance sense) must be open. More generally this is a quantitative alternative between low gain at scale NH/a^(J-2) and outside high gain at scale NH. This proof does not require the longer full-word CRT scale, and works with ANY containing alphabet (including a hypothetical larger one), not just the source support.

## 3. Stronger full-word CRT bound with a restricted interior alphabet

At the longer scale L>=Y^(J+eps1), repeat XXXI's first-occurrence CRT count for words with d distinct high labels, 2<=d<=j<=J, all in A_j. Instead of the unrestricted harmonic prime sum O(1/logY) per internal distinct label, use <=a/Y. Both endpoint choices still in source support s, one endpoint factor cancels against its matched weight (either direction). The two rough endpoint sieve is unchanged. With the same singular factor average on final offset as XXXI,
    F_closed,d,j(b) << L s²/log^4Y * (b+1)/Y
                       * (a(b+1)/Y)^(d-2) * J_loss,
where J_loss=1 for j=d if b+1>=log^12(3Y), and J_loss=(loglog(3Y))^12 otherwise. Fixed patterns and sides are absorbed. This holds also when all interior labels happen to be in the source support; no extra use of that support needed. No dependence on absolute deficit height.

Set
    b=floor(cY/a^((J-2)/(J-1))).
Since a>=log²Y and a<=O(Y), b grows at least as a fixed positive power of Y (J fixed), hence b+1>=log^12Y eventually; choose c small to satisfy b<Y-3. For d=J necessarily j=d, bound <=C c^(J-1)L on a bounded source-support bin. For d<J, the power of a in the bound is -(J-d)/(J-1), which absorbs the fixed loglog loss. Thus for ANY fixed tolerance the closed-small weight over original bins can be made smaller than that tolerance times NH. The low-tail estimate now costs
    O(Y G_low,all/(b+1))=O_c(a^((J-2)/(J-1)) G_low,all).
So under
    G_low,all=o(NH/a^((J-2)/(J-1))),
one obtains F_open >= F-o(NH) in the sense of arbitrary fixed tolerance and X->infinity (the constant in the little-o statement follows by taking the tolerance arbitrarily small; F itself is defined independently of b). Quantitative: macroscopic F with no macroscopic open gain forces G_low,all >> NH/a^((J-2)/(J-1)). For a=O(log²Y), this lower is NH/log^((2J-4)/(J-1))Y, near-macroscopic and stronger than XXXI's unrestricted internal-label polynomial lower. It concerns a different hypothesis: sparse containing alphabet, not merely sparse endpoints. Neither criterion implies a uniform bound on all high labels from the source support.

## 4. A strict conditional loss relative to height-transport saturation

For a clean asymptotic corollary assume Y->infinity, Y=X^o(1), L>=B Y^eps and L<=H, uniform alphabet bound a as above, near-minimal source support, and
    G_low,all=o(NH/a).
Then L>=Y^(J+eps1) for every FIXED J and each fixed tolerance. By choosing A,C0 large and applying the preceding bounds, after discarding an arbitrarily small fraction of original M the short distinct source-transition population is almost entirely open. More precisely the loss in F_open relative to M is at most O(NH/A) plus high-support-bin mass plus any prior bad-return mass plus arbitrary fixed counting tolerance times NH. For a population ALREADY satisfying same-label separation, choose A,C0 for each tolerance, take X large then tolerance to zero. It follows from (2) and G_all<=NH:
    [4/3+1/(3K0)] M <= G_all+o(NH),
    M <= [3K0/(4K0+1)] G_all+o(NH).                 (4)
This is strictly below the general 3/4 saturation coefficient. If using the original population before the bad-return discard, choose that discard with arbitrarily small tolerance as well and preserve weights; disjoint gain is paid within the retained population for each tolerance. If fixed polynomial Y, (2) with F_open>=F-o(NH) remains valid only for fixed A,J with the required CRT length; do not claim (4) by sending A unbounded at fixed exponent. A fixed positive F_open already gives a strict additive cost in (2). For J=2 pair scale suffices; J>=3 uses the stated longer scale or the stronger low-gain assumption of section2. The coefficient is not a strict loss in XVII's overlap inequality: M here is matched height transport, not the strengthened missing clock, and no proof that transport approaches 3/4 of total gain. Do not substitute one for the other.

## 5. Deep starting sources remove the low-reset loophole

Use STARTING matched weight on transitions whose starting source has ordinary postheight d'_s>6+E, E=actual total strict relay gain = D_gap-(p_s-1). Since each physical event decreases ordinary deficit by at most its gain, every intervening postheight is >=d'_s minus cumulative intervening gain >6. The next source preheight is also >6. Hence no intervening event is an adjusted reset, low or high. In particular the uniform depth condition d'_s>6+A Y suffices for all short transitions. This is a statement about the actual physical word, not just the endpoint consumer. The same count in sections 2-3 holds for starting weight (its prime cancels the corresponding CRT factor; the two supported endpoints are symmetric for counting). The long gap and LAST source loss for a deep starting population have the same bounds as before.

If a macroscopic population of source matched mass is deep enough for the chosen A, and low NONRESET gain satisfies the relevant smallness condition of section2 or3, the entire low relay on those words is bounded by that nonreset budget. The macro open conclusion then supplies G_out,nonreset>= (Y-1)/(3K0Y+1) F_open,deep, with no low reset assumption. This additional gain is disjoint from every selected source and consumer. No claim that deep source mass is forced: shallow sources can reach resets, and the low nonreset little-o from XXIX alone lacks the stronger rate for these sparse alphabet counts. Even without sparse consumer support, take only the source alphabet: this yields outside-source high nonreset gain (not necessarily outside consumers), and the deeper disjoint budget (2) then cannot be claimed. Distinguish these versions.

## 6. Diagnostics and next target

Run node research/min_unified_alphabet_escape_budget_audit.mjs 4096 16384 65536. Extended six actual prime-root runs and 48 finite controls of XXXI. For each bin build alphabet union of actual extracted source and consumer labels >=Y, count actual closed and open high words, exact outside high event union, check disjointness from endpoints and previous strict relay, exact gain inequality and weighted charge. Test closed shift sets under finite cutoff, and the exact deep condition d'_s>6+E, also stronger uniform d'_s>6+16Y, check every actual intermediate postheight and low/high nonreset partition, and starting-weight charge. Finite tests not claimed to realize asymptotic sparse-alphabet or near-minimal support, or long CRT; no independent Selberg proof, full cumulative kernel rerun or Lean. 
```json
{
  "controls": 48,
  "alphabetBins": 10065,
  "alphabetSize": 24219,
  "sourceGain": 806678,
  "targetGain": 540046,
  "sourceN": 12225,
  "targetN": 12599,
  "extraGain": 28242,
  "extraMass": 9006,
  "extraEvents": 540,
  "extraNonreset": 23308,
  "extraReset": 4934,
  "alphabetClosedMass": 32474,
  "alphabetClosedSmall": 17614,
  "alphabetShiftChecks": 747,
  "alphabetShifts": 747,
  "alphabetBudgetChecks": 10065,
  "deepWords": 1482,
  "deepMass": 38192,
  "deepStartMass": 45352,
  "deepEvents": 7067,
  "deepLowGain": 27048,
  "deepExtraGain": 17358,
  "deepExtraMass": 6916,
  "deepExtraStartMass": 16032,
  "deepUniformWords": 628,
  "deepUniformMass": 21970,
  "deepUniformLow": 11308,
  "deepUniformExtra": 10842,
  "extractMass": 306478,
  "G": 43258576
}
```
Main/direct unchanged. Next: force sparse combined endpoint support or prove quantitative low nonreset budget, or develop source/consumer alphabet expansion without assuming a small support. The distinction between extra nonreset gain and already paid consumer gain is now exact. Final NT overlap gap remains open.
