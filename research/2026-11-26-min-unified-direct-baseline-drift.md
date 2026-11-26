# Integration XXXIV: adaptive baseline variation and quantitative direct-transport non-saturation

2026-11-26 JST. Parent 387292fe0cb1cbe8659ab7f94149b988ed730027. Direct preflight [240e3de](https://github.com/tara-sooo/A166944-Lean/blob/240e3dea344526cac575e612ba4d538f42bd2a57/research/2026-11-26-min-direct-fast-pair-odd-shift-and-quadratic-escape.md). New: extend the odd-shift state count to adaptively partitioned actual source PRE-deficit and target POST-deficit sequences. Their variation measures the drift of the baseline between direct recovery cycles, not the large ordinary up/down variation inside each cycle. This baseline variation is bounded by unmatched height slack plus gain outside the direct endpoint sets. Thus obtain a quantitative non-saturation loss WITHOUT a sparse consumer alphabet or extra-relay alphabet escape. It is a submacroscopic loss, on the conditional direct-pair population, not the final overlap gap.

## 1. Direct latest transfer and notation

Retain XXXIII's actual consecutive high first pairs (source upward, target downward, only p<Y between them), labels p,r in [Y,KY], Y->infinity, fixed K. Original tag bins of prehorizon length L with B Y^epsilon<=L<=H, epsilon>0 fixed, full canonical paths start d=6 and total gain<=NH. Pair endpoints within same original bin. Use only one actual disjoint pair per source. Let E<=b, target wait w<=W, Q=5b+2W+7<Y, b=o(log²Y) in XXXIII, W=ceil(Y^alpha), alpha fixed positive <1. Actual odd shift 2hp-(2k+1)r=c, |c|<=Q, p!=r. Pair weights at most O(Y); we distinguish original source weights used in counting from direct matched weights m<=actual causal overlap. For the budget below use DIRECT matched weights only, no addition of the earlier XXIX mass.

Direct 240e3de proves global nearly quadratic escape and source/target diameter. On an original local bin XXXIII's state bound has prefactor Y(1+L/Y²), not H/Y uniformly. Put sigma=min(epsilon,1). If L>=c Y², the previous argument gives for every fixed delta in (0,1), choosing alpha<delta, all but o(NH) original mass has BOTH postdeficits >Y^(2-delta) (use h,k caps O(Y^(1-delta))). For smaller L the corresponding cap is Y^(1+sigma-delta) for 0<delta<sigma, alpha<delta. Individual predeficits differ by O(Y), so same lower order up to factor 1/2. These deductions apply to any macro subpopulation of fast first pairs with the same aggregate local source support O((NH/L)log²Y). At polynomial Y>=X^a, a>0 fixed, the divisor cap b_H=max(1,floor(log(C H+C B)/logY))=O_a(1). Direct's observation also gives the TARGET diameter without a target support assumption: each corresponding postheight differs from the source postheight by O_K(Y+Q), hence the two ranges differ by at most O_K(Y+Q). This corrects the limitation stated in XXXIII section5 about target range. The following argument is stronger than simply summing one range per original bin.

## 2. Adaptive variation bound for arbitrary baseline

For one original bin, order any retained actual disjoint fast pairs by source prehorizon. Let s_j be its number of distinct source primes, F_j total weight (either original or actual direct), and define three sequences of heights along the ordered pairs:
    x_i=d_source,pre ; y_i=d_target,post ; z_i=d_source,post.
For any one of these sequences let V_j=sum consecutive absolute differences (no entry cost). All are ordinary deficits, not adjusted multipliers. From actual bounded endpoint gains and clocks, |z_i-x_i|<=3KY+1, |z_i-y_i|<=KY+Q+6. These offsets are O(Y), so any contiguous sublist in which the chosen baseline sequence lies in an interval of width Y has source postheight range O_K(Y). For each fixed p there are O_K(1) possible actual multipliers h there, even at arbitrary baseline height, by the two progressions 2hp+6I.

Partition the ordered list greedily: start a new sublist when adding the next consecutive absolute baseline difference would make accumulated variation exceed Y. The edge crossing each cut is NOT included in the new sublist; it is charged together with the accumulated variation of the old one. These disjoint charged edge sets cost >Y each, so at most 1+V_j/Y sublists. Each sublist has range<=Y. The source prehorizon spans ell_i of the sublists are disjoint except endpoints, sum ell_i<=L. In each sublist use the exact local odd-shift state capacity of XXXIII with at most O_K(s_j) states, actual span ell_i (including singleton span 0), divisor cap b_H, not full L. For fixed p,h,c,E,I,J, at most b_H candidates r and at most 1+ell_i/(pr) actual starting horizons. Thus
    F_j <<_K b_H (b+1)(Q+1) s_j [Y+V_j+L/Y].           (1)
This is valid separately for each of the three baselines, so use their minimum variation. More precisely keep distinct actual source label counts in each sublist and sum s_sub*(Y+ell_sub/Y). No sieve error on short sublists; no repeat of full-bin span per sublist. No consumer label count or source absolute height cap. The bound counts necessary actual candidates even when many source states recur.

Suppose polynomial Y>=X^a, aggregate source support <=C0(NH/L)log²Y, total direct mass M>=rho NH, and b+1=O(log²Y), W=ceil(Y^alpha) with 0<alpha<sigma. Every bin's direct mass O(L+KY)=O(L) since source weight <=3p+1 and monotone source horizons. Discard bins with s_j>C1 log²Y for sufficiently large fixed C1, using Markov, losing <=rho NH/2. Count (1) on the retained bins: total Y+L/Y terms over O(NH/L) bins is O(NH(Y/L+1/Y)); multiplied by O(Y^alpha log^4Y) it is o(NH) since Y/L<=Y^-epsilon. Therefore each of the three variations separately obeys
    sum_j V_j >>_(rho,a,K,C0,epsilon,alpha) NH/(Y^alpha log^4Y).      (2)
This holds even if L is much larger than Y², unlike the single diameter estimate which gives only (NH/L)Y^(2-delta). In particular the ending-label-weighted consecutive variation of the SOURCE list (or target list), at labels>=Y, is >> NH Y^(1-alpha)/log^4Y, so bounded weighted selected-post variation is incompatible with this conditional macro regime. These are actual consecutive selected-list differences; no unweighted physical total variation bound inferred in reverse. A bound with b_H retained works at subpolynomial labels whenever b_H(b+1)(Q+1) log²Y (Y/L+1/Y)=o(1). For a fixed power cutoff alpha chosen arbitrarily small the lower is NH/Y^delta for every fixed delta>0 with alpha<min(delta,sigma). Such a statement quantifies a family of retained populations (cutoffs depend on delta), not a single uniform limiting exponent.

## 3. Baseline drift paid by unused transport resources

For actual direct pairs let u_i=d'_s-d_s>0, v_i=d_t-d'_t>0, m_i<=min(u_i,v_i) actual matched mass (no reuse). Set M=sum m_i, G_U=sum source gain, G_D=sum target gain, G_O=G_all-G_U-G_D>=0, n_pairs=#pairs. All gains on original tags; each endpoint appears once. Then
    sum |u_i-v_i| <= sum(u_i+v_i-2m_i)
                   <=3G_U+4 n_pairs+G_D-2M.
For two consecutive retained pairs on a tag in one bin, source PRE-deficit difference equals u_i-v_i plus actual changes of all nonendpoint events between the two source pre-states. Those intervening changes have absolute sum <=5 times their actual gain. Similarly target POST-deficit difference between consecutive pairs equals u_(i+1)-v_(i+1) plus actual complementary changes, including low relays. In either ledger the charged complementary intervals and pair mismatches do not overlap within a tag, even for arbitrary omitted pairs. Summing across disjoint original bins and tags:
    max(V_pre,V_target) <= sum |u_i-v_i| +5G_O.           (3)
The two variations are NOT added as two independent costs. Define nonnegative adjusted saturation slack
    Delta = G_all - (4/3)M + (4/3)n_pairs
          = (G_U+4n_pairs/3-M/3)+(G_D-M)+G_O.
Each bracket nonnegative because u_i<=3g_s+4, v_i<=g_t. Hence RHS of (3) <=5 Delta, exactly. In particular
    G_all-(4/3)M >= max(V_pre,V_target)/5 -4n_pairs/3.  (4)
This works on the entire original full lifetime; no extra initial deficit credit, no need for near-minimal support of consumers, no need for an outside-label relay. Pre-to-pre and target-post-to-post are important: source-post-to-source-post can include changes of the sizes of otherwise perfectly balanced cycles, so its variation is not charged by (3). The adaptive count (1) applies directly to the two correct baselines.

Combine (2)-(4), n_pairs<=NH/(Y-1) by distinct source gains. For polynomial Y, macro actual direct transport and the assumptions of (2),
    G_all-(4/3)M >> NH/(Y^alpha log^4Y).                 (5)
Equivalently M <=(3/4)G_all - c NH/(Y^alpha log^4Y) for some fixed c>0. This is a quantitative gap below 3/4 on the conditional fast direct population, even when consumer support is arbitrarily large. Unlike XXXII's constant loss, (5) is submacroscopic, but it does not require a sparse combined alphabet or an open-relay event. It excludes a saturation error O(NH/Y^delta) for delta>alpha (within the stated family). When deriving a new direct matched population from XXXIII, (5) concerns THAT new M; one must not infer it for the discarded original cross mass. In particular no contradiction follows merely from original M being macroscopic rather than near saturation.

## 4. Canonical precursor and reset-free region

If the first retained source in a tag has preheight d_pre>=D_* (e.g. from section1, D_* a fixed fraction of Y^(1+sigma-delta)), actual prefix before this event has gain >=(D_*-6)/5 and wait >=(D_*-6)/2. This follows from canonical initial d=6 and 2W_pre=G_pre+d_pre-6. Prefix contains no endpoint of any retained direct pair on that tag; its actual gain is already in G_O, not an extra independent charge. If every retained source is deep and M macro, there are Omega(N) tags with such a prefix and thus G_O>> N D_*. A source postheight >6+A Y also excludes every reset in a short relay of gain <=A Y as XXXII. At L>=c Y² near the top label scale D_* can approach Y² in the power sense, but neither (5) nor the prefix cost yields a fixed positive fraction of NH. If first large occurs before this prefix ends, its gain need not be missing clock. No substitution of the saturation slack for XVII overlap loss.

## 5. Diagnostics

Run node research/min_unified_direct_baseline_drift_audit.mjs 4096 16384 65536. Extend XXXIII actual six prime-root runs and 48 controls. Use positive actual newly matched first-pair mass, not old cross mass. Within each original tag-bin verify endpoint disjointness, unmatched rise and fall slack, actual baseline drift upper on source pre and target post, adjusted saturation identity, greedy adaptive partitions of all three sequences, disjoint span ledger, actual source-state ranges and CRT tuple capacities on the adaptive sublists, canonical prefix identity. Finite controls not assumed to satisfy asymptotic support, low-relay or polynomial fast cutoffs; no independent sieve proof or Lean. Main/direct unchanged.
```json
{
  "controls": 48,
  "baseBins": 2657,
  "basePairs": 2771,
  "baseMass": 59894,
  "baseSourceGain": 139550,
  "baseTargetGain": 77376,
  "baseOtherGain": 1322424,
  "baseGap3": 4389558,
  "baseRiseSlack": 169794,
  "baseDownSlack": 7572,
  "baseMismatch": 172418,
  "basePreV": 17290,
  "baseTargetV": 22690,
  "baseSourcePostV": 23244,
  "basePartitionChecks": 7971,
  "baseSegments": 8273,
  "baseSegmentStates": 8313,
  "baseSpan": 3972,
  "baseLocalCapacity": 3477181527.0588236,
  "baseCoarseCapacity": 49608802244.13072,
  "baseTupleChecks": 8313,
  "basePrefixGain": 846002,
  "basePrefixWait": 749162,
  "basePrefixChecks": 2657
}
```
Next: force quantitative near-saturation or extract a macro loss by combining drift with stronger arithmetic bounds; or revisit macro missing/high support. No final NT gap.
