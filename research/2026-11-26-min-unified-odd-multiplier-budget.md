# Integration XL: odd multiplier obstruction and whole-tag baseline cost without support sparsity

2026-11-26 JST. Parent bae8cff1ab76a1c9c1fe01e6758d27ba89f51ae4. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae). The clustered short-index branch of XXXIX is still open. Here a different, support-free constraint comes from the actual departure clock, the odd shifted multiplier identity of XXXIII, and the saturation ratio of XXXV. Near-saturation requires both deep endpoint multipliers and the complementary gain needed to create their baseline from the canonical initial deficit 6. This gives a quantitative (submacroscopic) gap at ALL label scales without the source-support, low-relay, or long-bin assumptions. It does not give the final overlap gap.

## 1. Actual ordered pairs and unadjusted slack

Use original complete tagged paths, each initially d=6, actual total gain G_i<=H. Select any chronological nonoverlapping upward/downward pairs s<t<s_next on a tag. Both endpoint labels p,r>=Y>=11, not necessarily comparable or distinct; each event is actual. Let m<=min(u,v) be actual matched weight with u=2w_s-(p-1)>0, v=r-1-2w_t>0. The matched weights are not added to other transport ledgers. The pairs can be selected in bins and then ordered on the whole tag; no reset, relay length, or source support assumption is needed. Let n_i be number of retained pairs and M_i their weight sum. Suppress the tag subscript in local calculations. Let G_U,G_D be endpoint gains, G_O=G-G_U-G_D>=0 all complementary gain. Set
    A=3G_U+4n-M, D=G_D-M,
    Delta=A/3+D+G_O=G-4M/3+4n/3.
All three terms nonnegative. Moreover D>=2 sum w_t>=2n, since every physical wait is a positive integer and m<=v. Consequently the UNADJUSTED slack satisfies
    Delta0=G-4M/3=Delta-4n/3 >= A/3+D/3+G_O >= Delta/3.       (1)
In particular n<=Delta/2, M<=3G/4. This observation removes the usual O(n) subtraction from the final lower bound, even at smaller growing label scales. It relies on actual downward waits, not a relaxed zero-wait limiting model.

## 2. Odd multiplier parity obstruction

For an actual event with parity I of its departure tick, ordinary postdeficit equals 2hp+6I, with nonnegative integer h. Indeed n_depart≡I(p+2) mod2p and C=e mod p, e=1-2I; hence d'=2n_depart-(C+p-1)≡6I mod p and is even, so d'-6I divisible by 2p. Nonnegativity of ordinary d and p>=11 ensures h>=0. For a source supplying heights >6, h>=1; the argument below also works for h=0. For target use d'_t=2kr+6J, k>=0.

Let E be total actual gain of strictly intervening physical events, V their total wait. No restrictions on intermediate labels or resets. V<=3E. Subtract the two actual postdeficits to obtain EXACTLY
    2hp-(2k+1)r=c, c=E-1-2(V+w_t)+6(J-I).
Here c odd and |c|<=5E+2w_t+7. Since 2h-6k-3 is an odd nonzero integer,
    p <= (2k+1)|r-3p|+|c|.
Thus
    p/(2k+1) <= lambda=|r-3p|+5E+2w_t+7.              (2)
The obstruction is different from merely ruling out the prime identity r=3p. Even arbitrarily close prime ratios cost at least an inverse multiplier, unless intervening gain or target wait pays that cost. No sieve or rational approximation is used, and the inequality does not require p!=r. Similarly, multiplying the odd identity by 2h and comparing against r/3 gives a source-side estimate if desired; we need only the target multiplier.

From XXXV, with a=2p-w_s>=0, r-3p=v-u+2-2a+2w_t. Since m<=min(u,v), sum |u-v|<=A+D, 2sum a<=A, 2sum w_t<=D, so sum |r-3p|<=2(A+D)+2n. Strict interiors of selected pairs disjoint, sum E<=G_O. Consequently
    sum lambda <=2A+3D+5G_O+9n <=6Delta+9n <=(21/2)Delta.    (3)
All bounds hold separately on each original tag, over all bins. These are alternative uses of the SAME slack, not additive charges to earlier drift or ratio bounds.

Since m<=3p+1<=4p, (2)-(3) give
    sum m/(2k+1) <=42 Delta,
    sum m Y/(Y+d'_t) <=42 Delta.                           (4)
The second follows 1+2k<=1+d'_t/Y. Thus the actual matched mass carried by k<=K0 is at most 42(2K0+1)Delta, with the analogous bound for postheight <=D0 Y. In a sequence with M>=rho NH and Delta0=o(NH), for every fixed multiplier or normalized height bound the matched mass below it is o(NH). In particular both endpoints have deep ordinary postdeficits relative to their labels if labels are comparable, using d'_s-d'_t=r+c+6(I-J), the near-saturation ratio and the relay/target-wait slack. More generally (4) gives a quantitative inverse-height cost with no source support hypothesis.

## 3. The canonical baseline is paid for on the WHOLE tag

For the target postheight sequence, order all retained pairs on a tag, including across bin boundaries. Starting at d=6, between the initial state and the first source, between pairs, and inside pair relays, the absolute physical deficit variation is bounded by 5 times complementary gain (each event has w<=2p and |2w-g|<=5g). At completed selected pair endpoints the source rise and target fall contribute net u-v, not u+v. Thus for EVERY target postheight, and every source preheight,
    d <=6+sum |u-v|+5G_O
       <=6+A+D+5G_O <=6+5Delta.                         (5)
Each complementary event at most once in this bound; partial prefixes only reduce the nonnegative upper terms. The first source preheight also satisfies the familiar canonical prefix bound G_pre>=(d_pre-6)/5. The argument cannot be made on an arbitrary isolated bin starting at a free unknown positive deficit; (5) uses the full original tag. It applies even if retained pairs occur only in common cores, paying for the actual prefix and omitted parts in G_O. No extra entry credit is assigned.

Since r>=Y, every retained k satisfies 2k+1<=1+(6+5Delta)/Y. Combine (4),(5) on the same tag:
    M <=42 Delta (1+(6+5Delta)/Y)
      <=252 Delta(1+Delta/Y)   (Y>=11).                   (6)
In particular Delta >> min(M,sqrt(M Y)), with absolute constants (split Delta<=Y or >Y). We can sum a simpler linear-in-M form without assuming uniform tag masses. Because M<=G<=H, Y<=H, if Delta<=sqrt(HY) then (6) implies M<=504 Delta sqrt(H/Y). If Delta>sqrt(HY), then Delta>=M sqrt(Y/H). Using (1), for every tag
    G_i-4M_i/3 >= (1/1512) M_i sqrt(Y/H).
A slightly sharper constant follows directly from the first bound in (6): for Delta<=sqrt(HY), 1+6/Y+5Delta/Y <=7 sqrt(H/Y), so M<=294 Delta sqrt(H/Y), hence Delta0>=M sqrt(Y/H)/882. Constants are inessential; use the conservative 1/1512 in the theorem. Summing tags gives
    G_all-4M/3 >= (M/1512) sqrt(Y/H).
If M>=rho NH, then
    M <=3G_all/4 - (rho/2016) N sqrt(HY).                 (7)
This is an all-scale, all-support, unconditional-in-relay quantitative non-saturation theorem for the stated actual ORDERED direct pair population. It is a submacro gap when Y=o(H), as in the original regime. At Y~sqrt X and H~X/log^.25 X, its scale is N X^.75/log^.125 X. It is weaker than prior logarithmic or fixed gaps when their assumptions hold, but has none of their source-support, consumer-support, local bin length, low-relay, or arithmetic cutoff restrictions. The canonical cost cannot be replaced by a separate sum over many bins. The proof neither asserts that a macro ordered direct population is forced nor excludes the crowded short-index structure of XXXIX.

## 4. Finite diagnostics

Run node research/min_unified_odd_multiplier_budget_audit.mjs 4096 16384 65536. Standalone six actual prime-root runs and 48 finite threshold/bin controls, reusing the actual consecutive-high upward/downward pair extraction of XXXVI (no relay cutoff). For each tag, order pairs across original bins; calculate actual E,V, endpoint odd identity, ratio and inverse multiplier budget, prefix/interpair/target baseline envelope, unadjusted versus adjusted slack, whole-tag quadratic inequality and its linearized lower. The exact audit also uses M<=42 Delta(1+(6+5Delta)/Y) and a conservative numerical linear bound; these are not assumed on isolated bins. Finite checks do not establish the macro population or final overlap. No independent analytic sieve (none used in new argument), full core/kernel rerun, or Lean verification.
```json
{
  "controls": 48,
  "tagsWithPairs": 22616,
  "pairs": 29671,
  "M": 726042,
  "G": 43258576,
  "adjusted3": 126990244,
  "unadjusted3": 126871560,
  "oddChecks": 29671,
  "parityChecks": 29671,
  "ratioChecks": 29671,
  "baselineChecks": 59342,
  "shallowPairs": 17468,
  "shallowMass": 535308,
  "lambda": 4860707,
  "inverse": 404555.34815802093,
  "weightedInverse": 278813.9127669124,
  "tagQuadraticChecks": 124560,
  "prefixChecks": 22616,
  "prefixGain": 5483208,
  "interiorGain": 284028,
  "lateSlack": 2017864,
  "downSlack": 408250,
  "nonconsecutivePairs": 18756,
  "lowerNormalized": 50.75715042694594
}
```
Main/direct unchanged. Next: use the inverse multiplier budget with short-index arithmetic and actual baseline range, or revisit the original overlap-to-transport implication. No final NT-scale overlap gap.
