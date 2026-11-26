# Integration XXXI: two-rough-endpoint high-word sieve and polynomial low-relay cost

2026-11-26 JST. Parent 2b7fa7d8083ff8798756215e1fe3c242ea33bd19; direct preflight [568cfa4](https://github.com/tara-sooo/A166944-Lean/blob/568cfa484c91708e7e9196731f7a8566b9deda52/research/2026-11-26-min-direct-bounded-word-crt-and-repeat-supply.md). New: apply the direct first-occurrence word CRT to XXX's consecutive actual extracted UPWARD sources (both endpoints rough, both labels in a near-minimal local support). A uniform short-shift singular-factor average removes the loglog loss on all-distinct words, yielding a polynomial rather than logarithmic low-relay cost at sufficiently low label scales. Also separate words by their actual number of distinct high labels. Not a general bound at medium or top scales.

## 1. Exact disjoint physical relays and hypotheses

Use XXX's actual original tag-bins of length L, with L>=B Y^epsilon, L<=H, comparable upward source labels in [Y,K0 Y], Y->infinity. Suppose near-minimal original matched support and macroscopic extracted cross weight as in XXX. Retain the same good separated sources; choose fixed A large to obtain macroscopic total ending-source weight F>=rho NH on consecutive distinct-label source pairs with prehorizon difference D<=AY. In each such actual pair include EVERY intervening physical event with label >=Y, even if unselected or not upward. Thus the high word has j events p_0,...,p_(j-1), endpoints are actual upward sources, distinct endpoint labels, intermediate high labels <=AY+1, j<=1+floor(AY/(Y-1)). Choose a fixed integer J>=2 bounding j (e.g. 2A+2). All low intervening labels <Y, and their total actual gain is E_low. Consecutive selected source relays have disjoint strict interiors on each tag, even though successive words share an endpoint source. Endpoint weights are counted once (ending-source weight <=3p_(j-1)+1=O(Y)). Consequently sum E_low over words <=G_low,all (all original actual low gain including resets). A cost on nonreset low gain alone is NOT sufficient without an additional bound on low reset gain.

For the new count assume L>=Y^(J+epsilon1) for fixed epsilon1>0. More precisely a class with d distinct labels requires only L>=Y^(d+epsilon1); constants from fixed A,K0,J absorbed. This is stronger than XXX's pair-scale condition, feasible at small polynomial Y, not automatic. E.g. choose L=X^.7 and Y=X^delta with delta<.7/(J+epsilon1) and delta epsilon<.2. As before discard bins with too many actual source labels: aggregate support implies one may retain a macroscopic population on bins with s=|S|<=C0 log²Y for sufficiently large fixed C0. Here S contains BOTH endpoint labels, but need not contain ANY internal labels. On a retained bin total source weight O(L+Y)=O(L), since comparable actual source gains and prehorizon span. No per-fragment initial credit. We work with arbitrary actual subsets of the short pairs, and each word is counted on its original tag (not multiplied by an inferred cohort).

## 2. First-occurrence CRT with two supported rough endpoints

Fix integer b>=0, b<Y-3, restrict E_low<=b. Follow direct 568cfa4: write cumulative low offsets E_i (E_0=0, 0<=E_i<=b), A_i=sum_{k<i}(p_k-1), C_i=C_0+A_i+E_i. Each horizon requires C_0=e_i-A_i-E_i mod p_i. At the FIRST appearance of each of d distinct labels, choose its offset, giving at most (b+1)^(d-1) choices. Once fixed, CRT gives a single class mod Q=product distinct labels. Every repeated label's offset then uniquely determined in [0,b] by its residue mod p_i>=Y. This determines the endpoint shift D as well. If an assignment is impossible, discard. No extra choices of repeat offsets. A fixed start and high word length determine at most one actual word. Equality patterns, sides and word lengths cost constants depending on J.

BOTH endpoints upward, so C_0+-1,C_0+D+-1 avoid all odd f<(Y-1)/4. On the Q progression their coefficients are invertible for small primes f<Y; for f>4 generic four distinct residues unless f|D(D²-4), D>=Y-1. Use same four-form translated Selberg bound as XXX, with padded parameter length ceil(L/Q)+2 and cutoff min(Y,L/Q)^(1/12). L>=Y^(d+epsilon1), Q<=O_(A,K0,J)(Y^d), so the count at fixed tuple is
    << L J(D)/(Q log^4Y),
where J(D)=J4(D) J4(D-2) J4(D+2), J4(n)=prod_(prime f>4 dividing n)(1-4/f)^(-1).
No roughness at internal events assumed. The bound counts necessary candidates on the actual start interval, not fictitious trajectories. Every word weighted by ending extracted mass <=3r+1 with r=p_(j-1). In summing labels r cancels its own factor in Q. Source p_0 reciprocal sum <=s/Y; endpoint r has <=s choices; remaining d-2 internal distinct labels have harmonic sum O_(A,K0)(1/log Y) each by Chebyshev. Endpoint labels distinct is essential for the cancellation. This is an improvement over treating the final label as unrestricted and using only the first endpoint's roughness, as in direct's general source-to-downward words.

## 3. Average singular factors on a polynomial-length offset interval

For any fixed integer q>=1, write J4(n)^q=sum_{m|n} a_q(m) with nonnegative squarefree coefficients, a_q(f)=O_q(1/f). For any interval I of length h in [1,C Y] (fixed C) we have
    sum_{n in I} J4(n)^q <= h sum_m a_q(m)/m + sum_{m<=CY} a_q(m)
                         <<_q h + (log(3Y))^(4q).
The last sum is bounded by the product over primes f<=CY of (1+a_q(f)); log product=4q sum 1/f+O_q(1), using the standard Mertens prime reciprocal estimate. This is a uniform translated-interval bound, not just a mean over all shifts. By Hölder with q=3,
    sum_{D in I} J(D) << h + (log(3Y))^12
for I inside [Y-1,AY] and large Y (extend or truncate shifted intervals; D-2>0). In particular if b+1 >= (log(3Y))^12, the singular factor summed over a final offset interval of length <=b+1 is O(b+1), uniformly in all other labels and offsets. If all high labels are distinct, the final offset is free, with D=A_(j-1)+E_(j-1). The subset of admissible offsets is contained in this interval, so positivity gives the bound even for adaptive choice of actual words. More generally it works whenever the ending label first appears at the final event and does not affect earlier offsets. For repeated ending label retain the elementary worst bound J(D)<< (loglog(3Y))^12 (each nonzero argument O(Y)); a sharper exponent is possible by using the union singular factor but not needed.

Let F_{d,j}(b) denote actual ending weight per original tag-bin with j high events, d distinct labels. For all-distinct j=d, and b+1>=log^12(3Y), the previous section and this averaging give
    F_{d,d}(b) << L s²/(Y log^4Y) * (b+1)^(d-1)/log^(d-2)Y.       (1)
For general d<=j<=J the same estimate multiplied by (loglog(3Y))^12 follows without final-offset averaging. If d=2 then the high labels are JUST the endpoints, so there is an alternative sharper pair-shift bound from XXX: at fixed ordered endpoint pair and bounded j, possible D from bounded integer multiplicities and E_low<=b are O_J(b+1). Thus total per bin
    F_{2,*}(b) << L s²/log^4Y * sqrt((b+1)/Y),                 (2)
valid already under L>=P²Y^epsilon1, using the original pair count. This includes repeated words with both endpoint labels; adjacent equal high labels impossible under b<Y-3 but no need to assume every word all-distinct. The all-distinct two-event case may instead use (1). Neither count assumes that roughness is independent across actual rays. For b<log^12 Y retain the general worst bound rather than falsely averaging on a tiny interval.

## 4. Polynomial low-gain cost under bounded local support

Take s<=C0 log²Y. For all words j<=J in the retained macroscopic collection choose
    b=floor(c [Y (log Y)^(J-2)]^(1/(J-1)))
with a small fixed c>0. For J>=3, b=o(Y), b>>log^12Y, and for d=J necessarily j=d. By (1) this class has weight <=C c^(J-1) L per bin (for large Y). For every d<J the general worst bound is o(L), since (b+1)^(d-1)/Y has a strict negative power of Y, which absorbs all log factors. For J=2 choose c small enough that b<Y-3 and apply (1) directly. In either case choosing c sufficiently small and summing O(NH/L) actual bins, the entire small-low-relay class carries at most rho NH/2. Thus the remaining words with E_low>b carry >=rho NH/2, and by their disjoint strict interiors and ending weight <=O(Y),
    G_low,all >= c' (NH/Y) [Y (log Y)^(J-2)]^(1/(J-1)).         (3)
Equivalently for J>=3 the lower is of order NH*(log Y/Y)^((J-2)/(J-1)), with constants depending on rho,J,A,C0,epsilon1. J=2 forces MACROSCOPIC low gain. This is a polynomial-scale improvement over direct's logarithmic source-diversity/low-relay obstruction under the ADDED two-upward supported endpoint and long enough CRT hypotheses. It is not a macro lower for J>=3. In particular it remains consistent with G_low,all=o(NH), and more so with merely small nonreset low gain (resets could supply the low budget).

A stratified form: for a subcollection with at most d0 distinct high labels (even if j>d0), d0>=3, use worst bound uniformly at its largest d and choose b of order
    [Y log^(d0-2)Y/(loglog(3Y))^12]^(1/(d0-1)).
Macroscopic weight then forces G_low,all>> NH b/Y at only L>=Y^(d0+epsilon1). If the maximal-d0 class is all-distinct or has final label first appearing at end, remove the loglog denominator by (1)'s averaging. For d0=2 use (2) with b=cY and get macro low gain, regardless of repeats. This gives a useful alternative at XXX's two-label CRT scale without requiring full J-distinct long progression: if total low gain is o(NH), the macro short source-transition weight cannot be carried by words using only their two endpoint labels, even if they repeat. It requires a third actual high label on a macroscopic population, not merely two intervening events. Such words contain a high interior event of gain>=Y-1, disjoint across relays; since ending weights O(Y), they require macro actual interior high gain (not necessarily outside source support). If the third label lies in the source support it still counts as interior gain, not an extra extracted endpoint weight. No claim of a macro outside-alphabet gain unless the actual interior label is outside the support.

## 5. Diagnostics

Run node research/min_unified_two_rough_word_relay_audit.mjs 4096 16384 65536. Extend XXX actual six prime-root runs and 48 finite controls. Construct actual full high words between consecutive extracted upward sources, with all actual intervening high events and low relays, finite A16, b=min(Y-4,ceil(sqrt(Y) logY)). Check length, exact cumulative offsets, repeated-label unique offset and linear relation, BigInt first-appearance product CRT, necessary finite four-form rough candidates and exact actual weighted tuple capacities. Check strict interior low-gain budget, reset/nonreset partition, closed/open support and two-event/multi-event partition. These are finite conditions, not proof of the asymptotic long-CRT or near-minimal assumptions, nor independent Selberg verification. No full cumulative kernel or Lean. Main/direct unchanged.
```json
{
  "controls": 48,
  "wordCount": 1697,
  "wordMass": 41480,
  "wordLow": 40502,
  "wordLowNonreset": 40010,
  "wordLowReset": 492,
  "wordTail": 21380,
  "wordSmall": 807,
  "wordSmallMass": 20100,
  "wordRepeats": 0,
  "wordDistinct": 807,
  "wordFirstOffsets": 1868,
  "wordRepeatOffsets": 0,
  "wordRepeatRelation": 0,
  "wordCRT": 807,
  "wordTuples": 807,
  "wordCap": 135692,
  "wordRootChecks": 550,
  "wordClosed": 13616,
  "wordOpen": 6484,
  "wordTwo": 16292,
  "wordMany": 25188,
  "maxHigh": 7,
  "maxDistinct": 6
}
```
Next: strengthen the stratified count for three or more distinct labels without the full product-scale condition, or use the disjoint interior high gain together with the source-consumer transport to obtain an actual strict budget deficit. Macro missing, high-support, broad-guard and reset-dominated branches remain open.
