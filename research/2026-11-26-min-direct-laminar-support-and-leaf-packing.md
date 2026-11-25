# Laminar support repeats, resonance distance, and varying-support leaf packing

Continuation of [8ad273f](https://github.com/tara-sooo/A166944-Lean/blob/8ad273f39d01c792926c9cfeabcfe9f2e481fc5c/research/2026-11-26-min-direct-event-discovery-and-log-scale-recovery.md) on the independent direct-arithmetic branch. The previous whole-word repetition intervals could overlap across patterns; the present argument uses a particular laminar family of individual label returns and disjoint minimal intervals. It gives an outside-gain budget even when the distinguished finite support changes from block to block, and a CRT supply bound on low-outside-gain minimal returns. It works in the relaxed horizon graph, hence for every actual adaptive path; no independence, clock competition or source ensemble needed. Paper deductions and finite diagnostics, not Lean verification or an external novelty claim. Twin infinitude remains open.

## 1. A laminar forest of visible repeats

Consider a finite contiguous event block with even horizons H, selected odd primes a, signs e in {-1,+1}, H=e mod a and H'=H+a-1. Fix a set F={p_1<...<p_k} of distinguished odd primes; all other events are called outside. Let B be the total gain of the outside events in this block, and K the number of F-events. Keep only the F-labels in their chronological order, but retain actual horizons and intervening outside gains.

A visible repeat of p is the interval [i,j) between two consecutive occurrences of p in this projected word, with no label greater than p in its interior. It includes the first p event and excludes the second, also in the physical event interval. The repeat intervals are laminar: if two intervals crossed i<u<j<v, their respective endpoint labels p,q would satisfy q<p from the first interval and p<q from the second. Identical endpoint labels cannot cross since the occurrences are consecutive. Intervals sharing just an endpoint are disjoint in the half-open convention. Properly nested intervals have strictly decreasing endpoint labels as one goes inward. The forest of visible repeats therefore has depth <=k, and its leaves (minimal visible repeats) have disjoint physical event intervals.

A word on at most r distinct ordered labels with no visible repeat has length <=2^r-1. More precisely its i-th smallest label occurs at most 2^(r-i) times (1-based). Proof: the largest label occurs at most once, otherwise a consecutive pair is visible. Split at that occurrence and induct, also allowing the largest label to be absent. For a leaf with endpoint label p_r, every interior high label is <p_r, and the interior word contains no visible repeat of its own (otherwise that is a nested interval in the original projected word). Its counts m_i for i<r satisfy
    0<=m_i<=2^(r-1-i),     sum m_i<=2^(r-1)-1.                       (1)
These are upper bounds, not a claim every such vector is realizable.

For a leaf let E be the total outside gain between its endpoints. Since H_j-H_i=(p_r-1)+sum_{i<r}m_i(p_i-1)+E and both endpoint horizons are signed residues modulo p_r,
    E = eps-(p_r-1)-sum_{i<r}m_i(p_i-1) mod p_r,
    E even, E>=0, eps=e_end-e_start in {-2,0,2}.                     (2)
In particular for any leaf the least nonnegative even representative of the residue is <=E.

Define delta_r(F) as the minimum of that representative in {0,2,...,2p_r-2}, over eps and all count vectors in (1). Define delta(F)=min_r delta_r(F). These finite arithmetic distances can be computed with k fixed; overcounting interior vectors or endpoint signs only makes the lower bound on E weaker. The term "resonance" below refers to these explicit affine congruences, not a new probabilistic assumption.

## 2. Disjoint outside-gain theorem

Write n_r for the number of p_r occurrences and v_r for its number of visible repeats. Each consecutive p_r interval not visible contains a higher label; such intervals for one fixed p_r are disjoint, hence
    n_r<=1+v_r+sum_{s>r}n_s.
Descending substitution yields
    K<=2^k-1+sum_r 2^(r-1)*v_r.                                    (3)
For every node in the visible-repeat forest assign its weight 2^(r-1) to one of its descendant leaves, e.g. the leftmost. For any one leaf the nodes assigned to it belong to its ancestor chain, which has distinct ranks; the total assigned weight is <=2^k-1. Thus, with L_leaf the number of leaves,
    sum_r 2^(r-1)*v_r <=(2^k-1)*L_leaf.
Since leaf physical intervals are disjoint, their outside gains sum to at most B. In particular if delta(F)>0,
    K <= (2^k-1)*(1+B/delta(F)).                                   (4)
If delta(F)=0, let L_0 be the number of leaves whose endpoint rank has delta_r=0; delta_+=min{delta_r:delta_r>0}, if this set is nonempty. Then
    K <= (2^k-1)*(1+L_0+B/delta_+).                                 (5)
If no rank has positive distance, use the preceding L_leaf bound directly. These statements do not charge a nested repeat twice and do not require the outside labels to be small. They are not a bound on an arbitrary collection of overlapping externally chosen blocks.

Explicit cases:
* For p>=5, delta_1=p-1; for p=3, delta_1=0 (two consecutive 3 events are possible). Empty interior vectors have these same distances for the anchor prime.
* For F={p,q}, 5<=p<q, delta_1=p-1, delta_2=q-p. For q a leaf anchor, the interior contains at most one p; with one p the three least even residues give q-p,q-p+2,q-p+4, with none the minimum is q-1. More precisely q leaf weight at most2, p leaf at most3 (including a possible q ancestor). This proves
    K <= 3+B*max(3/(p-1),2/(q-p)).                                 (6)
For p=3, delta_2=q-3 still holds but (6) cannot divide by a positive p-distance.
* Suppose k>=2, 5<=T<=p_1<=p_k<=T+Delta, and
    2^(k-1)*(Delta+1)+2<T.
Let g_min be the minimum gap of the ordered F. For any vector at anchor p, put m=1+sum m_i and D=1+sum m_i(p-p_i+1). The high gain is mp-D, and D+2<p. Thus E-D=eps mod p implies E=D+eps+zp with z>=0 (since E>=0 and D+2<p). When m>=2, D>=1+(g_min+1)(m-1), so E>=g_min. When m=1, the empty vector gives E>=p-1>=g_min under the narrow-band condition. Therefore delta(F)>=g_min and
    K <=(2^k-1)*(1+B/g_min).                                       (7)
In particular a path with no outsiders on a sufficiently narrow k-prime set has at most 2^k-1 events, a more explicit bound than the general recursive finite-support theorem. No short-block-length assumption is used here, since the leaves already have bounded interior length.

## 3. Rare near-resonant supports

Fix integer k>=2 and constant C>1. All distinguished primes are in [T,CT], T>=5. Let 0<=U<T-1. The number of k-prime supports F with delta(F)<=U is
    O_{k,C}((U+1)*(T/log T)^(k-1)).                                 (8)
For a witness to delta<=U, the interior vector is nonempty, because the empty-vector distance is p-1>=T-1. Choose its endpoint rank, count vector, eps and E<=U, and a nonzero interior coefficient. These are O_k(U+1) possibilities. Equation (2) is the exact linear equation
    (p-1)+sum m_i(p_i-1)+E-eps = z*p                               (9)
for a bounded nonnegative integer z=O_{k,C}(1), since the high word length is bounded in (1). Choose all primes except the one with nonzero interior coefficient. The omitted prime has at most one possible value. There are O_C(T/log T) primes in the interval by the usual unconditional prime upper bound. This proves (8), without estimating the probability that the omitted integer is prime. In particular for U=T/(log T)^(k+2), the proportion among all k-prime supports is O_{k,C}(1/(log T)^2), by PNT for the denominator. This is a statement about sets of primes; an actual trajectory need not sample those sets uniformly. It does not by itself bound how frequently a resonant support is used.

## 4. Small-leaf CRT supply, even with varying supports

Now let an actual path, or any relaxed horizon path, have a collection of pairwise disjoint contiguous event blocks within a common horizon interval [A,A+G] for their pre-horizons. For each block independently choose a distinguished support F_j of at most k primes in [T,CT], possibly based on the actual path. No restriction on other labels. Construct its forest as in section1. This is not a union of arbitrary overlapping blocks. Let B_tot be the sum of outside gains in the chosen blocks, K_tot the sum of distinguished-event counts, L the number of nonempty distinguished blocks. Classify leaves by their actual outside gain E: small if E<=U, otherwise large, with 0<=U<T-1. Since E is even, each large leaf consumes at least U^+=2*(floor(U/2)+1). Their physical intervals are disjoint across and within all blocks.

A small leaf uses exactly l distinct distinguished primes, 2<=l<=k: the repeated endpoint p>=T, the empty interior would require E>=p-1, impossible. The inner word has no visible repeats on its actual l-1 labels, so the number m of distinguished events before the second endpoint is l<=m<=2^(l-1). All interior labels <p. Encode only:
* the word of label indices (anchor p at both ends, all l-1 smaller labels used) and its m+1 signs;
* the ordered vector of m intervening outside gains E_i>=0 even, sum E<=U (not the outside labels, event counts or waits);
* l-1 of the l prime values, omitting a smaller label with positive count, and the integer z in (9).

The missing prime is determined uniquely by (9), and the gain vector determines the relative horizons of every distinguished event, including the final repeat. Their selected-label divisibility conditions fix the starting horizon in one CRT class modulo 2*prod of the l primes. There is no time or deficit factor: even in a relaxed path, each event pre-horizon on a fixed path is unique. Any inconsistent data are simply rejected. Let n_T=#primes in [T,CT] and Z_m=ceil(m*C+(U+2)/T). A finite upper bound for the number of small leaves on the disjoint blocks is
    A_k(G,T,U)=sum_{l=2..k} (1+floor(G/(2T^l)))*n_T^(l-1)
      * sum_{m=l..2^(l-1)} (l-1)^(m-1)*2^(m+1)*(Z_m+1)
                                    *binom(floor(U/2)+m,m).         (10)
The shape is counted by (l-1)^(m-1), sign choices by 2^(m+1), the gain vectors by stars-and-bars, and the bounded quotient by Z_m+1. For U=0 omit l=2 as well by the two-label formula. The start count is over code-horizon pairs; on one ray the small leaves have distinct starts, so no root multiplicity factor appears. The estimate is uniform over all varying choices of the disjoint blocks and F_j.

Equivalently, using the prime upper bound for fixed k,C,
    A_k <= O_{k,C}( sum_{l=2..k} (U+1)^(2^(l-1))
                       *[(T/log T)^(l-1)+G/(T*(log T)^(l-1))] ).   (11)
For U=0 the sum begins at l=3 (empty if k=2), giving
    A_k(G,T,0) <= O_{k,C}(G/(T*(log T)^2)+(T/log T)^(k-1))          (12)
for k>=3. This uses fewer than k labels if the actual leaf does not use its whole block support; padding it to k would give the wrong CRT denominator.

Combine (3), the forest weight assignment, (10), and the disjoint large-leaf charge. The main varying-support estimate is
    K_tot <= (2^k-1)*( L + A_k(G,T,U) + B_tot/U^+ ).                (13)
It includes all intervals from the chosen blocks, with no summation over overlapping repeat windows and no assumption delta(F_j)>0. In particular, even when each block has a resonant support, small actual outside gain forces a rare affine relation with a CRT spacing cost. This extends the previous repeated-identical-word estimates in a different way: the leaf word and even its outside-gain vector may vary, and arbitrary new support choices are allowed between disjoint blocks.

## 5. Consequences and limitations at the scale of the previous A1 analysis

Take fixed k>=2,C>1, T tending to infinity, T^k=O(G), and U=floor((log T)^eta) with
    0<eta<(k-1)/2^(k-1).
For l=2..k the exponent eta*2^(l-1)-(l-1) is strictly negative, since (l-1)/2^(l-1) is nonincreasing for l>=2. The two terms of (11), normalized by G/T, are bounded by those negative log powers (the first also has T^l/G=O(1)). Hence
    A_k(G,T,U)=o(G/T).
If K_tot>=c G/T with fixed c>0, and L=o(G/T), (13) requires
    B_tot >= (c/(2^k-1)-o(1))*U^+*G/T.                             (14)
In particular B_tot/(G/T) grows at least as a positive power of log T. This is a genuine superconstant outside-gain requirement per distinguished event, not just per fixed repeated word. Applies when T is comparable to log X and G comparable to X, as in the previous absolute-scale obstruction, or at polynomial scales satisfying T^k=O(G). It does NOT require B_tot to be a positive fraction of G; the right-hand side can be o(G).

A more specific conditional comparison: take G=Theta(X), T=Theta(X^(2/11)), 3<=k<=5. Equation (12) is then
    A_k(G,T,0)=O(X^(9/11)/(log X)^2 + X^(2(k-1)/11)/(log X)^(k-1))
              =o(X^(9/11)/log X).
Thus if a population of Omega(X^(9/11)/log X) events at this scale were covered by disjoint blocks on <=k distinguished primes with NO outside events and with L=o(X^(9/11)/log X), (13) would exclude it. This is a precise conditional exclusion for a narrow clustered population, not a derivation of the needed cover. The previous dyadic-band A1 lower bound does not force this scale, a bounded total support per cluster, or a negligible number of clusters. Moreover its precursors can have labels much smaller than their associated marks. On the log scale, even (12) can exceed the previous X^(9/11) lower count. Neither the sparse assumptions on canonical visits/high B nor these cluster assumptions follow from finite twins. No contradiction with that hypothesis. The previous X^(1-o(1)) log-scale two-recovery-label start construction is compatible with (13), since its distinct roots need not share one ray and its finite word has no repeated-label leaf.

Next directions: (i) derive disjoint block covers in which many recovery events are retained in a bounded-size comparable band and outside gain is small enough for (13); (ii) replace the fixed k assumption with variable-support entropy bounds and sharpen low-gain code enumeration (the gain vectors are compressed but still counted crudely); (iii) exploit further actual first-hit clock/deficit restrictions to cut down the resonant leaf codes, beyond the relaxed horizon relation. The key remaining problem is matching an upper population to the existing recovery lower population, including the nonsparse canonical/far-B branches.

## 6. Diagnostics and persistence

[Laminar audit 24b9e6e](https://github.com/tara-sooo/A166944-Lean/blob/24b9e6e9678e15efa7133f1cf48e88915f46e301/research/min_direct_laminar_support_resonance_audit.mjs), blob befd45fea63f48556987b11a3022abbf0887b7d3, exact remote readback. Run node research/min_direct_laminar_support_resonance_audit.mjs 12000. Actual ECMAScript executed in tool runtime (not a separate Node process). 5998 odd canonical roots through12000,87242 selected events (none unresolved at180 cap),12986 independent literal gcd ticks,11710 nonempty relaxed random paths. 33884 block/support controls,324920 distinguished event incidences,331868 outside event incidences;97490 visible intervals,36094 nested interval incidences,73312 leaves incl 17990 positive-distance leaves; maximum nesting depth5. 39750 leaf multiplicity checks,73312 exact resonance-charge checks,33884 forest/rank/combined checks,11130 all-support blocks including400 longer than 2^k-1 (all had zero resonance);2090 narrow-band blocks,5328 narrow support checks,1328 pair formula checks. Independently enumerated139287 supports of size2/3/4 across bands [T,2T], T11/31/71/131/251,30326 near-resonant at distance<=2 with exact linear witnesses. Counts overlap; they do not estimate the asymptotic rarity in (8). Initial assertion used p-1 also at p=3, which is false; corrected delta_1=0 at3, restricted (6) to p>=5 and reran all checks. Actual example 3,3 at H8; relaxed non-3 zero-outside leaf 13,5,7,5,13 at H73462 (not asserted canonical).

[Varying-support audit 2dedea9](https://github.com/tara-sooo/A166944-Lean/blob/2dedea9c668c0a201ecd71538612863c6c60fc39/research/min_direct_varying_support_leaf_packing_audit.mjs), blob 6526e6172aa5fbb219f31b564ba9b7d4d81ee2f9, exact remote readback. Run node research/min_direct_varying_support_leaf_packing_audit.mjs 18000. Actual ECMAScript execution. 8998 canonical roots through18000,133551 selected events, none unresolved at180 cap. 8756 nonempty relaxed paths and2 explicit relaxed controls. 71742 aggregate ray/cutoff checks,73018 disjoint-block controls,13908 ray/cutoff incidences with varying support. 269887 distinguished event incidences,40165 leaves:3532 small (2262 canonical actual,1270 relaxed),371 zero-outside,3161 positive small,36633 large. 3532 exact linear solve, gap vector and CRT code constructions;622 code groups,1509 distinct code-horizon pairs,887 exact BigInt CRT spacing comparisons,7 aggregate capacity inequalities,73018 large-gain checks. Largest small arity4. Actual zero-outside leaf 19,13,7,19 at H18792; actual positive-small leaf 7,5,7 at H78 with outside-gain vector (0,2). An initial diagnostic chose U=4,T=5, violating U<T-1; corrected to T=7 in that control and reran all tests. Finite bounds loose at these small scales; asymptotic statements are arithmetic deductions, not empirical extrapolation. All final assertions passed.

No Lean executable/kernel verification, no new Fourier exponent, no external novelty claim or finite-twins contradiction. Main and sibling branches not modified by this work.
