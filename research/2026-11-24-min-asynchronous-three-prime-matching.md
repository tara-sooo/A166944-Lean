# Asynchronous far matching: three-prime CRT product range and degenerate-parent elimination

2026-11-24 JST. Continues 9f993e58481ff8054536656adc92798dd7707cfd on the same research/min-cycle-forest-2026-11-24 branch. Paper deductions and exact finite audit, not Lean-checked. The overall matching bound and twin-prime conjecture remain open.

## 1. Setup and exact asynchronous identity

Use the previous note's source-preserving uniform or hybrid projected high-key absorption, original individual cutoffs, LOW7 L=210, N=X/2, B=ceil(sqrt(7X)), and globally disjoint far witness matching of the stopped roots. A stop cohort of size m yields floor(m/2) disjoint pairs separated in original M by at least m. Each pair is charged at its first common proposed projected high key. The existing budget R_pre=o(X^2) implies that no-twin windows require V >= (1/2-o(1))N such pairs. The target V=o(X), or a strict liminf deficit below N/2, is open.

Let (p,C) be such a first contact with distinct actual proposed times n,n'. The divisibility side of p at C is unique; its period is 2p. Thus n-n'=2jp with nonzero integer j. If both tags have previous executed high events, write their labels q,q', pre-horizons D,D', times u,u', post-horizons C-g,C-g', low gains 0<=g,g'<L even, and post-heights b+2kq,b'+2k'q' (b,b' in {0,6}, k,k'>=0). Set delta=n-u and delta'=n'-u'. Each is positive and <=3L+2r(C), including the proposed stop event. Subtract:
    2kq-2k'q'=4jp+e,
    e=-2(delta-delta')+g-g'-b+b',
    |e|<=7L+4r(C)+6.
The error e is even and may vanish. The parent projected keys are distinct by the first-contact property. At fixed C each previous key is determined by its label and g. For any two fixed previous keys the number of globally matched pairs between their original tag sets is <=min(m(q,D),m(q',D')), even over all possible clocks. The same degree-one principle bounds the number of matched pairs using one fixed previous key and fixed current key by its whole executed mass. All bounds below are on actual matched pairs, not all cross-products.

## 2. Three distinct primes with controlled CRT product

Fix 0<theta<1 and positive beta,gamma,delta_w, lambda with 3 beta+gamma+delta_w+lambda<1. Put H=log^beta B, z=ceil(log^gamma B), W=log^delta_w B, U=log^lambda B. Consider contacts satisfying:
    q,q'>=B^theta, all p,q,q' distinct,
    1<=k,k'<=H, 1<=|j|<=H, r(C)<=z,
    m(q,D)<=qW, m(q',D')<=q'W,
    p q q'<=X U.
No lower bound on p other than p>7. Normalized parent caps hold automatically in the hybrid process when theta exceeds the floor exponent. The proposed stop need not execute.

For fixed (p,k,k',j,e), the two parent primes solve
    k q-k' q'=2jp+e/2.
If the right side is zero, there are no solutions with distinct q,q'>=B^theta, because q would divide k' and q' would divide k. Otherwise, if gcd(k,k') divides the right side, parameterize by two affine linear forms in one integer with coprime positive slopes after division by the gcd. Their determinant is nonzero. On a dyadic band P<=max(q,q')<2P, P>=B^theta/2, embed the parameter interval in length O(P) comparable to P. Use the dimension-two upper-bound sieve from the previous note at level B^(theta/4) and a sufficiently small fixed power of B as prime cutoff. All actual primes exceed the cutoff. Exclude primes dividing the nonzero integer 2kk'(4jp+e) of magnitude O(B polylog B). Its exceptional sieve factor is O((log log B)^2): split exceptional factors at log B, apply Mertens to the small primes and use bounded reciprocal sum for the larger ones, since their product is O(B polylog B). The remainder O(B^(theta/4)log B) is negligible against P/log^2 B. Thus the candidate count in the band is O_theta(P (log log B)^2/log^2 B), uniformly in p and the other coefficients. Divide by P and sum O(log B) bands:
    sum_{distinct q,q' satisfying equation} 1/max(q,q')
        = O_theta((log log B)^2/log B).

For fixed p,q,q',g,g' and three divisibility signs, the three congruences on C are
    p|C+/-1, q|C-g or C-g+2, q'|C-g' or C-g'+2.
They give at most O(1+X/(pqq')) even C in the O(X) window. On the stated product range, this is O(U X/(pqq')), since U>=1. Each determines the preceding projected keys. Multiply by W min(q,q') to bound actual matching count at that triple, giving
    O_L(U X W/(p max(q,q'))).
No extra factor for clock times. Sum the displayed weighted sieve over p with sum_{p<=B}1/p=O(log log B), then over O_L(H^3(1+z)) coefficient/error tuples:
    V_smallprod=O_(L,theta)(X U W H^3(1+z)(log log B)^3/log B)=o(X).
With beta=gamma=delta_w=lambda=1/8 this is O(X(log log B)^3/log^(1/4) B); for the narrower product cutoff X (U=1) the estimate is O(X(log log B)^3/log^(3/8) B). This is an unconditional partial matching bound over any ancestry depth. It uses the three prime congruences; dropping the product restriction and replacing 1+X/(pqq') by X/(pqq') would be invalid.

## 3. Same large predecessor label at distinct projected keys

Suppose q=q'>=B^theta and first projected contact, with r<=z, k,k'<=H and 1<=|j|<=H as above. The distinct parent keys have D-D'=g'-g nonzero of absolute value <L. Both D,D' are even and congruent to +/-1 modulo q. For large B, q>L+2; hence D-D'=+/-2 and the two divisibility sides are opposite. Their previous clock phases are therefore 0 and q+2 mod 2q, at distance at least q-2. Consequently
    q-2 <= |u-u'| <= 2|j|p+3L+2z,
which implies p>=B^theta/(3H) for sufficiently large B. In particular p is polynomially large. The previous horizon congruences exclude q=p when p>L+3. If either previous post-height is reset (index zero), the cheap current p is impossible: the initial height is at most 6, intervening low gain is nonnegative and elapsed <=3L, so p-1<=6+6L+4r by the height inequality. Thus k,k'>0. If k=k', the short identity requires |4jp|<=|e|, impossible for polynomially large p. If e=0, (k-k')q=2jp and q!=p force q|2j, impossible for q>2H. Therefore
    (k-k')q-2jp=e/2
has nonzero coefficients and nonzero determinant, with coefficient magnitudes O(H).

For fixed coefficients and e, the positive prime solutions p,q>=B^(theta/2) satisfy a weighted bound sum 1/p=O_theta((log log B)^2/log B), by the two-linear-form sieve used in section 2 (dyadic bands of p; parameter interval length O(P) even for negative coefficients, or no solutions). For fixed labels and finite g,g'/sign choices, use only p and one q congruence at C to count O(X/(pq)) candidate horizons. Since pq<=B^2=O(X), there is no three-product loss. If the parent mass is <=qW, the degree-one matching count is <=qW; the resulting bound is
    V_sameq=O_(L,theta)(X W H^2(1+z)(log log B)^2/log B)=o(X).
This includes distinct previous keys with equal large selected label, a case not covered by the three-distinct-prime sieve. For an arbitrary current p equal to one of the large parent labels, the consecutive-high horizon congruence already excludes it: p=q>L+3 implies p divides the nonzero odd g-1+sigma_current-sigma_previous of magnitude <p.

## 4. Mixed reset and root exclusion without a sieve

If one previous high post-state is reset, the same height inequality gives p<=7+6L+4z. If the other is nonreset with label q'>=B^theta, then the short identity gives 2q'<=4H p+|e|=O_L(H(1+z)), impossible for large B. This requires bounded |j|, short current clock and large nonreset parent, but no normalized mass cap or upper bound on the nonreset height index. It removes the mixed reset/nonreset class entirely under these conditions. If both previous parents are reset, the upper bound on p still applies, but no analogous contradiction follows. If one member has no previous high event, its initial height is 6 and its initial low block has the same bounds. At its arrival at C the height is O_L(1), hence its hypothetical current post-height is O_L(1+z) and p<=7+6L+4z. The other member's proposed post-height differs by 4jp, so its previous high post-height is O_L(H(1+z)) by reversing the low suffix and the current event; a polynomially large nonreset previous label is again impossible. These are exact asymptotic exclusions, not claims that all finite diagnostic reset cases are absent.

## 5. Partial removal of the large-product residual via a one-arm estimate

In the cheap, two-nonreset-parent regime with k,k'<=H, suppose either previous label q<=p F, F=log^alpha B, alpha>0. Assume q>=B^theta and m(q,D)<=qW, and let r<=z. The height transition for this arm gives current h_now<= 2Hq+6+6L+4z=O_L(pHF); since h_now>=0 it also gives p<=2Hq+7+6L+4z, so q>=p/(3H) for large B. Also p>=B^theta/F>=B^(theta/2). Apply the comparable-parent transfer theorem from 8f091a3a28ca45665c204770dd4e73581152973c with comparison factor O(H), relative height threshold O(HF), clock threshold z, mass normalization W. Constants do not affect the exponent. It gives
    O(X (log log B)^2 log^(3 beta+2 alpha+gamma+delta_w-1) B)=o(X)
qualifying original tag incidences provided 3 beta+2 alpha+gamma+delta_w<1. As each tag has at most one matching partner, this bounds the matching pairs. No assumption on pqq' or on j is required. In particular alpha=beta=gamma=delta_w=1/8 works with exponent -1/8. This also includes all cheap current top-band p>=B/F with both large bounded-index parents, even when pqq'>X U.

What survives these estimates within the three-large-label, bounded-index, short-lag, normalized-mass, cheap-current regime must have:
    p q q' > X U, q>pF, q'>pF.
The +1 CRT error in this regime is a real gap: the arithmetic product exceeds the horizon window length, and the extra congruence cannot automatically be credited with a full factor 1/p. The two-variable prime sieve plus a trivial +1 count has no sufficient aggregate saving here. Neither the long-lag or high-index classes, small labels with large mass, nor double resets are addressed by this partial result. No assertion that this residual is small in the full source population.

## 6. Exact finite audit

Extended the previous disjoint matching audit by replaying each actual first asynchronous projected contact, with original root cutoffs and the same global matching. The saved script research/min_asynchronous_triple_matching_audit.mjs and JSON research/min_asynchronous_triple_matching_results.json were executed at X=256,1024,4096,16384,65536,262144, both diagnostic caps uniform floor(B/4) and hybrid 4 max(ceil(sqrt B),p). Verified the exact integer j, both elapsed/gain bounds, three-label height identity, short error bound, first-contact parent distinctness, and mutually exclusive diagnostic classifications. Previous audit root conservation, physical and projected matching classifications and literal gcd comparisons remain in the script. Exact remote readback of script and JSON at a0dc525c47fe409d1f21bc4ed3cc79e70f56f394.

| X | uniform async | with both prior high events | three distinct labels | product <= X among distinct | product > X among distinct | max abs(j) |
|--:|--:|--:|--:|--:|--:|--:|
|4096|123|81|79|13|66|15|
|16384|493|384|352|185|167|19|
|65536|2076|1728|1634|1115|519|34|
|262144|3661|3170|2905|2220|685|63|

At X262144, uniform T338, 5549 total matching pairs, 3661 asynchronous. Of those, 491 have at least one root-only previous low block; of the 3170 with both high predecessors, 35 both reset, 1454 mixed reset/nonreset, 1681 both nonreset. 79 have identical prior labels, 186 have one prior label equal to current p but distinct prior labels, 2905 all distinct. There are 1908 asynchronous pairs with |j|<=4. Product<=X covers 2220/2905=76.42% of the distinct-label class, not 76% of all pairs satisfying theorem hypotheses.

Hybrid W4 at X262144 has 17045 total matched pairs, 9716 asynchronous, 8029 with both prior highs, 7575 all distinct, of which 5696 product<=X and 1879 product>X. Maximum |j|=74. Finite illustrative diagnostic Q=max(11,ceil(B^.4))=18, indices k,k'<=4, |j|<=4, r<=31, p,q,q'>=Q, both prior masses<=4 times label yields 293 pairs, including 68 all-distinct nonreset pairs product<=X and 45 all-distinct nonreset pairs product>X. 162 mixed reset, 3 double reset and 15 other degenerate cases reflect finite thresholds that do NOT meet the asymptotic separation conditions. Among the 45 large-product nonreset diagnostic pairs none has min(q,q')<=2p. Example p23,C646782,j=-4,e=-52,r23,q163,q'373,k=k'=1, previous masses63 and48: 326-746=-420=4*(-4)*23-52; product 23*163*373=1398377>X. This example verifies the genuine residual when p is smaller than both parents; it is not a counterexample to any asymptotic theorem. Finite counts are not asymptotic evidence sufficient to close the proof.

## 7. Next target

The previous note identified asynchronous projected contacts as a substantial residual. Here the three-prime relation yields a proved matching bound when CRT product is at most X times a small logarithmic power, as well as same-label and comparable-parent deletions; mixed reset/nonreset with bounded lag is excluded under the stated large-label separation. The surviving large-product small-current-label case motivates keeping the quotient variables (C+sigma)/p, (C-g+eta)/q, (C-g'+eta')/q' instead of counting residue classes by a +1 term. A genuine bound on the resulting arithmetic correlations or a source-level estimate which avoids these contacts is still required. The high-index, long-lag and small-label populations also remain. The new lemmas do not establish a strict overall matching deficit. No main change, no new branch, no Lean compilation.
