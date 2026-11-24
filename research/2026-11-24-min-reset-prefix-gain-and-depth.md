# Reset first-excursion prefixes: gain-limited rough jumps and arbitrarily fixed-depth saving

2026-11-24 JST. Continues c3309b61f80e1c1f8bb97de1fab194417398f2e7 on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions using the established upper-bound sieve and exact finite diagnostics. No Lean compilation. The full first-excursion moment, reset mass saturation, early-sink estimate and twin-prime conjecture remain open.

## 1. Setup and gain-limited jump lemma

Use the common-cutoff reset forest of the preceding note. X dyadic, B=ceil(sqrt(7X)), K=floor((7X-1)/4), all hypothetical reset origins u in [X+3,K], initial horizon C_u=2u-b(u), b(u)=0 for even u, 6 for odd u. Follow actual MIN until next reset (including low-event resets) or terminal. H(u) counts selected high primes p>7, L=210. The first excursion includes its final executed event, not the final quiet tail.

At any pre-event state (t,C) of such a trajectory, let G=C-C_u be cumulative gain, h=2t-C. The MIN wait bound n-t<=2r(C) and r(C)<=p<=3(p-1)/2 give t-u<=3G. Thus
    h=b(u)+2(t-u)-G <= 6+5G.
After the next event with selected p the new height is nonnegative, giving
    p-1<=h+4r(C),
    4r(C)>=p-7-5G.
In particular if p>=10G+14 then r(C)>=p/8. This applies to an arbitrary prefix, not just the first high event, and does not assume that earlier labels were distinct.

Fix integer G0>=0 and real Z>=max(11,10G0+14). Count hypothetical reset origins that encounter ANY selected p>Z while pre-event cumulative gain G<=G0 (before their first subsequent reset or terminal). For fixed G (even), parity b, p and divisibility side sigma, C=2u-b+G and p|C+sigma determine one residue class u mod 2p after fixing parity. The possible variable interval has length O(X/p) and can be embedded in one of length comparable to X/p>=cB. The two forms C-1,C+1 avoid primes <=p^c for fixed sufficiently small c>0, by r>=p/8. Their slopes are invertible for odd primes other than p and their roots distinct; omit p and 2. The same standard dimension-two upper-bound sieve with small-power level used in previous notes gives O(X/(p log^2 p)) candidates uniformly in G and parity. The affine constants do not affect the root count. Summing p>Z using the elementary prime-counting upper bound and partial summation, sum_(p>Z)1/(p log^2 p)=O(1/log^2 Z). Summing gains and signs gives
    #origins with a jump p>Z after gain <=G0
        = O(X (G0+1)/log^2 Z).
All constants here are absolute (L fixed in the applications below). This is a count of distinct reset origins by union bound, not an estimate on repeated source-weighted high keys. It remains valid if Z>B (empty event set).

## 2. Explicit first-two-high cost bound

Define F_k(X) as the sum over all reset origins of r-cost through the kth high event, or the complete excursion if H<=k (including its final low block in that case). Thus each prefix uses <=k high events and <=k+1 low-only blocks. Let E_k be its executed elapsed sum, E_k<=2F_k. Let q,p be the first and second high labels if present. The first-high sieve from the preceding note bounds sum of first q by O(XB/log^3 B), including excursions with any subsequent length, since it counts the first high regardless of H.

We obtain
    F_2=O(XB/log^2 B).
Proof: if no second high, use first-high and low-block bounds. If p<=32(q+L), charge p to q+L, again O(XB/log^3 B). If p<=sqrt B, its sum is O(X sqrt B) regardless of q. In the remaining case p>32(q+L), p>sqrt B, preceding gain G<=q-1+2L, so p>=10G+14 and r(C)>=p/8. In particular q!=p. Let g0,g1 be the two intervening low gains, even <L. The first high pre-horizon is D=2u-b+g0; the second is C=D+q-1+g1. Fixed q,p,g0,g1,b and signs give two distinct-prime congruences in u, with CRT progression step 2pq. Its interval length n is comparable to 1+X/(pq), itself comparable to X/(pq) because pq<=B^2=O(X). Sieve C-1,C+1 along the progression, omitting 2,p,q. With sieve level n^(1/4) and sieve cutoff a sufficiently small fixed power of min(n,p), the same uniform two-root sieve gives
    O(n/(1+min(log n,log p))^2)
candidate origins. For bounded n use trivial count, and the standard residue remainder O(n^(1/4)log(2n)) is absorbed for large n. Since p>sqrt B and n<=O(X), this is O(n/(1+log n)^2). Multiplication by the second label p bounds its total cost for each tuple. There are only O_L(1) gain, parity, sign choices.

For q<=B^(1/4), n>=c B^(3/4), hence the weighted sum over q,p is
    O(X/log^2 B * sum_(q<=B^(1/4))1/q * pi(B))
      = O(XB log log B/log^3 B).
For q>B^(1/4), use logarithmic bands i=floor(log(B/p)), j=floor(log(B/q)), with each harmonic prime mass O(1/log B) uniformly in this range. Then n comparable to exp(i+j), p<=B exp(-i), and the weighted sum is at most
    O(XB/log^2 B) * sum_(i,j>=0) exp(-i)/(1+i+j)^2
      = O(XB/log^2 B).
The last double sum converges (sum over j bounded, then geometric in i). Low-only costs O_L(X), and all contributions combine to the bound. In particular the FULL cost/elapsed of excursions with H<=2 is o(XB). This estimate also bounds the first two events of arbitrarily deep excursions, without requiring the second event to reset.

## 3. Arbitrarily fixed depth and a slowly growing depth

The gain-limited jump lemma yields a qualitative result at EVERY fixed high-event depth, not only two. Let k>=1 be fixed, Y_k=sqrt B and recursively Y_(j-1)=log Y_j for 2<=j<=k (for sufficiently large B all these quantities are large). Classify a reset origin as bad if its jth high label exceeds Y_j at some 1<=j<=k, and take the FIRST such j. Before it, all high labels <=Y_(j-1), with at most j-1 high events and j low-only blocks. Its cumulative gain <=k(Y_(j-1)+L) for j>=2, or <L for j=1. For sufficiently large B, Y_j>=10k(Y_(j-1)+L)+14, and Y_1>=10L+14. The gain-limited jump count gives
    #bad origins <= O(X/log^2 Y_1
                 + X k sum_(j=2)^k (Y_(j-1)+L+1)/log^2 Y_j)
                  = O_L(X k^2/log Y_1).
On good origins, the prefix r-cost <=k sqrt B+(k+1)3L/2. On bad origins, <=kB+(k+1)3L/2. Thus
    F_k <= O_L(X k sqrt B + X k^3 B/log Y_1).
For fixed k, log Y_1 tends to infinity (asymptotic to the kth iterated logarithm of B, up to the harmless factor in Y_k). Therefore
    F_k=o(XB), E_k=o(XB) for every fixed k.
In particular all first excursions with any fixed bounded high-event count have total elapsed o(XB). No restrictions on the later trajectory are needed for the prefix estimate.

The same argument is uniform for the following explicit very slowly growing depth k=k(B). Take the largest positive integer k such that iterating logarithm k-1 times on sqrt B is defined and yields Y_1>=exp(k^4); take k=1 if the set is empty for small B. For sufficiently large B, k(B)->infinity; indeed every fixed k eventually qualifies. The recursive thresholds are increasing, log Y_1>=k^4, and Y_j=exp(Y_(j-1)) dominates 10k(Y_(j-1)+L)+14. Also k<=O(log B) by the iteration definition, so k/sqrt B->0. Hence
    F_{k(B)}/(XB) = O_L(k/sqrt B + 1/k) -> 0.
This is a slowly growing-prefix result, not a logarithmic-depth or polynomial-depth result. At the available finite sizes k(B) can still be very small. It is not a proof that all excursions finish by that depth.

## 4. Exact residual and a sufficient tail criterion

Write A(X)=sum_(u:H(u)>=2) l(u), the earlier multiple-high first-excursion elapsed target. For each u, after its kth high event (if H>k) there are H-k high events and at most H-k+1 low-only blocks. Their elapsed is <=2B(H-k)+3L(H-k+1) <=(2B+6L)(H-k), since H-k>=1. Thus
    A(X) <= 2F_k(X)+(2B+6L) sum_u (H(u)-k)_+.
A sufficient new marginal condition is uniform integrability of the unweighted high-event count over reset origins:
    lim_(k->infinity) limsup_(dyadic X->infinity)
          (1/X) sum_u (H(u)-k)_+ = 0.
Under this condition, first take limsup X for each fixed k, using F_k=o(XB), then k->infinity, to obtain A=o(XB). A uniform bound on X^(-1) sum H(u)^(1+delta) for some fixed delta>0 would suffice, but is not shown. An alternative sufficient condition is sum_u (H-k(B))_+=o(X) for the growing depth above. These are stronger than necessary because they charge every late label the maximum B; weighted late costs may be small even if these unweighted tail conditions fail. In particular do not infer uniform integrability from finite data. The marginal count is for the first excursion only, not the old full-future count after a reset.

The first-excursion moment A=o(XB) alone does NOT establish twin primes. The common-cutoff forest route still requires control of reset stops (positive-fraction escape), or a separately justified early-sink lower bound paired with the appropriate moment bound, as stated in the preceding note.

## 5. Exact finite prefix and jump audit

Executed the function body of research/min_reset_prefix_gain_audit.mjs:
    node research/min_reset_prefix_gain_audit.mjs 256 1024 4096 16384 65536 262144 1048576
All reset origins on the common cutoff, actual MIN until first reset or terminal. At every selected event check gain/height inequality, time/gain bound, rough gain-limited jump implications (G thresholds 0,10,34,100,500), exact LOW blocks, prefix and residual cost conservation. Literal parity-GCD at X256/1024: 671+2542=3213 decisions. Record prefix r-cost/elapsed, tail high counts and tail elapsed at k=1,2,4,8,16,32,64. Record separate H=2 total elapsed and maximum H, nonreset first high counts, examples of deep excursions. At tested sizes the optional diagnostic p2>16(q1+L) has no occurrences; this test is not evidence for the asymptotic p2-dominant bound. The paper bound uses the safer cutoff 32(q1+L). The full r-cost/elapsed and A agree exactly with the preceding cut-capacity audit. Script and JSON exact remote readback at d9fd17395ec80405524091ad64c49c2c6ec5abbe.

|X|B|H maximum|A|H=2 elapsed|prefix-2 elapsed|tail after 16 elapsed|tail high count after 16|
|--:|--:|--:|--:|--:|--:|--:|--:|
|4096|170|14|69849|11034|64320|0|0|
|16384|339|30|468854|58963|335848|17090|399|
|65536|678|66|3156454|312856|1823058|304868|6176|
|262144|1355|74|19065019|1537644|10079706|2423215|33261|
|1048576|2710|106|119004377|8734945|57177672|19295069|194258|

At X1048576, 786429 reset origins, total all-excursion elapsed 137050255, total r-cost 157799322, H sum1474259. Of the 454335 first high events, 183011 did not immediately reset (40.28%). For the largest observed H=106 there is no inference of unbounded maximum. 523 origins have H>64, tail beyond 64 contains 6618 high events and 707167 elapsed. One deep terminal excursion u1530229, H64, elapsed12023, begins [1531,97,13,11,59,101,11,457,19,17,73,11]. The empirical residual high count at fixed k16 divided by X increases in these windows, so there is no evidence here for a uniform-integrability theorem merely from a small fixed k. The observed weighted residual is much smaller than its B times high-count envelope. The next research target should be a genuine tail contraction or a weighted bound for late selected labels in nonreset excursions; the prefix theorem does not supply either. No new branch, no main edits, no Lean-verified theorem.
