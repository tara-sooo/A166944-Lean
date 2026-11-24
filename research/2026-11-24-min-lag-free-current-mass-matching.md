# Lag-free matching bound using current-key mass, plus extreme-height budget

2026-11-24 JST. Continues 6cbb947d650b7595aa55fb803cf6869ad5d8bc3b on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions using the previously established upper-bound sieve and exact finite diagnostics. No Lean compilation. The full matching deficit and twin-prime conjecture remain open.

## 1. Change the mass used in the disjoint matching bound

Canonical MIN, original odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original per-root cutoffs, LOW7 L=210, projected high-key absorption and globally disjoint sorted-half far matching of stopped cohorts. A witness pair is charged only once, at the first common proposed high key (p,C), whether or not that event executes. Suppose each arm has a preceding executed high event q,q', with low gains g,g', parity constants b,b', prior height indices k,k'>=0, and current hypothetical post-height indices K,K'>=0. The previous note gives
    2kq=(2K+1)p+e1,   2k'q'=(2K'+1)p+e2,
    |e1|,|e2|<=E=7L+4r(C)+7, each odd,
    K-K'=2j, n-n'=2jp.
Here j can be ANY integer, including zero. In particular the two separate congruences modulo p do not require a bound on j.

Earlier estimates charged each candidate contact to min(m(q,D),m(q',D')), which led to counting the possible j to determine q' from q. Instead impose a bound on the whole CURRENT proposed-key mass m(p,C) (including stopped proposals). Since the original witness matching has degree one, at most m(p,C)/2 pairs can be charged to the current key, independently of the prior masses. Overcounting the same key for different prior labels or parameters is legitimate for an upper bound. This works even if the projected key includes different actual clocks or splits later. It cannot be used with an executed-cap upper bound at an overshooting stop unless its whole actual stopped mass obeys the stated bound.

## 2. Uniform one-prime progression estimates

For prime p<=B and any nonzero residue a mod p, the number of primes q<=B in that class is
    O((1+B/p)/(1+log(B/p))).
Use the ordinary dimension-one upper-bound sieve for the parameter interval of length n comparable to 1+B/p. Omit p, sieve at a sufficiently small fixed power of n, level n^(1/4); the forbidden residue is unique at each other prime. The residue error O(n^(1/4)) is absorbed by n/(1+log n); the actual primes below the sieve cutoff can be counted trivially by O(n^c), also absorbed. For bounded n use the trivial bound. This proves the estimate even without a lower power bound on q.

There is also a useful harmonic version: for H>=1,
    sum_(prime q<=B, q=a mod p, q>=p/(4H)) 1/q
       = O((H+1+log log(3B))/p).
For q<p, at most one candidate and its weight <=4H/p. For q>=p, partition into intervals [2^i p,2^(i+1)p), i>=0 up to O(log B). The same sieve on length n comparable to 2^i, now for this interval, gives O(2^i/(1+i)) primes. Weight each by at most 1/(2^i p) and sum 1/(1+i). No distribution lower bound or independence of the two arms is used.

Two elementary sums will be used:
    sum_(p>=P prime) 1/p^2 <= O(1/P) (even summing over integers suffices),
    sum_(p<=B prime) 1/[p(1+log(B/p))^2] = O(1/log B).
For the latter, p<=sqrt B contributes O(log log B/log^2 B), using the prime harmonic bound. For p>sqrt B, logarithmic bands i=floor(log(B/p)) have harmonic prime mass O(1/log B) by pi(t)=O(t/log t); sum 1/(1+i)^2.

## 3. All-product, unrestricted-lag theorem

Fix positive beta,gamma,delta,lambda with
    4 beta+2 gamma+delta < lambda,
    2 beta+2 gamma+delta < 1.
Put H=log^beta B, z=ceil(log^gamma B), W=log^delta B, P=log^lambda B. (In particular lambda>max(beta,gamma).)
Consider first projected contacts with distinct prime labels p,q,q', both preceding high events, 0<=k,k'<=H, r(C)<=z, p>=P, and whole CURRENT proposed-key mass m(p,C)<=pW (a fixed multiplicative constant is harmless). There is no restriction on q,q' except that they are high labels <=B; no bound on the prior masses, on K,K', or on j; no CRT product range or offset condition.

Then the total number of such globally disjoint matched pairs satisfies
    V_lagfree = O_L(X W H^2 (1+z)^2
                    [(H+1+log log(3B))^2/P + 1/log B])
              = o(X).
For beta=gamma=delta=1/8, lambda=1, this is O_L(X/log^(1/8) B). In particular p>=log B suffices, unlike a fixed polynomial lower bound on the current label. The result applies to synchronous and asynchronous first projected contacts uniformly. It is an estimate on degree-one matching pairs, not all cross products.

Proof. For sufficiently large B, p>=P implies p>2H and p>2E, where E=7L+4z+7. The individual arm equations force k,k'>0 since otherwise the positive odd multiple of p would have magnitude <=E. As K>=0, they also give 2kq>=p-E>=p/2, thus q>=p/(4H), and similarly q'. Fix p,k,k',e1,e2 and both LOW gains and divisibility signs. The two individual congruences
    2kq=e1 mod p, 2k'q'=e2 mod p
give one residue class each, with a nonzero residue for any admissible distinct prime. We deliberately do not impose the equation relating j to the two arms. Instead sum independently over prime q,q' in these classes, overcounting as necessary. For each admissible distinct prime triple, the even horizon C satisfies three CRT congruences modulo 2pqq', so there are O_L(1+X/(pqq')) possible C in the window. Keep the +1 term exactly. By the degree-one matching and current mass bound, at most pW pairs per candidate C can be counted. Summed over the two prime classes this is bounded by
    O_L(W p A_p A'_p + W X S_p S'_p),
where A_p,A'_p are the unweighted progression counts from section2 and S_p,S'_p the corresponding harmonic sums restricted to q>=p/(4H). Thus the +1 term, over all p, costs
    O(W B^2 sum_p 1/[p(1+log(B/p))^2])
      = O(X W/log B),
using 1+B/p<=2B/p. The volume term costs
    O(X W (H+1+log log(3B))^2 sum_(p>=P)1/p^2)
      = O(X W (H+1+log log(3B))^2/P).
Multiply both by O_L(H^2(1+z)^2) possible height coefficients and individual errors, and the constant LOW gains/sign choices, to obtain the theorem. Note that the argument does NOT sum over j. This is why no large-lag loss occurs. It also does not require the earlier bounded-coefficient large-product theorem or quotient quadratics.

The theorem is unconditional for the specified class and follows automatically at executed keys p>=max(P,B^eta) of the earlier hybrid cap ceil(W max(B^eta,p)), and all executed p>=P of the pure normalized cap ceil(pW): executed integer mass <ceil(pW) implies mass<=pW. At a stopped key the statement only applies if actual mass<=c pW for a fixed c. The floor of the hybrid cap can make m(p,C)>pW for smaller p, including executed keys. Under uniform cap B it is conditional except when pW>=B. These distinctions are essential. It does not prove a bound on the entire overshoot population. Equal prior labels q=q' are not counted by the three independent CRT congruences and remain outside the theorem. The same current/prior label with p=q>L+3 is already impossible by the earlier consecutive high-block congruence, once p>=P.

## 4. Actual large-height and extreme-time-gap budget

Let R_i be the executed prefix r-cost of original source i before its contact or stop. At any physical attained state h=2t-C, the start h=6 and monotonic C plus elapsed<=2R_i give h<=6+4R_i. At a proposed event (including stopped proposal) hypothetical h_new<=6+4R_i+4B, since its wait<=2r(C)<=2B. For two proposed clocks n,n' at the same key,
    |h_new-h'_new|=4|j|p <= max(h_new,h'_new)
since both heights are nonnegative. Therefore for any A>6+4B the number of distinct original roots ever having hypothetical height >=A is at most 4R_pre/(A-6-4B), and the number of globally matched pairs with either height >=A, or with 4|j|p>=A, is bounded by the same quantity. This uses global degree one, not a per-event height count. An executed parent index k with 2kq>=A is also covered by this bound (even without the extra 4B term).

Under the uniform cap B, R_pre=O(X^2/log^3 B) (the lower-order LOW term is absorbed). Under the hybrid cap with W=log^delta B, eta<1, R_pre=O(X^2 log^(delta-3) B), by the preceding power-band note. Choose A=X/log^2 B. The corresponding extreme-height or extreme-time-gap witness count is O(X/log B) under the uniform cap and O(X/log^(1-delta) B) under the hybrid cap. Thus the most extreme physical time differences can be discarded globally. This does NOT imply a small logarithmic bound on k or j, since a moderate height can be many multiples of a small selected prime. The remaining moderate heights and large indices are a genuine unresolved population.

## 5. Exact finite diagnostics

Extended the prior individual-arm script at research/min_lag_free_current_cap_audit.mjs, executed for X=256,1024,4096,16384,65536,262144, both uniform diagnostic cap floor(B/4) and hybrid 4 max(ceil(sqrt B),p). Same root identities, cutoffs and global matching. At every first projected contact, including synchronous pairs, record whole proposed-key mass, whether it is a stop, both hypothetical heights and executed prefix costs, check the height-budget inequalities and exact 4jp height difference. If both prior highs exist verify both arm identities. Partition distinct-label contacts by prior indices, r, finite current-label/parent-label thresholds and current mass. Finite illustrative modes include extra parent lower bounds, and do not require the eventual separation p>2H,2E (many finite p are too small); these are diagnostic counts, NOT a count of all theorem hypotheses. Exact remote readback of script and JSON at e44e53cd223b6941d4e253945514c467c8a86fc7.

At X262144 (B1355,N131072):
- Uniform cap338: S11112, R_pre98554147, 5549 matching pairs. First contacts at stop 1641, before stop 3908; of all pairs 1753 have |j|>4 (625 at stop and 1128 earlier). Of all 5549, 2181 have whole current m<=4p (486 at stop,1695 before); 1155 first-at-stop and 2213 earlier exceed that mass normalization. 4598 both-prior-high first contacts pass individual arm checks. Max proposed height at matched first contacts4168, max |j|63.
- Hybrid W4 floor37: S34194,R_pre78434077, 17045 pairs, 5711 first-at-stop,11334 earlier, 5097 with |j|>4 (3129 at stop,1968 earlier). Whole current m<=4p for 7725, all earlier; 5711 stop and3609 earlier exceed4p. 13365 both-prior-high contacts pass both individual identities. Max proposed height4002, max |j|74. Neither run has a matched first contact with height or 4|j|p>=X/log^2 B in this window. This is a finite observation, not the proof of section4.

Hybrid finite diagnostic Q=18 (min prior label), P=11 (current label), H=4, z=31,W=4: 590 distinct-label, positive bounded prior-index, cheap contacts, including 430 with |j|>4. Of the 590, 22 satisfy current m<=4p, 7 of those have |j|>4, 16 have product<=X and 6 >X. All 22 are before stop. The other 568 fail the current mass condition. With Q=37,P=11,H=8,z=31,W=8, 376 such local contacts, 71 covered by current m<=8p, 26 of the 71 have |j|>4, 37 of the 71 occur at a stop. 41 of the 71 have product<=X,30 >X. Example p19,q349,q'59,j15,k=k'=2,e1=-29,e2=-49,C904608,r11,m66 (executed). All identities and the exact lag hold. This example does not satisfy asymptotic coefficient separation and is not an empirical proof of the bound.

At X262144 the strict W4 diagnostic covers NONE of the uniform run's 116 local pairs (90 long-lag). This and the large hybrid uncovered population make it incorrect to suggest that the theorem resolves all or most actual long-lag witnesses. The current-mass cap is a different restriction from the previous normalized-parent theorem.

## 6. Next obstruction

For the newly treated distinct-label bounded-prior-index cheap class, p>=log B and current mass O(p log^(1/8) B) suffice to remove all lag sizes and all CRT products. The previous bounded-lag theorem still handles many overshooting stops with bounded prior mass; neither dominates the other. The key remaining obstruction for this approach is actual large normalized CURRENT mass, particularly at small-label/floor stops and at first contacts reached through downward label transitions, plus the high prior-index, reset/root, same-prior-label and costly-clock classes. The extreme-height budget does not control moderate-height indices. Need a genuinely global anti-concentration or a matching construction avoiding the complementary classes. No overall matching deficit or twin-prime proof obtained. No new branch, no main edits.
