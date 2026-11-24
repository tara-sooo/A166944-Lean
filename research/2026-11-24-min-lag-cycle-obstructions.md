# Lag return cycles and unconditional removal of short large-return horizons

2026-11-24 JST. Continuation of b0b17927de404b5d2a5d0f74cf9c93b4d8b18ddf. New paper deductions and exact finite audits, not Lean-checked. No proof of the distance-band estimate or twin-prime infinitude.

## 1. Two-step lag returns

Use the canonical full MIN trajectories, B, N=X/2, r(C), W(C), R=sum r(C)W(C) from the full-horizon note. In this note Q=ceil(B/log^(1/3) B), so Q>5 eventually. Two distinct original trajectories at a common horizon have positive absolute time lag h. When both just selected the SAME prime p, 2p divides h: the side is uniquely determined by the shared post-horizon (p divides C or C+2), and their post-event times belong to one parity-clock progression.

If the two trajectories continue choosing common labels q,r at the next two events, and the positive lag returns to h, then 2r divides h as well. If p,r>=Q and h<2Q^2, necessarily r=p, since distinct p,r would force 2pr|h. Thus such a short return of the lag corresponds to the SAME consecutive label pattern p,q,p in both trajectories. This conclusion requires common previous label p, not merely a common horizon. For p>=5 the two consecutive p events without another label are impossible, since after its own gain p-1 the residue on either side is not zero modulo p (the possible nonzero offsets are -3,-1,1). In the p,q,p pattern, the endpoint divisibilities with signs sigma0,sigma2 in {-1,+1} yield
    p | (p-1)+(q-1)+sigma2-sigma0.
The expression is positive and even, so q>=p, q!=p and
    q=k p+c, k a positive odd integer, c=2+sigma0-sigma2 in {0,2,4}.
c=0 is impossible for distinct primes q,p. These are arithmetic constraints, not a monotonicity assertion for lag.

## 2. NEW unconditional deletion theorem for full-horizon budget (including LOW blocks)

Fix LOW7, L=210 as in the earlier notes; the following argument works for any fixed even LOW primorial. Consider the high word of a FULL trajectory (not truncated to 2P). A consecutive-high pattern p,q,p with p>=Q, q!=p, includes at most two LOW blocks between these events. Each LOW block gains less than L. Consecutive high p,p is impossible for large p by recharge and the LOW barrier.

Let C0 be the pre-horizon of the first p, E1,E2 the two LOW gains, and sigma0,sigma1,sigma2 the three signs. The pre-horizon of q is C0+p-1+E1. The last p divisibility implies
    q=k p+c, c=2+sigma0-sigma2-E1-E2, |c|=O(L),
    q>=p-2L>=p/2 for sufficiently large B.
Here p,q distinct primes; c cannot be zero. For a fixed p there are O_L(B/p) candidates for q even ignoring q's primality, and O_L(1) choices for E1,E2 and signs. The congruences
    p | C0+sigma0,
    q | C0+p-1+E1+sigma1
fix a CRT class modulo pq; C0 lies in [2X,7X). Thus there are O(X/p^2) candidates for C0 for each choice, since p<=B and X comparable to B^2. Include the three pre-high horizons and EVERY possible LOW pre-event horizon between them (offsets <L after the first and second high gains). The number of possible horizons S_short in this union is at most a fixed O_L(1) times the number of tuples. By prime counting pi(t)=O(t/log t) and summation over dyadic p bands,
    |S_short| = O_L(X B sum_(p>=Q prime) 1/p^3)
              = O_L(X B/(Q^2 log Q))
              = O_L(B/log^(1/3) B).
Thus |S_short|=o(B), unconditionally. The version with zero LOW gains is the consecutive-event pattern in section 1. The same lag-return argument applies across the two high blocks when both trajectories use identical FULL label sequences through the blocks and end with the large prime at lag h.

Every original source visits a pre-horizon at most once, hence W(C)<=N, and r(C)<=B. Therefore
    R_short := sum_(C in S_short) r(C)W(C)
            <= NB |S_short|
            = O_L(X^2/log^(1/3) B)
            = o(X^2).
This is an unconditional upper bound on ALL source mass at those horizons, even sources not executing the motif, independent of the coalescence weights. It is stronger than just a source-count estimate for actual short-return occurrences. One can delete S_short entirely from the full weighted clock-budget sum R and from the heavy excess J, with o(X^2) error. In particular the remaining sufficient condition is liminf J_outside_S_short/X^2<9/32, with the same tau and original source weights as in 73458de887def94d00eeaf2d2d3b9c59a44b8137. It does NOT imply that the contribution of S_short to the pair energy E_d is O(X^2B); use deletion directly in R or J before applying an energy criterion to the remaining horizons. No claim that this class is the dominant obstruction.

## 3. Longer periodic lag patterns: exact constraints

(a) For any contiguous common-label nonmerging run, all selected primes divide at least one positive OUTPUT lag. If H is the set of these lags, all selected primes divide the even integer D=2 times the product of the distinct odd primes dividing the members of H. By the deterministic even-multiple barrier, total common horizon gain is <D and the total r(C)-weight is <3D/2. In particular D divides lcm(H). If H has at most k members, all <=Hmax, D<=Hmax^k/2^(k-1) (for nonempty H; every member is even). This gives a per-run bound, not a bound on the total number of runs. If H consists of at most two lags 2p,2q with p,q>=5 prime, selected labels are among p,q. Adjacent identical labels are impossible. Four consecutive alternating labels p,q,p,q would require q>=p and p>=q by recharge, impossible for distinct primes. Thus such a run has at most three selections, with total weight <=3B, even if the lcm is large.

(b) Suppose a block of k common labels, all >=Q, is repeated exactly in two or three successive copies, with the same output lag word; all output lags are positive and <2Q^2. In fact repeating the lag word alone forces equality of the prime word if all selected labels are >=Q: at most one such prime divides any lag/2. Set G=sum_(i=1)^k (p_i-1)>0, the common horizon gain per copy, and let S be the set of distinct primes of the word. At any fixed position with label p, endpoint divisibility across copies gives p | G+sigma_(j+1)-sigma_j, with the signs of that position in successive copies. Thus for two copies, each p in S divides at least one of G-2,G,G+2. If G>2 and k(B-1)+2<Q^2, each of these integers is positive and below Q^2 and can have at most one distinct prime >=Q. Therefore |S|<=3 for such a twice-repeated word. For three copies, the two differences of successive signs are congruent modulo p and are in {-2,0,2}; since p>=5 they must be equal, hence both zero. Consequently every p in S divides G. Since G is even, 2 product_(p in S) p divides G. If |S|>=2, then k(B-1)>=G>=2Q^2. This excludes triple repetition of any shorter large-prime lag word using two or more distinct labels (and a single-label repeated word is impossible for p>=5). This does not exclude longer nonperiodic runs. Neither (a) nor (b) bounds the total weight of general lag changes.

## 4. Actual exact finite diagnostics

C++17 research/min_lag_cycle_audit.cpp includes the earlier full-horizon audit. Compile:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror -Wno-return-type research/min_lag_cycle_audit.cpp -o /tmp/min_lag_cycle_audit
    /tmp/min_lag_cycle_audit 256 1024 4096 16384 65536 262144 1048576
-Wno-return-type is for the macro-renamed included main only. All seven windows actually run. Source blob bc94fbdbe0c7d6a3f1b366cd4591125234bda795, exact remote readback at 972fc5a872f0b35683e02532a4b2c8ff636f364c. Parent include blob 995067c02c29590f5f64afb1bbcdc6cd482e29a2. The code enumerates the relaxed consecutive-event (NO LOW insertion) triple set, verifies that all actual triples are included, and evaluates the actual weight of all possible horizons. The LOW extension in section 2 and periodic restrictions in section 3 are paper deductions, not tested by this code.

For reversal pairs, require a previous event in BOTH paths and at least two further events. Group original sources by common C, next two labels and total elapsed time of those two events. Subtract pairs with equal first-event waits. The resulting pairs necessarily have distinct initial arrival times (determinism), nonzero intermediate lag (otherwise would merge), and the same signed initial and final lag, with intermediate lag different. Count ORDERED distinct original pairs with occurrence multiplicity (a pair can reverse multiple times). Far means original source separation >B. Count also same previous label; for this subset if both previous and second next labels >=Q, check the lag bound and equality of the labels. The largest lag column is the largest arrival-time spread of an entire grouping cell, an upper bound on all tested reversal lags, not necessarily an attained reversal lag.

| X | B | Q | all reversals | far reversals | far reversal weight (both steps) | possible direct triple horizons |
|--:|--:|--:|--:|--:|--:|--:|
|256|43|28|248|98|1776|15|
|1024|85|52|386|0|0|18|
|4096|170|99|19234|4804|80348|48|
|16384|339|189|177932|46436|583960|78|
|65536|678|363|888778|94936|1173464|105|
|262144|1355|702|5513990|674994|8563184|222|
|1048576|2710|1361|36180428|3968026|49608472|396|

No actual direct p,q,p with p>=Q occurred in these runs, nor any eligible large-lag return of section 1. Largest window: all events 19219036, R=730547400, weight over relaxed direct-triple horizons=123592 (all sources, irrespective of motif), max group lag spread 7722, same-prev far reversals 3290902. The parent exact far G_change=3487160354. The sum of r(C) over BOTH steps of all eligible far immediate reversals (49608472) is only 1.423% of that; because overlapping reversals can double-count steps, the union of eligible reversal steps accounts for AT MOST this fraction. Reversals starting at a root without a previous event are excluded. Short reversals as tested are therefore not the main observed G_change contribution. This ratio is finite, not asymptotic.

Independent Python literal parity-GCD and exhaustive source-pair oracle research/min_lag_literal_oracle.py:
    python3 research/min_lag_literal_oracle.py 256 1024
Both windows match all C++ reversal counts and far weights. Tested blob dfa437e7c797e69540f0f8db9056142159529caa; read back at eb9b6191812f588a4bf466068e9d936a7c98a29a. Genuine nonmonotone lag example: X256, M287,M333, C684, next labels 5,3, absolute lag 48 -> 50 -> 48. X1024, M1073,M1079, C2184, next labels 5,3, lag 42 -> 40 -> 42. These invalidate simple monotone-lag arguments, not the full energy bound.

## 5. Remaining task

The new deletion theorem removes a class of rapidly repeated large primes directly from R,J regardless of source weighting. The exact cycle restrictions show why treating repeated short lag words is insufficient. The larger unsolved part consists of common-label lag changes NOT in short two-step returns (and the earlier common-suffix mass and different-label splits). Next investigate maximal common-label segments, first-return versus new-lag steps and the number of distinct lag states along them, retaining original pair weights; no uniform aggregate estimate for such nonperiodic segments is obtained here. The original full-horizon budget, separated-pair estimate and twin infinitude remain open. Main untouched; no new Lean compilation.
