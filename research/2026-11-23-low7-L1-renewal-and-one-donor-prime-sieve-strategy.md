# Twin-prime-first: LOW7, source-weighted L1 q-returns, and one-donor prime-pair sieve

2026-11-23 JST. Research checkpoint, Issue #3 cross-Issue #4. This is a mathematical strategy with exact elementary reductions and finite computational diagnostics, NOT an asymptotic proof, NOT Lean-kernel certified, and NOT a proof of infinitely many twin primes.

## 1. A weaker target than the previous quadratic return moment

For dyadic X divisible by 4, let N=X/2 odd starts M in [X,2X), B=ceil(sqrt(7X)), s=M+2 and K=floor((7M-1)/4). Use the exact FINAL squarefree clipped parity-GCD B-wheel from the earlier research notes. Let a HIGH event mean an event d>1 containing any prime q>=11, and give it one owner equal to the smallest such prime. U_q(M) counts high events owned by q. Define F7=sum_(M,q>=11)1_{U_q>0}, R7=sum_(M,q>=11)(U_q-1)_+, T7=F7+R7.

The complete LOW7-only {3,5,7} finite graph has 2*(3*5*7)^2=22050 possible (time modulo 210, even C modulo210) states, no directed cycles, maximum elapsed56 and growth106. Existing executable finite enumerator: research/low_wheel_finite_graph.py. This is finite computational certification, NOT Lean yet.

Each low-only block on an actual full-wheel orbit is a prefix of a LOW7-only orbit and lasts <=56; if no terminal full-wheel sink has appeared, the next HIGH event is within 56+2B additional clock time. Thus, for any dyadic interval with no terminal twin-producing source, the exact total horizon H=9X^2/16-5X/4 satisfies

    H <= (T7+N)*(56+2B).

Since F7<=N*pi(B)=O(XB/logB)=o(XB), and B^2~7X, NO-sink implies

    R7 >= (9/224-o(1))*X*B.

Therefore the following unproved L1 condition suffices for infinitely many twins:

    liminf_(dyadic X->infinity) R7/(X*B) < 9/224.                (L1-OWNER)

Let N_q(M) count ALL actual q-bearing events (masked or owned) on the final B-wheel. Then (U_q-1)_+ <= (N_q-1)_+, and hence the stronger but simpler OPEN hypothesis

    for all 11<=q<=B prime: sum_(M in I_X)(N_q(M)-1)_+ <= C*X

uniformly in q and arbitrarily large dyadic X, would give R7<=C*X*pi(B)=O(XB/logB)=o(XB), and prove twin infinitude. A band-averaged version over q is enough, without per-q uniformity. This target needs only the L1 first-return Green function of the source-tagged q-deleted shadow from Issue #4, NOT its second moment.

## 2. Empirical comparisons and exact finite moment certification

The prior strict-compiled C++ research/twin_prime_lowblock_highowner_audit.cpp outputs:

X | B | R7 high-owner returns | R7/(XB) | Z7/(XB logB)
4096 | 170 | 2015 | 0.00289378 | 0.000977305
16384 | 339 | 17402 | 0.00313314 | 0.00144036
65536 | 678 | 83606 | 0.00188160 | 0.000784761
262144 | 1355 | 496800 | 0.00139863 | 0.000668973

Here Z7=sum_(M,q>=11)(U_q-1)_+^2. The fixed sufficient quadratic-moment threshold remains 243/25088 approximately 0.009686 for ANY fixed finite low-only time bound, since the leading PNT sum of (2q+lowTime)^2 remains (4/3)B^3/logB. In the previously checked full-data X=16384 window, LOW3 Z5/(XB logB)=.010526 (above the threshold), while LOW7 Z7/(XB logB)=.001440 (below).

The exact integer finite Cauchy certificate with LOW7 time56 uses
 D=H-XB-56*(N+F7)-2*FirstWeightedOwner and
 P2=sum_(11<=prime q<=B)(2q+56)^2;
if D>0 and N*P2*Z7<=D^2, at least one terminal twin exists. Recomputed from the existing full-wheel audit (separately with integer Python): every listed X4096,16384,65536,262144 PASSES; LHS/RHS respectively .24786534,.22391994,.10604421,.07732389. X16384 exact P2=11323264, D=138951946, LHS=4323366408290304, RHS=19307643297186916. This is finite mathematics/computation, not asymptotic proof or Lean checking.

In an independent literal odd-source event-jump audit at X16384, LOW7-owner D1=#{M,q:U_q>=1}=38241 and D2=#{M,q:U_q>=2}=9935, so D2/D1=.25979969>1/4. An overly strong global all-k doubling-contraction <=1/4 hypothesis is FALSE at this X; it is not needed for the scalar L1 or moment criteria.

Additional local strict-compiled original-GCD q-repeat scan found maximum all-q repeat/X occurs at q=11: 0.175049,0.348694,0.453018,0.591953,0.712930 for X=4096,16384,65536,262144,1048576 respectively. It is OPEN whether a uniform per-q O(X) bound holds; an aggregate bandwise result tolerates slow growth of individual fixed-q return means.

## 3. Exact recharge and a useful finite-prime alphabet barrier

Following ANY q-hit at time t, post C modulo q is 0 if t even and -2 if t odd. Until the next q event the q-deleted shadow accumulates even non-q growth E; to reactivate q:
  even q post: E modq is +1 or -1, so E>=q-1;
  odd q post: E modq is +1 or +3, so E>=q+1.

The LOW7-only growth maximum 106 gives an exact ESCAPE lemma:

    If q>=109 has two consecutive q-hits, an intervening non-q event
    MUST contain at least one prime r>=11.

The LOW3 growth maximum4 likewise proves a q>=7 high-owner event cannot be followed by another high-owner event of the SAME q without a different high-owner event in between. This cannot be extended to q=5: actual source M=303 has d=5 events at n310 and317 separated by two pure-3 events.

An appealing claim that q can return only after an event carrying a prime >=q is FALSE. Actual source M=4139 has q=31 hits at n4216 and4249, with non-q donor increments d=11 at n4237 and d=21 at n4242. Recharge=(11-1)+(21-1)=30=q-1, using only primes below31.

## 4. Concrete one-foreign-high-event prime-sieve lemma

Take two consecutive actual q-hits with exactly ONE intervening event d having any prime factor >=11, and all other intervening events LOW7 only. Two LOW7-only partial blocks each have cumulative growth at most106, so the complete q-free recharge E=(d-1)+A with A even, 0<=A<=212. The parity-specific q-reactivation congruences force

    q | d+A OR q | d+A-2 OR q | d+A-4.               (DONOR)

If d=r is a SINGLE prime r>=11, then r<=B. For q>(B+212)/2, the positive candidate integers are <2q; so the divisible candidate must equal q and

    -4 <= q-r <= 212, and q-r is even.               (NEAR-PRIME)

Thus in the TOP q band, a prime-only single-donor q return requires an ordered pair of primes q,r separated by one of finitely many even shifts. The standard two-linear-form Selberg upper-bound sieve counts such distinct prime-label pairs at O(B/log^2 B); cite the fixed-tuple upper bound in Corollary 21.3 (printed p218) of https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf . This is a familiar UPPER bound, unrelated to proving any positive lower twin-prime count.

For d=a*r with r the only high prime factor and a a divisor of 3*5*7=105, the same congruence gives k*q-a*r=O(212) for bounded integer k. These are again finitely many fixed-coefficient linear-prime-pair relations. Events with TWO OR MORE high prime factors must be handled separately.

**Critical obstruction:** the Selberg sieve only counts distinct prime labels (q,r); the desired return count is over original sources M and repeated episodes. The adaptive post-q dynamics can coalesce source fibres, so a guessed O(X/(qr)+1) source multiplicity is NOT justified. A source-conditioned multiplicity/transport bound is required before using the sieve result.

At X16384 for all q>=11 actual consecutive q-hit returns, there were 17717 in total: 646 with zero >=11 donor events in between; 4373 with exactly one; 3096 with two; 2438 with three; and 7164 with at least four. Among 4373 one-donor cases, 4215 had a prime-only donor. Hence short-excursion sieve alone covers only part of the return population; long adaptive excursions are essential.

## 5. Concrete proposal for an analytic attack

1. Formalize the 22,050-state LOW7 DAG/rank computation in Lean; the existing finite Python verifier independently confirms elapsed <=56 and growth<=106. Unlike LOW17's 450,900,450 post-q17 states, this finite component is small enough for direct certified enumeration.
2. Split prime labels into dyadic bands Q<=q<2Q. After an actual event involving a prime in the band, evolve a SHADOW with ALL band primes deleted until the first band event. By induction the full and band-deleted trajectories coincide before the first such event, including exact ties. This makes the intervening growth E_j independent of the particular q label within a band *conditional on the actual starting state*, and enables divisor/upper-sieve tests across all q in that band.
3. Split q-return excursions by number of intervening external HIGH events. Zero-event q>=109 returns are rigorously absent; one-prime-donor top-band returns obey NEAR-PRIME. Treat two+ donors via a source-weighted CRT/dispersion transfer on the finite LOW7 residue types (t mod210, even C mod210), NEVER by asserting uniform random q phases.
4. Seek a bandwise bound on the actual source-tagged first-return operator's Green function: for each prime band J, sum_(q in J)sum_(j>=1)||R_q^j nu_(q,first)||_1 <= C X * #J. This implies the aggregate L1-OWNER target after summation across bands; a weaker fixed-coefficient bound below 9/224*XB is enough.
5. Measure the source multiplicity of each (q,r,LOW7 residue state) witness and count q-return donor classes on larger original-GCD dyadic scans. The two persistent obstacles are adaptive source multiplicity and long multi-donor excursion tails, NOT a missing elementary congruence identity.

**No analytic return estimate or infinite twin-prime proof was obtained.** Finite graphs and scans are computational evidence, the implications and DONOR/NEAR-PRIME lemmas are elementary paper mathematics, and the source-selected transport/sieve bounds are proposed unproved inputs.