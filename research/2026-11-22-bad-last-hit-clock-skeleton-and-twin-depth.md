# A166944: exact BAD last-event clock skeleton, infinite modular quiet tails, and a fully certified twin-input 500-step reverse survivor

2026-11-22 JST. **Status: PAPER theorems and independently executed, exact integer certificates. The original a(1)=2 orbit is NOT known to attain the large artificial M below. Cap B and twin-prime infinitude remain OPEN. No new Lean kernel compilation.**

Continues [the exact inverse-gcd BAD exclusion](2026-11-22-bad-terminal-backward-crt-nonrealizability.md), [terminal factor first-hit clock](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), and [canonical reachability/GOOD-genealogy obstruction](2026-11-22-record-genealogy-quiet-parent-high-reuse.md). All integer certificates are reproduced by [the standalone standard-library verifier](bad_last_event_clock_cert.py).

## 1. Exact frozen-horizon last-hit clock

Fix a proposed EVEN horizon C>=2 at cutoff K and consider all indices <=K which WOULD be nonunit hits if the horizon remained frozen at C. Let `P_minus` be the distinct odd prime divisors of C−1 and `P_plus` those of C+1. For p in P_minus, the frozen nonunit even indices form the progression n≡0 (mod2p); for p in P_plus the frozen nonunit odd indices form n≡p+2 (mod2p). Hence the LAST possible frozen hit at or before K (requiring n>=3) is

    e_p(K)=2p*floor(K/(2p)),            p|C−1,
    o_p(K)=p+2+2p*floor((K-p-2)/(2p)), p|C+1,

where indices <3 are omitted. Define the exact frozen clock extremum

    R_*(K,C)=max({2} union {e_p(K)>=3} union {o_p(K)>=3}). (1)

Then the frozen-horizon gcd d_C(n) is EXACTLY 1 for all `R_* <n<=K`, and if `R_*>=3`, d_C(R_*)>1. Factorization of C±1 computes the extremum, or a direct gcd check of the final short interval can certify a specific value.

**Exact last-event skeleton theorem (PAPER).** Suppose some genuine parity-gcd history ending at (K,C) has a LAST nonunit event at index S<=K. Then

    BOXED: R_*(K,C) <= S <= K.                          (2)

Moreover for ANY r in [max(3,R_*),K] and ANY e>1 in the complete inverse predecessor list

    e odd, e|gcd(A,B), gcd(A/e,B/e−1)=1,
    A=r−2(r mod2), B=C+2(r mod2), C−e+1>=2,

there is a fully exact local segment starting with post-horizon C−e+1 at r−1, then event e at r, then only unit increments until K and post-horizon C. This is an IF-AND-ONLY-IF parametrization of locally possible **last-event suffixes**, not of the preceding canonical prefix. The remaining earlier history can be tested recursively, one event skeleton at a time.

If C±1 are NOT BOTH prime and K lies in the large canonical range, some composite neighbor has a prime factor q<=isqrt(C+1). That factor's clock has a hit no more than 2q behind K, so (2) automatically confines r to the previously known O(sqrt M) terminal window. But the new statement gives the EXACT arithmetic lower bound on r, not just an interval size.

**Exact historical checks:**

    genuine canonical M 13:  (K,C)=(22,40),   R_*=18, last S=20, 1 candidate last-event branch;
    genuine canonical M 43:  (K,C)=(75,132),  R_*=65, last S=66, 5 branches;
    synthetic canonical M 305: (K,C)=(533,852), R_*=518, last S=527, 3 branches.

The earlier locally BAD but inverse-impossible assignments

    M=101119, (K,C)=(176958,236004), R_*=176957;
    M=100549, (K,C)=(175960,241340), R_*=175955

have EXACTLY ONE locally possible last event each: `(r=K,e=3)` and `(r=K,e=5)` respectively. Their whole backwards trees still die after 8 and 6 steps, as proved in the preceding note. The last-event skeleton removes speculative unit-step branches but cannot by itself eliminate every local BAD possibility.

## 2. Why NO fixed finite inverse depth can refute every modularly admissible BAD candidate

**Infinite CRT-constructed locally BAD family (PAPER).** Choose any integer g>=22 with g≡1 (mod21). Set B=2g+1. We construct infinitely many integer quadruples

    r even, K=r+g, M=(4K+3)/7 odd, C=2r,

with the following properties:

(a) K=floor((7M−1)/4), M+2<r<K, and 2M−2<=C<=2K.

(b) The original exact gcd at r, from predecessor horizon C−2, has increment exactly 3: `gcd(r,2r−3)=3`; after r, the next g increments are ALL 1, so D(K)=C is a locally exact path segment. Its offset X(r)=2r−C is the aligned reset value 0, and X(K)=2g>=0.

(c) BOTH C−1 and C+1 are composite, so this terminal candidate is BAD; the small-prime frozen clocks do not fire in the g-step suffix.

(d) The artificial twin-prime input candidates M and M−2 are BOTH nonzero modulo **every prime p<=B**. This is finite prime-wheel admissibility, NOT full primality or historical reachability.

**Proof.** For every odd p<=B other than7, prescribe r modp avoiding `2r−1==0`, `2r+1==0`, `M==0` and `M==2` modulo p. For p>=5, at most FOUR residues are excluded, so one is available. For p=3, the unique permitted r residue is 0, compatible with M≡g≡1 mod3. Since g≡1 mod7 choose r≡0 mod7, and choose r modulo 49 so that M=(4(r+g)+3)/7 is neither0 nor2 mod7. Require r even. Take two distinct primes q1,q2>B, prescribe `2r≡1 modq1` and `2r≡−1 modq2`. CRT supplies an unbounded arithmetic progression of solutions r.

At event r, r is even and divisible by3, and `gcd(r,2r−3)=3`. For an even n=r+j with 1<=j<=g, every prime dividing the frozen gcd must divide `2j+1<=B`. For an odd n=r+j it must divide `|2j−5|<=B` (the zero case cannot arise because 2j−5 is odd). But no such prime divides either 2r−1 or 2r+1 by construction. Therefore every step in `(r,K]` is a unit increment. The forced primes q1,q2 divide C−1,C+1 respectively; for large r their proper quotients exceed1, so both are composite. All canonical size/offset inequalities follow for sufficiently large r. QED.

This proves that a proposed **fixed-depth reverse-tree extinction theorem based only on BAD endpoint, canonical numerical bounds, aligned local reset and any fixed prime-wheel input admissibility cannot hold**. It does NOT produce infinitely many genuinely twin-prime inputs, since that would require an unavailable theorem about twin primes in arithmetic progressions. It also does not produce a genuine BAD outcome from the original a(1)=2 seed.

The standalone auditor checks CRT examples for g=22,43,106, screening all primes <=45,87,213 respectively, and exact g-unit suffixes.

## 3. A substantially stronger finite counterexample: TRUE twin-prime inputs and 500 exact reverse steps

There is an explicit artificial canonical-shaped input with genuinely PRIME M-2,M:

    M   = 12783268038291131701,
    M-2 = 12783268038291131699,
    K   = 22370719067009480476,
    C   = 44741438134018960908.

This M is NOT asserted to have been attained by the original a(1)=2 recurrence. Nevertheless `K=floor((7M−1)/4)` and `2M−2<=C<=2K`; both terminal neighbors are composite:

    47 | (C−1),    53 | (C+1),

with quotients >1. At frozen post-horizon C, the exact last eligible clock is R_*=K−46: at index K−46 the frozen gcd is 47, and at all 45 later indices <=K the frozen gcd is 1. The next ACTUAL nonunit hit after cutoff is exactly `J=K+7`, with e(J)=53. Thus all the local BAD short-crossing/factor-clock arithmetic holds.

**Elementary, fully rigorous prime certificates.** The two integers are certified by the complete N−1 factorizations and one Lucas primitive-order witness each:

    N=M:   N−1=2^2*3^2*5^2*11*17*773*49411*1988633,
           Lucas witness a=6.
    N=M−2: N−1=2*19*131*167*199*313*246872729,
           Lucas witness a=2.

Every listed factor is prime (exact trial division to its integer square root), the products are precisely N−1, `a^(N−1) ==1 (mod N)`, and for every listed distinct q, `gcd(a^((N−1)/q)−1,N)=1`. The standard elementary order argument therefore PROVES both N are prime, rather than treating them as probable primes.

**Two DIFFERENT exact finite suffixes ending at the SAME (K,C):**

1. An even aligned reset at r=22370719067009480454 with prior horizon C−2, e(r)=3, post-horizon C=2r, followed by g=22 consecutive unit increments through K. Here X(r)=0 and X(K)=44. This is a locally valid 23-step segment; its earlier canonical history has NOT been supplied.
2. Independently, a **500-index exact gcd history** from

       n0 = 22370719067009479976,
       D(n0)=44741434510218131142,
       X(n0)=3623800828810,

   reaches precisely (K,C). Its only nonunit events, written `(n−K,e)`, are

       (-49,3623800829707), (-34,37), (-29,5), (-28,9),
       (-26,5), (-22,3), (-8,7).

   Every intermediate horizon is in `[2M−2,2n]`; every event increment e<=M. The total horizon growth in those 500 steps is 3623800829766. **This second suffix has an event at K−8** and is NOT the same history as the 22-unit aligned-reset suffix in item1. Both are legitimate local precursor branches of the same terminal BAD candidate.

The 500-index suffix is checked by 500 direct evaluations of the ORIGINAL parity-sensitive gcd, independent of reverse-tree enumeration. The local BAD terminal and the true twin-prime inputs are certified by arithmetic and complete Lucas witnesses. This finite witness refutes any proposed *uniform fixed inverse-depth <=500* exclusion applying to **all** twin-prime-input, numerically canonical-shaped BAD terminal candidates, even with horizon and record-size bounds imposed throughout the surviving suffix. It does NOT rule out an eventual theorem valid on the unique original attained record orbit or at a depth growing with M.

## 4. Remaining gap, with the direction sharpened

A terminal BAD candidate can satisfy: both input integers are genuinely prime, the cutoff arithmetic, a precise short post-K crossing, hundreds of legitimate preceding gcd steps, and the usual horizon bounds — and STILL be an artificial state not reached from the actual canonical start `(M+2,2M−2)`. Conversely, two other artificial BAD candidates have empty inverse trees within 6/8 steps.

The exact last-clock skeleton makes the inverse search event-based, but this evidence shows that an early universal local extinction statement is too strong. To complete Cap B one must prove a **global** exclusion for the canonical-start reachability condition: every terminal BAD candidate violates some inherited path inequality/CRT potential upon long enough backward propagation, or derive a BAD-specific invariant that makes the inverse event skeleton incompatible with the full canonical prefix. This problem remains OPEN. No new Lean kernel proof was compiled.