# Full-history clock congruence and twin-prime-input terminal sieve

2026-11-22 JST. **Status:** new exact paper congruence / finite-prefix lifting theorems, two explicit twin-prime-compatible local BAD witnesses, and direct recurrence audits. This is NOT a proof of Cap B or twin-prime infinitude, nor a new Lean kernel compilation.

Continues:
- [terminal factorized first-hit dichotomy](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md);
- [high-growth terminal F envelope](2026-11-22-high-growth-terminal-f-envelope.md);
- existing Lean [ReplayOffset210.lean](../A166944/ReplayOffset210.lean), which already formalizes a closely related **offset** and its event-residue update, but not the prefix-lifting statement here;
- original recurrence [Lemmas.lean](../A166944/Lemmas.lean) and user-provided `mission_scan/twin_proof/cap_bound/AllIndices.lean`.

## 1. Exact WHOLE-PREFIX canonical-clock identity

Start an authentic or artificial canonical-shaped odd parameter M at index

    s0=M+2, C0=D(s0)=2*M-2.

At relative index t>=1 set r=M+2+t and

    G_(t-1)=D(r-1)-(2*M-2),

the sum of all prior nonunit-growth increments, including every previous event. Then the **exact actual recurrence**, not merely a necessary divisor test, is

    d(r) =
        gcd(M+t+2, |2*t+7-G_(t-1)|),  if t is odd (r even);
        gcd(M+t,   |2*t+1-G_(t-1)|),  if t is even (r odd).  (1)

Proof: at even r,

    gcd(r, D(r-1)-1)=gcd(M+t+2,2*M-3+G)
                   =gcd(M+t+2, 2*t+7-G).

At odd r, similarly

    gcd(r-2,D(r-1)+1)=gcd(M+t,2*M-1+G)
                     =gcd(M+t,2*t+1-G).

The absolute value is only to make gcd arguments nonnegative; the original unsigned gcd remains identical.

For **every** prime factor p of d(r), (1) implies the simultaneous exact **time/growth sieve**

    p | (M+t+2) and G_(t-1)==2*t+7 (mod p), if t odd;
    p | (M+t)   and G_(t-1)==2*t+1 (mod p), if t even.     (2)

These two conditions are also sufficient for p to divide d(r). Crucially, (1) tracks the entire earlier trajectory through the exact accumulated G, not just the final few gcd tests. It gives a finite exact compatibility certificate for a **specified complete event word including all intervening unit steps**, and can reject prescribed unrealistic path histories.

The identity is algebraically equivalent to the previously formalized offset coordinate, so it is a useful **repackaging and implementation**, not a claim of an independent new inequality with a stronger asymptotic coefficient.

## 2. Finite-prefix CRT lifting: the mathematical limit of bounded-depth rules

Consider a fixed odd M and an exact prefix of length T, with relative integers

    R_t=2*t+(7 if t odd else 1)-G_(t-1),  1<=t<=T.

Assume every R_t is nonzero (this holds on a capped prefix with no new record, because a zero R_t would make the gcd equal to the positive index argument, which exceeds the old record M). Define the positive **even modulus**

    P=2*lcm(|R_1|,...,|R_T|).

**Exact periodic prefix theorem (paper).** For every integer k>=0, the artificial canonical-shaped start at M'=M+kP has **exactly the same increment word at its first T relative indices**:

    d_(M')(M'+2+t) = d_(M)(M+2+t),  1<=t<=T.       (3)

Moreover its horizon is lifted by 2kP at each corresponding time, while the relative G and every R_t agree exactly.

**Proof by induction.** At t=1 the growth G=0 is common. If earlier increments agree, G_(t-1) and R_t agree. The parity of r is unchanged since P is even. By (1), the gcd is with the same nonzero fixed integer |R_t|, while its other argument increases by kP, a multiple of |R_t|. Thus the next gcd is identical, closing the induction.

A stronger **bounded-sieve** version is available without any twin-prime distribution hypothesis. Suppose the original M and M-2 are both primes >B. Let Q_B be the product of all primes <=B. The infinite sequence of artificial starts

    M_k=M+k*P*Q_B, k=0,1,2,...

all has the same T-step increment word and for every q<=B has

    q does not divide M_k*(M_k-2).

This retains input **small-prime admissibility at every fixed finite wheel**. The lifted M_k,M_k-2 are NOT asserted to be prime; demanding that would be an unproved prime-pair problem.

**Interpretation:** a bounded number T of exact first-hit tests, even together with any fixed finite small-prime sieve at the input, cannot distinguish an original prefix from all of its arbitrarily large synthetic copies. Any proof closing Cap B needs a history-sensitive invariant at a scale growing with M, not a finite prefix or fixed modulus alone.

The companion [full-prefix audit](twin_input_full_prefix_crt_audit.py) verifies (1) for **every index** (including unit steps), and checks (3) for T=750, 1500, and 1600 at M=100549, 101119, and 45895573, respectively. The lifted modular periods have roughly 1300–1800 bits and yield identical gcd event words.

## 3. Universal cutoff-index congruence and genuine twin-input restrictions

Let M be **any odd integer**, K=floor((7M-1)/4), and

    zeta=7M-1-4K in {0,2}.

For an integer delta with r=K+delta>=3, put u=r mod2 (0 for even, 1 for odd). Then

    7*M = 4*(r-2*u) + A,  A=1+zeta-4*delta+8*u.    (4)

Because d(r) divides r for even r and r-2 for odd r, every prime p|d(r) obeys

    7*M == A (mod p).                               (5)

If **M and M-2 are prime and both >p** (the induction hypothesis for a hypothetical FIRST failed Cap B step), then M modulo p cannot be 0 or 2, and for p!=7 one obtains the new **prime-admissibility exclusion**

    A mod p is NEITHER 0 NOR (14 mod p).            (6)

For p=7, instead require A==0 mod7.

These conditions depend only on the original canonical parameter and the **absolute position relative to K**, so they connect an early input property to an otherwise purely local terminal event pattern.

**Three rigorous corollaries:**

1. **No 7 factor at the cutoff, for ANY odd M:** K mod7 is 1 if M==1 (mod4), and 5 if M==3 (mod4). If K is even, a 7-divisible increment would need 7|K; if K is odd, it would require 7|(K-2). Neither is possible. Thus

       7 does NOT divide d(K).                      (7)

2. If M-2,M are twin primes >=5 and 3 divides d(K), then

       M==7 (mod24) and K is even.                  (8)

   To see this, M==1 (mod6), so either M=12a+1 yielding K=21a+1==1(mod3), or M=12a+7 giving K=21a+12==0(mod3). The odd-K gcd divisor would require K==2(mod3), impossible; the even-K case forces M==7(mod12) and K even, thus M==7(mod24).

3. Under condition (8), **the next increment is coprime to 3*5*7=105**:

       gcd(d(K+1),105)=1.                           (9)

   Indeed K is even, so K+1 is odd and any prime factor q of d(K+1) divides K-1. The divisibility q=3 is impossible since K==0(mod3). q=7 is impossible because M==3(mod4) gives K==5(mod7). q=5 would imply from K=21a+12 with M=12a+7 that a==4(mod5) and hence M==0(mod5), contradicting its primality. Thus terminal patterns **3 followed by 3, 5, or 7** cannot occur for prime-pair input.

These are exact arithmetic obstructions, not claims that d(K) necessarily equals 3 or that all short BAD crossings are forbidden.

## 4. Strong limitation: two locally BAD patterns remain even with ACTUAL twin-prime input

Requiring M and M−2 to be prime removes the preceding [3,7] artificial family but does NOT exclude all BAD local cutoff events. The following two fully explicit examples use **actual twin-prime integers M**, and comply with canonical range bounds and the global 0<=W<=32 travel requirement. Each only ASSIGNS an artificial terminal state; neither claims the state is attained along the original trajectory.

**Witness A: 3 followed by 11**

    M=101119; M-2=101117; both prime;
    K=176958 (even), s=K-1=176957;
    H=236002, C=236004=H+2.

Then

    gcd(K,H-1)=3,   gcd(K-1,C+1)=11.

Consequently the two consecutive steps K and K+1 have exact increments 3 then 11. The pre-state H satisfies 2*M-2=202236<=H<=2*s and C<=2*K. The required artificial history growth G=H-(2*M-2)=33766 and travel T=s-(M+2)=75836 obey

    9*G-4*T=550>32.

Thus EVERY endpoint choice 0<=W(start),W(end)<=32 is compatible with the coarse kernel W-potential inequality. But the **actual** full prefix computed from this same M ends at C_actual=D(K)=203322 after 49 nonunit events, and 203321,203323 are prime. The artificial local C=236004 is NOT the actual reached state.

**Witness B: 5 followed by 3**

    M=100549; M-2=100547; both prime;
    K=175960 (even), s=175959;
    H=241336, C=241340=H+4.

Then

    gcd(K,H-1)=5,   gcd(K-1,C+1)=3.

The synthetic two-step continuation is again exact. Its artificial G=40240 and T=75408 give

    9*G-4*T=60528>32.

The actual original trajectory from this M ends at C_actual=D(K)=201210 after four events, whose neighbors 201209,201211 are prime. No terminal BAD crossing actually occurs.

**Therefore:** even simultaneously imposing initial input twin-primality, two exact terminal gcd hits, canonical state-size conditions, and the strongest *uniformly bounded endpoint W* global-growth test does not force an impossible arithmetic combination. What is missing is a new **correlation across the intervening complete path**.

## 5. Larger finite twin-input test, independently corroborated

The stand-alone [twin-input C++ finite scan](twin_input_canonical_cutoff_scan.cpp) uses an exact **factorized first-hit map** and deterministic primality checks. It independently cross-checks per-index gcd traces on small twin-prime inputs and then scans all twin-prime starting values 7<=M<=20,000,000.

Results:

    107406 twin-prime input values,
    4,859,867 first-hit events across their synthetic canonical paths,
    exactly TWO terminal non-twin cases: M=13 and M=43.

All twin-prime starts M>=45 in this FINITE window yield terminal twin primes at K. The inputs are actual prime pairs but the **canonical-shaped initial state is artificially assigned for each independent M**; they are not all reached as strict record states by a(1)=2. The result is finite numerical evidence, not any infinite bound. A much broader 100-million-input test was not completed and has no reported result.

The finite observation is stronger than the previous all-odd artificial-start scan to one million in the sense of a larger input range, but is weaker in its starting-value class (only twin prime M).

## 6. Next missing invariant, and what this work actually excludes

The new exact prefix identity is a checkable **entire-history encoding**, and the twin-input cutoff sieve eliminates some locally BAD branches previously considered. But the existence of twin-compatible local BAD witnesses proves that those arithmetic endpoint constraints and general W growth cannot by themselves complete the induction.

A successful global statement would have to exploit **interacting requirements at an unbounded number of intermediate indices**, beyond any fixed finite CRT wheel and fixed-length prefix. A concrete target is a growth-sensitive, multi-prime event-word exclusion certificate that forces the first **short post-K hit** to be absent on the actual canonical path, or directly proves C=D(K) has prime neighbors.

No such asymptotic exclusion is established in this note. No new Lean theorem has been kernel checked. The twin-prime conjecture remains OPEN.

**Reproduce:**

    python3 research/twin_input_full_prefix_crt_audit.py
    c++ -O3 -std=c++17 research/twin_input_canonical_cutoff_scan.cpp -o /tmp/twin-input-scan
    /tmp/twin-input-scan 20000000
