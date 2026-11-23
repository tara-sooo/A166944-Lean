# A166944 Issue #4 — Exact coalescence / noncoalescence split at a common q-clock

Date: 2026-11-23 JST. Dedicated branch: `research/issue-4-terminal-survivor-positive-budget`. This extends [the synchronous q-clock positive second moment](2026-11-23-synchronous-prime-clock-collision-energy.md) and [the mean-horizon weighted criterion](2026-11-23-average-horizon-and-weighted-clock-criteria.md). **The algebra below is proved on paper, and the numeric tables are finite complete original-parity clipped-GCD computations, not Lean kernel proofs. Neither the twin-prime conjecture nor the original A166944 strict-record conjecture has been proved.**

## Setup and exact state-multiplicity formula (PAPER)

Let dyadic even X>=256, B=ceil(sqrt(7X)), I_X={odd M:X<=M<2X}, s=M+2, K(M)=floor((7M−1)/4). At step n>s use the ORIGINAL odd squarefree clipped increment d_M(n) of the parity-specific gcd and let C_M(n) be the resulting even state. For all absolute clocks n and even state c, define

    m_n(c) := #{M in I_X: s(M)<n<=K(M), C_M(n−1)=c}.

This counts only canonical source orbits eligible for an update at n. Put sigma_n=1 for n even, -1 for n odd, and a_n=n for n even, n−2 for n odd. For q odd prime in [13,B] whose clock divides a_n, the exact q-hit count is

    mu_(q,n) = sum_(even c: c ≡ sigma_n mod q) m_n(c).

Since c are even and q odd, distinct contributing pre-states c must be spaced by a positive multiple of **2q** (not merely q). Let r_(q,n)=#{c: m_n(c)>0, c ≡sigma_n mod q}, and let the hit-populations at each such c be k_1,...,k_r; then mu=sum k_j and

    J_X = sum_(q,n clocks) q * mu_(q,n)^2
        = J_equal + J_distinct,
    J_equal = sum_(q,n,c hit) q*m_n(c)^2,
    J_distinct = 2*sum_(q,n) q * sum_(c<c' hit) m_n(c)m_n(c').

The **diagonal individual-source contribution** A_X = Σ_q q H_q = Σ_(q,n)q mu appears in J_equal, and J_equal−A_X counts genuine ordered distinct-source pairs already in the SAME pre-event state (n−1,c). Their future clipped-GCD steps coincide as long as both source deadlines remain valid. J_distinct counts ordered source pairs in DIFFERENT pre-event states but having the same q-clock hit.

For a common q-clock n, write the pre-event deficit z=2n−c (not the previous plateau deficit). The q-hit congruences and parity give the **exact carry-layer parametrization**

    n even: z=(2k+1)q−1,     k>=0;
    n odd:  z=(2k+1)q+5,     k>=0.

Thus different c in one (q,n) fibre are exactly distinct integer carry layers k, separated by 2q. The earlier necessary congruence q|(c−c') is automatic for such q-hitting pairs: on its own it is NOT an analytic upper bound on J_distinct.

## New direct, weaker peak-mass sufficient conditions (PAPER)

Define q-specific maximal simultaneous incidence mu_q^* = max_(q-clocks n) mu_(q,n). Because each q has |C_q| <=5X/(2q)+2, the first weighted moment satisfies

    A_X=Σ_(q,n) q mu_(q,n)
       <= (5X/2+2B) * Σ_(13<=q<=B prime) mu_q^*.

This gives a **NEW SINGLE OPEN SUFFICIENT CONDITION**, weaker in spirit than the uniform peak-fibre conjecture or the positive J estimate:

    BOXED:  Σ_(13<=q<=B prime) mu_q^* = o(X)      (MOM-PEAK, OPEN).

Indeed MOM-PEAK => A_X=o(X²), hence Λ_X<=A_X=o(X²) and infinitely many twins by the earlier sharp weighted clock certificate, conditional on the independently checked finite 133-step low-wheel lemma. This implication uses no second moment or signed cancellation.

Let r_q^* = max_n r_(q,n), and u_q^* = max_(n,c:q hit) m_n(c). Then mu_q^*<=r_q^*u_q^*. So a useful more specific sufficient condition is

    BOXED: Σ_(q prime<=B, q>=13) r_q^* u_q^* = o(X).       (TWO-LEMMA, OPEN)

An easy-to-state stronger pair is a universal **r_(q,n)<=R** and **m_n(c)<=U B** for every q clock contributing c, with fixed constants R,U. It yields Σ_q r_q^*u_q^* = O(B*pi(B))=O(B²/log B)=o(X), since B²~7X. In fact the uniform product r_max*m_max=o(B log B) also suffices. NO such uniform rank/multiplicity bound is proved. The finite data below only motivate it.

For comparison: the prior positive energy target J_X=O(XB²*pi(B)) similarly implies twins. The new MOM-PEAK condition is a different direct first-moment route, allowing exceptional heavy primes as long as their total peak masses are sublinear in X. A uniform O(B) bound for mu_(q,n) is sufficient but unnecessarily strong.

## NEW unconditional coalesced-pair growth charge (PAPER)

Take any (q,n,c) fibre of size m>=1. List the distinct odd original source parameters M_1<...<M_m, so M_{i+1}−M_i>=2. At the SAME exact pre-event c,

    G_(M_i)(n−1) := c − (2M_i−2) >= 0,

and successive values are separated by >=4. It follows rigorously that

    sum_(i=1)^m G_(M_i)(n−1) >= 4*(0+1+...+(m−1)) = 2m(m−1).

Multiply by q and sum over ALL high q-clock fibres:

    BOXED: J_equal−A_X <= (1/2) * sum_(M, q>=13 hitting M at time n) q*G_M(n−1).   (CHARGE1)

If the complete clipped increment at an event is odd squarefree d containing at least one q>=13, the sum of its high prime factors satisfies Σ_(q>=13,q|d)q <=(13/12)*(d−1) (with equality for d=13 only). For the nondecreasing excess G_M, the discrete telescoping identity

    Σ_(all nonunit events n) G_M(n−1)*(d_M(n)−1)
      = (1/2)*[G_M(K)^2 − Σ_(events n)(d_M(n)−1)^2]

holds. Consequently,

    BOXED: J_equal <= A_X + (13/48) Σ_M [G_B(M)^2 − Σ_(events n)(d_M(n)−1)^2]
                   <= A_X + (13/48) Σ_M G_B(M)^2.              (CHARGE2)

These are rigorous source-span / amortized-coalescence estimates, with NO uniformity assumption. They independently bound the large joined part using previous growth, not a per-prime CRT history. **Caveat:** an asymptotic second-moment estimate Σ_M G_B(M)^2=O(XB²*pi(B)) would by Cauchy already imply W_X=o(X²), hence twins directly. CHARGE2 is an analytic ledger and localization tool, not a complete solution or a demonstrably weaker independent breakthrough.

For the nonjoined part, state differences satisfy 2q|(c−c'), and the exact carry-layer pair sum in section 1 is a sharper description than the tautological condition q|gcd(a_n,c−c'). An eventual analytic solution needs an occupancy/dispersion bound on **actually reached, still-active carry layers**, not only a divisor bound over every integer c.

## Finite exhaustive original-GCD audits (NOT asymptotic)

`research/synchronous_pair_split.cpp` enumerates ALL canonical odd starts in every listed X interval with the exact parity-specific prime-clock jump recurrence. It stores every actual high hit as (q,n,C_M(n−1),M), sorts by q,n,c, and computes J_equal and J_distinct as literal integer sums. It validates old high-event totals, independently matches the literal-step GCD at M=7..119, asserts J=J_equal+J_distinct, CHARGE1, and CHARGE2. An **independent Python literal one-step implementation** `research/independent_literal_pair_reference.py` recomputes the ENTIRE pair split for each of X=256,512,1024 without using event clocks, confirming exact equality with C++.

| X | B | J_X | J_equal / J_X | J_distinct | max r_(q,n) | max state mass at hit | Σ_q mu_q^*/X |
|--:|--:|--:|--:|--:|--:|--:|--:|
| 4,096 |170| 7,026,317 | 96.50% |246,244|3|82|0.28711|
| 16,384 |339|94,697,035|96.16%|3,639,938|4|156|0.25134|
| 65,536 |678|1,253,556,984|98.67%|16,695,194|4|322|0.23050|
| 262,144 |1,355|14,564,362,886|98.99%|146,604,964|5|543|0.19021|
| 1,048,576|2,710|118,028,336,599|99.30%|821,462,704|5|977|0.12768|
| 1,999,996|3,742|343,403,550,924|99.38%|2,129,193,258|5|1,188|0.10600|

All high events inside the larger test were among the original starts even in the non-dyadic X=1,999,996. At X=1,048,576 the total high-prime incidence weight A_X=775,958,451, J_equal=117,206,873,895, and the genuinely joined, off-diagonal source-pair energy J_equal−A_X=116,430,915,444; the nonjoined J_distinct=821,462,704 (~0.7%). At X=1,999,996 the joined mass is 99.38% of J and the distinct contribution 0.62%.

Within each q-band at X=1,048,576, maximum distinct pre-state counts r_(q,n) were 5,2,2,2,1 in bands [13,B/16],(B/16,B/8],(B/8,B/4],(B/4,B/2],(B/2,B], respectively. Nonetheless this band-4 rank-one behavior is NOT universal: X=65,536 has noncoalesced pair contributions from q=373, greater than B/2=339. No absolute rank bound or O(B) mass estimate is inferred from the finite data.

For a more detailed numerical check of CHARGE1, X=1,048,576 gave sum over q hits of q*G_before = 1,320,680,000,000 (approximately), whereas 2*(J_equal−A_X)=232,861,830,888. The inequality has a wide finite margin. The exact sum of squared total increments over sources is subtracted in CHARGE2, but the weaker displayed bound was also verified.

## Remaining proof gap and next targeted experiment

1. Establish an upper bound on the **number of simultaneously reached q-hit deficit/carry layers** r_(q,n), perhaps only on average over q rather than pointwise.
2. Establish a transport-bound on **source multiplicities at a nonabsorbing event state** m_n(c), allowing O(B), or the combined q-averaged sum Σ_q r_q^*u_q^*=o(X). This concerns dynamically injected canonical states (s(M),2s−6) that subsequently merge at GCD events. It is NOT provided by the exact two-root CRT of the first post-reset high event.
3. A new local inverse-transition idea: the one-step squarefree GCD map F_n(c)=c+d_n(c)−1 has possible predecessor c'=c−d+1. At even n any such predecessor d must divide gcd(L_B,n,c); at odd n it must divide gcd(L_B,n−2,c+2). Thus the inverse local branching degree is bounded by 2^{ω(gcd(...))}. This is a rigorous constraint on source transport, but repeated inverse branching could still generate large multiplicities. A useful future task is to measure actual branching and prove a weighted contraction over high-event blocks, not claim the per-step degree bound suffices.

**Status:** conditional sufficient theorems and finite proofs for the numeric windows are complete, but the open rank/transport bounds remain unproved. This is not a twin-prime proof; no Lean kernel compilation or merge to main occurred.

## Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/synchronous_pair_split.cpp -o /tmp/synchronous_pair_split
/tmp/synchronous_pair_split 4096 16384 65536 262144 1048576 1999996
python3 research/independent_literal_pair_reference.py 256 512 1024
```
