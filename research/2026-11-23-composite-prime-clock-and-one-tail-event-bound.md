# A166944: composite squarefree event coincidences, deficit obstruction, and a SINGLE event-count sufficient theorem

2026-11-23 JST. Research Issue #4 of `tara-sooo/A166944-Lean` (parent Issue #1), branch `research/issue-4-terminal-survivor-positive-budget`. Continues `2026-11-23-heavy-catalyst-event-jump-two-tail-reduction.md`. The modular clock, deficit, first-event and event-budget proofs below are **elementary paper proofs**, not Lean kernel results. The table is a **finite C++17 original parity-GCD audit**, not an asymptotic result. Neither twin-prime infinitude nor the stronger original A166944 strict-record conjecture is proved.

## 1. Original parity-specific squarefree process

For even X>=256, `B=ceil(sqrt(7X))`; for odd `M in [X,2X)`, put `s=M+2`, `K=floor((7M-1)/4)`, `C(s)=2M-2`. For each `n>s`, let

    raw_g(n,C)=gcd(n,C-1)        if n even,
               gcd(n-2,C+1)    if n odd.
    d_B(n)=gcd(L_B,raw_g(n,C(n-1))),
    C(n)=C(n-1)+d_B(n)-1,

where `L_B` is the product of DISTINCT odd primes <=B, no prime powers. Its product is conceptual, never constructed by the verifier. The `E_B(M)` nonunit event times are `s<n_1<...<n_E<=K`, increments `d_i>=3` squarefree odd, `p_i=P^-(d_i)` the LEAST prime factor. Define terminal growth `G_B(M)=sum_i(d_i-1)` and least-clock load `Lambda(M)=sum_i p_i`. Put `W_X=sum_M G_B(M)`, `E_total(X)=sum_M E_B(M)`, `Lambda_X=sum_M Lambda(M)`.

Recall the already established canonical horizon invariant `0<=Z(n)=2n-C(n)` and terminal sqrt-wheel certificate: `W_X=o(X²)` along arbitrarily large even X suffices for infinitely many twin primes. The invariant may be checked directly: for even n, `raw_g(n,C)|Z(n-1)+3`; for odd n it divides `|Z(n-1)-3|`, where `Z(n-1)` is even, so the special case `Z(n-1)=3` cannot arise and the steps with Z=0 or2 give increments <=3 or1 respectively.

## 2. A STRONGER unconditional estimate: huge composite increments need NO independent budget

Between consecutive events (including the initial point `n_0=s`), C is frozen. Prime `p_i` divides the raw gcd at event `n_i`, so at the frozen previous state its parity-specific p clock must occur in no more than `2p_i` steps. If a p clock had occurred sooner, there would have been an earlier nonunit event. Hence

    n_i-n_(i-1) <= 2p_i,
    n_E-s <= 2 sum_i p_i = 2 Lambda(M).

When E>=1 the terminal C is attained at n_E. The horizon invariant gives

    G_B(M) = C(n_E)-(2M-2)
           <= 2n_E-(2M-2)
           = 6+2(n_E-s)
           <= 6+4 Lambda(M) <= 6+4 B E_B(M).

If E=0, G=0, so this formula holds with harmless +6 universally. Thus, **unconditionally, at every size and start**,

    BOXED: G_B(M) <= 6 + 4 sum_(events i) P^-(d_i) <= 6 +4 B E_B(M).   (C1)
    BOXED: W_X <= 3X + 4 Lambda_X <= 3X+4B E_total(X).                  (C2)

This is an important refinement of the PREVIOUS two-tail estimate `W_X<=B E_total+U_total`, where `U_total` is the oversized composite-increment surplus. The previous estimate was true but **its separate unknown oversized-surplus hypothesis is no longer needed**: (C2) handles arbitrarily large composite jumps automatically through their earliest small-prime clocks and the horizon bound.

**New single open target:** `E_total(X)=o(XB)` as even X->infinity (or on an unbounded subsequence). It implies `W_X=o(X B²)=o(X²)` and therefore twin-prime infinitude by the earlier certificate. More concretely, any fixed `0<alpha<1` with

    #{M in I_X : E_B(M)> B^alpha}=o(X)                            (C3, OPEN)

suffices: sources outside this exceptional set have `G<=6+4B^(1+alpha)=o(X)`; exceptional sources cost <=3X each. An `O(X (log X)^A)` bound for E_total, with any fixed A, is much stronger than needed. No estimate of these orders has been proved here.

There is a second **open** sufficient target: previously established arithmetic root weight

    w0(M)=sum_(3<=p<=B, p|(2M-3)(2M-1)) (p-1),
    R_X=sum_M w0(M)=O(XB/log B),

and (C2) show that even `Lambda_X=O(B R_X)` suffices, since then `W_X=O(X B²/log B)=o(X²)`. The finite values of `Lambda_X/R_X` lie between about 2.03 and 2.56, far below the allowed O(B), but no dynamical bound between these quantities is proved.

## 3. Exact simultaneous-prime clock lemma and CRT phase

At a frozen state (time t, even C), the only active primes are odd `p<=B` dividing `C-1` or `C+1` (these sets are disjoint). The candidate clock of p|C-1 is the next even multiple of 2p after t; that of p|C+1 is the next odd n with `n≡p+2 (mod 2p)` after t. The earliest of these clocks is exactly the next nonunit event; its squarefree increment equals the product of ALL primes whose candidate clock equals that earliest time. This exact next-clock representation is checked by independent literal GCD on small starts.

For distinct active p<q on the SAME side, their first clocks tie only if their common n is

    n≡0          (mod 2pq)      for C-1 (even n),
    n≡pq+2       (mod 2pq)      for C+1 (odd n).

Both clocks are first after t iff `1<=n-t<=2p`. Over a complete uniformly varied residue class of t modulo 2pq, precisely 2p of 2pq possible residues qualify, giving an **exact frozen-state phase fraction** `1/q`. With remaining cutoff time H=K-t, it is `min(H,2p)/(2pq)`. For a same-side set of k distinct active primes of product r, all their first clocks tie with residue fraction `p_min/r`. These are arithmetic statements for a FIXED C and a uniformly varied clock origin t, NOT probability laws for the ADAPTIVELY generated canonical plateau states.

Cross-side p and q NEVER share a clock because their event parities differ.

## 4. Deficit obstruction: a composite event requires accrued slack

Fix an actual plateau whose preceding event occurred at t (or t=s), with frozen state C, even nonnegative `z=2t-C`. Let next event be at n=t+delta, `delta>=1`, and suppose its increment d has at least two distinct prime factors `p<q`, with p the LEAST factor. Then `delta<=2p`, and d is divisible by pq. The two parity cases give exact divisibility:

    n even: d | z+2delta+1       (positive integer),
    n odd:  d | z+2delta-5       (odd nonzero integer).

For odd n, if the latter integer is negative it is -1 or -3 (z even, z>=0, delta>=1), impossible for composite d>=15. Thus for a composite event it must be positive. It follows that

    BOXED: z >= p(q-4)-1       for even composite event,       (C4e)
    BOXED: z >= p(q-4)+5       for odd composite event.        (C4o)

These formulae expose the exact **adaptively accumulated pre-event deficit** that a simultaneous pair needs. They do not imply uniform spatial rarity across M without additional control of the phases t and values C.

**First-event prime lemma (paper proof):** At canonical initialization t=s=M+2 (odd), z=6. Suppose first event increment contains two prime factors p<q. For odd n, delta is even and `d | 2delta+1`, where `0<2delta+1<=4p+1<5p<=pq`, impossible. For even n, delta is odd and `d | 2delta+7`. If q>=7, `d>=pq>=7p>4p+7` for p>=3, impossible. The only remaining pair is p=3,q=5; then delta is odd among 1,3,5 and `2delta+7` is 9,13,17, none divisible by 15. Therefore EVERY FIRST NONUNIT EVENT has a PRIME increment, even when the complete wheel includes many small primes. This stronger fact also excludes any equality of two active initial-plateau prime clocks, regardless of a third, earlier clock.

## 5. Exhaustive finite audit: a direct CRT test and what it shows

Source `research/composite_collision_audit.cpp`, compiled with `g++ -std=c++17 -O3 -Wall -Wextra -Werror`. It uses an SPF sieve and exact event jumps with original parity GCD. Independent stepwise-GCD runs over odd M7..119/cap41 match, and independent published full-wheel growth regressions at X4096,16384,65536,262144 match. EVERY event verifies the deficit lower bound (C4), all trajectories verify (C1) and `n_E-s<=2Lambda`, and every first event is prime. Exact same-side first-clock coincidence counts coincide with the sum over `binom(omega(d_i),2)` at the earliest event, including triple/quadruple events. Numerical results:

| X | B | total events | events with >=2 prime factors | oversized d-1>B | oversized surplus U_X | total min-prime clocks Lambda_X | Lambda_X/R_X | max E per source | # E>B^0.75 |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 4,096 | 170 | 29,349 | 535 | 98 | 13,980 | 383,261 | 2.557 | 73 | 46 |
| 16,384 | 339 | 171,428 | 4,162 | 162 | 102,054 | 2,693,532 | 2.511 | 148 | 203 |
| 65,536 | 678 | 795,689 | 19,964 | 528 | 308,254 | 18,591,985 | 2.356 | 170 | 143 |
| 262,144 | 1,355 | 4,082,904 | 97,023 | 1,231 | 1,555,957 | 131,738,306 | 2.345 | 243 | 72 |
| 1,048,576 | 2,710 | 18,585,269 | 466,545 | 1,022 | 1,756,272 | 831,523,563 | 2.027 | 377 | 1 |

Composite events were ~1.8%–2.5% of all events, but contributed 6.1%–14.0% of TOTAL growth, so deleting them is quantitatively unjustified. At X65536, 84 triple-prime oversized events incurred 173,040 of the total 308,254 oversized surplus (56.1%): large composites cannot be bounded by analyzing only two-prime event *magnitudes*.

For X262144, counting **every** same-side pair of active primes at EVERY frozen plateau gives 9,098,623 candidate pairs, 136,693 with identical next clock before cutoff, and 99,791 ties AT the earliest event, matching the exact sum over all actual events of binom(omega(d),2). The counterfactual sum of frozen-state *uniform phase fractions*, cutoff-adjusted, is 246,203.1, vs observed 136,693. At initial plateaus this counterfactual sum is 13,467.0 while observed ties are **exactly zero**, in agreement with the first-event prime lemma. This demonstrates that the canonical initial states and later adaptive plateau states are NOT distributed as uniform independent clock phases. The phase fractions are arithmetic, but averaging them over actual states is not automatically justified.

`G_B(M)<=6+4Lambda(M)` passed at EVERY source. Global ratios `W_X/(4Lambda_X)` ranged about 0.260–0.271, indicating slack; these ratios are not universal bounds. Earlier `W_X<=B E_total+U_total` remains true, but the new `W_X<=3X+4B E_total` is an alternative that makes U_total unnecessary for the infinite route.

## 6. Remaining proof and recommended next attack

The missing result is **the density of exceptionally long adaptive prime-clock chains**, not a separate control of composite-increment amplitudes. A concrete sufficient target is the single tail `# {M:E_B(M)>B^alpha}=o(X)` for any fixed 0<alpha<1. The numerical threshold alpha=3/4 gave 46,203,143,72,1 source(s) in the five scales, respectively, but those finite counts are not an asymptotic theorem.

A second target that exploits measured mean-clock cost is `Lambda_X=O(B R_X)`. Since initial first clocks are determined by linear congruences in M and the very first event is always prime, the first-event contribution to Lambda_X has a direct CRT/arithmetic first moment. The remaining stages are adaptively generated: they require a **phase-dispersion or amortization lemma** for repeated clock origins. The first-event prime lemma and deficit obstruction constrain these origins but do not yet bound their total number. Attempt a multi-scale (small-prime p vs large-prime p) sieve of *restarts at new plateau states*, retaining the signed deficit. An assertion of uniform phase at arbitrary adaptive state is false as a model of the audited finite distribution.

No Lean kernel compilation was run, and no modification to the main branch is made. Keep assigned Issue #4 OPEN, parent Issue #1 as integration tracker.

### Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/composite_collision_audit.cpp -o /tmp/composite_collision_audit
/tmp/composite_collision_audit 4096 16384 65536 262144 1048576
```
