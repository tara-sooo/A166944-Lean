# A166944: random and dyadic-band prime insertion, first-hit portfolio, and shared-factor response

Date: 2026-11-23 JST. Assigned [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [#1](https://github.com/tara-sooo/A166944-Lean/issues/1). Branch `research/issue-4-terminal-survivor-positive-budget`. Continues [the previous perturbation and global-moment note](2026-11-23-perturbation-response-and-global-moment-reduction.md). The finite algebraic identities and inequalities below are paper proofs **not Lean-checked**; random-permutation statistics are finite C++17 experiments and do not prove the twin-prime or original A166944 conjecture.

## 1. Arbitrary squarefree prime order and the cost-of-negative-variation identity

Fix even `X>=256`, `B=ceil(sqrt(7X))`, `I_X={M odd: X<=M<2X}`, `s=M+2`, and `K(M)=floor((7M-1)/4)`. For ANY subset `S` of odd primes `<=B`, let `L_S=product(S)` (the product is conceptual; the program factors small integers). Define the usual parity-specific clipped-GCD terminal growth `G_S(M)`. For a permutation `pi=(p_1,...,p_m)` of all the odd primes `<=B`, put `S_j={p_1,...,p_j}`, and

    Delta_(pi,j)(M) = G_(S_j)(M) - G_(S_(j-1))(M),
    P_pi(X) = sum_(j,M) [Delta_(pi,j)(M)]_+,
    Neg_pi(X) = sum_(j,M) [-Delta_(pi,j)(M)]_+.

**Exact identity for every permutation (paper):**

    BOXED: P_pi(X) = W_full(X) + Neg_pi(X),
    W_full(X) = sum_(M in I_X) G_(all primes <=B)(M).

This follows by telescoping and `[z]_+-[-z]_+=z`. In particular, `W_full` is independent of insertion order; random permutations **cannot** lower terminal growth. They can raise or lower the unnecessary negative stage variation. A good insertion ordering need not be increasing, but no order has `P_pi<W_full`.

## 2. Verified-on-paper unconditional first-hit portfolio lemma

Fix a partial wheel `S`, an odd start `M`, and run its **old** path. Write its consecutive frozen horizons `C_i` (before the next old nonunit event, and including the terminal plateau), old nonunit increments `e_i>=3`, and total old growth `G_S(M)=sum_(old events)(e_i-1)`. At the **first** opportunity of an uninserted prime `p`, the old and new trajectories still coincide. The new increment is `p*e_old` and the first *new* kick in horizon difference is `(p-1)*e_old`, where `e_old` is 1 if the p-hit precedes the next old nonunit event and is `e_i` if it coincides with that event. Let `F_(S,p)(M)` be this kick, zero if p never hits before the natural cutoff.

For every old plateau, a candidate p must divide `C_i-1` or `C_i+1`. Every horizon satisfies `C_i+1 < B^2` because `2K(M)+1<B^2` for `M<2X`. For either of the two odd numbers, at most three prime factors `p>sqrt(B)` can occur (four would have product >B²); their combined weighted contributions are <=3B. All primes <=sqrt(B) together sum to at most B. Therefore the *combined* candidate-prime weight over the two neighbor integers satisfies

    sum_(3<=p<=B prime, p | (C_i²-1)) p <= 7B.

A prime p is charged only to the plateau of its FIRST hit, and that first kick is at most `(p-1)e_i`, where e_i is the old event at its plateau endpoint, or 1 at the terminal plateau. Since the number of old nonunit events is at most `G_S(M)/2`, summing over plateaux gives

    BOXED: sum_(p notin S) F_(S,p)(M)
           <= 7B * (1 + 3*G_S(M)/2).                 (L1)

This works for **arbitrary subsets S**, not just nested primorial prefixes, and requires no distribution/equidistribution assumption. If T is the set of uninserted primes and the next p is drawn uniformly from T, then

    E_p[F_(S,p)(M) | S,M]
       <= [7B / |T|]*(1+3*G_S(M)/2).                 (L1-mean)

The inequality is *only for the FIRST kick*, **not** for the total direct p-injection J_p or the eventual terminal positive cost, which can include p-refires and large responses.

**Prime-size-band refinement:** for any band `Q<=p<2Q` with `Q>=3`, each of `C_i±1<B²` contains at most `2 log B/log Q` distinct prime factors in that band; every such prime weighs <2Q. Hence

    sum_(Q<=p<2Q, p | C_i²-1) p <= 8Q log B/log Q,

and therefore the total first kicks among available primes in that band obey

    BOXED: sum_(p in T subset [Q,2Q)) F_(S,p)(M)
           <= [8Q log B/log Q]*(1+3*G_S(M)/2).      (L2)

For `Q>=B^epsilon`, the prefactor is <=`(8/epsilon)*Q`, with epsilon fixed. Uniform random selection inside an unfinished band divides (L2) by `|T|`. These estimates are rigorous, but the factor `G_S(M)` and subsequent **dynamic response** remain uncontrolled. At X4096, the *mean over M* of the all-candidate upper bound at half the ascending stages was 213,830, while the mean of the actual first-kick portfolio was 78.38; a direct bootstrapping use of (L1) is extremely lossy.

## 3. Exact gcd factorization of the old-wheel response at arbitrary unequal states

For a step n, put `t=n` if n even and `t=n-2` if n odd. Let `a=C_old(n-1)-1` if n even and `a=C_old(n-1)+1` if n odd, and `H=C_new(n-1)-C_old(n-1)`. Define the squarefree time-active divisor

    D = product_(q in S, q | t) q,
    D_parallel = gcd(D, |H|),
    D_perp = D / D_parallel,
    c = gcd(D_parallel, |a|).

Since `D_parallel | H`, the common q-factors contribute identically at the two horizons. The old-wheel increments obey the **EXACT, unconditional factorization**

    BOXED: e_S(n,C_old)  = c * gcd(D_perp, |a|),
           e_S(n,C_new)  = c * gcd(D_perp, |a+H|),
           response_step = c*(gcd(D_perp,|a+H|)-gcd(D_perp,|a|)).   (F)

Moreover the two inner gcds are coprime (a common prime would divide both a and a+H, hence H, contradicting its membership in D_perp). Thus **only** prime factors q of the time coordinate t with `q ∤ H` can change the old-wheel increment; if D_perp=1, the local old-wheel response is exactly zero. At H=0 the response vanishes. The formula is a deterministic exact refactorization of the old-wheel mismatch, not a bound on its cumulative signed response or second moment. It extends unchanged to arbitrary insertion order.

The C++ audit recomputes (F) independently at every merged old/new event for ascending, descending and the first full-random permutation, including negative and nonzero H, and asserts agreement with the literal `e_S` and the `p`-factored new increment. Example regression at X4096 (ascending): 41,236 old-wheel mismatch event times, 42,545 disagreeing prime/event incidences, and **zero** mismatch events at H=0. These counts are exact finite results.

## 4. NEW random-order global-response-moment sufficient reduction (paper)

Let the existing exact decomposition for every p-stage of any order be

    Delta_(pi,p)(M) = J_(pi,p)(M) + R_(pi,p)(M),
    J >= 0,  R signed.

Let `N_pi` be the total count of activated `(p,M)` sources, `Q_pi=sum_(p,M) [R_(pi,p)(M)]_+²`, `J_pi=sum_(p,M) J_(pi,p)(M)`. The previous Cauchy bound is **pointwise in each permutation**:

    W_full <= P_pi <= J_pi + sqrt(N_pi * Q_pi).

Take the expectation over ANY distribution of permutations (including uniformly shuffling only inside dyadic prime-size bands). Cauchy over the permutation measure yields

    BOXED: W_full(X)
           <= E_pi[J_pi] + sqrt(E_pi[N_pi]*E_pi[Q_pi]).  (R)

The trivial `N_pi <= (X/2)*pi(B)` is valid for all permutations. Therefore a new **conditional route to infinitely many twins** is to prove for some convenient distribution of prime orders, along an unbounded sequence X,

    E_pi[J_pi] = o(X B²),
    E_pi[Q_pi] = O(X B³).                           [OPEN]

Then `W_full=o(X²)` and the existing squarefree-wheel terminal-twin certificate applies. This is genuinely weaker than requiring those bounds for the fixed increasing order; it permits averaging over the subset of primes already inserted. No such asymptotic bounds have been established here.

## 5. Finite permutation experiment

Compile and run the retained source [`random_order_mismatch_audit.cpp`](random_order_mismatch_audit.cpp). It uses original parity-specific clipped GCD and exact prime-event clocks, no multiplication of the astronomical primorial. Its C++17 SPFs agree with a direct literal stepwise gcd for odd starts M=7..119, using primes ≤17. First old-path p-clock and first kick are independently matched with the new path's first p-divisible event at **every source and stage**; terminal net `W_full` is computed again directly with the full prime set; the algebraic J+R decomposition and P−Neg=W_full are asserted; the shared-factor factorization (F) is asserted for merged event streams. The old-option portfolio bound (L1) is checked for **all starts** at empty S and at half the ascending stages.

C++ compiler tested: Debian `g++ 14.2.0`, `-std=c++17 -O3 -Wall -Wextra -Werror`. Each set of pseudorandom permutations is seeded with 20261123; output is deterministic for this tested standard-library implementation. The 'block-random' order shuffles primes separately in `[2^k,2^(k+1))` bands and concatenates bands from smaller to larger. Full-random orders are uniform random permutations (within the PRNG sampling). Different X use different finite sample counts; averages do not imply population properties.

| X | # random trials (per method) | final W_full | ascending P | descending P | full random mean P | block random mean P | min block P |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 512 | 50 | 20,048 | 26,042 | 33,596 | 27,000 | 22,555 | 20,738 |
| 1024 | 30 | 39,940 | 40,426 | 85,334 | 61,109 | 40,868 | 40,384 |
| 4096 | 24 | 399,142 | 445,678 | 863,504 | 638,347 | 446,863 | 436,144 |
| 8192 | 12 | 1,084,898 | 1,167,152 | 2,312,690 | 1,689,451 | 1,192,927 | 1,140,200 |

Observations: wholly randomizing the order increased mean total positive variation at all four tested X; descending order was particularly expensive. Block randomization preserved much of increasing-order performance, and for X512 its mean was actually lower than increasing-order P. At X4096 the 24 block-random orders averaged 446,863 vs ascending 445,678, with 11/24 lower than the ascending positive budget. At X8192 the 12 block-random orders averaged 1,192,927 vs ascending 1,167,152, with 3/12 lower. So it is false that ascending always minimizes finite `P_pi`, but no asymptotic gain was observed from full random ordering.

The terminal response energies also differ by order. At X8192, ascending `Q=236,231,116`, descending `Q=743,494,836`, full-random sampled mean `Q=458,568,738`, **block-random sampled mean `Q=221,169,126`**, slightly less than ascending despite block-random having a higher mean P. Thus energy and positive budget are distinct optimization targets; randomizing within prime-size bands might aid conditional-response moment arguments even if it does not lower measured P.

For reproduction:

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/random_order_mismatch_audit.cpp -o /tmp/random_order_mismatch_audit
    /tmp/random_order_mismatch_audit 512 50 20261123
    /tmp/random_order_mismatch_audit 1024 30 20261123
    /tmp/random_order_mismatch_audit 4096 24 20261123
    /tmp/random_order_mismatch_audit 8192 12 20261123

## 6. Remaining proof bottleneck

The rigorous first-kick bounds (L1,L2) have a `1+G_S` term, and the subsequent p-refire injection plus old-wheel response is NOT bounded by that first kick. The numerical middle-stage L1 bounds are thousands of times the actual first-kick sum, so using them directly as a growth bootstrap does not yield a useful theorem. The local factorization (F) deletes primes dividing H from the response, but does not establish that the surviving q-divisor mismatch events cancel or have a small second moment. Random order alone demonstrably does not reduce the positive budget in general; conditional-on-subset response moment control remains the exact missing step.

Proposed next analytic target: for a uniformly random *unfinished prime within one dyadic band*, prove a second-moment inequality for the **terminal signed** old-wheel response based on the factorization (F) and the old clock, with a global target `E_pi Q_pi=O(X B³)`. Preserve full terminal cancellation. A second goal is to turn conditional first-kick portfolio bounds into a bound on *all* repeated p-injections, potentially using the existing p-refire recharge lemma. Neither is proved in this checkpoint. No Lean kernel compilation, no proof of twin infinitude or original A166944 conjecture, and no changes to the main branch.
