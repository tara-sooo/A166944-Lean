# A166944 squarefree wheel: winning-clock episodes, screened prime clocks, and a weaker weighted moment criterion

Date: 2026-11-23 JST. Scope: [A166944-Lean Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4) (parent #1). Research branch: `research/issue-4-terminal-survivor-positive-budget`. This is a continuation of `2026-11-23-active-prime-clock-cancellation-and-winner-moment.md`, using the original parity-specific squarefree clipped GCD. **All new lemmas are elementary paper arguments, not Lean kernel-checked; numerical statements are finite exhaustive C++17 experiments. Neither twin-prime infinitude nor the stronger original `OeisA166944.conjecture` is proved.**

## 1. Setup, exact q activation episode, and one-switch survival lemma

For even `X>=256`, let `B=ceil(sqrt(7X))`, `I_X={M odd in [X,2X)}`, `s=M+2`, `K=floor((7M-1)/4)`, initial even `C(s)=2M-2`. At subsequent n, `g(n,C)=gcd(n,C-1)` if n even and `gcd(n-2,C+1)` if n odd, and `d(n)=gcd(L_B,g(n,C))`, with `L_B` the product of each odd prime <=B exactly once. Set `C'=C+d-1`. Nonunit event count `E_B(M)`, growth `G_B(M)` and global `W_X` follow prior notes.

At every plateau state `C` after its preceding event time `t`, let `A(C)={odd prime q<=B:q|(C-1)(C+1)}`. At a plateau with `A` empty, no further event can occur. For q>=5, an **activation episode** starts when q first belongs to A (at t=s or after a preceding event) and ends at a firing q-event, a nonfiring disappearance, or at cutoff. The old lemma proves that a q firing disarms it for q>=5; hence these are disjoint and yield the **exact individual-q identity**

    root_q + births_q = hits_q + nonfiring_deaths_q + terminal_q.       (E1)

For q=3 the correct identity instead includes `odd3_firings` on the left, because after an ODD event containing 3 the same active 3 persists:

    root_3 + births_3 + odd3_firings = hits_3 + deaths_3 + terminal_3.  (E1-3)

**NEW one-switch lemma (paper):** Suppose q>=5 is active, and during its episode an intervening non-q event has increment `3<=d<=q-2`. The q-clock is canceled unless `d=3` and q is active on the `C+1` side; that exceptional event switches q to `C'-1`. If another non-q event with increment `d'<=q-2` arrives while q still persists, the q-clock is canceled. Thus every q>=5 activation episode ending in a hit falls into one of three disjoint classes:

1. Immediate: q fires at the very next event after activation.
2. One `3`-switch: there is exactly one intervening non-q event, with d=3 on the plus side, and then q fires at the next event.
3. Large-rescue: one or more intervening non-q events have increment `d>=q-1`.

No independence, probability, uniformity, or averaging assumption enters this classification. The q=3 persistence exception is kept separate.

**NEW shifted-increment divisibility (paper):** For any q>=5 active before and after a non-q event of increment d>=5, the only possibilities for its previous/new side yield

    old C-1 -> new C'-1 : q|(d-1)
    old C-1 -> new C'+1 : q|(d+1)
    old C+1 -> new C'-1 : q|(d-3)
    old C+1 -> new C'+1 : q|(d-1).

Therefore

    BOXED: q | (d-3)(d-1)(d+1).                               (E2)

If d=3 then d-3=0 and arbitrarily large q may survive the unique plus-to-minus switch. For d>=5, every surviving nonfiring large q belongs to one of three explicit prime-divisor sets determined by d, not by the prior state. In particular, q<=d+1.

## 2. NEW elementary *screened clock* certificate, with no stochastic hypothesis

For plateau `(t,C)` whose remaining cutoff is `K-t`, let `a=min A(C)`, provided A is nonempty. The next parity-restricted clock of q in A is `tau_q` (even multiple of 2q if q|C-1; odd n congruent to q+2 mod 2q if q|C+1), and always `1<=tau_q-t<=2q`. Define its **screen indicator**

    screen_q(t,C) = 1{tau_q<=K and tau_q-t<=2a}.

Define `S_q(X)=sum_(M in I_X) sum_(plateaus with t<K) screen_q(t,C)` and weighted `S_X=sum_(q<=B) q*S_q(X)`. A prime q in the ACTUAL next event increment must have `tau_q=n` equal to the earliest clock. Because the active smallest prime a has a clock within 2a steps, `tau_q-t<=2a`, so every actual q hit is screened:

    H_q(X) <= S_q(X),
    Lambda_X = sum_(M,events i) P^-(d_i)
             <= sum_q q*H_q(X) <= S_X.

The existing unconditional travel/horizon lemma `G_B(M)<=6+4 sum_i P^-(d_i)` now gives

    BOXED: W_X <= 3X +4*S_X.                                    (E3)

Therefore either of the following **OPEN sufficient** conditions would imply twin-prime infinitude via the already verified squarefree sqrt-wheel terminal certificate:

    S_X = o(X*B^2),
    or for all q<=B uniformly S_q(X) <= C*X*B/q.               (E4)

For the second alternative, `S_X<=C*X*B*pi(B)=O(X*B^2/logB)=o(X^2)`. **Even the weaker condition on ACTUAL hits `H_q(X)<=C*X*B/q` suffices** by `W_X<=3X+4sum qH_q`. This improves the prior winner moment `H_q<=C*X*sqrt(B)/q` by an additional factor sqrt(B), because the current argument retains the q-weights of event primes instead of bounding only the number of events.

The screen calculation does not require knowing which prime actually wins the clock race: it asks only whether q's next clock is within `2a` of the plateau. The plateau states themselves still depend adaptively on previous events, so E3 is a rigorous reduction, not an asymptotic solution.

## 3. A NEW unconditional deficit sieve for screened larger primes

At a plateau let `z=2t-C>=0` (the existing nonnegative horizon deficit) and `a=min A(C)`. Suppose `q>a` is screened, so its hypothetical next q clock `n=t+delta` has `1<=delta<=2a`. On q's required parity side, q divides

    z+2delta+1       if n even and q|C-1,
    z+2delta-5       if n odd and q|C+1.

For the second case the integer is odd and at least -3. Since q>=5 and divides it, it is positive. Consequently

    BOXED: q <= z+4a+1.                                        (E5)

In particular **at the initial plateau** `z=6`, so an active smaller prime a completely screens out all q>4a+7 from firing first, no matter how large q is or how many other primes are active. (If q itself is the smallest active prime, this shielding argument does not apply.) E5 applies to a candidate screen even if some different prime wins the actual next event. The C++ verifier asserts E5 for every screened q at every visited plateau.

## 4. A precisely defined phase comparison — the main remaining obstacle

At FIXED C and for a fixed horizon allowance H, if one uniformly varies an **artificial clock origin t mod 2q** while holding the active q, the next q-clock distance is uniform in `{1,...,2q}`. For shielded q>a, the exact phase-model chance to be screened is

    m_(t,C,q) / (2q),    m_(t,C,q)=min(K-t,2a).

This is a model based on uniform phase, NOT a statement that actual canonical plateau origins are independent or uniform. Let

    F_shield(X)=sum_(M,actual plateaus (t,C))
                  sum_(q in A(C),q>a) q*min(K-t,2a)/(2q)
              = (1/2)*sum_(M,t,C) sum_(q>a) min(K-t,2a)
              <= sum_(M,t,C) a*(|A(C)|-1).

A uniform comparison of actual screened weighted shielded clocks with this phase benchmark, **together with** an upper bound on `sum_(M,plateaus) a*|A(C)|=o(X^2)`, would yield `S_X=o(X^2)` and twin-prime infinitude. These are TWO OPEN analytic statements, and an asymptotic estimate for the exposure sum is itself substantial.

Crucially, an individual adaptive plateau can have a q clock one step away even with a much smaller active a; an unconditional per-plateau `screen <= C*a/q` for fixed C is FALSE for any universal C. For example, take p=3, any odd prime q>=5, frozen even C=3q+1 and t=4q-1. The earliest q-clock is n=4q=t+1, whereas the next 3-clock occurs later, so the q screen is 1 although uniform-phase benchmark is 3/q. This is a valid frozen congruence state with z=5q-3>=0, but it is NOT asserted to occur on a canonical trajectory. Only an **aggregate, trajectory-sensitive discrepancy lemma** can justify the comparison.

## 5. Complete finite original-GCD clock-episode experiment

Source `research/clock_episode_screen_audit.cpp`. Built with `g++ (Debian 14.2.0) -std=c++17 -O3 -Wall -Wextra -Werror`. For each listed X, **every odd M in [X,2X)** is simulated by exact factorization and next-prime clocks. Independent literal one-step parity-GCD recomputation on all odd 7..119 with cap41 passes; prior full-growth and event regressions pass. Every source asserts the new screened-clock certificate E3; every q>=5 asserts E1; q=3 asserts E1-3; every event asserts the D1 small disarming and E2 shifted factors and every screen satisfies E5.

| X | B | events | all prime hits | weighted min-factor Lambda | weighted actual q hits | weighted screened clocks S_X | S_X/(sum qH) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | 170 | 29,349 | 29,884 | 383,261 | 392,422 | 617,328 | 1.5731 |
| 16,384 | 339 | 171,428 | 175,707 | 2,693,532 | 2,760,017 | 4,447,875 | 1.6115 |
| 65,536 | 678 | 795,689 | 816,075 | 18,591,985 | 18,965,049 | 29,450,411 | 1.5529 |
| 262,144 | 1,355 | 4,082,904 | 4,181,311 | 131,738,306 | 133,650,527 | 204,778,315 | 1.5322 |

For the shielded phase benchmark, weighted actual screen divided by `F_shield` at these four scales was respectively `0.92885, 0.96279, 0.92281, 0.90961`. This agreement of order one is finite evidence **not** an equidistribution theorem; early first plateaus have strongly correlated phases as proved in the predecessor first-event-prime lemma.

At X262144 the episode breakdown by geometric q band was:

| q band | activated episodes (root+birth) | successful q hits | success fraction | hit immediately | hit after one 3-switch | hit after large rescue |
|:--|---:|---:|---:|---:|---:|---:|
| [24,48) | 1,113,009 | 243,127 | 0.2184 | 182,317 | 60,480 | 330 |
| [96,192) | 981,389 | 117,340 | 0.1196 | 87,290 | 30,040 | 10 |
| [192,384) | 846,309 | 82,087 | 0.0970 | 59,143 | 22,944 | 0 |
| [384,768) | 758,503 | 60,338 | 0.0795 | 41,742 | 18,596 | 0 |
| [768,1356) | 565,588 | 21,956 | 0.0388 | 16,666 | 5,290 | 0 |

In the last q band, 539,294 active q episodes were canceled by a smaller non-q event with d+1<q; the last-band screen contained 47,393 q clocks (vs 21,956 actual hits). Despite ~565,588 activations, relatively few clocks came close enough to compete. Of 557,250 episodes beginning shielded by a smaller active prime, 15,555 eventually fired q; the other 6,401 hits came from unshielded episode starts. This strongly suggests **separately bounding the unshielded rough-state episodes and short-window shielded screens**. The numerical success fraction is NOT uniform across q and may vary at larger X.

The sum over q of ALL actual hits includes q=3 repeat fires; the q>=5 episode ledger is exact without a survivor exception. In finite scans the remaining active set was empty at every cutoff, but this is not a general assertion.

## 6. What would genuinely close this route

The strongest next target is a **uniform adaptive short-clock sieve**:

    S_q(X) <= C*X*B/q   (all odd primes q<=B).                 (OPEN)

Unlike q-winning counts, `S_q` depends only on the current C, its least active prime a, t, and elementary residue clocks — it does not ask which prime wins. A potentially more structured alternative is to prove (i) the weighted aggregate shielded phase discrepancy `actual <= C*F_shield` and (ii) `sum a*|A|=o(X²)` across all canonical plateaus; the latter likely needs a nontrivial dynamic bound on the number of visits to rough and composite boundary states.

Neither follows from the deterministic disarming rule alone: q can be reborn at later plateaus, and the plateau origins t are adaptively generated. The proof would have to establish a **mean equidistribution/cancellation principle for the actual q-free or small-prime clock histories**, not assert independent uniform phases on arbitrary states. The earlier artificial phase-concentration counterexample remains a warning against relying only on broad horizon geometry. One can also test the screen phase discrepancy separately for initial states vs event-created plateaus and for dyadic scales q, which should reveal whether a useful nonasymptotic inequality is plausible.

No Lean kernel compilation was run and main was not modified. Issue #4 remains open. Twin-prime infinitude and original strict-record A166944 conjecture remain unresolved.

## 7. Reproduce

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/clock_episode_screen_audit.cpp -o /tmp/clock_episode_screen_audit
/tmp/clock_episode_screen_audit 4096 16384 65536 262144
```
