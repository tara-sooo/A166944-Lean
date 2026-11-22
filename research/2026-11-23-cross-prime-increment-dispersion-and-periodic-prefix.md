# A166944: past-prime increments, future-residue dispersion, and a finite-prefix CRT theorem

Date: 2026-11-23 JST. Parent [#1](https://github.com/tara-sooo/A166944-Lean/issues/1); assigned research child [#3](https://github.com/tara-sooo/A166944-Lean/issues/3). Dedicated branch `research/issue-3-cross-prime-correlation`. Starts from public baseline `bd180e3de0fe6e12cc3c3ea25d65a985445344eb` and the [earlier four-residue aggregate note](2026-11-23-cross-prime-four-residue-correlation.md).

**Evidence levels:** The identities, causal shift-conjugacy and CRT inequality below have mathematical proofs. Finite numeric tables, finite-state absorption bounds and the resulting *explicit six-prime instance* rely on checked C++17 enumeration, NOT Lean kernel proofs. No asymptotic estimate for all growing primes has been proved. Twin-prime infinitude and the original A166944 conjecture remain OPEN.

## 1. Exact signed increment / future-prime correlation decomposition

For even `X>=256`, write `B=ceil(sqrt(7X))`, `U=2X+floor((3B+7)/2)+5` and `V_X={v odd:X<=v<U}`. Fix `P(v)=v(v-1)(v-3)(v-5)`.

Let the odd primes `q=3,5,...` below `B` be listed in order; define `L_q=product_{3<=r<=q, r prime} r` and `G_q(v)=G_{L_q}(v)` using the **same** natural terminal index `K(v)=floor((7v-1)/4)` for every cutoff, with `G_1(v)=0`. Set

    delta_q(v) = G_q(v) - G_{q^-}(v).
    I_p(v) = 1 if p divides P(v), otherwise 0 (p>=11).
    W_{>q}(v) = sum_{q<p<=B, p>=11 prime} p*I_p(v).
    J_q = #{p prime: q<p<=B and p>=11}.
    A_q(v) = W_{>q}(v) - 4*J_q.
    D_q = sum_{v in V_X} delta_q(v)*A_q(v).

The four roots are distinct modulo each p>=11. By the prime-prefix telescope, changing the order of the *finite* sums gives the exact identity

    E_{X,2} = sum_{p>=11} p*sum_{v in V_X} I_p(v)*G_{p^-}(v)
            = sum_{q<=B} sum_{v in V_X} delta_q(v)*W_{>q}(v)
            = 4*sum_{q<=B} J_q*sum_{v in V_X} delta_q(v)
                + sum_{q<=B} D_q.

The centered-term baseline equals `4*sum_{11<=p<=B}sum_{v in V_X}G_{p^-}(v)`. The exact Fourier form, with `e(x)=exp(2*pi*i*x)`, is

    D_q = sum_{q<p<=B, p>=11} sum_{a=1}^{p-1} S_p(a)*F_q(a/p),
    S_p(a) = sum_{r in {0,1,3,5}} e(-a*r/p),
    F_q(theta)= sum_{v in V_X} delta_q(v)*e(theta*v).

Indeed, `p*I_p(v)-4 = sum_{a=1}^{p-1} S_p(a)*e(a*v/p)` by additive character orthogonality. This is a **bilinear dispersion identity**, NOT a useful upper bound without new information about the adaptive `delta_q`.

**Signed caveat:** `delta_q(v)` can be negative. One direct *literal-step parity-GCD* example (all cutoffs share `K(619)=1083`): for `v=619`, `G_11(v)=24`, `G_13(v)=12`, hence `delta_13(619)=-12`. The C++ diagnostics cross-check the event-jump model against the literal gcd for small cases and verify this example.

## 2. Reproducible dyadic experiment and the explicit Cauchy-Schwarz loss

Compile and run [cross_prime_increments_audit.cpp](cross_prime_increments_audit.cpp):

    g++ -std=c++17 -O3 -Wall -Wextra research/cross_prime_increments_audit.cpp -o /tmp/cross_prime_increments_audit
    /tmp/cross_prime_increments_audit 4096
    /tmp/cross_prime_increments_audit 16384
    /tmp/cross_prime_increments_audit 65536

It calculates every `G_q(v)` using exact parity-specific first-hit event skipping. Its independent *literal step-by-step gcd* cross-check covers odd `7<=M<=111` at caps `1,3,5,7,11,13`; it also asserts an explicit negative-stage witness, the source-by-source algebraic identity, the total identity and the regression values below.

| X | B | exact E | exact baseline | sum_q D_q | sum_q abs(D_q) | sum_{q,v} abs(delta_q) |
|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 170 | 36,344,568 | 37,822,496 | -1,477,928 | 3,834,200 | 524,818 |
| 16384 | 339 | 485,635,362 | 481,859,104 | +3,776,258 | 49,171,738 | 4,161,244 |
| 65536 | 678 | 5,672,417,264 | 5,769,264,200 | -96,846,936 | 486,681,372 | 23,562,646 |

The test is already strong enough to reject an implicit *monotone-in-prime* replacement: sum of positive per-stage variations differs from the final growth, and the difference is real.

Define `H2=sum_{q,v}delta_q(v)^2` and `A2=sum_{q,v}A_q(v)^2`. Cauchy-Schwarz permits the *valid but weak* global bound `abs(sum_q D_q)<=sqrt(H2*A2)` and the stagewise bound `sum_q abs(D_q)<=sum_q sqrt((sum_v delta_q(v)^2)*(sum_v A_q(v)^2))`.

| X | H2 | A2 | stagewise Cauchy upper | actual sum_q abs(D_q) |
|---:|---:|---:|---:|---:|
| 4096 | 128,169,316 | 546,493,909 | 208,714,200 | 3,834,200 |
| 16384 | 3,330,039,128 | 13,668,623,643 | 4,722,522,408 | 49,171,738 |
| 65536 | 25,725,426,668 | 374,377,649,407 | 75,990,000,170 | 486,681,372 |

So direct `L2 x L2` has a factor ~54, ~96, ~156 loss *even against the sum of absolute stagewise correlations* at these scales (much worse against the fully signed sum). Merely invoking a general large sieve/Cauchy bound, without a new dynamical cancellation principle, does not explain the measured dispersion.

The stagewise `sum_q abs(D_q)` (rather than requiring cancellation between different `q`) is itself only ~8.6–10.5% of the raw positive `E` at these three sizes. This suggests an achievable stronger candidate:

    sum_{q<=B} abs(D_q) = O(X*B^2/log B).       [OPEN]

**Important separate obstruction:** This alone controls only the centered correlation. The baseline `4*sum_p sum_v G_{p^-}(v)` also needs `O(X B^2/log B)` to bound E. Further, E controls only the bounded-old-growth, height-zero, one-shot subset, not the full prime-stage signed growth or A166944.

## 3. Universal causal translation / finite-state lemma (paper proof)

For ANY odd squarefree wheel `L`, start the infinite `L`-clipped parity-GCD recursion from **odd** `v>=1` with `s=v+2` and `D(s)=2v-2`; use `d_L(n)=gcd(L, gcd(n,D(n-1)-1))` for even n and `gcd(L,gcd(n-2,D(n-1)+1))` for odd n. Do not stop the recurrence at the natural cutoff while proving the following congruence property.

**Lemma C (causal shift-conjugacy):** For odd `v' = v+2Lt` with `t>=0`, the complete relative increment streams are identical:

    d_L^(v')(v'+2+k) = d_L^(v)(v+2+k)  for every integer k>=1.

**Proof:** At the canonical seed, the times differ by `2Lt`, the initial even horizons differ by `4Lt`, and both trajectories therefore have the same parity, time residue mod `L` and horizon residue mod `L`. Every clipped gcd uses only these residues, so its increment is identical. Both horizons then gain the same increment-minus-one, preserving the congruence. Induct on the relative time k. QED.

The modular process has at most `2L^2` states `(time mod 2L, horizon mod L)` and is deterministic. Any state with `gcd(L,C-1)=gcd(L,C+1)=1` is *absorbing*: all future clipped increments equal 1. If every odd canonical residue reaches absorption by relative time `T_L`, then its entire infinite-time total growth `G_L^infty(v)` is periodic in `v mod 2L`, and whenever `K(v)-(v+2)>=T_L`, the natural cutoff `G_L(v)` equals `G_L^infty(v)`.

This lemma does **not** assert that every odd squarefree wheel absorbs, nor any universal upper bound on `T_L` as L grows.

### Finite exhaustive C++ certificates (not Lean)

The independent [finite automaton scanner](squarefree_finite_automaton_audit.cpp) traversed **all** modular states (not merely canonical starts) for the first four primorials:

| largest prime q | L_q | all 2 L_q^2 states | directed cycles | cycles with positive growth |
|---:|---:|---:|---:|---:|
| 3 | 3 | 18 | 1 | 0 |
| 5 | 15 | 450 | 3 | 0 |
| 7 | 105 | 22,050 | 15 | 0 |
| 11 | 1155 | 2,668,050 | 135 | 0 |

Every cycle in these four finite graphs is an all-unit (absorbing) cycle. The independent [canonical-residue terminal scanner](small_prefix_terminal_audit.cpp) enumerates **every** odd canonical seed residue modulo `2L_q`, including q=13 and 17, and checks the first absorbing time and terminal growth:

| q | L_q | canonical residues | max steps until safe | max infinite-time growth | `A_q=sum_(odd residue mod2Lq) abs(delta_q^infty)` | # negative delta residues |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 3 | 5 | 4 | 6 | 0 |
| 5 | 15 | 15 | 17 | 10 | 36 | 0 |
| 7 | 105 | 105 | 48 | 28 | 360 | 0 |
| 11 | 1155 | 1155 | 114 | 98 | 5,820 | 0 |
| 13 | 15015 | 15,015 | 157 | 148 | 81,000 | 145 |
| 17 | 255255 | 255,255 | 239 | 316 | 1,548,744 | 1,283 |

Each enumerated phase was stepped until both neighbor gcds became one, using integer arithmetic (for q<=17, at most the recorded 239 steps), and the above results are regression assertions. *The integer computations are finite evidence, not a substitute for Lean verification of these finite claims.*

For every odd v>=323, the natural cutoff has `K(v)-(v+2)>=239`. Therefore all the six listed `G_q(v)` and their `delta_q(v)` coincide with their terminal values and are exactly periodic in `v mod 2L_q` over the dyadic windows `X>=512`. Already q<=13 is covered for X>=256, since then `K(v)-(v+2)>=190>157`.

## 4. Fixed-prime CRT decorrelation theorem (paper proof + six-prime numeric input)

Suppose one fixed q has the cutoff-independent periodicity from Lemma C and the absorption criterion throughout the odd v interval. Fix p>q prime with p>=11. Since gcd(p,2L_q)=1, the values of v in any fixed odd class `r mod 2L_q` run through each of the p residues **once per p consecutive class occurrences**. Thus for a finite contiguous odd interval V,

    abs(sum_{v in V, v=r mod 2Lq} (p*I_p(v)-4)) <= 4*p.

Multiplying by the **constant** `delta_q(r)` on that residue class and summing gives

    abs(sum_{v in V} delta_q(v)*(p*I_p(v)-4))
       <= 4*p*A_q.

Then summing future primes and using the triangle inequality yields the exact CRT bound

    BOXED: abs(D_q) <= 4*A_q * sum_{q<p<=B, p>=11} p.

Consequently the finite C++ results above give, **for all X>=512, conditional only on the exhaustively checked small fixed-prefix absorption table**,

    BOXED: sum_{q in {3,5,7,11,13,17}} abs(D_q)
           <= 4*(1,635,966)*sum_{11<=p<=B} p
           = O(B^2/log B) = o(X*B^2/log B).

The standard estimate `pi(B)=O(B/log B)` is only used in writing the sharper `O` form; the weaker elementary bound `O(B^2)` is also negligible relative to the conjectured target as X grows. **This is an actual small-fixed-prime decorrelation result**, with an elementary proof and a finite C++-checked numerical premise. It does not require an assumption of probabilistic independence, and is valid despite negative `delta_13` and `delta_17`.

For example, the full q=17 terminal table covers 255,255 canonical congruence classes. Its absolute residue variation `A_17=1,548,744` is finite and independent of X; no issue arises from the natural cutoff for X>=512. The constant is too large to give a useful estimate at the already scanned finite dyadic sizes; its value is **asymptotic separation**, not a full quantitative growth bound.

## 5. Where an extension could actually solve the missing correlation

1. **Large q remains:** An `O(B^2)` CRT bound for *finitely many fixed q* is negligible, but the primorial `L_q` grows exponentially, so `A_q` and the finite-state window explode with q. The next problem is a **uniform in growing q**, potentially two-scale variant, not further checking a few fixed primes.
2. **A time-sliced version is true at every q:** for any fixed relative time k, `d_{L_q}(v+2+k)-d_{L_{q^-}}(v+2+k)` depends only on `v mod 2L_q`. Natural horizon `K(v)-(v+2)>=k` selects a contiguous suffix of the odd v interval. Its CRT error is bounded by a corresponding four-residue `4p*sum_residue(abs(step difference))`. Summing over times is universally valid but currently loses too much because it pays all phase residues at every step. A multiscale/renewal argument that controls the **effective active phase mass** could yield a nontrivial growing-q bound.
3. **The large-sieve loss is quantitative:** direct `L2` Cauchy gives 54–156 times the *stagewise* absolute correlation even at the finite scales above. Fourier decomposition is exact but the proof would have to use the special support/renewal structure of `delta_q`, not just its total second moment.
4. **The baseline is independent:** a dispersion estimate for the centered term cannot bound the uncentered mean term without a corresponding first-moment growth/renewal estimate. The positive postfreeze height>=1 and repeated-p cost barriers documented in the parent Issue also remain.

### Reproducibility / provenance

Build commands:

    g++ -std=c++17 -O3 -Wall -Wextra research/cross_prime_increments_audit.cpp -o /tmp/cross_prime_increments_audit
    g++ -std=c++17 -O3 -Wall -Wextra research/squarefree_finite_automaton_audit.cpp -o /tmp/squarefree_finite_automaton_audit
    g++ -std=c++17 -O3 -Wall -Wextra research/small_prefix_terminal_audit.cpp -o /tmp/small_prefix_terminal_audit

Runs:

    /tmp/cross_prime_increments_audit 4096
    /tmp/cross_prime_increments_audit 16384
    /tmp/cross_prime_increments_audit 65536
    /tmp/squarefree_finite_automaton_audit 3 all
    /tmp/squarefree_finite_automaton_audit 5 all
    /tmp/squarefree_finite_automaton_audit 7 all
    /tmp/squarefree_finite_automaton_audit 11 all
    /tmp/small_prefix_terminal_audit

No additional Lean compilation was done. This child Issue #3 remains OPEN for the missing uniform dynamic dispersion and original mean-growth conditions; #1 remains the full conjecture gate.
