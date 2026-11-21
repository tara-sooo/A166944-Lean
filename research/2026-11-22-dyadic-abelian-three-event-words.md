# Dyadic three-value Abelian-square obstruction in A166944 event words

2026-11-22 JST. **Status:** a new unconditional *local* paper lemma from exact gcd-event divisibility, a finite standard-library audit, and a general fixed-ratio bound. **No new Lean compilation, no global Cap B proof, and no proof of infinitely many twin primes.**

This follows [the repeated-event-word congruence note](2026-11-22-reuse-word-congruence-obstruction.md) and its earlier distinction between periodic exact words and aperiodic multikey reuse.

## 1. Scope and arithmetic source

At any genuine nonunit event of the original A166944 recurrence, let `e=d(r)>1` and `C=D(r-1)` (the pre-event horizon). The event-divisibility branch in [`Lemmas.lean`](../A166944/Lemmas.lean), also encoded in [`ReuseCongruences.lean`](../A166944/ReuseCongruences.lean), gives `e|(C-1)` or `e|(C+1)`; `e` is odd and `D` increases by exactly `e-1` at that event. Unit increments leave `D` constant.

If two occurrences of the *same* odd `e>=5` have intervening pre-horizon displacement `Delta`, both starting horizons are `+1/-1 mod e` and `Delta` is even. Therefore

`Delta = 2*k*e + epsilon` for some `k>=0` and `epsilon in {-2,0,2}`.      (1)

For occurrences in a six-event word containing each of three values twice, `Delta>=e-1>=4`, hence `k>=1`. A consecutive pair `e,e` has `Delta=e-1` and is impossible for `e>=5`. The older note proves that a four-event `p,q,p,q` and a six-event `a,b,c,a,b,c` are impossible when all involved values are pairwise distinct odd >=5.

Throughout, **an Abelian square of length three** means two adjacent blocks of three *consecutive nonunit event values*, each block containing the same three pairwise distinct values, possibly in a different order. Unit steps may occur between those events.

## 2. Main dyadic theorem (paper proof)

> **Theorem.** Let `a,b,c` be pairwise distinct odd integers >=5 with
>
> `max(a,b,c) <= 2*min(a,b,c)`.
>
> No genuine A166944 event path can contain six consecutive nonunit events whose first three values are `(a,b,c)` and whose final three values are any permutation of `(a,b,c)`.

This statement applies to composite increments as well as primes, and uses no hypothesis about record attainment, the Cap B cutoff, or asymptotic size.

**Proof.** Let the second block be a permutation `sigma` of `(a,b,c)`.

- `sigma=(a,b,c)` is excluded by the existing exact three-value double-word lemma.
- `sigma=(c,a,b)` or `(c,b,a)` begins with `c`, immediately following the first block's final `c`; two consecutive equal increments >=5 are impossible.
- `sigma=(b,c,a)` contains the adjacent four-event subword `b,c,b,c`, excluded by the exact two-value double-word lemma.

Only the two adjacent transpositions remain.

**Case A: `sigma=(a,c,b)`.** The event word is `a,b,c,a,c,b`. The consecutive occurrences of `c` have pre-horizon displacement `Delta_c=a+c-2`. By (1), `c` divides one of `a-4,a-2,a`. Because `a,c` are distinct odd integers >=5 and `a<=2c`, this forces `a=c+2` or `a=c+4` (the alternative `a<c` makes all three positive candidates smaller than `c`).

Put `delta=a-c in {2,4}`. The two occurrences of `a` have displacement `Delta_a=a+b+c-3`. Since `b<=2c`, one has `2<Delta_a<4a-2`. By (1), necessarily `Delta_a=2a+epsilon_a` with `epsilon_a in {-2,0,2}`, so

`b=delta+3+epsilon_a in {delta+1,delta+3,delta+5}`.

Together with pairwise distinctness, oddness, >=5, and the dyadic ratio, these conditions leave exactly eight ordered triples:

```text
(a,b,c) = (9,5,7), (11,7,9), (13,7,11), (9,7,5),
          (13,7,9), (11,9,7), (15,9,11), (17,9,13).
```

But the two `b` occurrences have `Delta_b=a+b+2c-4`. The corresponding residues `Delta_b mod b`, in order, are `4,4,3,1,6,3,6,3`; none is in `{0,2,b-2}`. This contradicts (1).

**Case B: `sigma=(b,a,c)`.** The word is `a,b,c,b,a,c`. The two `b` events have `Delta_b=b+c-2`, so the same argument gives `c=b+2` or `c=b+4`. The two `c` events have `Delta_c=a+b+c-3<4c-2`, thus `Delta_c=2c+epsilon_c` and `a=(c-b)+3+epsilon_c<=9`. The remaining eight triples are

```text
(a,b,c) = (5,7,9), (7,9,11), (7,11,13), (7,5,9),
          (7,9,13), (9,7,11), (9,11,15), (9,13,17).
```

The two `a` events have `Delta_a=a+2b+c-4`, producing residues `Delta_a mod a` of `4,4,3,1,6,3,6,3`, again forbidden by (1).

All six permutations are excluded. QED.

## 3. A coarse quantitative bound for any fixed ratio

There is also a general, size-independent **parameterized upper bound**. For a real `R>=1`, assume `max(a,b,c)<=R*min(a,b,c)` and two adjacent three-value blocks are multiset-equal. Then

`max(a,b,c) <= 42*(5*R+4)^2.`                       (2)

The four permutations excluded above remain impossible for every `R`, by the earlier two-/three-letter exact-word exclusions and the immediate-repeat exclusion. For either surviving adjacent transposition, write `E=max(a,b,c)`. Each corresponding pre-horizon displacement is a sum of at most five event-growth values, and hence `0<Delta_i<5E`. By (1), `Delta_i=k_i*e_i+epsilon_i` with even integers `k_i>=2`, `k_i<=5R+2` and `|epsilon_i|<=2`.

Writing `v=(a,b,c)^T`, the three displacement equations are `(A-diag(k_a,k_b,k_c))*v=t+epsilon`, where `A` has entries in `{0,1,2}` and each coordinate of `t+epsilon` has absolute value at most 7.

For `sigma=(a,c,b)`:

```text
A = [1 1 1; 1 1 2; 1 0 1].
```

For `sigma=(b,a,c)`:

```text
A = [1 2 1; 0 1 1; 1 1 1].
```

Put `u=k_a-1`, `v'=k_b-1`, `w=k_c-1`, all *odd*. The determinants are respectively

`-u*v'*w+v'+w+2` and `-u*v'*w+u+v'+2`.

Both are **odd and nonzero**. Every matrix entry has absolute value at most `5R+4`. Cramer's rule, together with the six-term expansion of a 3x3 determinant, bounds each coordinate of the solution by `6*7*(5R+4)^2/1`, yielding (2).

Taking `R=2` in (2) gives `E<=8232`; section 2 proves the stronger **absolute exclusion for every E**, not just E>8232.

## 4. Boundary and relevance to the open global packing problem

The coefficient `2` in the theorem describes the diameter of the *three values*, not the entire record path. The proof applies only when the six events are consecutive nonunit events. Small or large intervening event values can evade its configuration; arbitrary longer nonperiodic schedules are not excluded.

The necessary congruence condition *can* pass outside the dyadic ratio: the blocks `(5,19,23)` and `(19,5,23)` are compatible modulo the three increments, though their actual gcd realizability is not asserted.

Even inside a dyadic band, the four-value blocks

`(7,13,9,11)`, `(9,7,11,13)`

pass the corresponding necessary congruence test. Their pre-horizon displacements for values 7, 9, 11, 13 are respectively 44, 18, 24, 54. This is **not** a demonstrated actual gcd path. It shows that the three-value argument cannot simply be copied to all four-value blocks.

The theorem strengthens the earlier exact-word restriction from identical *order* to identical *multiset* for three distinct nearby values. However, it does **not** yet provide an asymptotic upper bound on the number of long prime first-hit events, a Hall/charging bound on overlapping reuse intervals, or an unbounded `F=4n-9D(n)` drawup. One can write abstract aperiodic words over a sufficiently large alphabet that avoid all these short forbidden patterns while reusing each letter many times. The exact gcd and first-hit constraints of such long schedules remain the unresolved target.

## 5. Reproducibility

[`dyadic_abelian_three_audit.py`](dyadic_abelian_three_audit.py) uses Python 3 standard library only. It checks:

1. All **16 small residual cases** from the two paper-proof transpositions.
2. All **663,264** ordered pairs of three-distinct-odd-value blocks with values in `[5,101]`: 250 pass the basic necessary modular tests, but **zero** have maximum/minimum <=2.
3. The four-value congruence-only witness above.
4. The **original recurrence from a(1)=2** through index 2,500,000: 17 attained canonical records with their cutoff windows fully covered and 228 nonunit events; zero adjacent three-block multiset repeats with three distinct values >=5.

Audit executed locally successfully and prints `PASS`. Finite tests corroborate the paper proof; the universal theorem is supported by the symbolic case analysis in section 2, **not by finite enumeration**. No Lean kernel verification, Prove2Me submission, Cap B proof, or twin-prime proof has been produced here.
