# Four-value Abelian-square classification and frozen-factor first-hit obstruction

2026-11-22 JST. **Research status:** new paper algebra, a standard-library *finite integer certificate* for four-value words, and a paper obstruction eliminating one all-prime candidate. Neither the Cap B mission nor the twin-prime conjecture is proved. No new Lean kernel theorem was compiled for these deductions.

Continuation of [three-value dyadic Abelian-square obstruction](2026-11-22-dyadic-abelian-three-event-words.md) and [mixed-prime event-word congruence restrictions](2026-11-22-reuse-word-congruence-obstruction.md). Source of the exact recurrence/divisibility and reuse-index residues: [`A166944/Lemmas.lean`](../A166944/Lemmas.lean), [`A166944/ReuseCongruences.lean`](../A166944/ReuseCongruences.lean), and [`A166944/FirstHitArithmetic.lean`](../A166944/FirstHitArithmetic.lean).

## 1. A four-letter finite reduction

Suppose eight successive nonunit event values have the form

`(e0,e1,e2,e3, e_{sigma(0)},e_{sigma(1)},e_{sigma(2)},e_{sigma(3)})`,

where the `ei` are pairwise distinct odd integers `>=5` and `max(ei)<=2*min(ei)`. Unit increments between events are permitted and are ignored in the word. The second block is a **permutation**, not necessarily a copy in the same order.

For each value `ei`, let `Delta_i` be the increase of `D` between the *pre-event* horizons of the two occurrences. Event horizon growth is `e-1`, hence

`Delta_i = sum_j A_ij*(e_j-1)`,

where `A_ij` counts occurrences of letter `j` between the two occurrences of letter `i`, **including the first and excluding the second**. The `4x4` matrix `A` has entries `0,1,2`; its row sums are between 1 and 7.

At both occurrences, the exact first-hit divisibility forces the pre-horizon to be `+1` or `-1 mod ei`. Hence

`Delta_i = q_i*e_i + eps_i`, with `eps_i in {-2,0,2}`.

Because each `ei` is odd and each `Delta_i` is even, `q_i` is **even**. Since `Delta_i>=ei-1>=4`, `q_i>=2`. The dyadic bound and at most seven intervening increments imply

`Delta_i <= 7*(E-1)<7*E <=14*ei` (`E=max(ei)`),

so `q_i<=14`. Thus `q_i in {2,4,6,8,10,12,14}`.

Writing `Q=diag(q0,q1,q2,q3)`, `e=(ei)`, `r_i=sum_j A_ij`, the necessary conditions are the **integer linear system**

`(A-Q)*e = r+eps.`                                             (1)

The occurrence order in the first block is used as the letter labelling, so checking all 24 permutations of the second block covers every possible two-block order.

Eight permutations contain either adjacent equal values `e,e` (impossible for `e>=5`) or an alternating four-letter subword `e,f,e,f` (impossible for distinct odd `e,f>=5` by the earlier paper lemma). For the remaining 16 permutations, there are exactly `16*7^4=38,416` coefficient matrices.

## 2. Exhaustive integer certificate: all surviving values <=175

[`four_value_abelian_first_hit_audit.py`](four_value_abelian_first_hit_audit.py) checks every matrix in (1) using **only Python's integer arithmetic and standard library**. It computes signed `3x3` cofactors and the exact `4x4` determinant; no floating-point rounding, numerical linear solver, or external primality package is used.

- **38,259 nonsingular systems:** the adjugate formula yields all exact integer solutions for every `eps in {-2,0,2}^4`; retain only positive odd, pairwise distinct dyadic values.
- **157 singular systems:** each has a nonzero left-null row of the adjugate. For all 81 permitted `eps`, that row has nonzero dot product with the right-hand side, so **none is solvable**.
- The complete necessary-congruence enumeration retains exactly **98 ordered pairs of four-letter blocks**. Their maximum increment is **175**.
- Exactly **four** ordered pairs have *all four increments prime*, all using the set `{109,127,131,163}`:

```text
(109,163,127,131) | (127,109,163,131)
(131,109,163,127) | (131,127,109,163)
(131,163,109,127) | (131,127,163,109)
(163,109,127,131) | (127,163,109,131)
```

**Result (finite-certified, not yet Lean formalized):** an actual gcd first-hit path with two successive four-event blocks containing the same four distinct odd increments in a dyadic band **must have maximum increment <=175**. In particular, it cannot realize such a pattern with any increment >=176.

The 98 outputs and four all-prime candidates are only **necessary-congruence compatible**, not verified actual event paths. This is a classification of a local word type, not a bound on the event count in an arbitrarily long aperiodic path.

## 3. Frozen-divisor run lemma (paper proof)

A complementary first-hit fact addresses the *index travel*, which the horizon-congruence system (1) omits.

> **Frozen-factor lemma.** Let `q` be an odd prime, `s<t` with `s>=2`, and suppose `q | D(s)-1` or `q | D(s)+1`. Suppose all increments `d(n)` for `s<n<t` satisfy `d(n)≡1 (mod q)`, and the final increment `d(t)` is **not divisible by `q`**. Then
>
> `t-s < 2*q.`                                                    (2)

Proof: the intermediate growth `d(n)-1` is divisible by `q`, so `D(n)≡D(s) (mod q)` up to index `t-1`. If `q|D(s)-1`, every even multiple of `q` forces an increment divisible by `q`; if `q|D(s)+1`, every odd index `n` satisfying `n-2≡0 (mod q)` does the same. Either residue class has period `2q`. If `t-s>=2q`, there is a forced `q`-hit in `(s,t]`, contradicting the intermediate congruence or the terminal coprimality. QED.

This is a **whole-run** bound: several large-prime events with increments `1 mod q` cannot use up `2q` index positions while `q` remains an active divisor of the horizon's adjacent number. It is stronger than merely applying the ordinary `gap<=2q` estimate separately to each event. For `q=3`, the full run has at most five index steps.

## 4. First-hit exclusion of an earlier four-value congruence witness

The older research note had exhibited

`(7,13,9,11 | 9,7,11,13)`

as satisfying the necessary **horizon** congruences. It is **not** an actual first-hit event word.

The projected factor sieve retains only the known factors of `P=9*7*11*13=9009`. The reuse-residue conditions force the starting horizon to satisfy

`C0≡6 (mod 7,11,13)`, and `C0≡1 or -1 (mod 9)`.

An odd first event `7` requires index `r1≡9 (mod 14)`. For each possible `r1 mod 2P`, check that the gcd with the **known factors** is exactly 7; then repeatedly take the first following index where the known-factor gcd exceeds one. At every stage the desired event value must be that known-factor gcd. This is an **overapproximation** of the true recurrence, since unknown factors could only force an *earlier* hit or increase the gcd.

The exact projected survivor counts after successive events `7,13,9,11,9,7,11,13` are

```text
C0 mod 9 =  1:   1287, 87, 29, 29, 9, 9, 9, 0
C0 mod 9 = -1:    858, 30, 10,  0, 0, 0, 0, 0
```

There is no full word even in the larger projected-factor model. The same standard-library script reproduces these counts. Importantly it computes `gcd(test_index, gcd(C +/- 1, P))` rather than taking a gcd with an arbitrary representative of `C mod P`: only factors of `P` may be used as known divisors.

## 5. Paper exclusion of one all-prime modular candidate using q=3

The four all-prime candidates are *not* automatically actual first-hit words. The following one can already be ruled out analytically:

`W=(131,163,109,127,131,127,163,109).`

Write event indices `r1<...<r8`, gaps `gi=ri-r(i-1)`, and `C0` for the pre-horizon of the first event. The pre-horizon offsets of the eight events relative to `C0` are

`0,130,292,400,526,656,782,944.`

For the repeated prime factors, the [Lean-proved parity/index residues](../A166944/ReuseCongruences.lean) force:

```text
131: event 1 odd -> event 5 even, (r5-r1) mod 262 = 129
127: event 4 odd -> event 6 even, (r6-r4) mod 254 = 125
109: event 3 even -> event 8 odd, (r8-r3) mod 218 = 111
163: events 2 and 7 same parity,     (r7-r2) mod 326 = 0
```

If `C0≡0` or `1 (mod 3)`, then after the first 131-event the horizon is `C0+130≡1` or `2 (mod 3)`. The increments at events 2, 3, 4 are `163,109,127≡1 (mod 3)`; event 5 has increment 131 coprime to 3. By (2), `r5-r1<=5`, contradicting the reuse congruence `r5-r1≡129 (mod 262)`.

If `C0≡2 (mod 3)`, then after event 5 the horizon is `C0+656≡1 (mod 3)`. The increments at events 6, 7, 8 are `127,163,109≡1 (mod 3)`. Hence

`g6+g7+g8=r8-r5<=5.`                                 (3)

From factor 127, `g5+g6≡125 (mod 254)`. The first-hit divisor gap bound gives `g5<=2*131=262`; from (3), `g6<=5`. Thus `g5+g6=125`.

From factor 109, `g4+g5+g6+g7+g8≡111 (mod 218)`. Here `g4<=2*127=254`, and `2<=g7+g8<=4`. The total lies between 128 and 383; the only number in that range congruent to 111 modulo 218 is 329. Consequently

`g4+g7+g8=204.`

From factor 163, `r7-r2=g3+g4+g5+g6+g7=g3+329-g8` must be divisible by 326. Yet `1<=g3<=2*109=218`, and (3) gives `1<=g8<=3`, so

`327 <= r7-r2 <= 546.`

There is no multiple of 326 in that interval. Contradiction.

Thus this particular prime-only word is **impossible**, even though it passed the horizon-only congruence classification.

The other three prime-only modular words are not excluded by this argument. Their full realizability is still unknown.

## 6. Relevance to Cap B, and the remaining obstruction

The project now has local exclusions for Abelian squares of length 2 and 3, a computer-assisted finite bound for length 4 in a dyadic band, and a frozen-prime run lemma linking *horizon residues* to *total index travel*. The last lemma is directly relevant to bounding `F(n)=4n-9D(n)`, because it prevents an active small factor from being bypassed by many distinct large primes with unchanged residue class.

However these restrictions do **not** imply `N_M=o(sqrt M)`, `liminf(P_M/sqrt M + sqrt(27/32)*sqrt(Q_M/M))<0.2283...`, or cofinally many slow intervals for the authentic record sequence. Long nonperiodic words with changing prime keys and changing small-prime phases are not yet controlled. An asymptotic capacity/packing estimate that includes these phase changes remains open.

**Reproduction:** `python3 research/four_value_abelian_first_hit_audit.py`. Local independent Python standard-library execution matched the exact classification and the projected-sieve counts; repository-side code and this note have not been kernel-checked in Lean.
