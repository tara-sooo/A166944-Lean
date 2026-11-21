# Exact event-word congruence obstruction for mixed-prime reuse

2026-11-22 JST. **Status:** new paper lemmas, elementary proofs, finite direct recurrence audit; **no new Lean kernel compilation**. This does not prove Cap B, the liminf event-count bound, or infinitely many twin primes.

This continues [prime/composite slow obstruction](2026-11-22-prime-composite-slow-obstruction.md) and [adaptive event count analysis](2026-11-22-adaptive-event-count-analysis.md). Its purpose is to probe the missing *cross-prime reuse* input with **exact** gcd first-hit divisibility, rather than adding the already known per-key `p-1` reuse growth estimates.

## 1. The exact one-hit source

The [Lean-proved moving-horizon event package](../A166944/Lemmas.lean) implies that at a nonunit event with increment `e=d(r)>1` and preceding even horizon `C`, **either `e | C-1` or `e | C+1`**, according to hit parity. Event horizon evolution is exactly `C'=C+e-1`. Every event increment at index at least three is odd. In particular, for any odd `e>1`, the pre-event horizon lies in the two residues `+1,-1` modulo `e`.

We consider **consecutive nonunit event-value words**, independent of their index gaps. Let

`W=(e_1,...,e_k)`, all `e_i` odd and at least 3, and `L(W)=sum_i(e_i-1)`.

A "double word" `WW` means the next `2k` consecutive nonunit events carry these values twice in exactly the same order; an "exact triple" `WWW` has three copies. All intervening unit steps are allowed and index gaps need not repeat. Crucially, the horizon before the corresponding event in the next copy is displaced by precisely `L(W)`, regardless of the gaps.

## 2. General double-word and triple-word theorems (paper)

**Two copies:**

`WW  =>  each e_i | one of L-2, L, L+2.`

Indeed, if the horizons before corresponding hits are `C` and `C+L`, both are `+1` or `-1` modulo `e_i`. Their difference is therefore `0,2,-2`. Equivalently,

`lcm(e_1,...,e_k) | L*(L-2)*(L+2)`.       (D)

This conclusion uses the exact gcd event divisibility, not a heuristic or event-count estimate.

**Three copies:**

`WWW => each e_i | L,` hence

`lcm(e_1,...,e_k) | L.`                  (T)

Proof: for each `e_i`, the three residues of `C,C+L,C+2L` belong to `{+1,-1}` modulo `e_i`. Two must coincide. If adjacent, `e_i|L`; if the first and third coincide, `e_i|2L`, and oddness of `e_i` gives `e_i|L`. This applies to composite increments as well as prime increments.

In particular, `WWW` is impossible whenever `lcm(e_i)>L`.

## 3. Exact exclusion of small mixed-value cycles

**Theorem (paper).** Suppose a word `W` consists of **two or three pairwise distinct odd numbers**, each at least 5, and each appearing once. The doubled word `WW` is impossible on *every* actual first-hit gcd path.

Proof for two values: arrange them as `a<b`. Then `L=a+b-2`. Since `b|L+t` for some `t∈{-2,0,2}`, it divides `a-2+t`, an integer strictly between 0 and `b`; contradiction.

Proof for three values: order them numerically `a<b<c` (the order of appearance need not be ascending), so `L=a+b+c-3`. From `c|L+t_c` and `t_c∈{-2,0,2}`, because `0<a+b-3+t_c<2c`, we obtain `c=a+b-h`, `h∈{1,3,5}`. The condition on `b` then says

`b | Y=2a-h-3+t_b`, `t_b∈{-2,0,2}`.

Here `0<=Y<2b`, and `Y` is even while `b` is odd. Consequently `Y=0`. Thus `2a=h+3-t_b<=10`, forcing `a=5, h=5, t_b=-2`, and then `c=a+b-5=b`, contradicting distinctness.

Examples excluded: `(p,q,p,q)` for distinct odd `p,q>=5`, and `(p,q,r,p,q,r)` for distinct odd `p,q,r>=5`. This generalizes the simple four-event alternating-reuse prohibition; it also handles prime/composite mixtures.

**Limitation of this exact proof:** length four is different. `W=(11,15,23,45)` has `L=90` and passes the necessary modular double-word test: `90 mod 11=2`, `90 mod 15=0`, `90 mod 23=21=-2`, `90 mod 45=0`. This is a counterexample **only to extending the modular numerical exclusion** to all four-value words. It is not claimed to be an executable gcd path; individual moduli may impose inconsistent simultaneous starting-horizon residues.

## 4. Product obstruction for arbitrary many distinct prime increments

When the `e_i=p_i` are pairwise distinct odd primes, (D) yields

`product_i p_i | (L-2)*L*(L+2)`,

and for `k>=2`, since the right side is positive,

`product_i p_i <= (L-2)*L*(L+2) < (L+2)^3.`   (P)

Consequently **a doubled word `WW` is impossible** whenever `product_i p_i > (L+2)^3`.

In the important square-root regime from the previous no-slow sparse-path reduction, fix constants `0<a<b`, and suppose `k>=4` is **fixed** and `a*sqrt(M)<=p_i<=b*sqrt(M)`, pairwise distinct. Then

`product_i p_i >= a^k*M^(k/2)`, whereas `(L+2)^3 <= (k*b*sqrt(M)+2)^3 = O_{k,b}(M^(3/2))`.

For every fixed `k>=4`, sufficiently large `M` makes the product bound impossible. For `k=2,3`, the stronger exact exclusions from section 3 work without a size threshold. Thus **no repeated fixed-length word of pairwise distinct primes in a common `Theta(sqrt M)` band**, once `M` is sufficiently large. This rules out exact short periodic blocks without requiring any repetition of index gaps.

The deduction does *not* bound the total event count: event-value words with differing order, recurring values within a block, growing block lengths, or aperiodic reuse can evade this test.

## 5. Relation to the F drawup target

Let `F(n)=4n-9D(n)`. The slow condition is exactly

`F(j)-F(i) >= 32+8*isqrt(D(j)+1)`.

Over a block of events with horizon growth `L` and index displacement `T`, its change is `Delta F=4T-9L`. The no-repeated-word congruences constrain `L`, but **do not determine `T`**: first-hit gaps can differ across word occurrences. Therefore they alone do not give a uniform positive `F` drawup or the missing global bound on prime event density. A future estimate must couple these modular word exclusions to *total index travel or growth* across many nonperiodic blocks, not just eliminate fixed short cycles.

This is also why paying every reappearance of prime `p` by the known `p-1` horizon growth (from [`TravelFactors.lean`](../A166944/TravelFactors.lean)) is not yet sufficient: events of other prime values can pay multiple overlapping reuse windows simultaneously, while the total available horizon growth at the canonical cutoff is `G<=2K-(2M-2)=(3/2)M+O(1)`.

## 6. Verification and next open target

The standard-library [finite audit](reuse_word_congruence_audit.py) checks:

- all 1,176 strictly increasing odd pairs and 18,424 strictly increasing odd triples in `[5,101]`, finding no double-compatible case;
- an explicit four-value modular example `(11,15,23,45)` that passes the *necessary* double-copy numerical filter;
- the **original recurrence** up to index 2,500,000, covering 17 genuine canonical records with `K<=2,500,000`, and 228 nonunit events in those cutoff windows. For word lengths `1..15` there were three doubled words, all `(3,3)`, and no triple words; all satisfy the general lemmas.

The script executed successfully. These tests corroborate the arithmetic but do not prove the general statements. The two- and three-value prohibitions are proved on paper above; **no new Lean declaration, no Cap B closure, and no twin-prime proof** is claimed.

**Specific missing mathematical input:** rule out, or force an unbounded `F` drawup within, the **nonperiodic, multi-prime** first-hit schedules with `Theta(sqrt M)` long prime events and possible overlapping reuse windows. Excluding short repeated words is one genuine new restriction on such schedules, but an asymptotic packing/capacity inequality remains to be established.
