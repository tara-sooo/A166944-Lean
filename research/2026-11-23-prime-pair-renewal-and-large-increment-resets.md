# A166944 twin-prime-first research: composite prime-pair return energy and large-increment reset localization

2026-11-23 JST. Cross-Issue #3/#4 research; canonical squarefree clipped parity-GCD wheel. The results below are **elementary paper deductions**, with finite C++17 and independent literal-GCD Python tests, not Lean-kernel-checked. Twin-prime infinitude remains **OPEN**. This checkpoint follows `research/2026-11-23-twin-prime-signed-and-composite-ledger.md` on the Issue #3 branch and the high-q renewal notes on the Issue #4 branch.

## 1. The exact canonical wheel and what is being tracked

Fix a dyadic integer `X>=256` divisible by four; take odd `M` with `X<=M<2X`. Set `s=M+2`, `K=floor((7M-1)/4)`, `C(s)=2M-2`, and `B=ceil(sqrt(7X))`. For integer `n>s`, form `h(n)=gcd(n,C(n-1)-1)` for even `n`, `h(n)=gcd(n-2,C(n-1)+1)` for odd `n`; `d(n)` is the product of DISTINCT odd prime factors `p<=B` of `h(n)` (or 1 if none); `C(n)=C(n-1)+d(n)-1`. Let `G(M)=C(K)-(2M-2)` and `W_X=sum_M G(M)`. Both `C` and `G` are even. The canonical invariant is `2M-2<=C(n)<=2n`, including at event times. Thus

`0<=G(M)<=Gmax(M):=2K-(2M-2)<=3X` for all `M` in the dyadic interval. (G0)

At a nonunit event, `d` is odd, squarefree, and `d|n` at even n, `d|(n-2)` at odd n. If `m>=5` is ANY odd squarefree divisor of an event's `d` (including `m=p`, `m=pq`, or products of more factors), call this an **m-event**. Let `N_m(M)` count its m-events up to K. For prime pairs set `m=pq`, `p<q` distinct, and define the exact pair-capacity weight per event as `(p-1)(q-1) * d/(pq)`.

## 2. NEW simultaneous-prime-pair return packing lemma (PAPER)

**Lemma R (all odd squarefree divisors m>=5).** Suppose a fixed source M has m-event times `t_1<...<t_k`, `k>=1`, with clipped increments `d_i` divisible by m. Immediately after an even m-event, `C(t_i) ≡ 0 (mod m)`; immediately after an odd m-event, `C(t_i) ≡ -2 (mod m)`. To fire again, the pre-event horizon must satisfy `C(t_{i+1}-1)≡+1 (mod m)` (even event) or `≡-1 (mod m)` (odd event). Since the intervening non-m events add an even nonnegative growth amount

`E_i := C(t_{i+1}-1)-C(t_i)`,

it follows that:

* `E_i >= m-1` always;
* if `t_i` is odd, `E_i >= m+1`;
* the event clock positions obey `t_i ≡ 0 (mod 2m)` if even, `t_i ≡ m+2 (mod 2m)` if odd, so `t_{i+1}-t_i >= m-2`.

Each m-event contributes `d_i-1>=m-1`, and its successive recharge gaps are disjoint from m-event costs and from one another. Therefore the **exact deterministic energy packing inequality** is

`BOXED: (2 N_m(M)-1)*(m-1) <= G(M), whenever N_m(M)>=1.`  (R1)

Equivalently for k>=2, the source must pay at least `3(m-1)` growth for even two occurrences of the **same prime pair** m=pq. No random residue, CRT independence, or unproved spectral bound is used. The restriction m>=5 is essential: after an odd 3-event, C may already be 3-active, so the m=3 recharge assertion is false in general.

**Uniform dyadic exclusion:** By (G0), if `m> X+1`, `3(m-1)>3X>=G(M)`, so `N_m(M)<=1` for every M. This applies to ALL squarefree pair products `p*q>X+1`, even on an adversarial source. The per-source stronger exclusion is `m>1+Gmax(M)/3`.

**Renewal viewpoint:** For fixed pair m, the number of its subsequent returns is bounded by

`(N_m(M)-1)_+ <= max(0, (G(M)/(m-1)-1)/2)`.

It limits repetitions of a given pair, not its first simultaneous event, and is therefore not itself an upper bound on W_X or Pair_X.

## 3. NEW canonical quotient/resets lemma for large nonunit increments (PAPER)

Because `d|n` for even events and `d|(n-2)` for odd events, the quotients are parity restricted. An even event has `n/d` a positive EVEN integer, at least 2. An odd event has `(n-2)/d` a positive ODD integer; quotient 1 is **impossible** at the canonical cutoff K:

If `n-2=d`, then `d>=M+1>=8` and `C_pre>=2M-2>=K>=n=d+2`. But `C_pre≡-1 (mod d)` and is even, so it equals `a*d-1` for a positive odd integer a; `C_pre<=2(n-1)=2d+2` forces `a=1`, contradicting `C_pre>=d+2`. Thus the odd quotient is at least 3. Hence

`BOXED: n even -> d<=n/2<=K/2; n odd -> d<=(n-2)/3<K/3.` (Q1)

A **RESET** means the post-event deficit `x_post=2n-C(n)` is 0 or 6. If `d > K/4`, the even quotient must be 2 and the odd quotient must be 3 (since the next allowed quotient is 4 or 5). For an even event `n=2d`, parity and `C_pre≡1 (mod d)` plus `n<=K<=2M-2<=C_pre<=2n-2` force `C_pre=3d+1`, so `C(n)=4d=2n` and `x_post=0`. For an odd event `n=3d+2`, the analogous bound and `C_pre≡-1 (mod d)` force `C_pre=5d-1` (here d>=5), so `C(n)=6d-2=2n-6` and `x_post=6`. Consequently:

`BOXED: d(n)>K(M)/4 -> post-event x(n) in {0,6}.` (Q2)

For `M>=25`, at most THREE such `d>K/4` events can occur on one trajectory. Indeed `Gmax=2K-(2M-2)<K-4` for M>=25, whereas four d>K/4 would add more than `4*(K/4-1)=K-4` to G.

**Semiprime and reset localization:** Let `p<q` both divide an event's clipped increment, `m=p*q`. If `m>K/6`, the event must be **exactly** `d=m`, because a third distinct prime factor would make `d>=3m>K/2`, contradicting (Q1). If in addition `m>K/4`, it is an **exact semiprime RESET** of type 0 (even) or 6 (odd). Thus any individual large-pair collision event has a semiprime increment (the same pair can still recur at a later event); the correction of Pair_X over exact nonlinear surplus is supported on pairs of product `<=K/6`.

For the `m>K/4` class, each collision contributes precisely `(p-1)(q-1)<=m<=K/2<7X/4`, and there are <=3 such events per source. Let `E_X` denote the number of canonical starts possessing at least one *composite* reset with `d>K/4`. Then

`BOXED: 0<=Pair_X^{(m>K/4)} <= (21/4) * X * E_X.`  (Q3)

In particular, a hypothetical `E_X=o(X)` would imply `Pair_X^{(m>K/4)}=o(X^2)`. This isolates a specific first-collision source-dispersion question; **E_X=o(X) is not proved**.

## 4. First-vs-repeat *pair charge*, and tested false shortcuts

For each fixed M and prime pair p<q, let its pair-hit sequence be times n with `pq|d(n)`, and give each the exact capacity charge `(p-1)(q-1)*d(n)/(pq)`. Set `PairFirst_X` to the charge on the FIRST such hit for this source and pair, and `PairReturn_X` to charge on later hits. Then

`Pair_X=PairFirst_X+PairReturn_X` exactly, and the prior `Extra_X <= Pair_X` still holds. The combined OPEN sufficient condition for twin-prime infinitude can therefore be written as

`liminf_(dyadic X) (RepeatWeightedPrime_X + PairFirst_X + PairReturn_X) / X^2 <3/16`.

**False shortcut:** 'No prime pair can occur twice along a canonical source' is disproved by a fully literal original-clipped path at M=17373, B=339: m=3*7=21 occurs at (n,preC,d,postC) = `(17556,35050,21,35070)` and `(17808,35512,21,35532)`. Recharge E=35512-35070=442>=m-1. Both post deficits are positive (42 and 84), so these pair events are NOT resets. A separate actual source M=49 at cutoff B=31 has a composite d=33 event at n=66, preC=100, postC=132, reset x=0; thus 'composite resets never happen' is also false. Neither example is a counterexample to twin-prime infinitude.

## 5. Finite full-source auditor and independent integer-by-integer oracle

The C++ program **actually generates all canonical event clocks** and verifies: invariants and modulo event clocks, odd/even quotient bounds, large increment resets, prime and pair recharge lower bounds (and stronger odd-post bound), spacing, every source's pair packing R1, per-source maximum m, semiprimality above K/6, fixed-window regressions and pair charge. Run:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_prime_pair_renewal_audit.cpp -o /tmp/pair_renewal
/tmp/pair_renewal 256 512 1024 4096 16384 65536 262144
python3 research/twin_prime_prime_pair_renewal_literal.py 256 512 1024 4096
```

The independent Python oracle computes every original n, including unit increments, rather than jumping between prime clocks. It agrees with the event-jump output on X256/512/1024/4096, including W, prime hits/returns, pair hits/returns, charge and products. An additional literal single-source check confirmed both M=17373 pair-return events and M=49 composite reset. Finite tests do not prove the universal lemmas or any asymptotic claim.

| X | Pair_X | first pair charge | returning pair charge | pair incidences | returning pair incidences | max product of a repeated pair |
|--:|--:|--:|--:|--:|--:|--:|
| 4096 | 36,604 | 36,604 | 0 | 535 | 0 | — |
| 16384 | 342,248 | 329,764 | 12,484 | 4,396 | 249 | 143 |
| 65536 | 2,049,576 | 2,012,600 | 36,976 | 20,808 | 1,467 | 267 |
| 262144 | 9,898,872 | 9,719,848 | 179,024 | 99,791 | 6,926 | 95 |

At all tested X>=256, no event had d>K/4 and no pair product exceeded K/6; these are finite observations (and M49 exhibits a larger composite reset at a smaller canonical start). PairReturn/Pair was ~3.65% at X16384 and ~1.81% at X262144, suggesting **first simultaneous prime-pair collisions** are a key separate analytic target. This is not an asymptotic estimate. No dependency on the original A166944 strict-record conjecture is assumed.

## 6. Mathematical handoff

The q-deleted shadow/renewal machinery from Issue #4 can treat **returns of an individual q**, while Lemma R generalizes the necessary recharge to product labels m=pq. The event-time restrictions and large-reset lemma give a disjoint large-product class whose only possible events are isolated semiprime resets; all non-reset large prime-pair interactions lie below the K/4 barrier, and triples are confined to pairs m<=K/6. This gives a concrete three-way proof plan:

1. Source-weighted first pair clock dispersion (`PairFirst_X`), particularly the first semiprime reset sources `E_X` and intermediate pair products.
2. Product-label renewal anti-concentration for `PairReturn_X`, using at least `m-1` of source-local recharge per return and the source-conditional first-return operator.
3. Weighted individual prime return budget (`RepeatWeightedPrime_X`) in the exact final B-wheel; do not conflate with first appearance in an intermediate prime-insertion path.

All three asymptotic inputs remain OPEN. Their combined bound below 3X²/16 along arbitrarily large dyadic windows would prove infinitely many twin primes via the previously established terminal certificate. This note claims only the deterministic paper lemmas and finite reproducible computations, with no new Lean theorem or main-branch changes.