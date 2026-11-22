# A166944 return-span entropy: a-coordinate CRT, temporal copies and permutation defects

Date: 2026-11-22 JST. **Status:** elementary PAPER theorems from the exact parity-dependent gcd recurrence, plus independently executed finite integer audits. **Cap B and twin-prime infinitude remain OPEN; no new Lean kernel compilation.**

Extends [cross-prime rainbow CRT capacity](2026-11-22-cross-prime-rainbow-CRT-capacity.md), [reset backbone and 12-wheel](2026-11-22-reset-backbone-mod12-recharge-and-sentinel.md), [full-history clock](2026-11-22-full-history-clock-crt-and-twin-input-cutoff-sieve.md), and original [A166944/Lemmas.lean](../A166944/Lemmas.lean).

## 1. A one-factor CRT invariant independent of event parity

Recall a(n)=n+D(n). At each nonunit event r>=3 of increment e=d(r):

- If r even, e divides r and D(r-1)-1; since D(r)=D(r-1)+(e-1), e divides r and D(r), hence **e divides a(r)**.
- If r odd, e divides r-2 and D(r-1)+1; after the same update e divides r-2 and D(r)+2, hence **e divides a(r)**.

Thus **d(r)|a(r)** for every r>=3. In particular, if odd prime p>=5 divides increments at two indices u<v, then

    boxed: p | [a(v)-a(u)]
         = (v-u)+(D(v)-D(u)).                         (A)

Unlike separate first-hit index/horizon residue statements, this is completely **orientation-free**.

Select a set of DISTINCT prime keys p>=5, one pair of p-events per key, within any finite path interval. For each p define its **a-return span**

    U_p = a(second p-hit) - a(first p-hit) >0.

Group keys by identical value U. The exact **cross-key span-bucket CRT theorem** is

    boxed: product_{p: U_p=U} p | U.                    (B)

No return-order, rainbow, parity or prime-increment-only assumptions. An increment may be composite and have several prime factors; the keys remain distinct.

For an *actually attained* canonical record M>=23, s0=M+2, K=floor((7M-1)/4), the exact initial value is a(s0)=3M and D(K)<=2K, hence every selected U satisfies

    U <= a(K)-a(s0) <= 3*(K-M) <= (9M-3)/4.          (C)

Fix c>0. For sufficiently large M, a single U-bucket contains at most TWO distinct prime keys p>=c*sqrt(M), because three give product >=c^3*M^(3/2), eventually larger than (C). Therefore, if k different keys this large recur within [s0,K], **at least ceil(k/2) distinct a-return spans must occur**, regardless of their return order.

This is a true global **return-span diversity/entropy necessity**, rather than a claim that there are few repeated large keys.

## 2. A second, independent CRT in INDEX time

At an even hit, p divides r; at an odd hit, p divides r-2. Therefore a pair of p-hits u<v has index distance L=v-u satisfying:

    even -> even or odd -> odd: L ==0 (mod p);
    even -> odd:                  L ==2 (mod p);
    odd  -> even:                 L ==-2 (mod p).

So p divides L(L-2)(L+2). For distinct keys with identical index-return distance L,

    boxed: product p | L(L-2)(L+2).                   (D)

If all such pairs preserve parity, product p divides L. As L is even and the product is odd, the stronger exact bound holds:

    boxed: 2*product p | L.                           (E)

Within a canonical window L<=K-(M+2)<3M/4. Thus three keys all >=c sqrt(M) cannot share a same-parity index-return distance when M is large enough. This also forbids an exact position-shift copy of an event motif carrying three large independent prime keys, regardless of intermediate event history.

The index and a-coordinate clocks together give a two-dimensional lattice interpretation of repeated prime divisors, but neither clock alone bounds the number of DIFFERENT return distances.

## 3. Original rainbow capacity WITHOUT contiguous blocks: the horizon-span entropy lemma

For any selected p-reuse pair, its inclusive horizon-return growth T_p=D(second)-D(first) satisfies

    T_p ==0 (mod p),  same hit parity;
    T_p ==-2 (mod p), even->odd;
    T_p ==+2 (mod p), odd->even.

Group distinct selected keys by equal positive even T>2. Then

    boxed: product_{p:T_p=T} p | T(T-2)(T+2).         (F)

For p>=c sqrt(M), each group contains at most SIX keys for sufficiently large M (the RHS is O(M^3)). If every selected pair preserves parity, each group has at most TWO keys.

Thus k reused large keys force at least ceil(k/6) different horizon-return spans T, or ceil(k/2) if all orientations match. Since distinct T are even integers, their max-min is at least 2*(b-1) for b distinct values; if all corresponding intervening growth increments are 1 mod12, each T is a multiple of12 and max-min is at least 12*(b-1). The **a-coordinate** bound (B) gives the stronger universal count ceil(k/2) on its *different* U clock.

In particular, k=Omega(sqrt M) repeated primes of size >=c sqrt M force Omega(sqrt M) **distinct** a-return span values and Omega(sqrt M) spread in that return-span coordinate. This is a necessary but not yet contradictory dispersion constraint; the available a-window has length Theta(M).

## 4. General two-block permutations: exact weighted zero defect and inversion penalty

Take two contiguous blocks of event increments that contain the SAME k distinct primes p1,...,pk, possibly in different orders, with arbitrary middle event word W. Let order A be the first block, B the second block. Put w_p=p-1 and

    T0=sum_{all keys} w_p + sum_{e in W}(e-1).

For key p, let B_before(p) and A_before(p) denote the sum of other key weights preceding p in their respective blocks, and define

    Delta_p=B_before(p)-A_before(p).

The inclusive horizon growth from first p to second p has the **exact formula**

    boxed: T_p=T0+Delta_p.                            (G)

There is a surprisingly simple weighted conservation law:

    boxed: sum_p w_p*Delta_p=0.                        (H)

Proof: for either ordering, sum_p w_p*(sum_{q before p} w_q)=sum_{unordered {p,q}}w_p*w_q. The difference therefore vanishes. So T0 is the weight-(p-1) mean of the actual return spans T_p.

**Inversion-penalty theorem.** If p occurs before q in A, but q occurs before p in B, then

    boxed: T_p-T_q=Delta_p-Delta_q >=(p-1)+(q-1)
                                             =p+q-2. (I)

Proof: in A the prefix weight before q exceeds that before p by w_p plus any intervening weights. In B the prefix weight before p exceeds that before q by w_q plus intervening weights. Add the two positive differences. For a reverse-order chain of r keys all >=P, the span range is at least 2(P-1)(r-1).

If the second permutation has I inversions relative to the first, it can be obtained by I adjacent swaps. At most 2I keys participate in these swaps, so at least k-2I keys have Delta_p=0 and hence T_p=T0. Applying (F), if all keys >=c sqrt M on a canonical window, then for sufficiently large M

    boxed: k<=2*I+6,                               (J)

or k<=2*I+2 if all keys return at the same parity.

**Order-or-spread dichotomy.** For k>=7 large keys in two corresponding blocks, an order-preserving second block is ruled out by (F), so some inversion exists and the return spans must have width >=2c sqrt(M)-2. The analogous all-same-parity statement starts at k>=3. This quantifies the **reordering complexity or dispersion** required to evade the previous exact rainbow product obstruction.

No claim that arbitrary long canonical reset chains necessarily contain large identical-key blocks has been established.

## 5. Independent full-recurrence audit and a true repeated motif

The stand-alone [return-span audit](return_span_permutation_capacity_audit.py) directly computes A166944 through n=2,500,000. It has 250 nonunit events, 45 distinct prime factors >=5, and 1,769 all-pair repeated-key intervals (not merely consecutive uses).

Grouping these return pairs:

    horizon spans T: 1552 distinct values, 110 values shared by >=2 keys, max 3 keys;
    a-spans U:       1701 distinct values, 22 values shared by >=2 keys, max 3 keys.

All selected pairs pass (A), (D), and (F), and every group satisfies (B). Among two contiguous prime blocks of length 2 that recur in reversed order, there are 23 exact occurrences; no reversed permutations of rank 3 or4 occur on this finite 250-event prefix.

An exact ORIGINAL-sequence non-rainbow example is

    indices 9,15,...,1326,1339
    increments 7,13,...,13,7.

The shared block baseline is T0=2634, but

    Delta_7=+12; T_7=2646;
    Delta_13=-6; T_13=2628.

The weights w7=6,w13=12 give 6*(+12)+12*(-6)=0. The inverted pair has T7-T13=18=7+13-2, so the inversion penalty (I) is sharp on the genuine trajectory. The orientation congruences also check: 7|2646, 13|(2628-2).

**A genuine finite exact repeated event motif with a simultaneous three-key time translation:**

    first indices      2674, 2675, 2676, 2680, 2682
    increments             7,   11,    3,    5,    3
    repeated indices 1427944,1427945,1427946,1427950,1427952
    same increments        7,   11,    3,    5,    3.

Every paired index differs by L=1,425,270; every post-horizon differs by T=2,850,540=2L, so each a value differs by U=4,275,810=3L. The three distinct large-enough-to-count keys 5,7,11 have product 385; exact integer ratios are

    L/(2*385)=1851, T/385=7404, U/385=11106.

This genuine motif witnesses the 2-dimensional CRT phase-locking. The keys are small, and the motif violates no asymptotic product barrier.

## 6. What is and is not accomplished

The previous rainbow theorem used **identical block order** to force the same horizon return growth. The new work:
1. Removes all order and parity assumptions for the **a-coordinate** key-bucket product;
2. Adds an independent **index-time** key-bucket product and two-dimensional repeated-motif obstruction;
3. Quantifies order changes by the **zero-sum permutation defect** and **inversion-cost**;
4. Shows that k reused keys of size Omega(sqrt M) force Omega(k) distinct spans, even without any rainbow blocks.

Still missing is an **authentic full-path mechanism that bounds the number or the range of distinct return spans, or forces low-inversion block replays**. The present entropy lower bound Omega(sqrt M) does not contradict the available Theta(M) span range, nor does (J) imply that a large low-inversion block actually exists. The artificial CRT starts from earlier notes also remain valid. This is a partial cross-key constraint and a specific new target for global first-hit correlation, NOT Cap B or a twin-prime proof. No new Lean kernel proof was compiled.
