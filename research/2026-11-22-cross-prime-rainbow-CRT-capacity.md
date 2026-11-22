# A166944 cross-prime overlap: multiplicative CRT rainbow and joint excitation capacity

Date: 2026-11-22 JST. **Status:** new exact paper deductions, independently executed original-gcd audits, and a CRT synthetic existence construction. **No new Lean compilation; Cap B and twin-prime infinitude remain OPEN.**

Context: [aligned k=1 reset 12-wheel and prime recharge costs](2026-11-22-reset-backbone-mod12-recharge-and-sentinel.md), [disjoint excitation discharge](2026-11-22-reset-prime-excursion-disjoint-budget.md), [generic factor-reuse Lean lemmas](../A166944/TravelFactors.lean), [signed CRT reuse congruences](../A166944/ReuseCongruences.lean). The earlier proof obstacle is that one event's horizon growth can recharge multiple distinct prime keys; simply summing each key's minimum charge counts the same growth repeatedly.

## 1. The fundamental same-growth CRT lemma

At a nonunit A166944 event of increment e, let C_pre=D(r-1), C_post=C_pre+e-1. Let odd prime p>=5 divide e. The parity-sensitive gcd gives

    r even: C_post==0 mod p;
    r odd:  C_post==-2 mod p.

At a later hit using p, its pre-horizon H is +1 modulo p when the later index is even, and -1 modulo p when the later index is odd. Thus the growth R=H-C_post before the later event satisfies

    first -> second     R mod p
    even -> even        +1
    even -> odd         -1
    odd  -> even        +3
    odd  -> odd         +1.

**New observation:** if the *later hit itself has increment divisible by p*, the inclusive return growth T_p=D(second hit)-D(first hit)=R+(e_second-1) satisfies

    T_p == 0 (mod p) when the two indices have the same parity;
    T_p ==-2 (mod p) for even -> odd;
    T_p ==+2 (mod p) for odd  -> even.             (1)

This statement remains true if other p-events occur between the two selected uses. It is also valid when the two increments are composite multiples of p. It is a consequence of the previously formalized factor-residue reasoning, but the **simultaneous shared-growth product theorem below is new.**

## 2. Rainbow theorem: overlapping recharge constraints MULTIPLY

Take a contiguous event subword

    p1, p2, ..., pk, W, p1, p2, ..., pk,            (2)

where p1,...,pk are distinct odd primes >=5, both displayed occurrences have increment EXACTLY pi, and W is any (possibly empty) event word. The events may be at arbitrary indices and mixed parities. Let d_j=e_j-1 be each event's growth, and set

    T=sum_i (pi-1) + sum_(e in W) (e-1).            (3)

**Equality of numerical recharge-span growth.** For each i, the events STRICTLY AFTER the first pi through and INCLUDING the second pi consist of the suffix pi+1,...,pk of the first block, then W, then the prefix p1,...,pi of the second block. Every pi therefore has

    D(second pi)-D(first pi)=T.                     (4)

These k recharge intervals overlap heavily in chronological time but have the SAME INTEGER growth T. They are NOT the same physical time interval.

Classify keys according to the parity change of the two hit indices:

    P0 = product pi for same parity;
    P+ = product pi for odd -> even;
    P- = product pi for even -> odd.
    (Empty products are 1.)

**Cross-prime multiplicative CRT theorem (PAPER):**

    P0 divides T,  P+ divides T-2,  P- divides T+2.       (5)
    boxed:  product_i pi divides T*(T-2)*(T+2).          (6)

Proof: (4) and (1) give each prime its prescribed divisibility. The pi are pairwise distinct, so products over each class divide the corresponding factor; multiplying yields (6). No horizon growth is counted more than once.

If all keys return at the same parity, the MUCH stronger statement follows:

    boxed: product_i pi divides T, hence T>=product_i pi.   (7)

## 3. 12-frozen amplification and a genuine bounded-width result

Suppose every event contributing to T in (3) has increment e==1 mod 12; this is the long-gap aligned k=1 reset condition **when the relevant event and its following gap are long**, not an unconditional condition on all reset events.

Then T==0 mod 12, all pi==1 mod 12, and P0,P+,P- are each 1 mod 12. The CRT constraints (5) give sharp **separate** necessary lower bounds:

    T>=12*P0,
    T>=10*P+ + 2,
    T>=2*P- - 2.                                   (8)

(For empty products these merely produce weak/trivial lower bounds.) For example T==2 mod P+ is T=2+j P+, and 12|T forces j==10 mod12. Similarly T==-2 mod P- forces j==2 mod12.

In the all-same-parity case:

    boxed: 12*product_i pi <=T<=G_total.             (9)

Here G_total is the actual horizon growth of an enclosing canonical window; (9) is a REAL CROSS-KEY SINGLE-CAPACITY inequality, not a sum of separate key costs.

For a genuinely attained canonical record M, s0=M+2 and K=floor((7M-1)/4), known D(K)<=2K gives

    G_M=D(K)-(2M-2)<=2K-(2M-2) = (3/2)*M+O(1).

Suppose all rainbow keys pi >= a*sqrt(M) for fixed a>0. The general (6) yields

    (a*sqrt(M))^k <=G_M*(G_M^2-4) = O(M^3).

Thus **k<=6 for all sufficiently large M**; seven such keys in a rainbow are impossible, irrespective of parity. If all key recurrences preserve parity, (7) yields **k<=2** for all sufficiently large M. For a 12-frozen all-same-parity two-key rainbow, (9) excludes p,q >=a sqrt(M) whenever a>1/sqrt(8), eventually.

These bounded-width conclusions are exact consequences of the stated rainbow/order hypotheses. They do **not** bound the number of different prime keys in an arbitrary event path lacking a rainbow subword.

## 4. More general balanced crossings and bounded defects

For a more general chronological pair of crossing returns, write

    p, A, q, B, p, E, q,

where A,B,E are words of other event increments. Put a=the growth of A, b=the growth of B, c=the growth of E, and T=b+(p-1)+(q-1). The inclusive return growths are

    T_p=T+a,    T_q=T+c.

If a=c, the two spans are **balanced**, so they share the same growth T+a. Then two same-parity prime returns imply

    boxed: pq divides (T+a).

If the word is also 12-frozen, then 12pq divides (T+a). This extends (9) beyond immediately adjacent leading/trailing key pairs. Different a and c are the exact *fringe defect* causing the multiplicative CRT to weaken.

A general quantitative extension handles imperfect synchronization. Suppose k distinct prime keys have chosen inclusive return growths Ti, and |Ti-T|<=E for some integer T>E+2. Each pi divides one of Ti,Ti-2,Ti+2. Consequently

    product pi divides product_{j=-E-2}^{E+2}(T+j),       (10)

and

    product pi <= (T+E+2)^(2E+5).                        (11)

This is a rigorous bounded-defect overlap lemma. For fixed E and pi>=M^alpha on paths with T=O(M), it bounds the number k independently of M. It is MUCH weaker than the exact rainbow bound when E grows, and is not claimed to solve the general Hall deficiency.

## 5. Joint, non-double-counting excitation/rainbow capacity ledger

Take a finite actual first-hit path [u,v]. Select:
1. completed excitation-to-first-primitive intervals from the previous paper;
2. 12-frozen, same-parity rainbow words of the form (2), each with charging span from just AFTER its first p1 to INCLUDING its second p1.

Require the FULL selected rainbow word supports to be pairwise disjoint and disjoint from the selected excitation supports. Then their **actual growth charging intervals are disjoint**, so

    sum_rainbows (12*product_i pi)
      + sum_excursions [2*m_j + 2 + (2/3)^m_j*(2p_j-6)]
        <= D(v)-D(u).                                    (12)

Equation (12) is an honest combined growth-capacity theorem: rainbow reuses are **charged multiplicatively as a single combined obligation**, excitation discharges by disjoint intervals, and no event pays twice. If the path has no such rainbow motifs, the first sum is empty and (12) does not exclude it.

For mixed-parity rainbows, replace each 12*product by the maximum of the three valid bounds (8), or use the exact integrality constraints (5); do not incorrectly add overlapping class obligations.

## 6. Direct independent audits of the ORIGINAL recurrence

The [standalone Python audit](rainbow_overlap_capacity_audit.py) runs the original parity-sensitive gcd recurrence through index 2,500,000 and collects all 250 nonunit events (including the initial n=2 hit). It scans ALL contiguous rainbow prime-increment motifs of rank 2 through 5. Results:

    rank 2: 41 motifs,
    ranks 3,4,5: 0 motifs,
    17 of the rank-2 motifs have both prime pairs returning at same parity.

All 41 satisfy (5)-(7) and, where applicable, (8). An especially transparent authentic occurrence is:

    event indices: 2674, 2675, 5474, 5491
    increments:       7,   11,     7,   11
    post-horizons: 5334, 5344, 10878, 10888

Thus

    D(5474)-D(2674) = 5544 = D(5491)-D(2675)
                    =72*(7*11),

an exact real cross-key product-charge example. It is not 12-frozen, so only (7) applies.

## 7. A CRT REALIZABILITY construction: the product barrier can be PAID locally

The theorem is not a blanket impossibility of overlapping reuses. For a very large but explicit finite set of primes, one can construct **arbitrarily large ARTIFICIAL canonical-shaped starts** with the exact all-odd, k=1 reset word

    p, q, r, p, q

using complete first-hit gcds, with p=421, q=2521 and r=2,228,813,161 (each is prime and 1 mod 420). Here

    T=(p-1)+(q-1)+(r-1)=2,228,816,100=175*(12*p*q).

For proof, take odd s0 and C0=2s0-6, and denote the five pre-event horizon offsets by

    shifts=[0, p-1, p+q-2, p+q+r-3, 2p+q+r-4].

Choose C0 by CRT, enforcing

    C0==0 (mod 420),
    C0==-1 (mod p),
    C0==-p (mod q),
    C0==1-p-q (mod r).                                (13)

The selected prime clocks then activate precisely at their own event positions:
- p divides Cj+1 only at j=0,3;
- q divides Cj+1 only at j=1,4;
- r divides Cj+1 only at j=2.
At other stages they divide neither Cj-1 nor Cj+1. These claims are straightforward modular checks using r+p+q-3=175*(12pq). Each selected active clock, with s odd and X=6, hits after gap (prime-1)/2 and has gcd equal to that prime.

Every other prime ell>=11 and <=r+6 can be made INACTIVE in ALL five stages by avoiding at most 2*5=10 residue classes for C0 modulo ell. At least one class remains, because ell>=11. The primes 3,5,7 are automatically inert by C0==0 mod420 and every increment being 1 mod420. Thus the global CRT system has a solution and an infinite arithmetic progression of arbitrarily large C0 solutions. Taking s0=(C0+6)/2 gives an odd canonical-shaped start; choosing C0 sufficiently large makes the five-event word lie well inside its K window. All intermediate gcds are then 1, by the factor-clock exhaustion. This is a mathematical finite CRT EXISTENCE proof, not a materialized explicit gigantic starting integer; the companion script checks selected-clock residues and an explicit partial CRT over all other primes <=1000.

**Important:** none of these artificial starts is asserted to be reached by the genuine a(1)=2 recurrence or to have twin-prime M. The construction demonstrates the **precise scope** of (9): simultaneous recharge can be funded, but only at the enormous product cost.

## 8. Remaining global bottleneck

The product obstruction is extremely strong for same-order, nearly synchronized multi-key reuses. It combines safely with disjoint excitation accounting. It still does **not** exclude arbitrary long reset chains:
- keys can return in a DIFFERENT order (e.g., nested rather than rainbow);
- intervening event words may be unbalanced, so their inclusive return growths differ substantially;
- many prime keys may be small, and the cubic product condition becomes weak;
- local artificial starts can be chosen by CRT to pay even giant product costs when M is allowed to grow.

Next potential move: control **return-span dispersion** |Ti-T| for overlapping requests, or prove an unavoidable abundance of bounded-defect rainbow patterns among the reuse-heavy runs from the previous note. Existing prime-event count / Hall work does not supply that implication.

The new result is a rigorous **partial cross-key capacity theorem**, not a universal Hall theorem, Cap B, or a proof of twin-prime infinitude. The new paper arguments have **not** been kernel checked in Lean.
