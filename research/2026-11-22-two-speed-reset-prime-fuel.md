# A166944: two-speed reset dynamics and the prime-fuel route

Date: 2026-11-22 JST. **Status:** elementary paper lemmas derived from the original exact recurrence and previously kernel-checked first-hit factor bounds; independently checked finite examples. The proposed *global fuel/escape inequality* remains a research conjecture. **No Cap B proof or twin-prime proof; no new Lean compilation.**

Previous inputs:
- [A166944/ReplayOffset210.lean](../A166944/ReplayOffset210.lean) already proves the core offset update `X'=X+2g-(e-1)` and the residue class `X' ≡ 0 or 6 (mod 2e)` for events with e>=5.
- [A166944/FirstHitArithmetic.lean](../A166944/FirstHitArithmetic.lean) proves the first-hit divisor bound `g<=2e`.
- [full-history clock and twin-input sieve](2026-11-22-full-history-clock-crt-and-twin-input-cutoff-sieve.md) expresses the same dynamical coordinate at arbitrary relative indices.
- [frozen-wheel synthetic paths](2026-11-22-frozen-wheel-phase-budget-and-neutral-paths.md) demonstrate that finite-length reset chains can be arbitrarily long when the artificial input M is permitted to grow. Any proposed uniform finite-state stopping time is false.

The new contribution is a **sharp two-speed quantization of the FIRST event after a 0/6 reset**, plus a **prime-burning and excitation-or-detour decomposition** designed for an amortized analysis. Its initial congruence algebra is a transparent reformulation of earlier Lean offsets, not an independent solution of Cap B.

## 1. Per-index exact offset/cofactor identity

Write `C=D(n-1)` for n>=3, and define `X=2(n-1)-C >=0` (because the original A166944 has `D(m)<=2m` for the relevant m). Then for increment e=d(n):

    e = gcd(n, X+3)              if n even;
    e = gcd(n-2, |X-3|)          if n odd.                (1)

After processing index n, the offset evolves by the **exact** update

    X_new = 2n-D(n) = X+3-e.                             (2)

The first equation follows from C-1=2n-(X+3) (even branch) and C+1=2(n-2)+(3-X) (odd branch). The second follows from D(n)=C+e-1.

Let `U=X+3` (even) or `U=X-3` (odd). If U!=0 and e>1, then e is an **odd divisor of |U|**. Hence there are only two size classes:

    (primitive)  e=|U|;
    (proper)     e <= |U|/3, with |U|/e odd >=3.       (3)

The n odd U<0 case is a tiny exception because X is nonnegative even: X=0 or2 and |U|=3 or1. For a positive U, a primitive hit maps **exactly** to

    X_new=0 if n even; X_new=6 if n odd.                 (4)

For a proper hit with X>=10 the offset cannot collapse rapidly. Using (2)-(3) gives

    3*X_new >= 2*X+6 (even);
    3*X_new >= 2*X+12 (odd).                            (5)

Thus any significant abrupt drop of a large X requires a primitive hit, while proper hits can reduce X by at most one third per event, up to the explicitly positive additive terms.

## 2. Main two-speed lemma: NEXT first hit after low-offset state

Let (s,C) be an exact moving-horizon state, with **X_s=2s-C=xi in {0,6}**. Let r=s+g be its next nonunit event and e=d(r)>=9. By definition all increments in (s,r) are 1, so at r-1 the offset is Xpre=xi+2(g-1).

The event cofactor congruence becomes

    e | (2g+xi+1)     if r even;
    e | (2g+xi-5)     if r odd.                          (6)

Because e>=9, the divisor arguments are positive at an actual event. Each is odd, e is odd, and the kernel-proved first-hit bound says g<=2e. Therefore its positive integer quotient k satisfies

    k is odd, 1<=k<(4e+7)/e<5,

hence **k belongs to {1,3}**, *without any assumption that e is prime*.

**Two-speed theorem (paper).** For this entire class of exact first hits, only the following two branches are possible:

    r even:
        2g+xi+1 = k*e,    k=1 or3,
        X_r=(k-1)*e in {0,2e};

    r odd:
        2g+xi-5 = k*e,    k=1 or3,
        X_r=(k-1)*e+6 in {6,2e+6}.                     (7)

Equivalently, the gap is either near e/2 (k=1, the **reset mode**) or near 3e/2 (k=3, the **excitation mode**). There is a forbidden gap band between these exact discrete alternatives.

For the excitation mode, the quantitative minimum gap is

    g >= (3e-7)/2   for an even first hit;
    g >= (3e-1)/2   for an odd first hit.              (8)

The reset mode restores the two-state manifold X=0/6. The excitation mode leaves X=2e or2e+6, forcing a subsequent cost before a new reset.

**Excitation-or-detour corollary.** Suppose an excitation of size e has just occurred. If its very next nonunit event is primitive (positive cofactor), with increment f, then

    f>=2e-3.                                          (9)

Proof: until that next hit, X can only rise by 2 per unit index; immediately before it, Xpre>=2e. Primitive f=Xpre+3 (even hit) or f=Xpre-3 (odd hit), giving (9). Otherwise that next event is a **proper** cofactor event and is subject to (5), except for the explicitly small offsets. So an excitation is cleared either by a nearly doubled primitive increment or by a sequence of proper-factor detours.

## 3. A one-use prime-fuel lemma

Let p>=5 be a prime dividing the increment e at any exact hit, with pre-horizon C and post-horizon C'=C+e-1.

At an even hit, p|C-1 implies C'==0 (mod p), so **neither C'-1 nor C'+1 is divisible by p**.

At an odd hit, p|C+1 implies C'==-2 (mod p), so C'-1==-3 and C'+1==-1 (mod p), again neither divisible by p for p>=5.

**Prime-burning theorem (paper).** Every odd prime p>=5 used as an increment factor is **inactive on both horizon neighbors immediately after the event**. To recur, it must be reactivated by other increments that change the horizon modulo p. This supplements the already studied per-prime reuse-growth estimates; it does not remove their cross-prime overlapping-credit difficulty.

An instructive synthesis:
- a k=1 reset *spends* a factor and restores X=0/6, with event gap approximately e/2 and growth e-1 approximately 2g;
- a k=3 excitation *spends* a factor, uses a gap approximately 3e/2 and leaves X approximately 2e, requiring a nearly doubled primitive jump or a detour through proper-factor hits;
- any repeated large prime factor needs a fresh activation from the intervening mixed event history.

This provides a candidate **induced two-state return map** with explicit additional obligations whenever the process leaves the reset manifold. It is not a finite-state machine on its own: the set of used factors and the arithmetic of C±1 are unbounded.

## 4. Exact finite checks and counterchecks

The standalone [two-speed audit](two_speed_reset_prime_fuel_audit.py) uses no external dependencies and implements the original per-index gcd, the offset identities, proper-factor constraints and the prime-burning property.

On the original A166944 through index 2,500,000, with 249 nonunit events after n=2:
- 98 primitive |U| events, 151 proper-factor events and no U=0 exceptions;
- of **46** events with e>=9 directly following an event state X in {0,6}, 36 use k=1 and 10 use k=3;
- the first k=3 case is previous hit s=318, next hit r=340, e=17, g=22, previous X=6, new X=34=2e.

Synthetic (NOT necessarily attained) canonical-shaped starts:
- M=367: six k=1 and one k=3 resets-to-large-hit.
- M=100549: one k=1 and one k=3.
- M=101119: two k=1 and two k=3.

Both modes genuinely occur in the exact recurrence. Artificial low-offset prime chains with all k=1 are known from the earlier frozen-wheel research; therefore the k=1 branch cannot simply be declared impossible. The two-speed lemma is a **structural reduction**, not a global stopping theorem.

## 5. The ambitious proof program: amortized fuel rather than F alone

A conceivable missing **global input** is an induced **factor-fuel / excitation budget** spanning the entire canonical window [M+2,K] for genuinely attained twin-prime M:

1. Use (7) to decompose all e>=9 first hits immediately after low-offset reset states into short-growth-intensive k=1 resets and long-gap k=3 excitations.
2. Charge every used large prime p>=5 as *burned*. For a second appearance, use the full first-hit CRT clock and **its activation history**, not merely p's isolated return cost. Recharging several keys at one event is the precise overlap loophole.
3. If k=3 occurs, allocate its stored 2e offset either to a future primitive event of size >=2e-3 (9), or to proper-factor events with restricted offset contraction (5). To close the argument, one would need an inequality that charges these intermediate events **without double counting**.
4. Prove that no chain satisfying all these obligations can continue issuing nonunit hits into the O(sqrt M) neighborhood after the canonical cutoff K. Then the already-checked short-crossing dichotomy and the canonical return Lean theorem yield Cap B and twin-prime infinitude.

A sharp candidate bridge would be a **multi-key, first-hit-realizable amortization lemma**: for every canonical path whose last hit lies near K, the sum of **new-factor fuel demands + excitation clearing costs** exceeds the actual horizon and index budget. This is deliberately a **target theorem, not an established inequality**.

The advantage over a direct global F drawup is that k=1/k=3 is a **discrete dichotomy with exact algebraic costs**, and the p>=5 "burning" rule has an explicit finite-modulus mechanism. The difficulty is still formidable: earlier CRT constructions realize arbitrarily long finite reset sequences from artificial starting states, so the missing bound must scale with M and use the input's actual twin-prime canonicality rather than a fixed-size wheel.

## 6. Lean formalization entry points

The per-index identity (1) and update (2) should be a short addition near [ReplayOffset210.lean](../A166944/ReplayOffset210.lean), with integer absolute values or signed differences for the small X=0,2 odd exceptions. Then split the first-hit case by e>=9 and the existing `moving_horizon_event_divisor_gap` to derive k=1 or3; (7) is an explicit finite two-case theorem. No Lean build was run for this note.

**Outcome:** new exact two-speed classification and prime-fuel/offset bottleneck; no unconditional capacity inequality, no terminal BAD elimination, no Cap B or twin-prime proof.
