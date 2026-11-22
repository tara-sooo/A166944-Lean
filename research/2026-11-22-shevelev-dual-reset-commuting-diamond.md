# Shevelev companion sequences: complementary clocks, reset certificate, and a commuting diamond

Date: 2026-11-22 JST. **Status: primary-source definitions verified, two elementary comparison lemmas derived, exact finite numerical checks. No new Lean-kernel proof, no Cap B or twin-prime infinitude proof.**

The user supplied an external comparison of OEIS A167493, A167495, A174214, A174216, A167168, and A213536 with A166944. The useful original texts were independently checked:

- https://oeis.org/A166944 — original additive parity-gcd recursion.
- https://oeis.org/A167493 and https://oeis.org/A167495 — switched parity recursion and record increments (record conjecture still open). Difference-prime conjecture FALSE: OEIS documents e=27 at index 620757 and other composite increments.
- https://oeis.org/A174214 and https://oeis.org/A174216 — reset on a nonunit gcd, and indices satisfying an equality; OEIS calls infinitude of these indices a **sufficient conditional theorem** for infinitude of twin primes.
- https://oeis.org/A167168 — representatives of prime-generating Rowland sequence classes, NOT simply a list of all canonical return states.
- https://oeis.org/A213536 — cousin-prime gap-4 recurrence, a generality control, not a direct two-state conjugate.
- Vladimir Shevelev, "Three theorems on twin primes", arXiv:0911.5478, https://arxiv.org/abs/0911.5478 .
- Vladimir Shevelev, "Theorems on twin primes—dual case", final revision v37 (Aug 31 2014), https://arxiv.org/abs/0912.4006 and accessible original HTML https://ar5iv.labs.arxiv.org/html/0912.4006 . Its §§4 and 6–7 have the most relevant extra recurrences and exact clock formulas.

## 1. A166944 and A167493: exact parity-complementary prime clocks

Write for EACH sequence its own horizon D(n)=a(n)-n, and let C denote a common hypothetical frozen even pre-step horizon. For original A166944 the nonunit factor tests at n are

    even n: gcd(n,C-1);     odd n: gcd(n-2,C+1).

For dual A167493 they are

    even n: gcd(n-2,C+1);   odd n: gcd(n,C-1).

Thus for every odd prime p|C-1:
    original trigger = n==0 (mod 2p), dual trigger = n==p (mod 2p).
For every odd prime p|C+1:
    original trigger = n==p+2 (mod 2p), dual trigger = n==2 (mod 2p).

**Exact paper lemma (complementary half-period clock):** in a common frozen horizon, each p clock in the two recurrences fires on complementary residue classes separated by p inside the same modulus 2p. This explains the parity duality at the state level, beyond merely copying the OEIS definitions. It does NOT imply either actual evolving trajectory stays synchronized: the two horizons evolve independently once their nonunit increments differ.

## 2. A174214 is the RESET shadow of A167493, not another additive-gcd path

Let B(n)=A167493(n), and R(n)=A174214(n) (R(9)=14). Both use the same gcd operand

    h(n,x)=gcd(n-2,x) for even n, gcd(n,x) for odd n.

Their difference is that B(n)=B(n-1)+h(n,B(n-1)), while

    R(n)=R(n-1)+1               if h(n,R(n-1))=1,
         2n-4                   otherwise.

Suppose R(r)=2r-4 is a reset (r even, r>=12). Until the NEXT reset, the exact formula is R(t)=t+r-4. The fundamental equality

    2 R(k) = 3(k-1)

then forces k=2r-5. The intervening quiet stretch has length r-5.

During this frozen unit stretch the gcd tests simplify EXACTLY:

    even t: gcd(t-2,r-3);
    odd t:  gcd(t,r-5).

**Elementary reset/prime equivalence (r even >=12):**

    No further reset at r<t<=2r-5
        IF AND ONLY IF
    r-5 and r-3 are both prime.

Proof: when prime, the earliest eligible even multiple of r-3 is at index 2r-4, one AFTER the proposed fundamental equality, while the earliest eligible odd multiple of r-5 is 3r-15, also afterward for r>10. If either neighbor is composite, its least proper prime factor q has q<=sqrt(r-3), and its appropriate parity clock fires within <=2q<=r-5 steps after r, before or at 2r-5. As usual, a composite factor clock's hit is necessarily an actual nonunit reset unless another reset occurred sooner (which itself invalidates the quiet stretch).

Conversely, any sufficiently late actual equality 2R(k)=3(k-1) comes after a last reset r=(k+5)/2, with r even (odd reset r would force another reset at r+1); hence k certifies the twin prime pair

    ((k-5)/2, (k-1)/2).

This gives a direct mechanism behind the OEIS conditional A174216 theorem. **What remains hard is proving such unusually long quiet intervals occur infinitely often.** This is the same arithmetic bottleneck as the cutoff/Cap B terminal-roughness problem, not an automatic alternate proof.

OEIS data nuance: A174216 has **seed a(1)=15**, but at n=15 the equality is NOT satisfied, because R(15)=26. Its first actual equality term is n=27 (R(27)=39). The literal Maple code in that OEIS entry accidentally references A173214 instead of A174214; its definition and Mathematica implementation correctly reference A174214.

Direct checks:
- A167493's fundamental indices through 50000: 7,27,63,123,279,567,1143,2307,4623,9303,18687,38283.
- A174214 equalities through 50000: 27,63,123,279,567,1143,2307,4623,9447,18927,38283.
- They coincide from 27 through 4623, split at 9303 versus 9447, and both include 38283.
- At index 4680 both B,R have value9300; at 4681 their common gcd factor is31 but B(4681)=9331, R(4681)=9358; they differ through 19035 and resynchronize at 19036. Hence equality of fundamental values is NOT a pointwise identity or a monotone domination result.

## 3. A more DIRECT additive comparison in the original Shevelev dual-case paper, §4

An additional recurrence **f**, not listed by the other assistant, is defined in Shevelev's original paper:

    f(1)=2;
    odd n:  f(n)=f(n-1)+gcd(n, f(n-1));
    even n: f(n)=f(n-1)+gcd(n, f(n-1)+2).

Shevelev CONJECTURES that its record increment values above 7 coincide with A167493, despite different nonunit events. We independently tested both through n=1,000,000:

    exact B(n)=f(n) at 999600 of 999999 indices n>=2 (99.9601%);
    15 distinct record values >=13 coincide, in the same order;
    each corresponding f record appears exactly TWO indices BEFORE
    the B=A167493 record (e.g. 13 at n26 vs n28,
    4651 at n9302 vs n9304, 310231 at n620462 vs n620464).
    the record coincidence remains a finite observation, NOT theorem.

This surprising numerical agreement has a precise **three-step commuting-diamond lemma**:

Suppose n is even and B(n-1)=f(n-1)=x. Put v=x-n+2 and q=gcd(n,v)=gcd(n,x+2)>1, and suppose gcd(n-2,v)=gcd(n-2,x)=1.

The f increment at n is q, while B has unit increment. If the odd increments at n+1 are both unit AND f's even increment at n+2 is unit, then B's even increment at n+2 is necessarily q (because its gcd is gcd(n,x+2)=q), and

    B(n+2)=f(n+2)=x+q+2.

Exact sufficient conditions, all computable at the common pre-state x:

    gcd(n+1,x+1)=1,
    gcd(n+1,x+q)=1,
    gcd(n+2,x+q+3)=1.

The main q event has been **moved two indices earlier**, but the two paths merge after n+2. On the first million indices, there were 59 synchronized even initial states with q>1 and dual e=1; 53 satisfied all three unit conditions and merged after two steps, and 6 were short local "diamond defects". Repeated merging has not been proved globally.

This is an actual mechanistic explanation for why the paper's record-value coincidence is plausible. It is closer to the A166944 BAD project than A174216's tautological conditional infinitude because it models **competition and cancellation of prime-factor clocks between different additive recurrences**.

## 4. Relevance and next test for A166944

The original A166944 challenge is a global BAD-path exclusion, not merely constructing a recurrence which produces twin primes when a long quiet interval is ASSUMED. These comparisons suggest:

1. Use the exact parity-complementary clock lemma as a **counterfactual "ghost clock"** for each factor q|D±1 along a real A166944 canonical window. Annotate the actual q activation/foreign preemption events with where the dual frozen clock would have rung. This is bookkeeping, not an extra arithmetic constraint by itself.
2. Borrow the three-step commuting-diamond technique from A167493 vs Shevelev's f(n). Look for exact short **reordering/merging motifs** among A166944's adjacent event activations, where different orders of q-events lead to the same post-horizon after a bounded number of indices. A genuine global defect budget, especially BAD-specific, could distinguish a stable record-return path from a terminal BAD short crossing.
3. Use A174214 as a reset-only **control**: it shows that forced canonicalization eliminates history complexity but does not eliminate the necessity of a long two-sided prime-rough interval. If a proposed proof from the reset model does not generate such an interval without assuming twin primes, it has not bypassed the open obstruction.
4. A167168 (Rowland classes) and A213536 (gap-4 cousin prime) are good robustness checks for a newly proposed invariant, but are less directly informative for the present first-hit CRT task.

No known theorem currently couples the actual A166944 original and dual horizons tightly enough to force universal Cap B. All derived lemmas above are elementary paper proofs or finite checks only, and the A167493-f record agreement is still a conjecture.

Reproduction: [shevelev_dual_reset_diamond_audit.py](shevelev_dual_reset_diamond_audit.py).
