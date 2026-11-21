# Phase-locked prime reuse: exact wheel-spacing and large-separator barrier

2026-11-22 JST. **Status: paper theorems and independent direct-gcd/integer audits; no new Lean kernel compilation.** This research does NOT prove Cap B, the event-count liminf claim, or twin-prime infinitude. It continues [the wheel-inert synthetic path analysis](2026-11-22-frozen-wheel-phase-budget-and-neutral-paths.md).

## 1. General 3-event modular amplification (no low-offset assumption)

Let p and q be **distinct primes** congruent to 1 modulo a fixed integer W>=4; assume a true local first-hit path has three **consecutive nonunit event values** p,q,p. Let C1,C3 be the pre-event horizons at the first and third p hits. The first-hit divisibility in [Lemmas.lean](../A166944/Lemmas.lean) gives C=+1 modulo p at an even p hit, and C=-1 modulo p at an odd p hit. The horizon difference is exactly

    C3-C1 = (p-1)+(q-1) = p+q-2.              (1)

Write p=W*h+1, q=W*k+1, h,k>=1. The three parity cases yield:

* **Same hit parity:** p divides C3-C1, so q=2 modulo p. Thus W*k=1 modulo p. Because W*h=-1 modulo p, p divides k+h. As k+h>0, k+h>=p, hence

    q >= (W-1)*p+2.                            (2)

* **First p odd, last p even:** C3-C1=2 modulo p, so q=4 modulo p. Hence p divides k+3*h. Since W>=4, p>3*h, giving

    q >= (W-3)*p+4.                            (3)

* **First p even, last p odd:** C3-C1=-2 modulo p, so p divides q. Since q is a prime distinct from p, this is impossible.

Thus, **in every possible case, q>=(W-3)*p+4**. For W=420 this is q>=417p+4; same-parity uses the stronger q>=419p+2. The first-hit minimality/gap bound is not needed for (1)-(3); exact gcd divisibility and horizon updates suffice.

This applies to genuine A166944 paths with no restriction to low offset or canonical records. It also applies to exact locally synthetic paths.

## 2. Phase-locked neutral 420-wheel: horizon/index spacing

A *neutral* event starts and ends at X=2s-C=6; when its increment is e, its gap is g=(e-1)/2. Assume all events under consideration are odd hits with e congruent to 1 modulo 420, as in the earlier synthetic 420-wheel construction.

If a prime p congruent to 1 modulo 420 is used at two such events, let C1,C2 be their pre-event horizons. Since every intervening event adds a multiple of 420 to C,

    420 | C2-C1.

The two p hits are both odd, so p | C1+1 and p | C2+1, hence p | C2-C1. The moduli are coprime; the positive horizon displacement satisfies

    420*p | C2-C1,     C2-C1 >= 420*p.          (4)

Because X=6 at both starting states and both p events have the same neutral gap (p-1)/2, the two actual hit indices r1,r2 satisfy

    210*p | r2-r1,     r2-r1 >=210*p.           (5)

For an immediate recurrence p,q,p, (4) is equivalent to q>=419p+2, matching (2). If there are h intervening neutral events with values e1,...,eh, their horizon growth H obeys

    H=sum(ej-1)>=419p+1.                       (6)

The constraint (4) also has a broader **same-wheel-phase** interpretation without X=6: any two p hits with the same parity and pre-horizon residue modulo 420 must have C-displacement divisible by 420p (provided gcd(420,p)=1). The neutral hypothesis makes that phase agreement automatic and converts it into the index-spacing identity (5).

## 3. First-hit square-gap bound: an exact finite and asymptotic exclusion

The existing Lean first-hit inequalities imply

    g*g <= 4*(C+1)                              (7)

for any event of gap g and pre-horizon C. This follows by multiplying g<=2e and g*e<=2*(C+1). On an actual canonical interval [M+2,K], K=floor((7M-1)/4), one has C<=2K, by the existing global D(n)<=2n.

Put R=isqrt(2K+1). For a neutral middle event with increment q, g=(q-1)/2, so (7) gives

    q-1 <=4R.

For a neutral p,q,p word with p,q congruent to 1 modulo 420, combine with q>=419p+2:

    419p+1 <=4R
    (419p+1)^2 <=16*(2K+1) <=8*(7M+1).        (8)

Thus any such word with the smallest possible p=421 requires

    M >=555,660,000.

At the official M=45,895,573, K=80,317,252 and R=12,674. Equation (8) would require p<=120, while every prime p congruent to 1 modulo 420 is >=421. **Therefore no neutral 420-wheel p,q,p word can occur entirely before that official cutoff, regardless of whether a slow interval exists.** The stronger conclusion comes directly from first-hit feasibility, not from assuming absence of slow intervals.

Asymptotically, (8) excludes these words when p exceeds approximately (2*sqrt(14)/419)*sqrt(M) =0.01786...*sqrt(M).

The same square-gap bound plus (6) controls the intervening **event count**. Every intervening neutral event satisfies ej-1=2gj<=4R, so

    h >= ceil((419p+1)/(4R)).                 (9)

At the official cutoff, if p>=isqrt(M)+1=6775, the right side is at least 56. For p=421, it is at least 4. Hence a large prime cannot recur quickly within an entirely neutral 420-wheel path, even if the intermediary values and their order vary.

## 4. Independent executable checks

[phase_locked_reuse_audit.py](phase_locked_reuse_audit.py) uses only integer arithmetic and the Python standard library:

- Algebraically verifies the least q>=1 congruent to 1 modulo 420 and to 2 or 4 modulo several example p values; the formulas (2)-(3) agree with exact enumeration.
- Replays **every intervening gcd** from the synthetic seed M=9,801,898,053,991 with exact events (421,176401,421), gaps (210,88200,210), including their terminal values. This seed is NOT an attained canonical record from a(1)=2.
- Confirms the equality in (4)-(5): delta C=176,820=420*421 and delta hit index=88,410=210*421. The middle q=176401 is exactly 419*421+2, the minimum permitted integer and is prime.
- Confirms the official-cutoff R=12674, p<=120 obstruction, and 56-intervening-events bound for p>=sqrt(M).
- Independently computes the *original* A166944 recurrence to n=2,500,000. Among seven actual 3-event p,q,p patterns with p>=5, one has p,q congruent to 1 modulo 6 (p=7,q=331) and satisfies the W=6 inequality; there are no examples with both increments 1 modulo 420 in that finite range.

The finite audit passed. The general statements above are proved symbolically on paper; no Lean kernel verification was performed.

## 5. Where the global argument remains open

The new bound is particularly strong for paths that remain in a fixed neutral wheel phase. But a hypothetical path without slow intervals may change its offset, hit parity, active small-prime residues, and increment congruence classes. Then the 420p amplification need not hold. Even within a phase-locked path, a prime may recur after many smaller intermediate events satisfying (6); this can fit the global O(M) growth allowance for sufficiently large M.

Thus the result does not yet establish any unconditional asymptotic event-count bound for actual canonical records, any upper bound on total G below M/3, or an unbounded F=4n-9D(n) drawup. The next obstacle is a phase-changing generalization with coefficients strong enough to exclude *long, aperiodic* multi-prime schedules, not just short returns in a fixed residue class.

This note has been saved as research, not as a completed Cap B or twin-prime proof.
