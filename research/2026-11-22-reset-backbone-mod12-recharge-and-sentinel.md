# A166944: aligned reset backbone, the 3 mod 4 sentinel, and 12-wheel recharge amplification

Date: 2026-11-22 JST. **Status:** new elementary PAPER theorems and finite direct-gcd audit. These claims have NOT been compiled into Lean. The global Cap B obstruction and twin-prime infinitude are still unresolved.

Continues [two-speed reset prime fuel](2026-11-22-two-speed-reset-prime-fuel.md), [disjoint excitation-recovery budget](2026-11-22-reset-prime-excursion-disjoint-budget.md), [exact full-history congruences](2026-11-22-full-history-clock-crt-and-twin-input-cutoff-sieve.md), and the existing kernel-checked factor-reuse baseline [TravelFactors.lean](../A166944/TravelFactors.lean).

## 1. Genuine aligned reset states and prime factors

An **aligned reset state** is (s,C) with even C=D(s) and either:

    s even and X=2s-C=0; OR
    s odd and X=2s-C=6.

A genuine canonical record M odd starts at s=M+2 odd, C=2M-2, X=6. Every k=1 first hit e>=9 from an aligned reset state returns to an aligned reset state, by the previously derived exact two-speed formula.

For e>=9, k=1, the cofactor equation is

    r even: e=2g+X+1;
    r odd:  e=2g+X-5;    g=r-s.

Using the parity forced by the aligned origin and r, **e=1 (mod 4)** in every case. The earlier composite first-hit rigidity theorem narrows such e to:

    e prime with e=1 (mod 4), OR e in {9,25}.       (1)

The misaligned synthetic e=15 example from the earlier paper is NOT on an aligned backbone: its starting s was even with X=6.

Every aligned reset state satisfies C=0 (mod 4), hence C-1=3 (mod 4). Thus C-1 always has an odd prime factor q=3 (mod 4). This is the **permanent 3-mod-4 sentinel**. It does not mean the SAME q persists after a reset.

## 2. Exact prime-clock race from an aligned state

For every odd prime q dividing C-1, the first even r>s divisible by q occurs at s+g_minus(q). For q dividing C+1, the first odd r>s with r-2 divisible by q occurs at s+g_plus(q).

The following table is exact and includes the small exceptional clocks:

    aligned origin     q mod4    q|C-1: g_minus          q|C+1: g_plus
    X=6, s odd         1         (q-7)/2  (q>=13)       (q-1)/2
                       1         9 if q=5              (q-1)/2
                       3         (3q-7)/2              (3q-1)/2
    X=0, s even        1         (q-1)/2               (q+5)/2
                       3         (3q-1)/2              (3q+5)/2 (q>=7)
                       3         (3q-1)/2              1 if q=3

The special q=3, X=0, C+1 clock has a **negative** cofactor quotient: g=1, rather than the superficially plausible g=7. The q=5, X=6, C-1 clock skips its negative g candidate and first occurs at g=9.

**Exact clock theorem:** The next actual nonunit increment has gap

    g = min_{q | C-1 or C+1, q odd prime} g_sign(q),

and its increment is the exact parity-sensitive gcd at r=s+g. Every odd prime divisor of a nonunit gcd is among the listed factors, and each clock is its first positive eligible index.

For every sentinel q=3 (mod 4) dividing C-1,

    g <= (3q-(X+1))/2.

If the winner is a PRIME k=1 reset e=p, combine this bound with the k=1 cofactor equation. Since p=1 (mod4) and 3q=1 (mod4), one obtains the strict sharper inequalities

    r even => p <= 3q-4;       r odd => p <= 3q-8.    (2)

The two bounds are sharp even for exact synthetic local gcd trajectories:

    (s,C)=(63,120): q=7 divides C-1, next r=68, e=p=17 =3q-4.
    (s,C)=(399,792): q=7 divides C-1, next r=405, e=p=13 =3q-8.

This forces every LARGE reset prime to outrun an always-present, competing 3-mod-4 prime factor clock.

## 3. A first-hit gap above 6 FREEZES the prime 3

From ANY even horizon C, if 3 divides C-1 or C+1, the next nonunit hit occurs within 2*3=6 indices (parity-specific CRT periodicity).

Therefore a gap g>6 forces C=0 (mod 3).

For two CONSECUTIVE first-hit gaps g_i>6 and g_(i+1)>6 in a reset backbone, the pre-horizon C_i and the post-horizon C_i' (which is the pre-horizon for the next hit) are both 0 mod3, so

    e_i-1 = C_i'-C_i = 0 (mod 3).

Since k=1 aligned increments are 1 mod4, this yields the **12-wheel theorem**:

    e_i ==1 (mod 12).                                  (3)

For a long run all of whose consecutive gaps exceed 6, EVERY event with a following gap in that run satisfies (3). The final event may not, until its next gap is known.

This result uses not just the increment's prime factorization, but the absence of all earlier gcd hits during two complete gaps. It is stronger than the simple residue property of a single event.

**Additional 12-wheel strengthening of the sentinel.** If both the incoming and outgoing first-hit gaps around a prime k=1 event are >6, then both pre- and post-horizons are 0 mod3, hence p=1 mod12. For the sentinel q|C-1, q=3 mod4 and q!=3 (since C=0 mod3), so q=7 or11 mod12 and 3q=9 mod12. Equation (2) consequently strengthens to the UNIFORM

    boxed: p <=3q-8.                                      (2b)

This is sharp for an exact aligned local event with a sufficiently long incoming gap: from (s,C)=(396,792), X=0, the next hit at r=405 has g=9 and p=13, while q=7 divides C-1, and 13=3*7-8. The following gap in this particular local example is short; the sharpness claim is for the incoming-gap and p-residue/sentinel argument, not for an indefinitely long 12-frozen run.

## 4. Oriented fuel is amplified from p to 9p and 11p

Take two uses of the SAME prime p>=13 on an aligned k=1 backbone, with **all intervening increments 1 mod12** and p=1 mod12. Let R>=0 be the actual even horizon growth from immediately after the first use to immediately BEFORE the second use.

Since every intermediate increment e_i is 1 mod12, R=0 mod12. Since p is an increment factor at both endpoints, the exact parity-conditioned congruence is:

    First use even -> next even: R ==+1 (mod p)
    First use even -> next odd:  R ==-1 (mod p)
    First use odd  -> next even: R ==+3 (mod p)
    First use odd  -> next odd:  R ==+1 (mod p).

Because p=1 mod12, the MINIMAL NONNEGATIVE common solutions to these congruences are:

    First -> second             MINIMUM R
    even -> even               11p+1
    even -> odd                 p-1
    odd  -> even                9p+3
    odd  -> odd                11p+1                         (4)

**Proof of minimum:** for R=kp+c with c in {+1,-1,+3}, the condition R=0 mod12 gives k=11 mod12, k=1 mod12, k=9 mod12, respectively. The resulting least positive values are exactly those in (4). This improves the generic p-1/p+1/p+3 bounds from previous research under the explicit 12-frozen assumption.

**Single-key summed non-overlap.** If p occurs t>=2 times during a 12-frozen pure-reset segment and all its inter-use increments satisfy (3), at most ceil((t-1)/2) consecutive inter-use windows can use the cheap even->odd orientation; TWO cheap windows cannot be adjacent. So at least floor((t-1)/2) windows cost >=9p+3 rather than p-1. Inter-use growth windows for this SAME p are disjoint. Writing G for the total horizon growth over the segment,

    boxed: G >= (t-1)*(p-1)+(8p+4)*floor((t-1)/2).  (5)

The right side is a genuine individually funded growth lower bound. Summing (5) over DIFFERENT keys would generally double-count shared horizon growth and is NOT justified.

**One-separator escalation.** If three CONSECUTIVE k=1 events have increments (p,q,p), all three gaps >6, and p is a prime >=13, then p and the middle increment q are 1 mod12. The intermediate increment q cannot be 25, since the exact reuse congruences would require p to divide 21,23,or25, incompatible with p=1 mod12 and >=13; and q cannot be 9 by (3). Therefore q is prime 1 mod12. Since R=q-1, (4) yields:

    first p -> last p:         q >= 11p+2 if same parity;
                                q >= 9p+4 if odd->even;
                                IMPOSSIBLE if even->odd (would require p|q).

    In all cases: q >=9p+4.                         (6)

The 9-fold amplification is for a short one-separator p,q,p arrangement; it is not a ban on reuse after several intervening events. It rules out the naive p,p+4,p recharge cycle once the two-speed path is genuinely long-gap and 12-frozen.

## 5. An asymptotic global necessity: macroscopic pure-reset paths need MANY REUSES

Assume there is a genuinely attained canonical record M>=23, s0=M+2, K=floor((7M-1)/4), and consider a contiguous aligned k=1-only run whose start a>=s0 and last hit b<=K. Every hit in the run has increment >=9, no small (3,5,7) or k=3 events intervene. Put

    T=b-a,    h=floor(sqrt(2*K+1)),     P=4h+7.

At every first hit before K, the pre-horizon C satisfies 2M-2<=C<=2K and C>K. If both C-1 and C+1 were prime, its next nonunit hit would be C+3>K. Thus at least one neighbor is composite. Its least proper prime divisor q<=sqrt(C+1) gives the first-hit bound

    g<=2q<=2h.

Therefore the run contains at least

    N>=T/(2h)                                           (7)

events. Every aligned k=1 increment e>=9 has e<=2g+7<=4h+7=P. By (1) and the fact that **two consecutive composite k=1 hits are impossible**, at least floor(N/2) increments are primes <=P.

A proof of the no-adjacent-composites claim:
- e=25 can occur only from X=6 at odd s to an even hit, g=9. For the other three aligned orientation choices its factor 5 would cause an earlier hit. Since g=9>6, its pre-horizon C=0 mod3. The post-horizon C'=C+24 is 0 mod3, and the new aligned state has X=0, s even; hence the NEXT hit cannot be 9 (3 is inert), nor 25 (a factor-5 hit would precede the putative 25).
- e=9 at an even hit leaves C'=0 mod3 and X=0, so the NEXT k=1 hit cannot be 9 or25.
- e=9 at an odd hit leaves X=6, and because r-2 is divisible by 9, r+1 is divisible by 3 but not 9. The exact immediate next hit is e=3, so the run of e>=9 k=1 ends.

Among prime increments at most pi(P) are FIRST OCCURRENCES of their keys. Therefore the number of repeated PRIME increments in this run is at least

    boxed: max(0, floor(N/2)-pi(P))                    (8)

and N>=ceil(T/(2h)). Here pi(x) denotes the number of primes <=x.

**Strong asymptotic consequence (conditional only on the existence of such a long run):** If along arbitrarily large genuine canonical records such a pure-reset run has T>=delta*M for any fixed delta>0, then h=Theta(sqrt M), N=Omega(sqrt M), and pi(P)=O(sqrt M/log M)=o(sqrt M), so

    number of repeated prime reset events = Omega(sqrt M).

Indeed the proportion of prime reset occurrences using a key that appeared EARLIER IN THIS RUN tends to 1. This follows from the classical elementary prime-counting bound pi(x)=O(x/log x), and does NOT assert that such macroscopic runs actually exist.

This theorem addresses a limitation of prior CRT synthetic paths: those can be arbitrarily long for each finite event count, but their length need not fill a fixed positive fraction of a canonical window. **Any macroscopic reset-only obstruction inside a genuine capped window must be reuse-heavy, not a forever-fresh-prime chain.**

## 6. Verification and remaining challenge

[reset_backbone_mod12_audit.py](reset_backbone_mod12_audit.py) verifies:
- all individual prime clocks and exact first gcds for 20,100 independent aligned synthetic states s=13..20,112;
- all four sharp 12-wheel directional recharge minima by modular search for primes p=1 mod12 up to 500;
- exact signed/gcd facts for the genuine A166944 trajectory from index2 through 2,500,000 (249 later nonunit events), and for synthetic canonical-shaped M=367,100549,101119;
- sentinel sharpness witnesses, composite-exclusion and no-consecutive-composite checks.

On the authentic 2.5M prefix the **strictly parity-aligned** reset subclass has 26 reset events, 18 maximal runs and longest run length 3, including seven occurrences of composite e=9 and three of e=25. This is different from the prior 36 k=1 counts over all low-offset states, because some states with X in {0,6} are NOT parity aligned (for example small e=3 can produce X=6 at an even index).

**Remaining OPEN:** (4)-(8) prove real reset-fuel obligations without double counting for each individual p, but different-prime recharge windows may overlap; even an Omega(sqrt M) repetition count need not exceed the available O(M) growth. A global cross-key, path-realizable Hall / capacity bound, or another invariant using the permanent 3mod4 sentinel, would still be required to exclude bad cutoff crossings. None of these results proves Cap B or twin-prime infinitude. No new Lean kernel compilation was performed.
