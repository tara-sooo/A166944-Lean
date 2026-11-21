# Cross-key startup credit, extremal-gap localization, and a new slow-interval test

Date: 2026-11-22 JST. **Status: paper theorems and direct integer audits.** The new assertions are not Lean-kernel compiled. The global Hall inequality for the Lean residual-phase 24/11 balance, Cap B for all authentic records, and twin-prime infinitude remain **open**.

This note continues [Cap B prime-debt mod 210](2026-11-21-prime-debt-mod210.md), [the existing prime-overlap finite reductions](2026-11-21-cap-b-prime-overlap.md), and [the phase-switch CRT capacity note](2026-11-22-phase-switch-crt-lift-and-event-capacity.md). The purpose is to count growth **only once** across overlapping requests of distinct primes, and localize any unpaid residual to a very narrow near-maximum-gap subcase.

## 1. Prerequisite: the 210-state potential

At a genuine first-hit event (s,C) -> (r,C'), set g=r-s, e=d(r), and C'=C+e-1. The committed [finite 210-potential verifier](cap_b_prime_debt_210.py) certifies a function V with 0<=V<=29 and the step inequality

    g + V(after) <= (e-1) + V(before) + b,           (1)

where b=0 for composites and prime increments 3,5,7, and for a prime e=p>=11,

    b = max(0, g-(p-1)+V(after)-V(before)).         (2)

For positive-debt prime p>=61, the pre-event horizon is inert modulo 210, hence V(before)=0. For the results below the weaker generic bounds 0<=V<=29 suffice.

The kernel-proved first-hit factor bound gives g<=2p. Thus b<=p+30, and the **overdraw**

    eta = max(0, b-(p-1))

obeys 0<=eta<=31.

Moreover, eta>0 implies

    g > 2*(p-1) - (V(after)-V(before)) >=2p-31,

and since g is an integer,

    2p-30 <= g <=2p.                              (3)

The kernel-proved cofactor gap estimate g*p<=2*(C+1) then yields

    p*(p-15) <= C+1                               (4)

for every overdraw event with p>=61. In particular, on a canonical cutoff interval with pre-event C<=2K, such p is <=isqrt(2K+1)+15. This is a stronger size restriction for these exceptional events than for arbitrary positive-debt events.

## 2. Main new theorem: overlap-free startup credit for arbitrary prime keys

Consider a genuine first-hit path, and select a finite set P of distinct primes >=61. For each p in P, select 2m_p+1 chronological **positive-debt** p-event occurrences, m_p>=1. The first occurrence is the free **startup event**; the remaining 2m_p occurrences are demand events, grouped into m_p adjacent paired requests. Other, unselected events may occur anywhere. Let

- A be the smallest selected pre-event horizon;
- B be the greatest selected pre-event horizon, and p_* the prime used by that final selected event;
- R=sum_p 2m_p be the number of demanded events;
- Debt=sum over all demanded events of their individual b;
- Excess=sum over all demanded events of eta=max(0,b-(p-1));
- k=#P and p_min=min P.

**Theorem (exact aggregate accounting).**

    (B-A)-Debt >= sum_{p in P, p!=p_*}(p-1)-Excess.   (5)

In particular,

    (B-A)-Debt >=(k-1)*(p_min-1)-31*R.              (6)

If (k-1)*(p_min-1)>=31R then **every selected paired request is paid in aggregate by the one actual horizon span B-A**, independently of how the requests for distinct primes overlap. Thus any aggregate deficit requires

    (k-1)*(p_min-1)<31R.                           (7)

It also requires enough exceptional near-maximum gaps to satisfy

    #{demand events with eta>0} >
        (sum_{p!=p_*}(p-1))/31.                     (8)

**Proof.** Since C' = C+(p-1) at a selected event, every selected event except the unique one starting at pre-horizon B contributes its own p-1 growth inside [A,B]. Every other event contributes nonnegative growth. There are 2m_p+1 selected events for each key p, so

    B-A >= sum_p (2m_p+1)*(p-1) - (p_*-1).

For each demanded event, b <=(p-1)+eta. Summing the 2m_p demand events and subtracting from the preceding bound gives exactly (5). Equation (6) follows from eta<=31. If the left side of (5) is negative, the right side must also be negative, which implies (7) and (8). QED.

This uses the *actual ordered increment growth* and does not double-count a separator event even if it lies inside many different prime-reuse windows. It is a new generalization of the elementary many-distinct-key event-growth argument from the previous [overlap note](2026-11-21-cap-b-prime-overlap.md) to **arbitrary repeated request counts**.

**Important scope distinction:** This is an aggregate necessary/funding test for the earlier mod-210 **prime debt b**, not yet a complete interval Hall allocation for the different 24/11 **residual-phase signed balances** in [CreditWindows210.lean](../A166944/CreditWindows210.lean). An aggregate inequality for one family of requests does not automatically establish every Hall subwindow for that later formalized model.

## 3. Sparse long-prime paths reduce potential deficits to bounded key count

Suppose on a hypothetical sequence of genuine canonical records M->infinity we have N_M<=A*sqrt(M) (for fixed A>0), and consider requests whose every prime key satisfies p>=a*sqrt(M) (for fixed a>0). Then R<=N_M and (7) implies, for any unpaid aggregate collection,

    k < 1 + 31*A*sqrt(M)/(a*sqrt(M)-1)
      = 1 + 31*A/a + o(1).                         (9)

Thus the **number of distinct keys in any such deficient collection is bounded independently of M**; it cannot itself grow like sqrt(M)/log(M).

For the specific long-gap reduction in [prime/composite slow obstruction](2026-11-22-prime-composite-slow-obstruction.md), one may take a=3/(16A), giving the explicit conditional asymptotic bound

    k < 1 + (496/3)*A^2 + o(1).                     (10)

This is a bounded-key reduction **for the large-prime subcollection under the stated sparse-event premise**, not a proof that the entire interval has a bounded number of prime keys, nor a bound on small-prime events.

## 4. Independent new finite sufficient slow-interval criterion

Let M>=23 be an **actually attained canonical record**, s0=M+2, K=floor((7M-1)/4), and G_M=D(K)-(2M-2). Define H_M as the number of prime-increment events with p>=11 in (s0,K] whose potential debt satisfies b>p-1 (equivalently eta>0).

Let S be the last nonunit event index <=K, taking S=s0 if there is none. Summing (1) from s0 to S, and using V(s0)<=27, yields

    S-s0 <= G_M +27+sum_prime b
          <=2*G_M+27+31*H_M.                       (11)

The previous adaptive quiet-block lemma says that a completely unit-increment block of length

    L(u)=14+2*isqrt(2u+1)

from u>=24 is a slow interval. If no slow interval exists within [s0,K], the terminal unit suffix K-S is <L(S)<=L(K). Therefore absence of a slow interval implies

    K-(M+2) <=2*G_M+31*H_M+41+2*isqrt(2K+1).     (12)

**New sufficient criterion (contrapositive):** if

    2*G_M+31*H_M+41+2*isqrt(2K+1) < K-(M+2),   (13)

there is a slow interval in [M+2,K], hence Cap B for that record by the previously inspected conditional slow-interval theorem.

Along unbounded *actual* canonical records M, the still-unproved sufficient hypothesis

    liminf (2*G_M+31*H_M)/M < 3/4                 (14)

would force infinitely many slow intervals and thus infinitely many twin primes using the existing mission implication. When H_M=o(M), the simple condition liminf G_M/M<3/8 suffices; it improves the bare endpoint-F criterion's 1/3 coefficient **under that additional premise**. Neither premise has been proved unconditionally.

This deduction relies on the **finite 210-potential certificate** and the previously recorded adaptive quiet-block lemma, both currently paper/certificate-level, not all Lean-compiled.

## 5. Direct finite evidence and reproduction

The companion [cross_key_startup_credit_audit.py](cross_key_startup_credit_audit.py) imports the original [210-potential verifier](cap_b_prime_debt_210.py) and rechecks its 22,050-state certificate, then performs:

1. 1,200 seeded abstract event-word accounting tests, of which 649 satisfy the stronger key-count certificate (6). These stress only the exact growth accounting, not first-hit realizability.
2. A **direct exact-gcd synthetic** sequence from state (s,C)=(8,289,324,16,578,642), with three 61-event pre-horizons 16,578,642, 16,578,762, 16,579,008 and b=(28,40,12). The selected span has B-A=366, paired debt b2+b3=52, Excess=0. This is an artificial start, not a certified canonical record.
3. The **actual** recurrence from a(1)=2 through 2,500,000: 250 nonunit events, just 5 positive-debt **prime p>=61** events, 5 distinct p keys, and zero eta>0 among those five. All individual bounds (3)-(4) were checked wherever applicable. Finite evidence is not an asymptotic estimate.
4. The official previously certified threshold M=45,895,573: exact replay of 37 events from its canonical state gives terminal (S,C)=(45,896,532,91,793,058), G_M=1,914, and H_M=2, corresponding to (p,g,b,eta)=(17,30,24,8),(47,90,48,2). Both 91,793,057 and 91,793,059 are prime, certifying no further hits before K=80,317,252. For (13):

    left side = 2*1914+31*2+41+2*12674 = 29,279;
    right side = 80,317,252-(45,895,573+2) =34,421,677.

The criterion is decisively satisfied for this finite record. Its authentic attainment uses the existing A166944 certified record history; the script independently replays only the subsequent 37 events.

## 6. Remaining mathematical obstruction

The bound (5) **settles overlap-free accounting for collections with sufficient distinct-key startup credit**, and it isolates unpaid debt to exceptional g>=2p-30 events. It does **not** establish the desired global Hall inequality for arbitrary repeated keys. For few keys, (7) may fail even if all actual requests are ultimately fundable; in the general case the fraction of near-maximal events is not asymptotically bounded.

Crucially, (5) handles **prime debts in the 210-potential ledger**; it does not automatically pay the 24/11 residual balances already formalized under CreditWindows210. A bridge relating their credits, or a separate first-hit estimate on their minimal deficient windows, is needed before reaching the final Cap B theorem.

**Verification level:** mathematical proofs in sections 1–4, finite Python and direct-gcd audits, GitHub persistence and readback. No new Lean kernel proof, no unconditional bound (14), no claim to have proved infinitely many twin primes.
