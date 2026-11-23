# Twin-prime-first: dynamic inverse sieve audit, sparse active-prime cone, and one-large-prime insertion theorem

2026-11-23 JST, Issue #3 / #4. Focus: try to lift the finite LOW7 pairwise Lyapunov potential and the 2026 Jacobsthal inverse/stopped-bin method to the complete clipped squarefree prime-clock wheel. Exact elementary deductions, a sharp unbounded-prime-family theorem conditional only on the previously certified finite LOW7 graph, and reproducible finite diagnostics are below. **No bound tau_{p<=B}=o(B^2) is obtained, so this note is NOT a proof of twin-prime infinitude.** The new mathematical deductions are paper-level, not newly Lean-checked. The separate LOW7 22,050-state numerical potential was Lean kernel checked in draft PR #5 / Actions run 45130164879.

## 1. The crucial distinction: canonical numerical cone versus the full CRT torus

For the canonical full clipped squarefree trajectory associated with odd M in [X,2X), t=M+2, K=floor((7M-1)/4), and cutoff B=ceil(sqrt(7X)), the elementary invariant 2M-2<=C<=2n holds for every plateau n<=K. Consequently C<=2K<7X<=B^2. In the unrestricted 2P^2-state automaton, where P=product_{p<=B}p and state coordinates are only residue classes, a representative C can be as large as O(P); this **does not** satisfy the numerical cone bound. It is therefore material whether an analytic estimate is claimed for all CRT residues or for the actual canonical trajectories.

At a plateau, let A_Q(C) be the active primes p in [Q,B], i.e. p|(C-1)(C+1). For even C, gcd(C-1,C+1)=1. All active primes are distinct factors of C^2-1, and therefore

    product_{p in A_Q(C)} p <= C^2-1 < B^4,
    |A_Q(C)| * log Q < 4 log B.               (ACTIVE-CONE)

For Q=B^alpha (0<alpha<=1): **|A_Q(C)|<4/alpha**, pointwise for every canonical plateau. For Q=B/2 and B>32: **at most four top-half primes are simultaneously active** (since (B/2)^5>B^4 for B>32). These are genuinely universal inequalities on the canonical numerical cone, not heuristics about random residue classes. They do NOT bound the number of *successive births and deaths* of active primes over a long trajectory.

## 2. A sharp prime-insertion lemma: time and growth from a smaller finite wheel

Let S be any finite set of odd primes whose unbounded event-clock graph has no directed cycles, whose **uniform** total travel is <=L, and whose **uniform** clipped growth is <=G, for every state (t,C), C even. Let q be any odd prime not in S and assume

    q-1 > G.                                      (INSERT)

Then in the full S union {q} wheel:

1. **q appears in at most one nonunit event.** After any q event, C mod q is either 0 (even q event) or -2 (odd). To activate q again from a q-free path of even growth E requires E>=q-1 (after an even q hit; odd q hit requires E>=q+1). But the path from the post-q plateau until its next hypothetical q event is a PREFIX of the S-only trajectory, and hence E<=G<q-1, contradiction. Tied events with q and other S primes do not change the post-q residues or the argument.
2. **Total travel <=2L+2q.** There is an S-only prefix of travel <=L before the first q event; its q clock from the last frozen plateau has gap <=2q. After that q event, the remaining trajectory is S-only and has travel <=L. If no q event, travel <=L.
3. **Total growth <=2G+q P_S-1**, where P_S=product_{p in S}p: the unique q event is d=q*a with a|P_S, so d-1<=qP_S-1.

Apply with S={3,5,7}, L=56, G=106 (kernel-verified finite certificate). For EVERY prime q>=109 and EVERY even-state start, including states not derived from canonical M,

    # q-bearing events <=1,
    tau_{3,5,7,q}(t,C) <= 2q+112,
    total clipped growth <=105q+211.         (ONE-HIGH)

This is a proved-by-elementary-argument INFINITE FAMILY of prime alphabets, not merely a finite simulation. It is not the all-primes-up-to-B alphabet needed for twin-prime infinitude: other high primes can donate growth that exceeds 106 and enable q reactivation.

The threshold is sharp for the arbitrary-state statement. For q=107, start at (t,C)=(5563,5458). The literal full {3,5,7,107} wheel has q event (n,d)=(5564,107), followed by (5567,105), (5568,3), and then the SECOND q event (5673,107). The intermediate LOW7 growth is 104+2=106=q-1. This state even satisfies 0<C<2t; hence the gap at q=107 is real, not a residue-only artifact.

**Additional finite canonical-origin strengthening.** Exhaustively enumerate the odd M residues modulo 2*105*q, using t=M+2, C=2M-2 and the SAME clock algorithm. For each prime 11<=q<=107 there are precisely 105*q canonical classes. On all 142,170 classes across 24 prime values, each q>=29 fires at most once. Small q=11,13,17,19,23 do repeat: q=11 gives 15 refiring canonical classes and q=23 gives three. For q>=109, the analytic ONE-HIGH theorem applies without enumeration. Hence the one-high bound for all canonical origins and all q>=29 is supported by an exact finite complete residue audit plus the infinite-tail theorem. This finite claim has not been Lean kernel checked and cannot be transferred to the full all-prime wheel: intervening foreign-high events change the post-q state ancestry.

## 3. Why the 2026 Jacobsthal inverse-rational-alignment theorem does not automatically transfer

Primary paper: OpenAI, *A quadratic bound for Jacobsthal's function* (Sep 25 2026), particularly Section 8 (the inverse alignment criterion Da_p = A mod p), Sections 9-10 (variance, stopped prime bins), and Theorem 1.2. HTML primary text available at https://wcook04.github.io/plectis-atlas/papers/A-quadratic-bound-for-Jacobsthals-function-September-25-2026.html ; original paper https://github.com/openai/math/blob/main/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf . The theorem is for one **fixed prescribed residue class per prime**, not a time-dependent clock.

At a frozen (t,C) plateau, the EVENT-TIME residue for any ACTIVE p is EXACTLY either

    a_p = 0 (mod p), if p|(C-1) (even n),
    a_p = 2 (mod p), if p|(C+1) (odd n),

plus the separately specified parity of n. Thus **EVERY active prime is already aligned with one of the two bounded rationals 0/1 and 2/1** in the inverse theorem's sense. Alignment is not a rare exceptional configuration in our problem. The existing Jacobsthal inverse estimate, applied to these event-time classes alone, gives no restriction on the number of reactivations; the structural challenge is **when primes become active, die, and reactivate** as C changes. Its stopped-bin and variance tools may inspire a dynamical analogue but do not supply one here.

A plausible corrected transfer must control the source-selected, event-triggered *birth/race process*, not classify the 0-or-2 event calendars as pseudo-random. In particular, at an event of increment d, a new p activation requires

    p|(C+d-2)(C+d), but p does not divide (C-1)(C+1),

where C is the pre-event value. The event d itself is selected adaptively by gcd clocks. Controlling these selected divisibilities is the remaining arithmetic-correlation task.

## 4. Exact activation/return ledger; why pointwise sparsity is not enough

For any prime q>=5, a q-bearing event kills q activity (C mod q becomes 0 or -2). Every repeated q firing therefore needs a subsequent **birth** of q into the set of active primes, at some intervening non-q event. Hence for any interval and prime band J,

    R_J = number of successful post-first-q activity episodes
        <= number of q births AFTER the first q hit.     (BIRTH-CHARGE)

An activity episode is a consecutive run of plateaus with q active; it ends by q firing (success) or deactivation without q firing (failure). Repeated q firing is injectively assigned to its immediately preceding successful reactivation episode. This is an exact combinatorial identity, not a probabilistic assumption.

Strict original parity-GCD audit of all odd canonical starts at X=4096, 16384, 65536, 262144, with q>=B/2 and counted q even when masked by smaller simultaneous factors:

    X       B   top-q first top-q returns   post-first top-q births  max simultaneous top active
    4096    170      571          11                104                      4
    16384   339     2139           8                240                      4
    65536   678     8585           0                605                      4
    262144 1355    29749           0               1678                      4

The gap between post-first births and actual q returns is large: in the X262144 top band 1,678 births follow a prior q firing, yet ZERO top q returns occur. This is the foreign-prime clock-race preemption mechanism. Merely proving at most four simultaneous active top primes cannot turn the birth upper bound into the desired o(XB) returns.

An independent random stress test of **arbitrary even post-q states inside the numerical cone C<=2t and C<B^2** finds actual q returns while some LOW7 clock is active, e.g. at X8192, B240, (q,t,C)=(229,11223,18318), next q event at 11450 with LOW7 active. This is a valid clipped clock start/trajectory, but is **not identified as a state reached from an actual canonical M**; a claimed pointwise no-low-active q-return lemma on the numerical cone alone is false. A positive result must exploit stronger canonical ancestry or source averaging.

## 5. A deterministic large-composite tail bound

For any canonical trajectory through the cutoff K, its total growth satisfies G_total=C(K)-(2M-2)<B^2. An event has increment d>=3 and preceding clock gap g<=2*min_{p|d}p<=2B. For any threshold Y>2, the number of events with d>=Y is <B^2/(Y-1). Their total preceding clock travel therefore obeys the uniform bound

    sum_{events: d>=Y} g < 2 B^3/(Y-1).            (BIG-INCREMENT)

Taking Y=B^(1+epsilon), 0<epsilon<1, makes this O(B^(2-epsilon))=o(B^2). Thus very large simultaneous-factor events are **unconditionally negligible for elapsed clock time**, even though they can contribute dramatically to growth. The missing o(B^2) bound can focus on events with d<B^(1+epsilon), including prime-only high events and their successful reactivations. Finite X4096 through 262144 showed no events above the chosen threshold ceil(B^1.25), but the uniform inequality itself does not depend on this observation.

## 6. Current theorem target, with the genuine missing estimate

For canonical starts, an unconditional bound tau_{p<=B}(M+2,2M-2)=o(B^2) uniformly in odd M in [X,2X) would imply infinitely many twin primes by the previously established terminal twin certificate: K-(M+2)=(3/4+o(1))X ~3B^2/28, and 2B=o(B^2). An O(sum_{p<=B}p)=O(B^2/log B) bound is more than enough, but NOT proved.

The candidate route is now more precise:

* Treat the canonical numerical cone C<B^2, where each logarithmic top prime band has O(1) simultaneously active primes, as the actual domain of the Lyapunov estimate.
* Use the exact one-large-prime insertion theorem as a base case for a **dynamical prime birth/race** expansion; each q>=109 return requires other-high-prime donations, and giant composite increments can be omitted from the elapsed-time budget by BIG-INCREMENT.
* A stopped-bin/inverse estimate would have to quantify how often a *selected* newly active large q wins its calendar clock before other prime clocks change C. The rational intercepts of time classes are already 0 or 2, so the inverse theorem's rarity-of-alignment step cannot be reused unchanged.
* Still OPEN: an unbounded, source- or history-weighted estimate strong enough to bound successful q reactivation episodes (equivalently the repeat-owner weighted clock budget) by o(B^2). Neither ACTIVE-CONE, the finite pairwise LOW7 potential, BIRTH-CHARGE, nor ONE-HIGH on its own yields this all-prime estimate.

This is a corrected research target, not a theorem that the twin prime conjecture has been resolved.

## 7. Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low7_large_prime_bridge.cpp -o /tmp/low7_onehigh
/tmp/low7_onehigh
python3 research/low7_onehigh_literal_oracle.py

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/canonical_active_birth_sieve_audit.cpp -o /tmp/active_birth
/tmp/active_birth 4096 16384 65536 262144
```

The C++ low7 large-prime checker exhausts canonical residues 11<=q<=107 and validates the q107 multiple-hit witness; the independent Python verifier checks direct per-integer gcd dynamics against the first-hit event algorithm on 891 small source cases plus the q107 witness; the activation scanner follows the ORIGINAL full clipped-GCD wheel and checks fired-prime deactivation and R<=post-first births for all specified test windows. Existing LOW7 kernel verification is separate (PR #5). No changes to main.