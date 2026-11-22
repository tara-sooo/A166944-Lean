# A166944: event-localization sufficiency and directional prime-clock preemption

Date: 2026-11-22 JST. **Status:** two elementary paper deductions, independently checked with exact parity-gcd event-jump arithmetic; new conjectural strategy. **No proof of event localization, Cap B, or twin-prime infinitude. No Lean kernel build.**

Related: [Shevelev companion dual/reset/diamond comparison](2026-11-22-shevelev-dual-reset-commuting-diamond.md), [BAD event density/recycling](2026-11-22-bad-path-prime-reuse-roughness-dichotomy.md), [BAD last-hit clock](2026-11-22-bad-last-hit-clock-skeleton-and-twin-depth.md), [terminal BAD/GOOD](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md). Companion exact audit: [event_localization_clock_preemption_audit.py](event_localization_clock_preemption_audit.py).

## 1. A different sufficient theorem: localization of the LAST event, not bounding event COUNT

For a genuine (or artificial) canonical-shaped state M odd >=7, put s=M+2, K=floor((7M-1)/4), D(s)=2M-2. Let S(M) be the last nonunit event index n in (s,K], or s if there is no event.

From the proven BAD-path frozen first-hit argument, a BAD terminal pair D(K)±1 necessarily satisfies

    K-S(M) <= 2 sqrt(2K+1).

Consequently, for all sufficiently large canonical-shaped M, any *event-localization* theorem

    BOXED: S(M)-s <= M/2                                  (L)

implies GOOD at K: because K-s~3M/4 and then K-S~M/4 >> sqrt M.

For induction along the genuine A166944 record chain, it would suffice to prove (L) eventually for all truly attained canonical states. An even weaker sufficient asymptotic statement is S(M)-s=o(M) along the attained records, whereas an O(sqrt M log M) upper bound is a stronger possible but presently speculative goal.

**Crucial distinction:** (L) does NOT bound the number of nonunit hits, the total repeated-prime-factor count R, or a priori their total growth. Thus it is compatible with the numerous HIGH-R artificial GOOD windows found earlier. It aims to explain why the many factor-reuse events nevertheless occur EARLY, allowing an exceptionally long quiet terminal interval. This avoids targeting a uniform R <=0.2004 sqrt M bound that has high-R GOOD synthetic counterexamples.

Selected EXACT factorized first-hit replay data, whose genuine status is established separately from original-seed scans:

    M       type                N   S-(M+2)    [S-(M+2)]/sqrt M     K-S
    305     artificial BAD     26     220           12.597              6
    365     artificial GOOD    29     203           10.626             68
    5419    genuine GOOD        9      75            1.019           3987
    28549   artificial GOOD  177    1887           11.168          19522
    113623  artificial GOOD  107    2181            6.470          83034
    355723  genuine GOOD       57    1317            2.208         265473
    475381  artificial GOOD  186    4173            6.052         352360
    22933441 genuine GOOD    209   14343            2.995       17185735
    91793059 genuine GOOD     53   15195            1.586       68829597

These finite observations favor event SPATIAL CONCENTRATION over counting upper bounds. They do not prove any uniform asymptotic concentration theorem.

## 2. Exact canonical deficit-coordinate reformulation

Write

    X(n)=2n-D(n),      d(n)=D(n)-D(n-1)+1.

Then for all n>=3, the original parity-sensitive gcd equations are EXACTLY

    n even: d(n) = gcd(n, X(n-1)+3),
    n odd:  d(n) = gcd(n-2, X(n-1)-3),                   (X1)

and

    BOXED: X(n)=X(n-1)+3-d(n).                          (X2)

At a canonical start s=M+2, X(s)=6. Thus a unit step adds +2 to X; an event of size3 leaves X invariant; an event e>=5 decreases X by e-3. This gives a deterministic "drift-up / sudden-drop" excursion picture. The swapped parity clocks in A167493 amount to interchanging which of X+3 and X-3 is read at even/odd indices, but they do not keep the two evolving X values equal.

This coordinate makes event order and the *failure* of merging visible, without requiring a new external shadow process. Any local event-normal-form proof would have to control the frequency, size and timing of downward jumps relative to upward drift, especially after the state moves far above X=6.

## 3. NEW directional preemption/recharge lemma for distinct event sizes (PAPER)

Let C be an even pre-event horizon. Suppose q>=7 is odd prime and q divides at least one of C-1,C+1 (at most one, since gcd(C-1,C+1)=1). A different earlier event with odd increment e satisfying 5<=e<q changes horizon to C'=C+e-1. Then:

    (a) q divides NEITHER C'-1 nor C'+1, so that event
        cancels q's currently active clock unconditionally.

    (b) For any LATER EVEN horizon C''>=C' with q|C''±1,
        the extra growth y=C''-C' (even, nonnegative) satisfies

        q|C-1  ==>  y >= 2q-e-1 >= q+1,
        q|C+1  ==>  y >= 2q-e+1 >= q+3.               (R)

The side-specific minima 2q-e-1 and 2q-e+1 are EXACTLY attainable as congruence solutions; they are the smallest nonnegative *even* values of y satisfying the target activation congruences. They are not a claim that the true recurrence must produce such a recharge.

Proof: if q|C-1 then C≡1 modq, so C'≡e modq. The future activation targets are ±1 modq. Since e and q are odd and 5<=e<q, the least positive EVEN lifts of y≡1-e or -1-e modq are 2q+1-e and 2q-1-e. The minimum is 2q-e-1. If q|C+1 then C≡-1, C'≡e-2, and the least positive even lifts to ±1 are 2q+3-e and 2q+1-e; the minimum is 2q-e+1.

**Exceptional increment e=3:** if q|C+1 and e=3, the shift by2 carries C from -1 to +1 modq, *immediately switching the active side*; the q clock is not deactivated. For q|C-1 and e=3, the q clock deactivates and the smallest future even recharge is 2q-4. This special parity-side switch is an important exception to any blanket "all small preemptions kill large clocks" argument.

**Interpretation as directed noncommutativity:** An event of size e<q, e>=5, cannot pass an already active q clock without destroying it and forcing >=q+1 later growth for q to fire again. This blocks naïvely porting Shevelev's *same-q* two-step additive commuting diamond into a cost-free two-distinct-prime swap in the original recurrence. Conversely, a large event could change a small q clock without this barrier, depending on the residue of e-1 modq. The precedence relation is highly asymmetric. Multiple q clocks could share the SAME recharge growth; summing (R) across primes without a non-overlap argument would be incorrect.

Example (local exact original parity-gcd): pre-horizon C=36 at even n=40 has q=7 active via 7|(C-1)=35, and e=gcd(40,35)=5. C'=40 has neither neighbor divisible by7. The anticipated q-hit at even n=42 is suppressed; at least 2*7-5-1=8 additional EVEN horizon growth is needed before 7 can be active again. This is not presented as an attained original record.

Exhaustive arithmetic audit: 21,066 side/e pairs for odd primes 7<=q<501 satisfy exact minima, with no failures.

## 4. Research idea: an event-normal form with a deficit/defect budget

Instead of globally bounding R, investigate each late prime q clock along the canonical window:
- Was it already active before a smaller increment e>=5? If so the exact recharge penalty (R) applies before any subsequent q-event.
- Was it only created by a foreign increment while previously inactive? If so charge it to that catalyst's event and track possible sharing across many q.
- Did e=3 flip its active +/- side at no recharge cost? Handle this as a separate mod3/phase-switch transition.
- Can several large q clocks share a single growth interval that satisfies all their recharge congruences? Use the exact CRT of the targets, not the sum of independent recharge lower bounds.

The plausible new target is a **synchronization-versus-escape** dichotomy: all but a controlled number of incompatible clock preemptions can be merged/cancelled at bounded cost, leaving a last nonunit event before a fixed linear fraction of the canonical cutoff. The specific sufficient global theorem is event localization (L), which excludes BAD even if R is enormous.

This is a concrete testable research program, not a theorem yet. The difficult missing step is a quantitative simultaneous-charge/CRT overlap inequality across multiple q recharges. The simple single-q recharge lemma is true for all trajectories but by itself gives NO global last-hit bound. Its value is to constrain proposed event-order swap/merging diagrams and provide a side-specific minimum cost.

## 5. Scope

The OEIS A174214/A174216 reset model has an exact "long quiet interval iff twin primes" certificate. It recasts the underlying obstruction rather than resolving it. The A167493 vs Shevelev f(n) local diamond is genuine, but same-q timing shifts in distinct recurrences do not automatically produce free commutation of different prime hits in A166944. The directional preemption lemma is an exact difference worth using, not a twin-prime theorem. **Cap B and twin-prime infinitude remain open; all new mathematics here is paper-level and finite integer checks only.**
