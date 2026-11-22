# A166944: unconditional BAD-path prime reuse and square-root rough-pair dichotomy

Date: 2026-11-22 JST. **Status:** new elementary paper theorems, independently computed authentic and artificial gcd checks. The universal GOOD/Cap B theorem and infinitude of twin primes remain OPEN. No new Lean kernel compilation.

This continues [terminal BAD/GOOD dichotomy](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), [budgeted CRT/first-hit wheel](2026-11-22-budgeted-first-hit-crt-anti-resonance.md), [cross-prime overlap CRT](2026-11-22-return-overlap-CRT-energy.md), and [reset-only reuse](2026-11-22-reset-backbone-mod12-recharge-and-sentinel.md). The key change is that the following event-density and factor-reuse necessity holds on the **ENTIRE hypothetical BAD canonical path**, without assuming an aligned k=1 backbone, bounded excitation count, frozen wheel, a dyadic prime band, or any CRT motif.

## 1. The BAD hypothesis forces ALL event gaps to be O(sqrt M)

Let M>=23 be an actually attained canonical record. Set

    s0=M+2; K=floor((7M-1)/4); C0=D(s0)=2M-2;
    C=D(K); G=C-C0; T=K-s0; h=isqrt(2K+1).

Assume C-1 and C+1 are NOT BOTH prime (BAD at the cutoff). Denote by N the number of nonunit events in (s0,K], and list their indices s1<...<sN. Include the two endpoints s0 and K, forming m=N+1 nonnegative gaps g0=s1-s0,...,gN=K-sN (with the obvious convention N=0).

At every state s_i<=K after an event (including s0), let C_i=D(s_i). Since C_i>=2M-2>K and C_i<=2K, **both C_i-1 and C_i+1 cannot be prime**: otherwise there would be no nonunit gcd event through K and the terminal neighbors would be prime, contradicting BAD. Therefore at least one C_i +/- 1 is composite. Its least proper prime divisor q is <=sqrt(C_i+1)<=h. The exact factor-clock first hit after s_i is at distance <=2q<=2h. Hence every complete gap and the final censored gap obey

    boxed: 0<=g_i<=2h.                                  (1)

This argument uses the actual minimum-gcd first-hit rule for *all* steps; it does NOT assume the increment is itself prime or is a reset.

The exact whole-window budgets are

    T=sum_i g_i >= (3/4)M-4;
    G=sum_{hits}(e-1) <=2K-(2M-2)<=(3/2)M+2;
    2h <4 sqrt(M).                                    (2)

Consequently

    boxed: N+1 >= T/(2h),
           N >= (3/16-o(1))*sqrt(M).                    (3)

For fixed large M, the weaker explicit N>=sqrt(M)/6 holds for M>=4,000,000.

## 2. UNCONDITIONAL repeated-prime-factor necessity on every BAD path

Among N nonunit events, at least floor(N/2) have

    e-1<=2G/N <=(16+o(1))*sqrt(M).                     (4)

This follows from the event-growth sum G and (3). Select one odd prime factor p of each of these events. All selected primes satisfy p<=e<=(16+o(1))*sqrt(M), so the number of different possible p is at most

    pi((16+o(1))*sqrt(M))=o(sqrt(M)).

All selected occurrences except the first for each distinct p are **REUSES** of a prime factor along the actual path. Thus:

**Theorem A — global BAD-path recycling, without backbone hypotheses:**

    boxed: repeated prime-factor event occurrences
           >=(3/32-o(1))*sqrt(M).                       (5)

This counts event occurrences, not necessarily distinct reused keys; one event is assigned only ONE selected factor and is not counted twice. An explicit finite-M lower bound for M>=4,000,000 is

    R >=sqrt(M)/12-1-pi(floor(19*sqrt(M))).            (6)

The right-hand side becomes positive only at sufficiently large sizes; (5) is the substantive asymptotic statement. It is a necessary condition on any BAD canonical path, not a contradiction.

The earlier prime-reuse asymptotic required a macroscopic aligned k=1-only run. (5) removes that prerequisite completely.

## 3. Multiscale gap packing forces MANY simultaneous rough-neighbor pairs in sparse BAD paths

For any real threshold 0<lambda<2h, let Q_lambda be the number of the m gap lengths g_i which are >=lambda. Since each short gap is <=lambda and each long gap <=2h, exact interval packing yields

    boxed: Q_lambda >= max(0,(T-lambda*(N+1))/(2h-lambda)).  (7)

For every counted gap beginning at some s_i, all prime factors q of BOTH horizon neighbors C_i-1,C_i+1 satisfy

    boxed: q >= g_i/2 >=lambda/2.                       (8)

Proof: a prime q dividing either neighbor would by parity CRT create a nonunit event at one of the next 2q indices if C_i stayed fixed. If a sooner nonunit event occurs, that is already the endpoint of the gap. Therefore the first event or the endpoint of the censored no-event suffix cannot be later than 2q. Equivalently, a gap of length g forces 2q>=g. This is a two-sided **rough-neighbor sieve**, for every factor and every sign, not just a least-factor statement. For all odd primes q<lambda/2, C_i modulo q avoids +1 and -1 simultaneously.

Suppose N<sqrt(M), take lambda=sqrt(M)/4. By (2) and (7),

    Q_lambda >=(1/8-o(1))*sqrt(M).                     (9)

For M>=4,000,000 a safe explicit bound is Q_lambda>=floor(sqrt(M)/9). These are DISTINCT increasing event-horizon states.

Each such C_i is in [2M-2,2K], so C_i+1 <3.5M+1. Meanwhile each prime factor of C_i-1,C_i+1 is >=sqrt(M)/8. At M>=4,000,000,

    (sqrt(M)/8)^3>3.5M+1.

Therefore both C_i-1 and C_i+1 have **at most two prime factors counted with multiplicity**: each is a prime or a semiprime P_2. Since BAD forbids both being prime at a state, at least one of each pair is semiprime.

**Theorem B — unconditional sparse BAD structural alternative:**

    N<sqrt(M)  ==>  at least floor(sqrt(M)/9) distinct
                     C_i with BOTH C_i +/-1 P_2 and
                     ALL their prime factors >=sqrt(M)/8. (10)

There is NO assumed reset-only run, primality of the input M, or small fixed wheel in the proof, except the genuine canonical starting-state/height inequalities and terminal BAD assumption.

**Four-prime-clock corollary:** each C_i has at most four prime-factor clocks (counted with multiplicity) across its two neighbors. The exact NEXT hit is the minimum of those clocks. A neighbor that is itself prime cannot trigger a nonunit hit at index <=K<C_i-1, so only proper factors of semiprime neighbors participate in capped-window events.

## 4. In the sparse BAD branch, many event INCREMENTS are themselves prime and recycled

For every long gap in (10), other than a possible final gap ending at K instead of an event, the next actual nonunit event r<=K has increment e dividing one of C_i-1,C_i+1. Since both neighbors are P_2 and

    1<e<=r<=K<C_i-1<C_i+1,

**e must be PRIME**, even if the two factors of a semiprime are equal. By (8), e>=sqrt(M)/8.

Thus at least (1/8-o(1))*sqrt(M) events have prime increments e>=sqrt(M)/8. Their total e-1 growth is bounded by G<=(3/2)M+2; therefore at least HALF of these events have

    sqrt(M)/8 <=e<=(24+o(1))*sqrt(M).                (11)

The number of distinct primes in this fixed-multiple-of-sqrt(M) band is o(sqrt M). Consequently the number of events whose PRIME increment value has appeared previously in the same path is at least

    boxed: (1/16-o(1))*sqrt(M),                        (12)

under the sparse BAD hypothesis N<sqrt(M). For M>=4,000,000 one can use the weaker fully explicit statement: there are at least floor(sqrt(M)/20) prime-valued events with sqrt(M)/8<=e<=40*sqrt(M); the asymptotic repetition lower bound follows from prime counting.

**Unified statement:** every large BAD canonical path necessarily has Omega(sqrt M) repeated odd-prime factors (Theorem A). In the sparse branch, many such repeats occur as prime-valued increments at approximately square-root scale, and their immediate pre-hit horizon neighbors are prime/semiprime pairs (Theorems B and (12)). This is the requested GLOBAL STRUCTURE-EXISTENCE step. It is still a necessary condition, not yet a contradiction.

## 5. CRT + exact first hit converts a false budget candidate into an enforced BIG jump

Let (u,D(u)) be an exact starting state for a common-core interval (u,v]. Suppose the complete exterior factor-return constraints of a putative event history give an even growth CRT progression

    H=D(v)-D(u) ==b (mod 2P),   0<=b<2P,

and B=2(v-u)+X(u) is the intrinsic upper growth bound. Replay the exact h=b **truncated-factor wheel** from the previous note, with modulus Lambda_b=lcm(1,3,...,b+1), and let Z_b be its total growth.

**Theorem C — CRT first-hit lift and jump forcing:**

    Z_b !=b ==> H>=b+2P;
    Z_b<=b and H>=b+2P ==> some true event has e>b+1. (13)

Proof: budget-wheel soundness means H=b would reproduce Z_b=b. Thus H!=b, and the CRT progression forces H>=b+2P. If all true event increments were <=b+1, each divides Lambda_b and the entire truncated replay would be exact, yielding H=Z_b<=b, contradiction. If Z_b=0, the FIRST actual increment e>1 has **no prime factor <=b+1** (since its state coincides with the initial horizon until that first event, and the wheel never detects a small-prime hit). This gives a prime-roughness certificate, not merely a large-numeric-gcd certificate.

For pairwise disjoint certified cores of an alleged BAD path, their strengthened lower growth costs can be summed exactly once:

    boxed: sum_cores (b_i+2P_i) <= G_M.               (14)

Any chosen complete-fringe CRT history violating (14) cannot occur. This is a usable finite witness of impossibility, but no theorem currently guarantees a family of disjoint incompatible cores on every BAD canonical path.

**Genuine example A.** Original A166944 at (u,v]=(66,150], D(u)=132. Factor-return p=5,11 gives H==58 mod110 and B=168. Wheel at b=58 reports growth 6, not 58, so H>=168. Hence H=168; the true hits are (79,7),(141,139),(150,25). At least one e>59 is forced, realized by e=139.

**Genuine example B.** At (u,v]=(1339,2674], D(u)=2658 and B=2690, p=5,7 reuse gives H==16 mod70. Wheel b=16 predicts growth ZERO. Factorized exact next-hit clocks of C-1=2657 (prime) and C+1=2659 (prime) force first hit (2661,2659), adding growth2658. The smallest CRT candidate >=2658 is H=2676, and cap B=2690 forces H=2676. The remaining actual hits are (2667,13),(2674,7). This is a large-scale, exact original-sequence anti-resonance certificate with no guessed increment.

## 6. Critical fixed-wheel limitation, shown by a true trajectory

At authentic event state (s,C)=(356268,712530), C is divisible by 210. Exact factorization:

    C-1=712529=719*991,
    C+1=712531 (prime).

The next true nonunit event is (r,e)=(356624,719), at gap356, with **every intermediate gcd equal to 1**. The budget-8 factor wheel has Lambda_8=315, and gcd(C-1,315)=gcd(C+1,315)=1, so its simulated horizon remains IDENTICALLY FIXED for the entire interval and it reports zero growth. The actual growth is 718.

This is not a refutation of budget-wheel soundness: the actual growth is >8. It shows why a *fixed small-budget* sieve cannot see the square-root-scale prime events forced in the sparse BAD alternative (10)-(12). Either the CRT constraints must force an unaffordable large jump, or the argument must control the adaptive factor clocks/near-semiprime pairs at a scale growing with M.

## 7. Reproducible checks and next exact gap

Companion [bad_path_forced_structure_audit.py](bad_path_forced_structure_audit.py) executes the original parity-sensitive gcd recurrence and the displayed finite structural identities. On all 997 synthetic canonical-shaped odd inputs 7<=M<=2000, exactly nine are terminal BAD: 11,13,23,25,39,41,43,45,305. Every BAD path satisfies (1),(7),(8). The actual A166944 is checked through n=2,500,000 (250 nonunit events including n=2); both genuine CRT lift examples and the real 719 hidden-prime hit are independently reproduced. An additional artificial M=4,000,001 checks the large-number first-hit roughness property on an exact path; this start is GOOD and is NOT evidence for a large BAD example.

**Unresolved theorem needed for Cap B:** exclude BOTH branches (A dense repeated-factor path, B sparse path traversing Omega(sqrt M) simultaneous P_2/P_2 rough-neighbor states with repeated prime increments) on all sufficiently large ACTUALLY attained canonical records; or prove that their compulsory prime-return histories contain mutually inconsistent CRT+first-hit cores whose disjoint growth charges exceed G_M. The known factor reuse/CRT/excursion lemmas alone do not supply such an upper bound. Finite tests and paper deductions are not Lean kernel proofs.

## 8. A particularly sharp SUFFICIENT missing upper bound, and actual-record baseline

Define `R_M` on the canonical window `(M+2,K]` as the number of nonunit EVENT INDICES whose increment shares at least one odd prime factor with an EARLIER increment inside that same window. Each event is counted once, irrespective of its number of prime factors. Theorem A establishes the universal necessary implication

    BAD at large attained M  ==> R_M >= (3/32-o(1))*sqrt(M).  (15)

Thus a uniform, **non-circular** induction target is to prove, for every genuinely attained canonical M beyond an EXPLICIT reachable threshold M0,

    boxed: R_M <= (3/32-epsilon)*sqrt(M)                (16)

for some fixed epsilon>0, together with a finite verification of any smaller attained records needed to reach M0 and of the finite range where the `o(1)` error in (15) is material. An effective `R_M=o(sqrt M)` theorem valid on these reachable canonical windows would also suffice. This reformulates the missing result as a quantitative **prime-factor recycling upper bound**, without needing to predict all individual CRT cores. Merely postulating an already-unbounded attained-record chain would be circular for a proof of twin-prime infinitude.

On the authentic A166944 trajectory through n=2,500,000, 17 attained canonical records have complete cutoffs. Selected exact results (M,N,R_M):

    (43,5,2)       BAD early, R/sqrt(M)=0.3050;
    (2659,11,5)    GOOD,      R/sqrt(M)=0.0970;
    (5419,9,4)     GOOD,      R/sqrt(M)=0.0543;
    (355723,57,40) GOOD,      R/sqrt(M)=0.0671;
    (1427749,72,51) GOOD,     R/sqrt(M)=0.0427.

All NINE checked attained records with M>=5419 have `R_M/sqrt(M)<3/32`. This is finite evidence only, and the inequality is NOT necessary for GOOD. Artificial independent canonical-shaped starts can exceed it even with terminal twin primes, so (16) is an **attained-record-specific conjectural route**, not a universal theorem about arbitrary synthetic starts.