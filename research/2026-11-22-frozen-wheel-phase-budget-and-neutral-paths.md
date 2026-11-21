# Fixed-wheel phase charging and neutral first-hit paths

2026-11-22 JST. Status: **paper mathematics plus reproducible direct-gcd tests**. The global Cap B bound and twin-prime infinitude remain OPEN. The arbitrary-length construction below uses Dirichlet's theorem and CRT, and starts from an **artificial** canonical-shaped state; its existence is not a claim about attainment from a(1)=2. No new Lean compilation was performed.

Sources: [Lemmas.lean](../A166944/Lemmas.lean), [ReuseCongruences.lean](../A166944/ReuseCongruences.lean), [FirstHitArithmetic.lean](../A166944/FirstHitArithmetic.lean), and [four-value frozen-factor analysis](2026-11-22-four-value-frozen-factor-obstruction.md).

## 1. New simultaneous prime-phase accounting inequality (ACTUAL A166944)

For odd prime q, and an actual sequence interval 2 <= u < v, define:

- A_q(u,v): count of integers s in [u, v-2q] with D(s) congruent to +1 or -1 modulo q. Set A_q=0 when the index range is empty.
- B_q(u,v): count of r in (u,v] with d(r) not congruent to 1 modulo q.
- G(u,v)=D(v)-D(u)=sum over (u,v] of d(r)-1.

**Frozen-prime witness lemma.** If q divides D(s)-1 or D(s)+1, some r in (s,s+2q] must have d(r) not congruent to 1 modulo q. Otherwise D stays fixed modulo q in this interval, while one of the 2q positions must be an even multiple of q (first sign) or an odd index r congruent to q+2 modulo 2q (second sign). At this position the actual gcd increment is divisible by q, contradiction.

Assign each active s to the first such phase-changing r. Every r can receive at most 2q assignments. Hence the unconditional inequality

    A_q(u,v) <= 2q * B_q(u,v).                         (1)

For any finite set S of odd primes and nonnegative weights lambda_q summing to at most one, the increments are odd at indices >=3, so each phase-changing increment has d(r)-1 >= 2. Consequently

    sum_{q in S} lambda_q * A_q(u,v)/q <= G(u,v).      (2)

This is an exact simultaneous *growth lower bound*, not a bound on the event count from above. Its effectiveness requires substantial occupancy of active residues.

## 2. The exact offset-six normal form

For a local state (s,C) with C=2s-6, write r=s+g. Euclid's algorithm gives

    gcd(r,C-1)       = gcd(r, 2g+7)   for even r;
    gcd(r-2,C+1)     = gcd(r-2, 2g+1) for odd r.       (3)

Let p be prime with p congruent to 1 modulo 420, and take g=(p-1)/2 (an even integer). Suppose s is odd and p divides r-2. Then (3) yields an **exact** gcd of p at the odd index r, provided there was no earlier nonunit hit. Updating the horizon gives

    (s,C) -> (s+g,C+p-1),  X_before=X_after=6.

If C was divisible by 210, it remains so, because p-1 is divisible by 420. Over such an event the potential F=4s-9C falls by exactly 7(p-1):

    F_after - F_before = 4g-9(p-1) = -7(p-1).         (4)

All prior gcds at gaps h<g are controlled by numbers at most p+4 via (3), which makes the following finite CRT restrictions sufficient to enforce genuine local first hits.

## 3. Theorem: arbitrarily long inert-wheel local words (PAPER)

**Claim.** For every positive integer t and every finite bound B>=7, there are synthetic local states (s0,C0=2s0-6) and distinct primes p1,...,pt>B such that:

1. The exact first-hit gcd rule produces the t successive nonunit increments p1,...,pt at gaps (pi-1)/2, with *every earlier index in each gap having gcd 1*.
2. Each pi is 1 modulo 420, the offset X stays 6 after every event, and throughout the whole finite segment C is divisible by EVERY prime <=B. Thus all these small primes are inert in C-1 and C+1.
3. s0 can be made arbitrarily large compared with max(pi)^2. Then the entire artificial segment has NO slow interval, in the same local F/height sense used by the Cap B analysis.

**Construction/proof.** Choose Q >= max(B,2t+7) and let P_Q be the product of primes <=Q. Using Dirichlet's theorem, recursively choose primes pi, each sufficiently large, satisfying

    pi = 1 (mod 420 * P_Q * product_{j<i} pj),

and choose pi larger than the sum of all earlier (pj-1) plus 20, as well as Q+20.

Write gi=(pi-1)/2, Si=sum_{j<i}gj and Ci=2(s0+Si)-6. Choose s0 via CRT with the following constraints:

- s0 odd;
- C0=2s0-6 is 0 modulo each prime <=Q;
- s0+Si+gi-2 is 0 modulo pi, for each chosen pi;
- for each other odd prime ell with Q<ell<=pt+4, all Ci avoid residues +1 and -1 modulo ell.

The last line excludes at most 2t<ell residue classes of s0 modulo ell, so an allowed residue exists. All selected pi exceed Q and are distinct; the constraints are therefore simultaneously solvable. CRT also permits s0 to be chosen arbitrarily large.

For the designated prime pi, the third line implies Ci=-1 modulo pi. At a *later* event j>i, Cj=-2 modulo pi: the first update adds pi-1=-1, while later pk-1 are divisible by pi. At an *earlier* event j<i, the intermediate horizon growth is positive and smaller than pi-3, so Cj=-1-growth is neither +1 nor -1 modulo pi. Thus the designated prime can divide a horizon neighbor only at its own event.

At that event, the proposed odd gcd is exactly pi by (3). At each earlier index of the same gap, every possible prime divisor of the gcd is <=pi+4. All such prime factors are ruled out by the chosen horizon residues, except for pi itself; pi cannot occur earlier because on odd tests 2h+1<pi, and pi does not divide the even-test horizon neighbor. This proves the exact first-hit property inductively.

Between completed events, equation (4) makes F strictly decrease at every event endpoint. The maximum rise during a unit stretch is 4(gi-1), so any forward F-drawup along the full finite segment is at most 4(max gi-1)<2 max pi. Choosing s0>=max(pi)^2 makes the slow threshold 32+8 floor(sqrt(C+1)) strictly larger. QED.

**Scope:** These are valid local first-hit trajectories from artificial states, not Lean HasMovingHorizonPathTo certificates for the original a(1)=2 sequence. The constructed primes may grow enormously with t; neither the true canonical time horizon K nor the real record-attainment hypothesis is enforced.

## 4. Finite reproducible witnesses, including prime reuse

The companion [frozen_wheel_first_hit_audit.py](frozen_wheel_first_hit_audit.py) checks every intervening individual gcd, both parity branches, the offset and 210 residue, and the absence of a local slow interval.

- **Twin-prime-shaped artificial start:** M=1,369,875,375,961, with both M and M-2 prime. Starting at s=M+2, C=2M-2 gives events (gap,e)=(210,421),(1260,2521). Every horizon is 0 modulo 210, X returns to 6, and maximum local F drawup is 5036 versus an initial slow threshold 13,241,784.
- **Three distinct inert events:** M=735,167,457,611,161, events (210,421),(1260,2521),(1680,3361); all first-hit gcds are exact and the local slow inequality never holds.
- **An inert REUSED prime:** M=9,801,898,053,991, events (210,421),(88200,176401),(210,421). This locally valid p,q,p sequence reuses 421 without activating any of 3,5,7; all event endpoints retain X=6. This also shows that finite-wheel inertia does not itself forbid prime reuse.
- The actual recurrence was independently calculated to index 1,000,000, checking (1)-(2) on four windows with q=3,5,7,11; all passed.

The synthetic start M in the first example is a genuine pair of twin primes, but its D(M+2)=2M-2 is artificially assigned, NOT established from a(1)=2. The two other synthetic M need not be prime.

## 5. Exact obstruction to the contemplated proof strategy

Inequality (2) *does* combine the forced small-prime hits and their growth costs. But the paths in section 3 have A_q=0 for every fixed small prime q throughout their entire (arbitrarily many-event) local segments. In particular, the lower bound becomes 0<=G; it places no restriction on prime-event count or F.

The construction does not disprove an asymptotic global packing theorem for **actual records**. It pinpoints what such a theorem must additionally control: **time spent in inert states with large, changing or reused prime increment values**, charged against the true horizon budget G<=2K-(2M-2), with enough strength to force a large F drawup or a slow interval. A finite fixed wheel alone cannot supply that conclusion from bounded local event patterns, even when those events obey the exact first-hit gcd equation.

Validation status: new symbolic paper arguments, independently executed standard-library Python certificate, GitHub persistence verified separately. No new Lean kernel proof and no proof of Cap B or twin-prime infinitude.
