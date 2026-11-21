# Phase-switch CRT lifts: exact 420-wheel prime-reuse cost and run capacity

2026-11-22 JST. **Status:** new paper deductions and a locally executed Python standard-library audit; NOT yet Lean-compiled. Cap B, the authentic-record global event bound, and twin-prime infinitude remain **open**.

This note extends [the neutral 420-wheel reuse result](2026-11-22-phase-locked-prime-reuse-spacing.md) to paths in which the 420 residue **changes arbitrarily between hits**, using the true first-hit residues already kernel-checked in [ReuseCongruences.lean](../A166944/ReuseCongruences.lean). The earlier [first-hit and frozen-wheel note](2026-11-22-frozen-wheel-phase-budget-and-neutral-paths.md) shows why a fixed small wheel is not by itself enough to prove Cap B.

## 1. The exact two-coordinate CRT phase graph

Write \`d(r)=a(r)-a(r-1)\` and \`D(r)=a(r)-r\`. If \`r\` is a nonunit event and \`p>7\` is a prime **dividing \`d(r)\`**, let \`C=D(r-1)\`, \`alpha=C mod 420\`, and \`sigma=+1\` if \`r\` is even, \`sigma=-1\` if \`r\` is odd.

Exact first-hit divisibility gives

\`C==alpha (mod 420)\`, \`C==sigma (mod p)\`.

Since \`p\` is coprime to 420, CRT gives the **unique** residue \`R_p(alpha,sigma)\` modulo \`420*p\`:

\`R_p(alpha,sigma) = alpha + 420*(((sigma-alpha)*inverse(420 mod p)) mod p)\`.    (1)

Consider two chronologically ordered events whose increments are divisible by \`p\`, with pre-horizons \`C1<C2\`, and residue/sign states \`z1=(alpha1,sigma1)\`, \`z2=(alpha2,sigma2)\`. Then

\`C2-C1 == R_p(z2)-R_p(z1) (mod 420*p)\`.

Define \`cost_p(z1,z2)\` as the **least strictly positive integer** in that residue class, taking \`420*p\` when the difference is zero modulo \`420*p\`. Thus

\`C2-C1 >= cost_p(z1,z2)\`, and \`420*p | ((C2-C1)-cost_p(z1,z2))\`.    (2)

Equation (2) holds even if arbitrarily many other prime hits, composites, and 420-phase changes lie between the two \`p\` hits. It is a *precise congruence lower bound*, not a claim that the least cost is always realizable by an actual first-hit trajectory.

In particular, if two hits have **the same 420 phase AND the same parity**, then

\`C2-C1 >=420*p\`, without requiring that the phase be constant in between.

A short-return example showing the importance of parity/phase: on the original A166944 orbit, \`p=13\` divides increments at \`(r1,C1)=(15,12)\` (odd) and \`(r2,C2)=(156,300)\` (even). The phase changes, and \`C2-C1=288=cost_13(z1,z2)\`, far below \`420*13\`. Therefore a universal \`420*p\` cost for all reuses is false.

## 2. A phase-return amplification, valid despite intermediate switches

Suppose \`p==1 (mod 420)\`, and at least three \`p\`-divisible hits occur at \`C1<C2<C3\`. The 420 phases at the **first and third** hits are the same; the middle phase is arbitrary.

Put \`sigma_i=+1\` for even hits and \`-1\` for odd hits. For each consecutive pair, the first-hit congruence and evenness of the horizon difference give

\`C(i+1)-Ci = (sigma(i+1)-sigma_i) + 2*p*k_i\`, with integer \`k_i>=1\`.

Indeed, the first event itself increases the horizon by at least \`p-1>2\`. Let \`K=k1+k2>=2\`. Summing,

\`C3-C1=(sigma3-sigma1)+2*p*K\`.

Because \`C3==C1 (mod 420)\` and \`p==1 (mod 420)\`:

- **Same first/last hit parity:** \`K==0 (mod 210)\`, hence \`C3-C1>=420*p\`.
- **Odd first / even last:** \`K==209 (mod 210)\`, hence \`C3-C1>=418*p+2\`.
- **Even first / odd last:** \`K==1 (mod 210)\`, but \`K>=2\`, hence \`K>=211\` and \`C3-C1>=422*p-2\`.

Therefore

\`boxed: C3-C1 >=418*p+2.\`                                 (3)

If **all three** p hits have the same 420 phase, the pigeonhole principle gives two of the same parity, and their horizon displacement is at least \`420*p\`. Thus the entire three-hit span is at least \`420*p\`.

The coefficient **418** in (3) is sharp as a statement of CRT congruences alone: for \`p=421\`, the artificial pre-horizon/sign states

\`(C1,odd)=(420,odd), (C2,odd)=(5472,odd), (C3,even)=(176400,even)\`

have wheel phases \`(0,12,0)\`, valid \`C==sigma (mod p)\` at each hit, and \`C3-C1=418*p+2=175980\`. These are **congruence-compatible states, not asserted exact first-hit events**.

## 3. New phase-switching COUNT bound for the actual recurrence

On any index interval \`[u,v]\` with \`2<=u<v\`, let

- \`G=D(v)-D(u)\`;
- \`B=#{r in (u,v]: d(r)>1, 420 does NOT divide d(r)-1}\`, the number of horizon phase-changing events;
- \`N_p=#{r in (u,v]: p divides d(r)}\`, for any prime \`p>7\`, including factors of composite increments.

Split the event list **immediately after** every phase-changing event. There are at most \`B+1\` runs, and within each run all PRE-event horizons \`C\` have the same \`alpha=C mod 420\` (a phase-changing event belongs to its prior run).

For any such run, p-hit horizons are confined to just two CRT residue classes modulo \`420*p\` by (1). A single residue class supplies at most \`floor(G_run/(420*p))+1\` distinct pre-horizons across a horizon interval of growth \`G_run\`. Sum the contributions over all runs; the disjoint run spans together use at most the global growth \`G\`. Hence the **unconditional paper theorem**

\`boxed: N_p <= 2*(B+1)+2*floor(G/(420*p)).\`                 (4)

If all the \`p\`-divisible hits in this interval have the SAME parity (in particular, if all are odd), each run uses just one CRT class, so

\`boxed: N_p <= B+1+floor(G/(420*p)).\`                     (5)

These include arbitrary changes of parity of *other* events, arbitrary composite increments, and arbitrary 420 phase changes. A phase change can permit additional early p reuses, but every such change is now explicitly counted as a new run. Equivalently,

\`B >= max(0,ceil(N_p/2)-1-floor(G/(420*p)))\`

is a necessary phase-switch budget for each prime key.

**Inert-phase corollary.** Let \`N_p^I\` count just the p-factor hits whose pre-horizon is inert with respect to 3,5,7, i.e. \`gcd(C-1,210)=gcd(C+1,210)=1\`. There are exactly 15 inert residues modulo 210, hence **30 even residues modulo 420** and at most **60** CRT classes (two hit parities). Without any restriction on the number of phase switches,

\`boxed: N_p^I <= 60*(1+floor(G/(420*p))).\`                  (6)

In particular, for the positive-debt large prime events already known to have inert pre-horizons, (6) is an unconditional per-key capacity estimate. The stronger of (4) and (6) can be used at a chosen interval.

**Sharpness:** in the exact locally synthetic 421 -> 176401 -> 421 path of the preceding note, \`B=0\`, both 421 hits are odd, and the pre-horizon difference is exactly \`420*421\`. Thus the single-parity single-run estimate (5) is attained at the two p-hit pre-horizons, including the coefficient 420.

## 4. Direct gcd audit and limitations

[phase_switch_crt_lift_audit.py](phase_switch_crt_lift_audit.py) checks the exact original recurrence \`a(1)=2\` through index 2,500,000. It records **250 nonunit events** and \`D(2,500,000)=2,860,770\`. For five nontrivial windows, and every prime \`p>7\` dividing any observed event, it checks:

1. Exact hit-side \`C==+1/-1 (mod p)\`, all consecutive p-hit CRT edge congruences and their positive-cost inequalities.
2. Bounds (4) and (5) (where the same-parity hypothesis holds), and inert-hit bound (6).
3. The exact real recurrence's p=13 phase-changing reuse with cost 288.
4. Every individual gcd in the synthetic 421,176401,421 path, which attains the same-parity wheel-lap cost \`420*421\`.
5. The three-hit phase-return CRT sharpness witness above.

All tests passed in local Python 3 with standard-library-only integer arithmetic. The repository file was additionally checked by GitHub readback. **No new Lean declaration has been compiled or kernel-checked**.

For the original recurrence on the full interval \`(2,2,500,000]\`, \`B=249\` out of 250 nonunit events. Therefore the switch-sensitive bound (4) is usually weak if applied directly to long intervals with frequent wheel changes.

More fundamentally, in the crucial regime \`p=Theta(sqrt(M))\`, \`G=O(M)\`, the term \`G/(420*p)\` is still \`Theta(sqrt(M))\` while the previously proved pigeonhole argument requires only \`Omega(log M)\` reuses of some such p. Even (4) or (6) alone is much too weak to force an event-count contradiction. Summing separately over different prime keys repeats overlapping growth charges, so the global multi-key packing problem remains unresolved.

**Next specific mathematical target:** a joint, cross-key phase-capacity theorem that charges a single phase-changing event and the growth between it and neighboring events **without multiplying its credit arbitrarily across several large primes**. The exact CRT residue graph (1)-(2) provides finite state-compatible edge costs for a rigorously defined combinatorial search or Lean encoding, but is not itself a proof of Cap B or infinitely many twin primes.
