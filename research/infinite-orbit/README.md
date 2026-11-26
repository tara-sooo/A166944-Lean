# Hypothetical infinite MIN worlds I: a simultaneous profinite survivor

2026-11-26 JST. Independent branch from main bd180e3de0fe6e12cc3c3ea25d65a985445344eb. Parent research tracker #1. User-selected scope: construct hypothetical infinite survivors of the finite-twin assumption, progressively impose established constraints and isolate the remaining realizability obstruction. No sibling merge, no change to the recurrence or final target. This is an abstract arithmetic construction and finite audit, not Lean verification, a proof of twin infinitude, or an external novelty claim.

Sources: direct [425a4b9](https://github.com/tara-sooo/A166944-Lean/blob/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a/research/2026-11-25-min-direct-arithmetic.md) (finite exact CRT lifts), direct [3793617](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md), direct [3e19d7e](https://github.com/tara-sooo/A166944-Lean/blob/3e19d7e945788d39b12a17744c2139970e90da8d/research/2026-11-26-min-direct-thickened-cut-recovery-and-local-supply.md), unified [6ec6ce3](https://github.com/tara-sooo/A166944-Lean/blob/6ec6ce3cc11afb8efa86611cc8c6eabf0aa872fa/research/2026-11-26-min-unified-radical-fan-lifetime-sieve.md). The first source already established finite common lifts. Here we construct one compatible infinite residue assignment for a countably infinite translated family, not merely separate lifts chosen after each finite transcript.

## 1. State semantics

For an actual odd root R>=5 let t0=R+2, C0=2R-2. At relative tick j>=1 with previous accumulated even gain E, n=R+2+j, C=2R-2+E. The raw parity gcd is
    gcd(R+j+2, |2j+7-E|) if j odd,
    gcd(R+j,   |2j+1-E|) if j even.
Select its least prime factor, or label 1 if it is 1; after selection add p-1 to E. In the adaptive MIN only factors p with p^2<=C+1 are eligible. On any finite uncut transcript, a sufficiently large positive diagonal lift makes all selected labels eligible. Do not equate an entire uncut trajectory and adaptive trajectory.

For a virtual root no magnitude or square root exists. We will define precisely the uncut relative rule via a residue assignment; adaptive validity is only a finite realization property. We use the word 'world' solely for this explicit weak structure, not a model of Peano arithmetic or of all established theorems.

## 2. A single simultaneous assignment

Enumerate all odd integers b as 1,-1,3,-3,... . Recursively choose distinct strictly increasing odd primes q_b > b^2+3 (e.g. the least prime above both this bound and the preceding chosen prime). Assign
    rho(2)=1,
    rho(q_b)=-b/2 mod q_b,
    rho(p)=1 at every other odd prime.
All residues are nonzero. This is an element of the product of the prime residue fields, or an element of the profinite integers after choosing compatible prime-power lifts. No prime-power lift is needed for MIN. For every even nonnegative offset k define the virtual root R_k=rho+k, sharing ONE rho. At gain E the formal center is 2rho+2k-2+E. For both signs s=+-1 its neighbor is divisible in the residue sense by q_b, where b=2k-2+E+s is odd. Thus all formal even centers at nonnegative offsets have two designated factors. We do not assign standard integer primality or an ordering to rho.

At tick j put h=2j+7-E if j odd, 2j+1-E if j even; select the least prime divisor p of |h| with rho(p)+k+j+2=0 mod p if odd j, or rho(p)+k+j=0 mod p if even j. If none, select 1. This is a finite effective rule at every tick. With d=6+2(j-1)-E>=0 before the tick, h=d+3 or d-3, always odd and nonzero. If a prime is selected then p<=d+3 even when h<0. Hence d_new=d+3-p>=0; quiet ticks add 2. This proves the canonical deficit envelope for all virtual ticks and also |h|<=2j+7. E is nondecreasing and even.

## 3. Infinite events and unbounded selected primes

On any plateau, q_b for either designated neighbor has a compatible future parity clock within 2q_b ticks. If the plateau lasts until that clock, q_b divides h by the gcd identity, so the uncut rule must have an event then, or earlier. Thus every virtual ray has infinitely many nonunit events and unbounded gain E. Every actual selected label p obeys wait w<=2p: the selected prime's clock recurs with period 2p and no earlier eligible tick can lie inside the same plateau. Consequently
    d'=d+2w-(p-1),  -(p-1)<=d'-d<=5(p-1)
(the upper follows from 4p-(p-1)=3p+1<=5(p-1) for p>=3). These statements apply at successive post-event states or from the canonical initial state.

No tail can use a finite prime set S. Let P be its product. Choose arbitrarily large even gain J beyond the beginning of that tail satisfying 2rho(p)+2k-2+J=0 mod p for every p in S; CRT gives a progression modulo 2P. At a strict crossing E<=J<E+p-1 with p in S, J-E is even, lies in [0,p-3], and must be congruent to +1 or -1 mod p because the selected prime divides a center neighbor. No such even distance exists. But unbounded gain crosses every J. Contradiction. Thus labels are unbounded. This is the translated primorial-barrier argument without an absolute root.

## 4. Simultaneous finite realization theorem (paper deduction)

Take ANY finite set of offsets k and finite tick bounds (not necessarily the same). Let T be their maximum. Choose a finite CRT system for an ordinary integer M:
* M=rho(p) mod p for all primes p<=2T+7, including p=2;
* M=rho(q_b) mod q_b for both neighbors of every visited plateau in the chosen prefixes, including the terminal plateau.
Overlaps impose exactly the same residue. Its solutions form a single infinite arithmetic progression. Choose M sufficiently large so all M+k>=5, every selected label p satisfies p^2<=2(M+k)-2+E+1, and all designated neighbors are positive and exceed their q_b. Induction on j and the bound on h prove that the literal integer parity gcd has exactly the same set of prime factors as the virtual rule at every observed tick, thus the same least factor. Quiet ticks also transfer. Since selected p is eligible, the adaptive rule agrees. The designated factors certify BOTH neighbors composite at every visited plateau, including the terminal one. The entire family transfers under the SAME M, with all relative offsets, common physical states, coincidences and noncoincidences unchanged. M can be arbitrarily large. For k=0 every CRT residue is a unit, so the single-root prime-lift refinement also follows from Dirichlet as in the direct source; no simultaneous prime-root claim for k>0.

Corollary: every finite relation invariant under the common diagonal translation of all roots, times and horizons, and valid for sufficiently large actual canonical odd-root adaptive MIN prefixes, is valid on this virtual ensemble. This includes exact relative clock/deficit relations, divisibility and finite reuse/ancestry relations that have the required semantic hypotheses, as well as finite projected coincidences. Conditional relations transfer only if the hypotheses transfer too. This does NOT cover finite statements involving absolute magnitude, a fixed numerical cutoff, prime root ensembles, or asymptotic densities, simply by virtue of being finite. Nor does composite certification on visited plateaus imply a global finite-twin hypothesis on the standard integers.

## 5. Exact obstruction to a single standard-integer realization

This construction gives a genuine compatible infinite residue assignment, not a fixed natural root. For any fixed nonnegative integer M, the congruences q_b | 2M+b cannot all hold: for arbitrarily large positive odd b, 0<2M+b<q_b. In fact even along a single virtual ray the visited b=2k-1+E become arbitrarily large. For a finite lift that retains the designated factor on this plateau, positivity implies
    M >= (q_b-b)/2 > (b^2+3-b)/2.
Thus any sequence of lifts matching the chosen certificates must escape every bounded root range. Even if one omits the designated factors, a finite transcript lift need not yield a fixed-root infinite realization; we do NOT assert that the bare label word is impossible for all standard roots on the basis of this inequality.

The obstruction is deliberately introduced by our certificates, not an inconsistency in real finite-twin arithmetic. It exhibits explicitly how finite local consistency can coexist with nonrealizability of the complete virtual data. Absolute-scale and ensemble-density constraints are now the next filters. In particular the direct offset-twin witness lemmas use actual standard integers and a global twin threshold, and cannot be applied to this residue-only world merely because its formal neighbors have factors.

## 6. First concrete next targets

(a) Define a rooted scale-window model with actual finite centers X<=C<lambda X and actual cutoff sqrt(C+1), not just fixed relative time followed by an arbitrarily large lift. Impose the direct paper's factor-two high-band deficit-chain inequalities, explicitly retaining their high-band gain and deficit-cap hypotheses, and the localized corridor inequalities with the no-offset-witness hypothesis. Search for a compatible abstract sequence of scaled budgets, then add the first-hit residue constraints. A numerical feasible model is only scalar until a lifting argument is supplied.

(b) Extend to ensembles of N(X) canonical roots in actual bounded windows: original source mass, stopped paths, phase/sector and physical slot collision, actual missing-clock mass and forward survival. The unified note gives necessary constraints under finite twins; macro missing mass is NOT an established assumption. A finite collection of translated sources at an arbitrary large M does not satisfy the dense-source hypotheses automatically.

(c) For a solver, tag each imported constraint with semantic domain, antecedent, quantifier, scale and verification level. Seek minimal infeasible sets only within a sound finite relaxation; a single finite infeasibility is not a uniform contradiction. The registry is initialized in theorem_registry.md. It is not yet a complete inventory of all Lean declarations or all research notes.

## 7. Reproduction

Run:
    node research/infinite-orbit/audit.mjs

The exact audit function executed in the available ECMAScript runtime; standalone Node process not used. Four offsets k=0,2,8,30; T=128,512,2048. Uses deterministic q selection, exact finite CRT with BigInt, independent literal gcd on the lifted integer states, direct eligibility and proper divisor checks, period and deficit checks. Final counts:
| T | tick comparisons | nonunit incidences | proper divisor checks | distinct certified offsets | CRT moduli | max label | lift digits |
|---:|---:|---:|---:|---:|---:|---:|---:|
|128|512|29|66|33|82|139|215|
|512|2048|45|98|57|222|139|663|
|2048|8192|45|98|57|610|139|1974|

All checks pass. Counts overlap between nested lengths. Gains at T=2048: 90,86,74,396; no additional event after T=512 in these four finite runs. Infinite-event proof above is algebraic, not extrapolation from this audit. Audit uses a positive CRT lift, not a claimed prime. No Lean execution or external novelty search. Main and sibling branches are not edited.
