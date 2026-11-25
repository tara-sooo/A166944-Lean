# Independent MIN arithmetic: diagonal lifting, exact cuts, and the absolute-scale obstruction

2026-11-25 JST. User-requested independent lane, based on main bd180e3de0fe6e12cc3c3ea25d65a985445344eb. No cost allocation, source-weighted energy, Hall network, donor decomposition, or asymptotic distribution assumption. PAPER deductions and finite audit, not Lean checked. No proof of twin infinitude or of the stronger A166944 record conjecture, and no external novelty claim.

Reviewed recent heads: prime-root [1ccfb6af](https://github.com/tara-sooo/A166944-Lean/commit/1ccfb6af1957dcada4ee3286d01206288664e135) (fixed-age primorial boundary Hall envelopes), stable-heavy [80e7125e](https://github.com/tara-sooo/A166944-Lean/commit/80e7125e523d2f273fe42867325306a27ab208e1) (first common recorded attainment and quadratic moments), and recent-large-merge [a31a2f787](https://github.com/tara-sooo/A166944-Lean/commit/a31a2f7872d58733177936e54c34070367a00a7c). Definition reference: [canonical_min_prefix.lean](https://github.com/tara-sooo/A166944-Lean/blob/1ccfb6af1957dcada4ee3286d01206288664e135/research/canonical_min_prefix.lean). Prior exact residue cylinders and relative defect identities are already in [eb350115](https://github.com/tara-sooo/A166944-Lean/blob/eb350115d5fe904b7b034b6871a1c3e68a76602e/research/2026-11-24-min-transcript-crt.md). The distinct objective here is a direct CRT lifting obstruction and a phase-free cut classification, not the earlier finite-window conditional distribution/return-cost target.

## 1. Start from the finite-twins assumption itself

Use an even horizon C>=4 and integer time t>=2. At an even tick n the eligible odd primes satisfy p|n and p|C-1; at an odd tick n they satisfy p|n-2 and p|C+1. At the first active tick choose the least eligible p and replace C by C+p-1. Define the **adaptive square-root MIN** to use the pool p<=floor(sqrt(C+1)), recomputed only when C changes. This is a deliberately specified variant of the fixed B canonical MIN. The selection rule and all local arithmetic are unchanged; no transfer of full paths between the variants is assumed.

A horizon has no eligible clock at all iff C-1 and C+1 are both prime: if either is composite it has an odd prime factor <=sqrt(C+1); if both are prime neither belongs to the pool (C>=4). Each such factor has an eligible tick within 2p. Hence if twin primes are finite, there is C_* such that EVERY adaptive MIN trajectory with initial C>C_* has infinitely many strictly increasing event horizons, and crosses every larger even integer in finite time. Conversely, proving that adaptive MIN must stop for arbitrarily large actual roots would prove infinitely many twins. This is a direct termination objective, not the fixed-cutoff terminal certificate or a signed budget.

For a finite cutoff B, provided C+1<=B^2 and C-1>B, a stopped horizon has the same meaning. The second inequality rules out a prime neighbor itself being included in the pool. In a large canonical window it is automatic.

Unbounded labels are necessary on any infinite adaptive trajectory. If a tail uses only a finite set S of odd primes, choose an even multiple J of their product at or above its first horizon. For any such p, a jump cannot strictly cross J: if C=J neither neighbor is divisible by p; otherwise the even distance J-C is congruent to +/-1 mod p and at least p-1. Thus that tail is bounded, contradiction. This does not rule out infinite rays with unbounded primes. The next sections test whether purely arithmetic barriers can do more.

## 2. Exact arithmetic cut, stronger than the primorial special case

Fix an even J>=6, and an odd prime p with p^2<=J+1. Ignore the time and MIN competition initially, retaining only C even and p|(C-1)(C+1). A strict crossing has C<=J<C+p-1, so d=J-C is even with 0<=d<=p-3. The residue r=J mod p must lie in the union of d+1 and d-1 mod p. Therefore a relaxed strict crossing by p exists **iff**

    r in {1,3,5,...,p-2} union {p-1}.                  (A)

In particular every r in {0,2,4,...,p-3} blocks p, not only r=0. For odd r the closest crossing predecessor is C=J-r+1 (even-side), with d=r-1. For r=p-1 it is C=J (odd-side). These are the minimal possible distances, so for the adaptive pool a relaxed strict crossing exists iff (A) holds AND p^2<=C+1 for this closest predecessor. A strict bypass from C<J in the fixed pool is possible iff p>=5 and r is odd. The p=3 step cannot bypass an even center. These are exact statements about the RELAXED horizon graph, not assertions that a possible crossing is taken by any canonical trajectory.

If there is an unbounded sequence J with all residues outside (A) for p<=sqrt(J+1), each J is a barrier and would contradict the infinite rays of section 1. However this is too restrictive as a practical route: it already forces J±1 prime, and imposes extra half-residue exclusions for many primes. Finite exhaustive enumeration of even 6<=J<=10^6 found only 13 such barriers: 6,12,18,30,42,60,72,102,270,312,420,660,1302. The adaptive relaxed test gives the same set in this range; 52 fixed-pool no-bypass centers, last 1572. Neither count proves finiteness.

A phase-sensitive direct objective can be stated without any ensemble cost. From a root (t0,C0) with C_*<C0<=J, set B=floor(sqrt(J+1)). Under the finite-twins assumption the first strict crossing of J must occur by t0+3(J+B-1-C0): each chosen p before/at crossing is <=B, each wait <=2p<=3(p-1), and the terminal post-horizon is <=J+B-1. Any crossing candidate (n,C,p) in this finite box must satisfy (A), C=J-d, the adaptive cutoff, and the exact parity clock congruence. A certificate that NONE of these candidates is reachable by the actual MIN from the root gives a contradiction (the trajectory must have stopped at twins). One could attempt a uniform construction of modular phase-space cuts, allowing different blocked p at different states rather than requiring all r even simultaneously. No such unbounded family of reachable-state cut certificates is established. The crude deadline is just a single telescoping inequality, not an assumption about return costs or merging.

## 3. Exact diagonal translation and composite lifting of any finite transcript

Use actual canonical odd roots M>=5, t0=M+2, C0=2M-2. Write j=n-t0 and E for the accumulated gain immediately before tick j, so C=2M-2+E. The raw parity GCD equals

    gcd(M+2+j, 2j+7-E),   j odd;
    gcd(M+j,   2j+1-E),   j even.                      (B)

The gcd on the right uses absolute values. This is exact by subtracting the neighbor from twice the clock argument. The second argument h_j is always odd, never zero. The familiar invariant C<=2t is valid for the least-prime step even without a cutoff: in an even tick the positive difference 2n-(C-1) is divisible by p, hence C+p-1<=2n. In an odd tick use 2(n-2)-(C+1): if positive then p is at most that difference; if negative, the prebound C<=2(n-1) makes its absolute value <=3, hence p<=3 and again C+p-1<=2n. Quiet ticks preserve the bound. Thus for j<=T, |h_j|<=2T+7. This also holds in the fixed or adaptive cutoff models.

For any finite T-tick actual uncut MIN transcript, let

    Q = 2 * product of distinct primes dividing some |h_j|, 1<=j<=T.

For each even root shift Delta divisible by Q, the translated root M'=M+Delta (M'>=5) has the SAME T-tick uncut MIN transcript. Induct on j: the preceding E and h_j are identical, parity agrees, and for every possible prime divisor of the parity gcd (all must divide h_j) the clock argument in (B) has the same residue. Hence exactly the same set of active primes and the same least label or quiet tick. With Q replaced by 2*lcm_j |h_j|, the entire raw GCD is preserved as well. For a fixed B transcript the same proof preserves its fixed-B choices. For a transcript of the uncut rule in which every selected p satisfies the adaptive bound, the same transcript is adaptive MIN both at the original root and at all positive lifts: at every actual event the least raw prime remains in the enlarged pool, and at quiet ticks the raw gcd is 1. A fixed-B transcript that ignored a larger raw prime need not transfer to an enlarged B.

Now take the finite set of distinct visited gains E (include initial and terminal). For each (E,s) with s=+/-1, choose a distinct odd prime q_(E,s) greater than 2T+7 and all absolute offsets |E-2+s|. Impose

    Delta=0 mod Q,
    2(M+Delta)-2+E+s=0 mod q_(E,s).                   (C)

All moduli are pairwise coprime except for the internally combined Q, so CRT gives an entire arithmetic progression of Delta, unbounded above. Choose Delta sufficiently large that each indicated neighbor exceeds its q. The translated trajectory has precisely the same finite relative event/quiet transcript, but BOTH neighbors at EVERY visited horizon are composite. This works even if the original transcript reached a genuine twin center and remained quiet for its entire observed tail. For adaptive MIN the composites may have additional eligible clocks after the observed prefix; no claim of an infinite identical lift. For the fixed canonical K(M), a larger translated source may have a much later stopping index, so only the indicated finite prefix is preserved.

Prime roots: if M is prime and gcd(M,Q)=1, the residue of M' in (C) is coprime to each modulus: for q_(E,s) it is (2-E-s)/2 mod q, nonzero since E even and 2-E-s is odd and smaller in magnitude than q. Dirichlet's theorem on primes in reduced arithmetic progressions then gives arbitrarily large PRIME roots M' with the same composite-certified finite prefix. This uses the classical Dirichlet theorem, not a prime-tuple assertion; no claim for a simultaneous family of prime roots. For finitely many all-odd roots and prefixes, take the common shift divisible by all Q and impose separate composite certificates for every visited neighbor. This preserves all relative trajectories and any observed physical coalescences in that finite family.

Consequently an implication from only a finite relative MIN transcript to a twin center, without any absolute-size or global assumption, is false. The lifting construction is not a counterexample to infinitely many twin primes; it identifies what finite local arithmetic does NOT force. The finite-twins hypothesis is compatible with each individual finite relative pattern in this sense, not necessarily with an actual global infinite orbit satisfying additional constraints.

## 4. Direct modular small-representative target

The relative transcript cylinder itself was already derived in eb350115. Formula (B) gives an exact tickwise version requiring only factors of |h_j|. At each tick with label p>1 require M congruent to -(j+2) for odd j or -j for even j modulo p, and exclude that residue modulo each smaller candidate q|h_j. At a quiet tick exclude it for every q|h_j. Intersect these constraints primewise to obtain A_q. An odd M>=5 realizes the transcript iff M mod q belongs to A_q for every constrained q. This follows by induction and includes the least-prime competition, not just a selected-label congruence. For uncut transcripts with a fixed B extension, the same conclusion holds when all selected labels lie in the relevant pool.

Let the last L ticks of a consistent T-tick transcript be quiet, with final gain E. For any realization M satisfying

    C=2M-2+E>=4,    2 floor(sqrt(C+1)) <= L,            (D)

the horizon C has twin prime neighbors. Indeed any composite neighbor has a factor p<=sqrt(C+1) with an eligible clock in those L ticks. Because it is the UNCUT transcript the quiet ticks exclude that clock. Equivalently C+1 < (floor(L/2)+1)^2 is a simple exact integer condition. This is a local terminal certificate without a budget or moment bound.

Thus a direct number-theoretic sufficient statement is: for arbitrarily large lower thresholds N, construct a consistent quiet-ending relative word and a positive odd realization M>N of its residue cylinder whose absolute size satisfies (D). Under finite twins every such cylinder is EMPTY in this small representative range once C0>C_*. The goal is to derive a contradiction from that emptiness, e.g. by a modular construction of small representatives of a family of nontrivial words. Uniform CRT on the complete period cannot give this: (C) explicitly supplies arbitrarily LARGE realizations with all neighbors composite. The period can be exponentially larger than the desired quadratic scale. Merely finding many quiet-ending words, or reproducing their residues at huge roots, does not establish the necessary small-representative theorem. The all-quiet word already contains the ordinary twin-pair sieve obstruction. Allowing nonzero gains changes the modular constraints but does not resolve the small-representative question. This is an OPEN proof principle, not a proved improvement of the old analytic bounds.

## 5. Audit

Source: [min_direct_arithmetic_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/8c79f9f65a249aebc76f243784d4bb91f5281131/research/min_direct_arithmetic_audit.mjs), blob 74430ac56dbe72ea2134c76705c299c794b672c9. Exact remote readback verified. Reproduce from branch:

    node research/min_direct_arithmetic_audit.mjs 1000000

Executed the actual ECMAScript function in available runtime, not a separate Node process. Literal gcd at every tick; 12,054 cylinder equivalence comparisons (odd roots 5..199 and 5..249, T=40), 3,338 relaxed crossing comparisons against explicit predecessor enumeration for J<=1000; barrier enumeration through 10^6. All checks passed.

Concrete example: prime root M=1663, C0=3324, T=120. Only nonunit events are (j,p)=(2,5),(3,3). Terminal C=3330 gives the genuine twin pair 3329,3331 and 117 consecutive quiet ticks; 2*floor(sqrt(3331))=114. Both selected labels are within the adaptive pool, so this is also an actual adaptive and sufficiently large fixed-pool MIN prefix. Exact CRT lift:

    M'=1042992752915773477855961309763299155100001037224612003831740822715695731890761083

All 120 literal MIN choices, gains and relative defects match. At gains E=0,4,6, the translated minus/plus neighbors have respectively certified proper divisors (347,349), (353,359), (367,373). Thus no visited translated center is a twin center. The displayed M' is not asserted prime; the single-prime-root refinement above is a Dirichlet existence argument. Original long quiet plateau is a positive control, lifted plateau a counterexample to a scale-free finite-pattern inference.

## 6. Status / next work

Paper: infinite-ray consequence of finite twins for the adaptive MIN; exact relaxed arithmetic crossing residues and cutoff refinement; diagonal translation/composite CRT lift (including single prime-root variant using Dirichlet); exact local small-representative sufficient condition. Finite audit as above. No Lean executable available in this session; no Lean changes or kernel-checked new theorem. The exact stopping/termination theorem, an unbounded family of phase-sensitive cut certificates, or the small-representative theorem remain OPEN. The branch is deliberately based on main and does not merge or alter the two recent cost-based lanes. It should not be reported as a proof, external novelty, or a direct contradiction already obtained.
