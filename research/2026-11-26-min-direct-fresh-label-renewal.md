# Fresh-label escape dichotomy, event-count compression, and constructive uniform support bounds

Continuation of [7777700](https://github.com/tara-sooo/A166944-Lean/commit/7777700f1aee12b0ff7d86a5f9b37954782a9eee) on the same independent direct-arithmetic branch. The earlier relative GCD/cylinder identities are from [425a4b9](https://github.com/tara-sooo/A166944-Lean/commit/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a) and the prior transcript CRT work; the new results are the exact bounded/unbounded-next-label alternative, its event-count rather than tick-count decision, its renewal construction, and a constructive bound replacing the compactness proof of [f239d2e](https://github.com/tara-sooo/A166944-Lean/commit/f239d2e1b38bd0697abbf3aff391f9b965745a8a). No source-merger, energy, return-cost, or prime-distribution assumption beyond ordinary CRT and Dirichlet for a single prime in a reduced progression. Paper deductions and exact finite diagnostics, not Lean kernel verification or external novelty claim. Twin infinitude and A166944 remain OPEN.

## 1. Setup and exact cylinder constraints

Use canonical odd roots M>=5, t0=M+2, H0=2M-2. On even tick n the raw gcd is gcd(n,H-1); on odd tick n it is gcd(n-2,H+1). Uncut MIN uses the least prime factor when this gcd exceeds 1; adaptive MIN ignores it if it exceeds sqrt(H+1). For relative tick j=n-t0 and pre-event accumulated gain E, the raw gcd is

    gcd(M+j+2, 2j+7-E),     j odd (absolute even side),
    gcd(M+j,   2j+1-E),     j even (absolute odd side).

For an actual prefix, the odd defect h_j in the second argument is nonzero and |h_j|<=2T+7 for j<=T, by H<=2t. In particular E<=2T+6 at the end. More generally for any finite proposed word, all h_j are fixed odd nonzero integers even before checking its feasibility, so their possible prime divisors lie in a finite set.

Fix a finite proposed uncut tick word through relative tick T, with N nonunit events, selected prime support S, and accumulated gains E_0=0,E_1,...,E_N=E. For each odd prime q let A_q be its allowed root residues. At a quiet tick exclude the raw-gcd residue of M if q|h_j. At a specified nonunit event p, require its raw-gcd residue for q=p (reject if p does not divide h_j), exclude that residue for q<p if q|h_j, and impose no condition for q>p. This exactly characterizes the least-factor word by induction. For the prime-root variant intersect A_q with the nonzero residues mod q, since we seek arbitrarily large PRIME roots; isolated roots equal to q do not count in that claim.

For all-odd roots, nonemptiness of every relevant A_q gives arbitrarily large realizations by CRT and odd parity. For prime roots, use nonzero residues and Dirichlet on the resulting reduced residue class. The moduli can be taken to be the distinct prime divisors of all h_j and all specified labels, with 2 for parity. Every fixed finite word is identical in the uncut and adaptive models for sufficiently large roots, because the raw gcd divides a fixed h_j and the growing absolute cutoff then contains all its prime factors. We do not claim that a small-root adaptive word necessarily obeys the uncut constraints.

## 2. Event-count compression of full word feasibility and terminal avoidance

During plateau i of gain E_i, any q hit, whatever its time, requires

    M in F_q(E_i) = {(1-E_i)/2, (3-E_i)/2} mod q.

Here 2 is inverted modulo the odd q. If q is not a selected label, the entire word only imposes exclusions, at most two residues per distinct plateau, with N+1 plateaus total. If q>2N+2 (all-odd variant), or q>2N+3 (prime-root variant), there remains a residue outside the UNION of all N+1 sets F_q(E_i), and outside 0 in the prime variant. Such a residue satisfies every word constraint and avoids BOTH final-neighbor divisibilities.

Thus the following finite decision set is EXACT for both nonemptiness and the question whether some allowed residue avoids the terminal pair at every prime:

    K_odd   = S union {odd primes q<=2N+2};
    K_prime = S union {odd primes q<=2N+3}.                (1)

For an arbitrary proposed schedule, test the selected labels as required, including their actual hit condition and any contradictory earlier exclusions. If every A_q for q in K is nonempty, the schedule is realized by arbitrarily large odd roots (respectively prime roots). The omitted primes can all be satisfied simultaneously by CRT over the finite set relevant to the word. If every tested A_q also contains a residue outside F_q(E), the same is true for ALL primes; this means per-prime modular avoidance, NOT a single integer whose two neighbors are indivisible by every prime simultaneously. This distinction is essential.

The result reduces the number of primes that need to be examined from a bound on elapsed ticks to a bound on number of actual events and the given selected labels. A long quiet interval adds no new prime to the decision set (1). For an unselected q, even the sharper necessary condition for A_q nonempty and A_q subset F_q(E) is q<=2N+2 for all-odd roots or q<=2N+3 for prime roots: only the preceding N plateaus can exclude residues outside the final F_q(E). The compressed test is valid regardless of the magnitudes of selected primes.

The per-prime test need not iterate over quiet ticks. On a plateau (a,b) ending at event tick b with label p, for sign e=+1 (even absolute clock) use c=(2-E_i+1)/2 mod q and relative hit j=-c-2 mod q with j odd; for e=-1 use c=(2-E_i-1)/2 and j=-c mod q with j even. Each gives a single residue mod 2q. Remove c if a hit occurs in [a+1,b-1], or at b if q<p. If q=p, require its correct-side residue and actual hit at b. For the final plateau use all quiet ticks through T. Hit existence in any interval is a single arithmetic-progression endpoint calculation. This gives exact residue sets by processing N+1 plateaus; unselected large primes need not be factored or enumerated to decide existence. Constructing a literal full CRT modulus may still be huge.

## 3. Bounded vs arbitrary fresh next label

Assume the prefix is feasible for the chosen root variant. Define a prime q to be FORCED at the endpoint if A_q subset F_q(E). Otherwise call it avoidable. Call a prefix FREE if every q is avoidable; by section 2 this is an exact finite test on (1).

**Escape dichotomy.**
- If some q is forced, every sufficiently large root realizing the word has an eligible q-clock at its final plateau. Its next event occurs within 2q ticks; for the selected label p at that next event the relative defect bound gives

      p <= 2T+4q+7.

  This is a uniform bound over the entire sufficiently-large-root cylinder. It applies to the chosen variant (prime-only forcedness uses the nonzero A_q).
- If the prefix is free, then for EVERY prime p>2T+7 and either side e in {+1,-1}, there are arbitrarily large roots in the same cylinder whose next event is precisely p on side e. The claim for prime roots assumes feasibility and freedom with the nonzero residue sets. In particular no intermediate event occurs.

For the second assertion write B=2T+7, choose p>B, require M=(2-E+e)/2 mod p. The prefix imposes no restriction mod p. The residue is nonzero even for prime roots: 2-E+e is odd nonzero and has absolute value <p by E<=2T+6. With H fixed, the first p hit is at relative tick

    j_e = (k*p+E-7)/2,     e=+1,
    j_e = (k*p+E-1)/2,     e=-1,

where k is the unique member of {1,3} with kp=1-E mod4. Indeed the relevant h_j must be a multiple of p with residue 1-E mod4, and the first such positive multiple gives the first strict future hit. Since p>B, j_e>T; there is no earlier negative multiple in the remaining plateau (h_j>=-3 there), and j_e<=T+2p. The hit residue has the correct relative parity. The same k works for both sides; the odd-side hit is exactly three ticks later for its corresponding root class.

For every other odd prime q<=2j_e+7, choose an allowed root residue outside F_q(E); it exists by freedom, including for q>B where the prefix is unconstrained. Combine by CRT, also M odd. If prime roots desired, all chosen residues can be nonzero and the class is reduced, so Dirichlet gives arbitrarily large prime roots. Select M sufficiently large that the uncut and adaptive trajectories agree through j_e. For all future ticks through that event, possible raw gcd factors divide h_j with |h_j|<=2j_e+7: no q other than p can compete. At the designated p-clock, p is the least raw factor. This proves the alternative for both sides.

The statement is about varying integer roots with a FIXED finite prefix. It does not assert that the next label of one fixed root is arbitrary or that a free prefix stops. A forced prime may be a previously selected label (its residue is then fixed), or an unselected small prime due to accumulated exclusions. If no previously selected prime divides a neighbor at the endpoint and no unselected prime <=2N+3 is forced, the prime-root prefix is free. Thus all genuine modular obstructions to unrestricted fresh-label entry are localized by (1).

## 4. Renewal of free prefixes

The escape alternative can be made stable under adding new events, rather than just one last event.

Let the prefix be free for the chosen root variant. Put

    Q = product of distinct primes in S union {odd primes q<=2N+5}.

For any sufficiently large prime p=1 mod Q, in particular p>2T+7 and p>2N+5, append the event of section 3 on either side at its stated tick. The enlarged prefix is feasible AND FREE.

Proof: for q in the defining set of Q, take an allowed residue avoiding F_q(E). Since the new gain is p-1=0 mod q, F_q(E+p-1)=F_q(E); the same residue avoids both the old plateau and the new endpoint, while preserving the prefix. For the fresh label p, use M=(2-E+e)/2 mod p; after its event the horizon is e-1 mod p, either 0 or -2, neither +/-1 because p>=5. For every other q>2N+5, exclude the neighboring divisibility residues on ALL N+2 plateaus including the new endpoint, and exclude 0 if prime-root variant. At most 2N+5 residues are forbidden, so one remains. All constraints for the extended word and for terminal avoidance are therefore individually satisfiable. The finite CRT argument and section 2 give a feasible free word; the appended event is exactly the p hit, by the same relative-clock proof. Dirichlet supplies arbitrarily large primes p=1 mod Q, and separately arbitrarily large prime roots in the corresponding reduced class for any fixed extension. No simultaneous-prime conjecture is used.

Iterating, starting from ANY free prefix, there are free extensions containing arbitrarily many strictly increasing new labels, with arbitrarily large prime-root realizations at each finite depth. This generalizes the earlier special reset-word construction; it does not require even-side resets or bounded deficit. It also explains an obstruction to trying to prove twin infinitude just by excluding sufficiently many fresh labels through a fixed finite transcript: the class of free prefixes admits arbitrarily long such extensions. Their integer root representatives can grow without bound with depth. The nested cylinders need not have a common ordinary integer root; no infinite actual ray, finite-twins counterexample, or twin proof follows.

## 5. Explicit uniform support bound for all k, without compactness

We can also replace the earlier nonconstructive finite-alphabet theorem by a completely explicit recursion. Consider the relaxed horizon path H even, H=e mod a, H'=H+a-1 with odd integer labels a>=3 (primality unnecessary). Let B(j) be already-proved uniform bounds for blocks on at most j distinct labels, with B(0)=0. For example B(1)=2, or use the previous exact prime bounds B_R(1,2,3)=2,6,18 and actual-clock bounds B_M(1,2,3)=2,5,11.

For any k>=2 define

    B(k) = B(k-1) + k! * 2^k * product_{j=1}^{k-1} binom(B(j)+j,j).   (2)

This is a valid uniform upper bound in the same model for which the smaller B(j) are valid (relaxed, actual, or arbitrary odd integer labels in the relaxed model).

Proof: consider a block using exactly k labels; before the first occurrence of the last new label there are at most B(k-1) events. At every post-event horizon after all k have appeared, record a RECENCY SIGNATURE:

1. the permutation of labels in increasing order of their LAST occurrence;
2. the sign e at each of those k last occurrences;
3. for the gap strictly between successive last occurrences, the vector of counts of each label appearing there.

After the oldest last occurrence, only the remaining k-1 labels can occur; between the next pair only the remaining k-2 labels, and so on. A gap with j remaining labels has at most B(j) events, hence at most binom(B(j)+j,j) possible count vectors by stars and bars (allow sum <= B(j)). The newest last occurrence is the current final event, so no final gap remains. The total number of signatures is bounded by the product term of (2).

Crucially each signature determines H mod a for every fixed label a in the support: its last occurrence had pre-horizon residue e, and every subsequent event count is known from the signature, including the individual boundary last occurrences. Thus H mod a is e-1 plus the sum of all subsequent gains modulo a. If the same signature occurred at two different post-horizons, every congruence mod the fixed labels would agree. The intervening nonempty word could be repeated indefinitely in the RELAXED graph by translation, contradicting the fixed-label barrier at an even multiple of their product. This applies even to actual-clock blocks: repetition of a signature need only create an impossible relaxed path, not preserve the times. Hence no signature repeats.

If the first all-seen index is m<=B(k-1)+1, the number of recorded poststates is length-m+1. This gives (2) exactly. Induction starts at B(1)=2 (3 can occur twice, larger odd integer labels at most once). For paths with fewer than k labels the prior bound already suffices. No infinite-branch lemma, linear algebra, or existence theorem for simultaneous primes is required. It does not depend on the magnitudes of labels.

Concrete, nonoptimal upper bounds obtained by substituting the previous exact prime bases:

| k | relaxed-prime B_R(k) | actual MIN B_M(k) |
|--:|--:|--:|
|1|2|2|
|2|6|5|
|3|18|11|
|4|42,900,498|8,805,899|
|5|60548075721037283800061572541207700498|22062626296810518489216121850853899|

For general odd integer labels without using the prime-specific base, B(2)=26, B(3)=54458, B(4)=11722653801604301498. These are very coarse explicit bounds, not estimates of the actual optimal values. (2) can be sharpened by recording only realizable count vectors rather than all stars-and-bars possibilities. It proves a quantitative version of the global result without invoking the previous compactness proof.

Under finite twins every large-root adaptive trajectory is infinite. If its current prefix has k distinct selected labels, it must encounter a new label within at most B_M(k)+1 additional nonunit events (or sooner, since part of the bound has already been used). The uniform spatial window from the earlier note may now use any explicit m=B_M(k)+1. This is a bound on the time in EVENT COUNT to the next new label, not an upper bound on the total number of labels in an infinite trajectory. No contradiction yet.

## 6. Exact finite diagnostics

[Fresh-label audit at a296e48](https://github.com/tara-sooo/A166944-Lean/blob/a296e488d932ef440b13f4ed1d61f60a28cf4e86/research/min_direct_fresh_label_audit.mjs), blob 59f8c988a6f0051f4e4ad834f76aeed6184c6085; [renewal/recency audit at 9327545](https://github.com/tara-sooo/A166944-Lean/blob/932754552d1295b71695aea7982033d1b0f20237/research/min_direct_renewal_recency_audit.mjs), blob d569265408010faa253ee8229d542948ea5381b3. Both exact remote readback. Run from repository root:

    node research/min_direct_fresh_label_audit.mjs
    node research/min_direct_renewal_recency_audit.mjs

Executed the actual ECMAScript functions in the tool runtime, not separate Node processes. The first audit deduplicated 808 actual uncut relative words from odd roots 5..151 and T=0..24. All-odd cylinders: 624 free,184 forced. Prime-root variant:388 free,107 forced,313 infeasible for arbitrarily large prime roots (not necessarily no small prime root). 41208 literal prefix membership checks,138 forced-next bounds; 17148 compressed decision comparisons including 7766 additional proposed words with one/two events, not merely known feasible words. 23432 exact per-prime residue-set comparisons and 94362 omitted-prime checks; all assertions passed. In the additional proposed words 115 are feasible for all-odd roots,84 for prime roots.

Example: from M=5 the word [1,1,1,3] through T=4, E=2 forces q=3; [1,1,1,3,3,1] through T=6, E=4 is free, including the reduced-residue variant. The 1 symbols mean quiet ticks. For the empty word and the latter six-tick word, the audit constructs full reduced CRT classes for p=53,101,257, both sides, and literally replays the adaptive parity-GCD word at a large representative of each class (12 constructions). These representatives are not asserted prime; Dirichlet supplies arbitrarily large prime representatives. For example six-tick word and p=101 yields next relative tick49 on even side or52 on odd side. Actual arithmetic checks use BigInt for the constructed root and gcd.

The second audit checks renewal twice from each seed and each side with the event-list interval algorithm (not enumerating the 1.46 million ticks). From empty word, p=31 then19531; from six-tick word, p=211 then974821, with Q respectively 15,3255 or105,243705. Both appended prime labels and exact tick formulas verified; the resulting compressed cylinders are feasible and free for prime roots, not a primality assertion for a concrete huge root. For recency signatures, check 699 exact maximizing relaxed paths for all one/two/three-prime sets from 3..59 and three sampled four-prime supports: 1456 signatures,2808 gap-count comparisons; reconstructed residues and nonrepetition all pass. Recursion (2) evaluated with exact BigInt binomial coefficients.

## 7. Research status and next target

The new-label dichotomy is exact at the level of a fixed finite transcript across arbitrarily large roots, and its decision depends on event count rather than elapsed ticks. It identifies a concrete obstruction to bounded-support termination proofs that use only finitely many relative congruences: free cylinders can renew with arbitrary increasing fresh labels indefinitely at the finite-prefix level. The explicit recency theorem now supplies a constructive uniform upper bound for every fixed support size, in addition to the previous exact small-k results.

The central missing step is still ABSOLUTE-SCALE control of a single integer root or a family of small representatives of the cylinders. In particular neither CRT freedom nor the existence of arbitrarily long prefixes proves nontermination of a fixed root, and the support bound does not make the support finite. A new narrower research target is to relate the forced/unforced classification to the size of the SMALLEST root realizing the word, or to prove that a sufficiently small actual root cannot undergo the required free renewal without first exhausting its eligible labels. The exact compressed feasibility test may help distinguish restrictions intrinsic to the word from restrictions that arise only at the absolute sqrt(H) cutoff. No Lean executable available, no Lean files changed. No finite-twins contradiction or A166944 record proof; no claim of external novelty. Main and sibling branches unchanged.
