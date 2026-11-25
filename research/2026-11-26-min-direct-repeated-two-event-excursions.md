# Arbitrarily long finite chains of long two-event canonical excursions

Continuation of [34c5171](https://github.com/tara-sooo/A166944-Lean/commit/34c517152608c231cf73487ee7c20e310ea18222) on the independent direct-arithmetic branch. The previous even-reset construction has an immediate mod-5 obstruction to repetition. Changing the second event to an odd reset permits arbitrarily many consecutive long two-event first returns along one actual integer trajectory, with any prescribed minimum excursion size. A modular spacing bound nevertheless restricts reuse of a second label within this class. No infinite trajectory constructed, no contradiction with finite twins, no Lean kernel verification.

## 1. The previous even-reset cylinder is not self-repeatable

Write X=2M for an odd canonical root M. In the previous construction, X=4 mod5, r=3 mod220 and the return changes X to X'=X+r+5. Therefore X'=2 mod5, outside its original residue condition. Two consecutive returns from that precise cylinder are impossible. This concerns the sufficient cylinder of the previous note, not all even-reset two-event returns.

## 2. Odd-reset two-event cylinder

Let r>23 be prime, r=3 mod4. At a canonical root M>=r^2, X=2M=2 mod4, impose:
- X=2 mod3, X=3 mod7, X in {3,4} mod5;
- for primes 11,13,17,19, X avoids 1,3 mod l;
- X avoids -3,-5 modulo every odd prime l<r;
- X=-5 modr;
- if r+4 is prime, X != -3 mod(r+4).

The first event is p=7 at relative tick7: the initial even-side defects at odd relative ticks1,3,5,7 are 9,13,17,21, and the odd-side defects at even ticks2,4,6 are 5,9,13. The conditions exclude all competitors earlier and at tick7, leaving raw gcd7. Thus H1=X+4, t1=M+9 even, ordinary deficit d1=14. At this horizon, H1-1=X+3 and H1+1=X+5 have no prime factors below r, and r divides only H1+1.

For relative offsets j after this plateau, the even-side defect at even j is 15+2j, the odd-side defect at odd j is 9+2j. Put w=(r-9)/2, positive odd. For odd j<w the defect is <r, and at j=w it equals r. For even j<w, the defect is <=r+4. The only such defects >=r are r and r+4 (the even defects increase by4); r does not divide H1-1, and r+4 either is composite with all prime factors <r (since r+4<2r for r>4), or is excluded by the final condition. Therefore no earlier event occurs, and at j=w the odd-side raw gcd is exactly r. Both selected primes are adaptive-eligible by M>=r^2.

This gives at absolute tick n2=M+(r+9)/2 the horizon H2=X+r+3, ordinary post deficit6 and adjusted deficit0. Since r=3 mod4, H2 is divisible by4, and the event itself is a canonical reentry. No earlier reentry because d>=14 after the first event until the second. The exact first-return gap and the excursion statistics are
    F(M)-M=(r+5)/2,
    max pre-tick d=r+3,
    # consecutive pre-tick times d>=r/2=(r+9)/4.
Here pre-tick times count the state after the preceding tick, including the tick immediately before the second event. To see the count, write r=4a+3: the even deficits run up to 4a+6, and the threshold r/2 requires d>=2a+2. There are a+3 such values after the first event. For r>=39 the initial pre-tick values <=18 are strictly below r/2, so this also counts all high-deficit times in the segment. In the chain construction and diagnostics below all r exceed 39. For r=31 the initial pre-ticks can contribute additional threshold visits, not included in the stated consecutive interval. The maximum r+3 always dominates the initial pre-tick maximum18.

If X'=X+r+5 satisfies X'=3 mod7, the new canonical root is nonterminal, since H2-1=X'-3 is divisible by7. In particular all the chained examples below are actual F returns, without needing any convention about terminal quiet ticks.

## 3. Arbitrary finite consecutive chains, with positive-density starting classes

Theorem. Given any positive integer k and real A>0, there exist increasing primes r_0<...<r_(k-1), all >max(A,39), and a nonempty fixed set of odd starting residue classes such that every sufficiently large starting M in those classes has k consecutive actual first returns with event words (7,r_i). All return targets are nonterminal, all excursions have maximum deficit r_i+3 and at least (r_i+9)/4 consecutive times of deficit >=r_i/2. Each return begins with post-event ordinary deficit14, then goes directly to an odd adjusted reset. No intervening return segments. The construction is unconditional.

Choose B=max(21,2k+1) and an auxiliary prime L>B. Inductively choose r_i>max(A,39,L+4,r_(i-1)+4) satisfying
    r_i=3 mod4;
    r_i=1 mod5 for even i, 4 mod5 for odd i;
    r_i=-5 mod l for every odd prime l<=B other than5,
        and for each earlier selected prime r_j;
    r_i=-4 mod L.
These are a single reduced residue class modulo the product of the distinct moduli (including4). All specified residues are coprime to their moduli, so Dirichlet's theorem on primes in arithmetic progressions gives arbitrarily large choices. In particular r_i+4 is composite, being a multiple of L with r_i>L. This eliminates the extra final even-clock competitor in section2.

Put s_0=0 and s_i=sum_{j<i}(r_j+5). The desired successive roots have X_i=X_0+s_i. For l<=B other than5 all s_i=0 modl. Fix X_0=2 mod3, 3 mod7, and 0 mod the other odd primes <=B except5. Fix X_0=3 mod5: then X_i alternates 3,4 because s_{i+1}-s_i is 1 or4 mod5. All these small-prime conditions guarantee the initial 7 event and the roughness exclusions for each intermediate plateau.

At a selected prime r_j impose X_j=-5 modr_j, equivalently X_0=-5-s_j modr_j. Stages i<j have r_i<r_j and need no exclusion at r_j, since their final even-clock extra competitor has already been made composite. Stage j has r_j dividing only its odd-side neighbor. At stage j+1, X_(j+1)=0 modr_j, and later shifts are 0 modr_j by the inductive prime choice. Thus all later stages avoid -3,-5 at r_j.

For every remaining odd prime l<=r_(k-1), l>B (including L), each stage with l<r_i excludes at most two residues of X_0, namely -3-s_i,-5-s_i. There are at most2k<l excluded residues, so an allowed class exists. No condition is needed at primes above r_(k-1), because all r_i+4 are composite. Add X_0=2 mod4. The CRT gives a nonempty set of simultaneous classes for X_0 modulo 4 times the product of odd primes through r_(k-1). Equivalently there are a positive proportion of odd roots M in a fixed finite period. Choose M>=r_(k-1)^2, then every stage meets eligibility. The section2 rule proves each consecutive return inductively. The final root is still X_k=3 mod7, so it is nonterminal.

Hence neither a uniform upper bound on the number of consecutive long two-event excursions nor one on their total duration (in terms solely of the first nonreset deficit14) can hold. The arbitrary length assertion is about finite chains with a varying initial integer. It does not produce a fixed ordinary integer carrying an infinite chain: the modulus and primes change with k, and CRT only solves the finite constraints.

## 4. A necessary spacing bound within the closed odd-reset class

For this subsection a closed segment means the section2 cylinder whose target also satisfies X'=2 mod3, X'=3 mod7 and X' in {3,4} mod5. The constructed chains satisfy this, including at their final target. In any chain of such segments:
    r_i=1 mod3, r_i=2 mod7,
    r_i=1 mod5 if X_i=3 mod5, and r_i=4 mod5 if X_i=4 mod5.
Indeed X_(i+1)-X_i=r_i+5, so the fixed mod3,7 classes give the first two conditions. Since r_i is prime>23, r_i+5 !=0 mod5, and the mod5 class must switch. Combined with odd-reset r_i=3 mod4, every successive shift is a multiple of84, and every pair of successive shifts is a multiple of420.

Suppose a second label r occurs at indices i<j. Its mod5 residue determines the source's mod5 class in this closed class, so j-i is even. Both X_i and X_j are -5 modr, and by the preceding congruences X_j-X_i is divisible by420. Since r>23 is prime and coprime to420,
    X_j-X_i >=420r.
This is a bound on actual root spacing on a single chain, independent of the unobserved clock phases. In particular no adjacent reuse is possible. For reuse two segments later, with intervening label s,
    X_(i+2)-X_i=r+s+10 >=420r,
    s>=419r-10.
Equivalently (s+10)/r is a positive integer congruent to419 mod420. This rules out the pattern r,s,r when the intervening label is of comparable size (for example s<=100r). For reuse after h segments with all intervening labels <=P, h(P+5)>=420r. For a chain of starts in a coordinate interval of length V, a fixed second label r occurs at most 1+floor(V/(420r)) times. These are necessary restrictions only for the closed cylinder defined above, not for arbitrary MIN returns or all two-event returns. They do not contradict an infinite chain using sufficiently many different primes.

## 5. Exact diagnostics and persistence

[Audit 3c5a843](https://github.com/tara-sooo/A166944-Lean/blob/3c5a843e6cc2f904deaee1a351f85473d7b3460a/research/min_direct_repeated_two_event_excursions_audit.mjs), blob 0c2fb8dad9f83b662205eb612414cb8254d84e83, exact remote readback. Run node research/min_direct_repeated_two_event_excursions_audit.mjs. Actual ECMAScript execution in tool runtime, not separate Node process.

A greedy search over primes <=15000 tried 20 candidate extensions, obtaining the sequence
    331,499,751,919,1171,1759,2011.
The finite examples use direct CRT consistency, not the deliberately stronger inductive prime selection in section3. The audit explicitly excludes the r+4 prime competitor when applicable (e.g. 499+4=503); all certified residue classes then satisfy section2. Prefix chains of lengths2,4,7 tested on two BigInt CRT lifts each; the respective representatives have 209,383,849 decimal digits and total durations420,1260,3738. All six chains actually follow their prescribed consecutive first returns, with 10836 literal GCD ticks, 52 event checks, 3624 small-factor residue checks, all passed. The seven-segment chain has peak deficits334,502,754,922,1174,1762,2014 and high-interval lengths85,127,190,232,295,442,505. Its terminal canonical root is nonterminal (eligible7). The greedy search stopped at seven under its chosen prime bound; it is not a maximal-length theorem.

Initial diagnostic used (r+5)/4 rather than (r+9)/4 for the high-tick count. The direct check at r331 detected the off-by-one, corrected before all reported counts. An additional residue exclusion for a prime r+4 was added after checking the exact even-side defect at w-1; both the final proof and final verified code include it. The finite examples have r>39, so there is no initial-tick threshold ambiguity. No formal Lean verification, no claim of a macroscopic infinite path, no external novelty claim. Main/sibling branches unchanged.

The result closes another uniform finite-chain upper-bound route. The remaining potential approach would require a genuinely global frequency bound on a single infinite ray or a stopping invariant; arbitrary finite chains, even with increasing labels and many exact returns, are compatible with finite twins.
