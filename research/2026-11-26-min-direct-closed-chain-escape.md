# Closed two-event chains: record-side attrition and quantitative density-zero theorem

Continuation of [9eb9e43](https://github.com/tara-sooo/A166944-Lean/commit/9eb9e437e1d55289453b45001277a45dd4cbf545) on the independent direct-arithmetic branch. Arbitrarily long finite chains of the preceding odd-reset cylinder exist. This note proves the complementary global result: the natural-density upper bound for roots beginning a long chain of this class tends to zero, with a quantitative rate. The argument permits repeated or decreasing second labels and uses the actual necessary roughness condition, not an independence model for successive events on a fixed integer ray. No assertion that every fixed integer chain ends, nor a contradiction with finite twins.

## 1. Relaxed closed return map

Use X=2M, M odd, for canonical states. The preceding closed odd-reset two-event class has the following necessary conditions for each segment:
    X=2 mod4, X=2 mod3, X=3 mod7, X in {3,4} mod5;
    r>23 prime, r=3 mod4;
    r is the least prime dividing (X+3)(X+5), and r divides X+5;
    X'=X+r+5 satisfies the same small-modulus conditions.
The least-prime condition follows from the previous cylinder's exclusion of ALL primes below r from both intermediate neighbors, and its condition X=-5 modr. This note concerns that cylinder, NOT all possible two-event returns with labels 7,r. Drop the additional initial-clock exclusions at 11,13,17,19, the r+4 competitor test and adaptive eligibility. The resulting deterministic partial map on X is a relaxation: every actual closed-cylinder chain is also a chain of this map, though the converse need not hold. For ordinary integers, no positive primality hypothesis is needed to bound its length by the following argument.

## 2. A direct barrier for the return map

A step of label r changes X to X+r+5 with X=-5 modr. An even cut J divisible by r cannot belong to the half-open interval [X,X+r+5). Indeed J-X is an even nonnegative integer congruent to5 modr, whose least possible value is r+5 for r>23. Landing on J itself is allowed.

For R>=23 put P_R=product of odd primes <=R. Every multiple of 2P_R is a simultaneous cut for all allowed labels <=R. Thus any contiguous chain of the relaxed map using only labels <=R has total X-coordinate gain at most 2P_R, irrespective of multiplicity or order. Each step has gain >=1, so a chain of K steps with K>2P_R must use a label >R. The same bound works in a formal residue vector: relative to the current starting shift, solve by finite CRT for the next nonnegative even offset at which all coordinates for p<=R are zero. This offset is <2P_R. A path of shifts cannot pass it. In particular a simulation using only known primes always ends after finitely many steps, either failing a closed-map test or reaching a state with no known divisor. This also shows that an infinite chain, if one exists, has unbounded record labels.

## 3. Reveal prime residues only when a new record is needed

Take independent uniform residues X_0 mod p for all odd primes p, with X_0=2 mod4. Equivalently this is the Haar product of finite residue spaces, not a random model for fixed integer trajectories. At any stage X=X_0+s for an even integer shift s. Initially reveal all primes <=23; enforce the small-modulus root conditions. If they fail, stop.

Given all revealed primes <=L, simulate the relaxed return map using the least known divisor of (X+3)(X+5) at each stage. If that divisor violates the necessary class conditions, stop. If no known divisor exists, a record search starts. By section2 this decision is made after finitely many known-prime steps. The shift s at that decision is determined entirely by the revealed residues. Reveal fresh primes in increasing order until one divides either X+3 or X+5. For each fresh prime p, exactly one of its p possible residues gives p|X+3, and a different one gives p|X+5. Both have conditional probability 1/p, independent of the previously revealed data and earlier misses in this search. The first hit exists almost surely because the two-root prime product tends to zero. Conditional on the first hit being any specified p, its side is equally likely. Therefore
    Pr(record search yields a permitted continuing step | known information) <= 1/2.   (1)
The side X+3 is always fatal to this relaxed class. The other side can also fail the size, congruence or closure conditions, so equality is not asserted. In particular the conditional probability of m successful record searches in succession is <=2^(-m). No independence of successive record labels, intervening steps or successive actual excursions is used. Revealing p itself and all smaller primes preserves the independent uniform distribution of unexposed coordinates, including when the stopping label p is random: condition on each possible finite transcript.

Together with the finite known-prime barrier, (1) proves that almost every formal residue vector has only a finite initial relaxed closed chain. This alone does not prove an ordinary integer cannot have an infinite such chain; the ordinary integer vectors are countable and have product measure zero.

## 4. Quantitative cutoff escape

For integer R>=23 define E_R to be the event that the known-only simulation at cutoff R reaches a root with no divisor of (X+3)(X+5) among primes <=R, BEFORE failing any necessary class test. This is a finite residue event by section2, and depends only on X_0 mod primes <=R and parity X_0=2 mod4. A genuine closed-cylinder chain that uses a label >R must satisfy E_R: all earlier labels <=R are selected identically by the known-only simulation. A chain may satisfy E_R and nonetheless fail at the next actual or formal record. E_R is decreasing in R, since a larger-cutoff escape must follow the same smaller-cutoff simulation until its escape, or else would fail there too.

Let L be the last revealed prime bound when a record search starts. For u>=L its next hit p obeys the exact conditional tail
    Pr(p>u | revealed transcript)= product_{L<l<=u, l prime}(1-2/l).
Use Q(x)=prod_{3<=l<=x prime}(1-2/l)=Theta(log^-2 x), proved in [6bdbf35](https://github.com/tara-sooo/A166944-Lean/commit/6bdbf354a5cb13f13abb6493da96acfe08e95531). Thus the tail is <=C(log L/log u)^2, uniformly in the transcript. In particular, for V=log(p+16)/log(L+16) and v>=2,
    Pr(V>v | transcript) <= C'/v^2.
For example choose u=(L+16)^v-16; u>L and log u>=v log(L+16)/2 for L>=23, v>=2. Conditional tail integration yields E[V|transcript]<=B for one absolute B>1 (take B>=2). This controls logarithms, not the expectation of the absolute record label.

Let L_m be the revealed prime bound after the m-th record search, whether successful or fatal; start L_0=23, and freeze the bound if the process has already stopped before that search. Each search occurs after a finite deterministic simulation with known primes; that simulation either stops or gives the shift needed for the next search, without exposing additional residues. Consequently iteration of the preceding conditional expectation bound gives
    E log(L_m+16) <= log(39)*B^m.
If E_R occurs, then either the record search crossing R (possibly a fatal hit) is among the first m searches, or at least m record searches succeeded. In the first case L_m>R. Therefore
    Pr(E_R) <= 2^(-m)+log(39)*B^m/log(R+16).
For R sufficiently large choose m=floor(log(log(R+16))/(2 log B)). Then there is an absolute beta>0, for instance beta=min(1/2,log 2/(2 log B)), such that
    Pr(E_R) = O((log R)^(-beta)).                    (2)
This proof does not require a known explicit optimal value of B. The bound also holds, with a multiplicative constant depending on the finite initial revealed bound, after conditioning on any finite prefix of a trajectory determined by finitely many prime residues, provided a canonical root is reached and the same closed cylinder starts there. The known-prime barrier and record-side argument still apply from that root. This is a finite-prefix extension, not a uniform estimate for arbitrarily late entry depending on all primes.

## 5. Transfer to ordinary integer roots

Write N for a large absolute root scale (not the X=2M coordinate). Among odd M in [N,2N], the proportion satisfying E_R differs from its product-space probability by O(P_R/N): as M runs over odd integers, X_0=2M ranges with stride4, which is invertible modulo the odd product P_R. Each complete period of P_R odd roots therefore gives the exact product distribution. A final incomplete period has at most P_R roots. By (2),
    proportion of odd roots in [N,2N] satisfying E_R
      <= O((log R)^(-beta)+P_R/N).                    (3)
This is an upper bound on actual cylinder escape, even when adaptive eligibility or additional clock tests prevent a return in the relaxed process.

For a chain of at least K consecutive actual closed-cylinder returns, choose R=floor(log K/(8 log 2)), for K sufficiently large. The elementary Chebyshev bound theta(R)<=4(log2)R implies P_R<=sqrt K. Thus K>2P_R for large K, and the chain must satisfy E_R. The same implication holds if its total X-coordinate gain is >=K, because K>2P_R. Equation (3) now proves uniformly for sufficiently large N,K,
    proportion of odd roots in [N,2N] beginning a closed-cylinder chain
      with >=K returns OR total X-gain >=K
      <= O((loglog K)^(-beta)+sqrt(K)/N).              (4)
The right side may be vacuous at extreme K; useful ranges include K=(log N)^a or K=N^a for fixed 0<a<2. Infinite chains are included in either condition for all K. Here total gain means the gain of the maximal consecutive initial chain of this specified class, not gain later on the unrestricted MIN trajectory. The use of a relaxation in (3) is essential; the result is an upper estimate, not an exact density formula for the actual closed-cylinder chain.

In particular for every fixed a>0, the fraction beginning a chain of gain >=(log N)^a or length >=(log N)^a tends to zero as N->infinity. The exceptional fraction is O((logloglog N)^(-beta)+ (log N)^(a/2)/N). The set of odd integer roots beginning an infinite closed-cylinder chain has natural density zero (sum the dyadic interval upper bounds, or use periods directly). Even for any fixed prescribed finite prefix leading to such a chain the corresponding exceptional family has density zero, by the conditional extension in section4 and finite CRT. This does NOT permit taking an unrestricted countable union of density-zero integer sets, and it does not say that no integer has an infinite closed-cylinder tail.

These results are compatible with the previous positive-density construction for every FIXED finite k and lower bound on labels: (4) bounds the density as the demanded chain length or gain tends to infinity. They also imply no positive-density family can be confined forever to this particular closed return type. Under finite twins an infinite canonical ray may leave this type immediately or may alternate many other types of segments; finite twins do not force the hypotheses of an infinite closed chain. Thus the density-zero result is a genuine restriction on this class, not a twin-prime contradiction. It uses no prime-tuple conjecture, PNT in AP, or unverified independence for integer trajectories.

## 6. Diagnostics and persistence

[Audit ba9147a](https://github.com/tara-sooo/A166944-Lean/blob/ba9147a845d2e43e9201f52dd77ef82a225bda7e/research/min_direct_closed_chain_escape_audit.mjs), blob 549e88347f886f59b179911e6a0de74f830cd0f8. Exact remote readback. Run node research/min_direct_closed_chain_escape_audit.mjs. Actual ECMAScript execution in tool runtime, not a separate Node process.

For 30,000 consecutive odd M in [5000001,5060001), applied the known-only relaxed map at cutoffs23,79,331,499,919,2011: 180,000 cutoff and nesting checks. Escape counts286,155,91,71,60,42 respectively. In this particular small sample none of the known-label steps passed all class tests; these counts are diagnostics of nested escape, not empirical tests of the asymptotic exponent. For all odd primes through251 and every shift residue, enumerated exactly one hit residue per side and no overlap:6079 shift/prime checks,995773 individual residue checks.

Reconstructed the seven-segment CRT witness of 9eb9e43, on two distinct lifts. At cutoffs23/79/331/499/919/2011 the known simulation follows 0/0/1/2/4/7 prescribed steps, escaping at every earlier cutoff; at2011 the relaxed class subsequently fails. Twelve chain/cutoff comparisons, 42 total known-map barrier checks including witness controls, 7476 independent literal BigInt GCD ticks for the two actual seven-segment paths. All assertions passed. No numerical estimate of beta from finite samples, no Lean kernel verification, no external novelty claim. Main/sibling branches unchanged.

Next: extend the fresh-prime side obstruction beyond the restrictive all-small-factor exclusion of the closed cylinder. A possible route is to expose primes by increasing size while allowing all bounded-label MIN dynamics, then study what fraction of new record hits force or prevent canonical return. The one-sided record test here is specific to this cylinder and cannot simply be assumed for generic MIN records.
