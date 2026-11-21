# Extremal prime overdraw: rough-horizon sieve, finite 210-state classification, and the remaining G barrier

Date: 2026-11-22 JST. **Status:** new paper arguments (elementary CRT and a classical divergence theorem for reciprocal primes), new finite 210-state certificate, and direct recurrence audits. This is NOT a Lean kernel proof, not an unconditional Cap B proof, and not a proof of infinitely many twin primes.

The input is the genuine original A166944 recurrence, not artificial local states. Sources:
- [previous cross-key/overdraw analysis](2026-11-22-cross-key-startup-credit-and-extremal-gaps.md);
- the existing [210-state potential verifier](cap_b_prime_debt_210.py), which gives the integer potential 0<=V<=29 and validates its finite edge inequalities;
- the kernel-checked exact first-hit framework in [Lemmas.lean](../A166944/Lemmas.lean) and [FirstHitArithmetic.lean](../A166944/FirstHitArithmetic.lean);
- the earlier [adaptive quiet interval criterion](2026-11-22-adaptive-event-count-analysis.md).

## 1. Definitions and a strengthened first-hit roughness lemma

At a genuine first-hit step (s,C) -> (r,C+p-1) with prime increment p>=11, put g=r-s and define the potential debt

    b=max(0,g-(p-1)+V(r,C+p-1)-V(s,C)),

and its overdraw

    eta=max(0,b-(p-1)).

As already derived, eta>0 forces

    2p-30 <= g <=2p.                                  (1)

**Roughness lemma (paper).** For **every odd prime q** dividing either C-1 or C+1 at this event, the first-hit property implies

    g<=2q.                                             (2)

Indeed, when q|C-1 an even multiple of q occurs in every 2q consecutive index positions. When q|C+1 an odd index r congruent to 2 modulo q occurs in every 2q consecutive index positions. At the corresponding test the gcd is at least q>1, so the true first nonunit hit cannot be later. This argument is valid up to r because all preceding indices retain horizon C.

Combining (1) and (2):

    eta>0 and q|(C-1)*(C+1) => q >= p-15.            (3)

Equivalently, **both C-1 and C+1 have no prime divisor smaller than p-15**. This is stronger than merely knowing that p divides one of them.

## 2. Uniform CRT count for the large-prime overdraw tail

For fixed odd-prime cutoff y>=3 define

    P_y = product of odd primes q<=y;
    R_y = product of (q-2) for odd primes q<=y;
    rho_y=R_y/P_y=product(1-2/q).

For even C=2t, each odd prime q excludes precisely two residue classes of t mod q via q|(2t-1)(2t+1). By CRT, exactly R_y of the P_y residue classes of t mod P_y avoid all those exclusions.

In any interval of N consecutive t-values, at most rho_y*N+R_y values are allowed (partition into full P_y cycles and a shorter suffix).

For an **actually attained canonical record** M, put s0=M+2, K=floor((7M-1)/4), G_M=D(K)-(2M-2), and H_M(y+) the number of overdraw events in (s0,K] with prime increment p>=y+16. The pre-event horizons C are distinct even numbers, are >=2M-2, and are <=D(K)-2, so there are at most G_M/2 possible C/2 positions. By (3) all these positions avoid prime divisors q<=y. Therefore the unconditional **finite inequality**

    H_M(y+) <= (rho_y/2)*G_M + R_y.                   (4)

Here unconditional refers to the recurrence and the certified 210-potential definition of overdraw; the CRT proof needs no liminf hypothesis or no-slow assumption.

Examples of the exact sieve coefficient:

    y=7:   P_y=105,   R_y=15,   rho_y=1/7,
           H_(p>=23) <=G_M/14+15.
    y=13:  P_y=15015, R_y=1485, rho_y=9/91,
           H_(p>=29) <=9*G_M/182+1485.

As y->infinity, rho_y->0 because sum over primes 1/q diverges, and log(1-2/q)<=-2/q. Using the previously established global G_M<=(3/2)M+O(1), (4) implies:

**Theorem (paper).** For EVERY prescribed integer threshold Y(M)->infinity, along ANY unbounded sequence of genuinely attained canonical records,

    #{overdraw events with prime increment p>=Y(M)} = o(M).  (5)

This is uniform in the growth of Y(M), even if Y(M) increases arbitrarily slowly. The constant R_y is fixed while taking M->infinity; only afterwards is y increased.

Consequently, H_M=o(M) **if and only if** for every fixed prime p>=11 the count H_{M,p} of that particular prime's overdraw events is o(M), along the same unbounded record sequence. The reverse implication follows from splitting at fixed y and applying (4), then letting y grow. This isolates the genuinely dynamical **fixed-prime** obstacle.

## 3. Strong finite 210-state refinement for all overdraw primes

For a non-inert pre-horizon C mod210 (at least one of 3,5,7 divides C-1 or C+1), the 210-clipped first hit occurs by gap 14. A true event with prime increment p>=11, coprime to 210, must occur STRICTLY before that clipped hit, so g<=13. Since -29<=V(after)-V(before)<=29,

    eta>0 implies 2*(p-1) < g + Delta V <=42.

Thus for every p>=23 a non-inert overdraw is impossible WITHOUT any extra finite enumeration.

For p=11,13,17,19, [the companion independent audit](extremal_overdraw_sieve_audit.py) constructs and verifies all 22,050 states, 58,232 edges and the 19-round 210-potential certificate. It then exhausts all 210 residue pairs (s,C) with even C, non-inert C and all g in [1,min(2p,h-1)], where h is the first clipped hit; retain those for which g+V(after)-V(before)>2(p-1).

Exact results:

- p=11: 376 admissible (s,C,g) residue triples; the non-inert C residues are
  {10,22,24,26,28,34,36,40,64,100,104,106} (12 residues);
  maximum signed overdraw is 10.
- p=13: 184 triples; C residues {20,22,36,64,100} (5 residues);
  maximum signed overdraw is 8.
- p=17: zero non-inert overdraw triples; maximum signed overdraw is 0.
- p=19: zero non-inert overdraw triples; maximum signed overdraw is -7.

The audit uses an **overapproximation**, ignoring further divisibility constraints on p and all other horizon factors. Hence excluding a candidate in this larger model is sound for actual first-hit events.

**Finite-certificate consequence:** EVERY overdraw prime event with p>=17 has inert pre-horizon C mod210, while p=11 and13 may overdraw at specified additional non-inert residues.

There are exactly 15 inert even C residues mod210, or 15 classes of t=C/2 mod105. Therefore across any canonical growth span G_M, ALL inert overdraw events together number at most

    G_M/14 +15.

For the p=11 non-inert exceptions, combine the 12 allowed C mod210 classes with the two hit-side conditions C=+1 or -1 modulo11. CRT gives 24 eligible t-classes modulo 105*11, hence

    H_11,noninert <=12*G_M/(105*11)+24.

For p=13 the analogous five classes give 10 t-classes modulo 105*13:

    H_13,noninert <=5*G_M/(105*13)+10.

Adding these THREE DISJOINT CLASSES (inert; non-inert p=11; non-inert p=13) yields a new **finite-certified universal bound**

    H_M <= [1/14+12/1155+5/1365]*G_M+49
         = (2567/30030)*G_M+49.                    (6)

The coefficient is 0.08548118548..., so the density relative to *horizon growth* is bounded by ~8.55% plus a constant. This estimate counts each pre-horizon at most once in the inert class, without summing possible keys.

No mathematical assertion that H_M=o(M) follows from (6), because G_M can be proportional to M; the finite-state potential alone admits positive-density fixed-p exceptions.

## 4. Consequence for no-slow paths, and why this does not yet prove twin primes

The previous paper sufficient condition says that if NO slow interval exists inside [s0,K], then

    K-s0 <=2*G_M+31*H_M+41+2*isqrt(2*K+1).       (7)

If additionally G_M/M <=3/8-epsilon along an unbounded family of such no-slow records, (7) forces

    H_M/M >=2*epsilon/31 -o(1).                     (8)

By (5), that much overdraw cannot be supplied by primes whose values tend to infinity. Therefore **at least one FIXED prime p>=11 must contribute a positive linear fraction of overdraw events along an infinite subsequence of those hypothetical records**. This is a new finite-key obstruction in the low-growth/no-slow regime.

But this does not rule out the **high-growth branch G_M/M >=3/8-o(1)**. The existing direct endpoint F-drawup criterion would already guarantee a slow interval if G_M/M<1/3-o(1), so substituting (6) into (7) and seeking an upper bound on G alone is NOT a stronger global route. The numerically inferred criterion G/M <~0.161 from such a substitution is strictly **weaker as a sufficient result** than the already available direct-F sufficient threshold 1/3.

The remaining mathematical tasks are therefore precise and separate:

1. For a fixed prime p (especially 11,13,17), rule out or quantitatively control a **positive-density** sequence of eta>0 first hits on the *authentic* canonical record history. Fixed modular residue counts still permit such local patterns.
2. Control the **high-growth** canonical-record scenario directly, or derive a global relation that turns repeated large horizon growth into an F-drawup or an exit before K.

Both are unresolved. Proving only that high prime values are negligible does not control G_M, which has the much weaker general upper bound (3/2)M+O(1).

## 5. Reproduction and exact finite observations

Run from the repository root:

    python3 research/extremal_overdraw_sieve_audit.py

The standalone Python 3 script rederives the 210-potential in 19 rounds, verifies every edge inequality, exhausts p=11,13,17,19 non-inert cases, checks full-period CRT roughness counts through y=13, and replays:

- the original recurrence from a(1)=2 through n=2,500,000: 250 nonunit events and exactly SIX overdraw events (four with p=11, one with p=13, one with p=17), with no larger p;
- the independently certified canonical starting state M=45,895,573 through 37 exact first hits: G_M=1914 and H_M=2 (p=17 and p=47), with C-1 and C+1 both prime at the end.

These observations are *finite* and are not evidence of an asymptotic numerical rate by themselves.

**Verification status:** complete paper proofs for the CRT/roughness/asymptotic reductions, executable finite 210-potential and recurrence audit, remote GitHub commit/readback; no new Lean kernel check, no universal Cap B theorem, and no proof of twin-prime infinitude.
