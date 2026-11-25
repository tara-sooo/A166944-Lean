# Constructive reset words and phase-sensitive arithmetic primality certificates

2026-11-25 JST. Continuation of independent MIN lane at [425a4b9](https://github.com/tara-sooo/A166944-Lean/commit/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a). No source ensembles, pair energies, return-cost decompositions, or probabilistic assumptions. Paper deductions, finite audit, no Lean verification or external novelty claim. Twin infinitude remains OPEN.

## 1. Exact clocks from even reset states

Let C>=12 be divisible by 4, t=C/2 (even), and p an odd prime dividing C-1 (minus/even side) or C+1 (plus/odd side). At fixed C the first strict next hit for this particular p is the following gap w, interpreted as the unique positive representative modulo 2p:

| p mod 4 | minus side | plus side |
|--|--|--|
| 1 | (p-1)/2 | (p+5)/2 |
| 3 | (3p-1)/2 | (3p+5)/2 |

Proof: C=kp+1 for minus, C=kp-1 for plus, k odd. For C=0 mod4 the minus quotient k is 3 mod4 if p=1 mod4, 1 otherwise; the plus quotient k is 1 mod4 if p=1 mod4, 3 otherwise. Substitution into t=C/2 and the clock residues 0 or p+2 modulo 2p gives the table. The plus p=3 formula 7 wraps to 1. From the canonical odd root time t=C/2+3, subtract 3 and take the positive representative again; for p>=11 this gives the four unwrapped expressions (p-7)/2, (p-1)/2, (3p-7)/2, (3p-1)/2. The actual MIN selects the earliest eligible hit, ties by least prime, not necessarily the smallest divisor across both sides.

If an even-side p=1 mod4 (p>=13) wins at a canonical root, its gap is (p-7)/2 and the poststate is an even reset C'=2t'. From an even reset the same type of winning event has gap (p-1)/2 and preserves C'=2t'. This elementary observation supplies a constructive word family below. The reset phenomena themselves have also been studied elsewhere in this repository; no claim of novelty for the individual clock identities.

## 2. Arbitrarily long reset words via direct CRT construction

Fix any k>=1 and quiet-tail length L>=1. Put E_0=0. Choose primes p_1,...,p_k recursively with

    p_i >= 13, p_i > E_(i-1)+3,
    p_i = 1 mod [4 * product(odd primes q<=2(k+1)+1) * product(p_h, h<i)],
    E_i = E_(i-1)+p_i-1.

(Overlapping factors are harmless; the progression is reduced.) Dirichlet's theorem supplies arbitrarily large primes at each finite step. The p_i can be chosen strictly increasing; E_(i-1)+3 already exceeds p_(i-1). All gains are multiples of 4, and every later gain is a multiple of each previous label. Prescribe the k nonunit ticks at relative times

    j_1=(p_1-7)/2, j_i=j_(i-1)+(p_i-1)/2 (i>1).
    T=j_k+L=E_k/2-3+L, B=2T+7.

For each p_i impose C0=1-E_(i-1) mod p_i. At the intended prestate C0+E_(i-1), the minus neighbor is divisible by p_i. At every earlier prestate the residue is 1-d, where d is a positive even sum of intervening gains, 12<=d<=E_(i-1)<p_i-3; it cannot be +/-1. At all later states C0+E_j, j>=i, the residue is 0 because the current gain is p_i-1 and all later gains are divisible by p_i. Thus each selected label is eligible ONLY at its designated stage, including absence at the terminal.

For each other odd prime q<=B choose a residue of C0 excluding

    C0 = +/-1-E_j mod q, 0<=j<=k,
    C0 = -2 mod q (if a prime root is desired).

If q<=2(k+1)+1, every gain is divisible by q and C0=0 is permitted. Otherwise at most 2(k+1)+1 residues are forbidden, strictly fewer than q. The selected p_i residues also avoid -2: 3-E_(i-1) is odd nonzero and smaller than p_i in absolute value. All these constraints plus C0=0 mod4 combine by CRT. They prescribe a reduced residue class for the odd root M=C0/2+1 modulo 2 times the product of the odd q. Dirichlet therefore permits arbitrarily large PRIME M satisfying them. Without a prime-root requirement, ordinary CRT suffices for arbitrarily large odd M.

Take M large enough that all selected labels satisfy p_i^2<=C0+1. Induct on actual ticks. Before the first prescribed event the horizon is C0; thereafter each prescribed gain gives the expected E_j and even reset, by section 1. All primes <=B other than the intended label are ineligible at every corresponding plateau. At each tick up to T, every possible raw GCD prime divides the odd nonzero relative defect h=2j+7-E (j odd) or 2j+1-E (j even). Its absolute value is <=2T+7=B by the envelope C<=2t (or directly by the prescribed resets), as proved in the previous note. Thus no larger prime can compete or fire in the terminal quiet tail. The exact prescribed word holds for both uncut and adaptive square-root MIN (also for any fixed cutoff containing its labels).

Moreover, choose 2(k+1) distinct odd fresh primes q>B, all larger than E_k+3. Add congruences C0+E_j+s=0 mod q_(j,s) for j=0..k, s=+/-1. All moduli are coprime to the old ones; 2-E_j-s is odd nonzero of smaller absolute value than q, so the root residue remains reduced. With sufficiently large M, each of these neighbors strictly exceeds its prescribed divisor. Consequently we can realize the exact same arbitrary-length reset word and quiet tail at arbitrarily large PRIME roots with BOTH neighbors composite at EVERY visited plateau. Dirichlet is applied only to ONE prime root variable, never to simultaneous primality of the neighbors.

This gives explicit families of words with distinct labels, bounded recorded reset deficit after each event, and arbitrarily long relative quiet tails. None of these local properties alone forces a twin center at a controlled absolute scale. In particular this is not an infinite bounded-deficit adaptive orbit: for each fixed integer root later events may resume and the labels/certificate depend on k,L.

## 3. Exact small-representative obstruction within the constructed family

Let D=product p_i in the nested-congruence construction of section 2. Because all later gains are divisible by previous labels, the final horizon Z=C0+E_k is divisible by every p_i and by 4. Thus the selected-label constraints are exactly

    Z=0 mod 4D,
    M=(Z-E_k+2)/2.

The equivalence here concerns the selected-label congruences and canonical parity ONLY, not full first-hit competition. It reduces the candidate roots to a single progression of step 2D. If p_k is to be selected in the adaptive pool, its pre-horizon is Z-(p_k-1), so necessarily

    Z >= p_k^2+p_k-2.

The previous general quiet certificate L>=2 floor(sqrt(Z+1)) then requires L>=2p_k. The improved phase certificate below has a smaller sufficient L. A finite small-representative search can enumerate multiples of 4D between the adaptive lower bound and the quiet-certificate upper bound and test the exact prefix inequalities and terminal exclusions. The CRT guarantee of section 2 does NOT force one of these multiples into the required interval.

For a fixed reset prefix, the terminal uncut quiet condition eventually excludes exactly the residues Z=+/-1 mod every odd p<=floor(L/2), irrespective of earlier choices; larger p may add phase-dependent exclusions. So the small-representative issue includes a genuine simultaneous two-neighbor sieve on that progression. The prefix restrictions can only remove roots from this set. Arbitrarily many admissible words or positive CRT density do not directly give the small representatives.

There is also a simple coverage observation: any twin center Z>=12 is 0 mod6. If Z=0 mod4, the canonical odd root M=Z/2+1 starts at Z. If Z=2 mod4, M=Z/2 is odd and divisible by 3; its initial horizon is Z-2, and the next even tick M+3 is divisible by 6. The label 3 is eligible since Z-3 is divisible by 3, and necessarily wins. The poststate is Z at deficit 6. Thus any sufficiently large twin center already has a canonical adaptive realization with at most one nonunit event. The unrestricted existence of a quiet-ending word with a small representative is therefore not in itself stronger than finding twin centers via a very simple root. Nontrivial prescribed prefixes are useful only if they supply extra constructive arithmetic control, not merely because they are long.

## 4. A sharper direct certificate at an even reset

Write b=floor(sqrt(Z+1)) for an even reset Z=0 mod4. If either neighbor is composite it has an eligible odd factor p<=b, and the exact table gives a hit by

    floor((3b+5)/2)

ticks. Consequently an uncut or adaptive quiet tail of this length is sufficient for twins; the old general 2b bound can be reduced asymptotically by a factor 3/4 at these resets. For any earlier fixed cutoff containing the factors up to b the same implication holds. A small-representative objective may therefore use L>=floor((3 floor(sqrt(Z+1))+5)/2) in place of 2b. This remains a sufficient certificate, not a theorem that a suitable reset must occur.

There is a stronger structural conclusion for shorter quiet tails. Suppose the L ticks after an even reset are quiet, 2L-5>=b, and ((2L-5)/3)^3>Z+1. Then every composite neighbor has least prime factor p with

    p=3 mod4, p>(2L-5)/3.

Indeed, a factor p<=b congruent 1 mod4 would fire by (p+5)/2<=L; a factor congruent 3 mod4 with 3p<=2L-5 would also fire by L (wrapping only makes it earlier). All prime factors of a composite neighbor exceed (2L-5)/3, so three factors with multiplicity would exceed Z+1. It follows that either the neighbor is prime or it has precisely the following factorization into two primes:

    Z-1 = p r, p=3 mod4, r=1 mod4, r>b;
    Z+1 = q s, q=3 mod4, s=3 mod4, q<=s,

where p and q exceed (2L-5)/3 and are <=b. The condition on r follows from the exclusion of small 1 mod4 factors. These statements apply separately to composite minus and plus sides. This is an arithmetic narrowing of the obstruction, not a proof that the two semiprime forms cannot coexist.

For instance Z=59988, t=29994 is an abstract even reset state; Z-1=223*269, Z+1=239*251, all four factors prime. It is quiet for 333 ticks (about 1.3596 sqrt(Z+1)); the next hit is at gap 334. Both neighbors are composite. This is a counterexample to promoting the shorter quiet/semiprime criterion to a twin certificate. No claim is made that this abstract reset occurs from a particular canonical root.

## 5. Reproducible finite audit

[Source at 15642f4](https://github.com/tara-sooo/A166944-Lean/blob/15642f47ff36b74fa0ba25982805e1d5803c1dda/research/min_direct_reset_words_audit.mjs), blob 3356826331bb4e2f11e82dde2209a4e58918bce6, exact readback. Run from repo root:

    node research/min_direct_reset_words_audit.mjs

Executed the actual ECMAScript audit function, not a separate Node process. The finite selected words (13), (13,37), (13,37,73) do NOT obey all the deliberately stronger nested divisibility choices of section 2; instead the program verifies the required local residue exclusions directly. In particular their selected progression is computed by general CRT and need not equal Z=0 mod4D. Literal raw parity GCD and adaptive trace agree with the constructed word and tail for each large CRT root, and each composite lift is checked by proper divisors. Reduced residue classes are constructed; displayed concrete large roots are not tested for primality.

For each word and L=200 the script scans every positive odd candidate in the selected residue class through M=10^7, checks adaptive prefix, exact uncut full-word residue constraints, and primality of the final neighbors. First twin column refers to the actual adaptive prefix ending at twins, independent of whether the uncut trace remains quiet for the entire 200 ticks. The small certificate count uses the OLD 2b sufficient condition as a conservative comparison.

| word | event ticks | selected M residue / modulus | first adaptive prefix M | first adaptive twin M | full uncut word count | small certificate count |
|--|--|--|--:|--:|--:|--:|
|13|3|21 / 26|125|151|12746|9|
|13,37|3,21|125 / 962|12631|12631|61|0|
|13,37,73|3,21,57|40529 / 70226|2638891|none to 10^7|0|0|

The second word's first actual twin center is 25308; the first word's is 312. The three constructed large CRT roots have 167,185,215 decimal digits and the all-composite lifts 178,201,237 digits. At L=200 the 3-label example has no small representative even for the improved phase certificate: all matching adaptive prefixes begin at M>=2638891, much above its scale. This illustrates why the mere congruence construction does not close the proof.

Independent exact phase check on every even reset Z=0 mod4, 12<=Z<=200000: 149168 eligible prime/side clock comparisons against the least positive modular residue; 1535 states meeting the shorter structural certificate; 489 individual composite-neighbor cases with the asserted semiprime forms, 46 states with both neighbors composite. All assertions passed. This finite range concerns abstract even resets, not actual source incidence. The example Z=59988 has largest ratio L/sqrt(Z+1) among these both-composite cases.

## 6. Next task

The improved reset-specific stopping criterion and two-semiprime characterization are useful without any cost decomposition. The constructive word family provides exact candidate progressions and identifies the actual absolute-size problem; the one-step coverage observation shows that merely increasing the word length is not a route past the twin sieve. Seek a mechanism that controls the smallest actual representative or excludes the two-semiprime obstruction by using the relation of the last selected label to the final center, rather than using full-period CRT as if it gave short-interval distribution. A possible narrower target is a uniform construction of reset centers Z=p m with p near sqrt(Z) for which the phase exclusions force primality of both neighbors; no such construction is established. Main and other branches unchanged. No new Lean theorem, no twin-prime proof.
