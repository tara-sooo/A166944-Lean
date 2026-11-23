# Genuine MIN prime returns: exact recharge, a sparse first-three-high p–q–p class, and the remaining global moment

Date: 2026-11-24 JST. Research-only continuation of `research/canonical-min-sampled-prefix` at 08a90af9376590a1acc327f6dd8949761de105ed.
This note distinguishes the **proved elementary deductions** below from the **unproved full sampled-prefix return moment**. Neither the note nor the Lean module proves twin-prime infinitude.

## 1. Unconditional recharge at the second and third selection of a prime

Take any canonical MIN trajectory with even horizon C. Fix odd prime p>=5. At a first selected p-event, let the sign be sigma_0=+1 or -1, so p | C+sigma_0. The event adds p-1. At the next selected p-event, let sigma_1 be the side and E the **total gain of all intervening selected labels other than p**. Thus

    p | C+sigma_0,
    p | C+(p-1)+E+sigma_1.

All actual gains are even. Subtraction shows

    p | (p-1)+E+sigma_1-sigma_0.

For E < p-1, the expression on the right is an even integer strictly between 0 and 2p. Such an integer cannot be divisible by odd p (the only multiple of p in that interval is odd p). Consequently

    E >= p-1.                                             (R1)

If E<=2p, the same expression is positive, even, divisible by p, and <4p. Its only possibility is 2p. Therefore

    E = p+1+sigma_0-sigma_1
      in {p-1,p+1,p+3}.                                   (R2)

The cases are attained in the finite canonical runs below, so the three values cannot be replaced by a singleton.

For three consecutive selected occurrences of p, the two intervening donor-gain windows are disjoint; (R1) applies to each:

    E_1+E_2 >= 2(p-1).                                   (R3)

This statement concerns the second/third **p-occurrence** and allows arbitrarily many interleaved other labels. It is independent of the sampled every-third high-word choice. The standalone Lean file `research/min_return_recharge.lean` proves (R1)-(R3) for the exact two-divisibility-state model, with all hypotheses explicit. The bridge to a genuine MIN event pair follows by telescoping the canonical update `C' = C+(label-1)` and choosing the sign bit for C±1.

## 2. A genuine source-uniform counting theorem for the early one-donor pattern

Let X be a positive multiple of 4 and B=ceil(sqrt(7X)). For each ODD canonical source M in [X,2X), begin the canonical MIN wheel at s=M+2 and C(s)=2M-2, and stop at its own K(M)=floor((7M-1)/4). Fixed LOW7 means selected labels {3,5,7}; HIGH means a selected label >=11. Define N_Q(X) as the **number of original source M** whose FIRST THREE selected HIGH11 labels are

    p, q, p

with Q<=p<=B, p prime. Intermediate LOW7 selections are unrestricted. The third p is the **second occurrence** of p; the subclass with first FIVE HIGH11 labels p,q,p,r,p (a third p-occurrence) is contained in it.

**New elementary upper bound.** There is an absolute constant C such that, for 840<=Q<=B,

    N_Q(X) <= C [B log(2B) + X/Q + X B/Q^2].              (R4)

In particular, on dyadic windows with Q=6[pi(B)-pi(y)] (provided 840<=Q<=B), the prime number theorem gives Q ~ 6B/log B, so

    N_Q(X) = O(B log B) = O(sqrt(X) log X) = o(X).         (R5)

The purely integer-summed proof of (R4) gives O(B(log B)^2) at Q~B/log B.
For (R5) we retain the fact that p is PRIME and use the standard prime-counting
upper bound pi(t)<<t/log t. Partial summation then yields
sum_{p>=Q} p^-2 <<1/(Q log Q) and
sum_{p>=Q} p^-3 <<1/(Q^2 log Q), as well as
sum_{Q<=p<=B}1/p <<log(B/Q)/log Q. Substituting these into (R8)-(R10),
with X~B^2 and Q~B/log B, gives the sharper O(B log B).

This counts ORIGINAL sources without replacing multiplicities by distinct reset states.

### Full elementary argument for (R4)

For each of the three LOW7-only blocks (before p, between p and q, between q and final p), the even-multiple barrier with L=210 gives even gain E_0,E_1,E_2 in [0,210), i.e. **105 possible values per block**. This is a deterministic theorem for any even starting C and does not use a finite LOW7 ghost enumeration.

By (R1), the other-label gain between the first and second p selections is q-1+E_1+E_2 >= p-1. Since E_1+E_2<=416, we get

    q >= p-416 >= p/2                   (p>=840).        (R6)

The two p-divisibilities and the intermediate gains imply

    q = 2 + sigma_0 - sigma_2 - (E_1+E_2) (mod p).        (R7)

There are three values for sigma_0-sigma_2 and 209 possible even values for E_1+E_2. For each fixed p, (R7) therefore restricts the INTEGER q to at most

    627 * (floor(B/p)+1)             possibilities.      (R8)

No primality estimate for q is used here. q cannot equal p: that would mean the first and second HIGH events were both p, separated only by E_1<210, contradicting (R1) for p>=840. Thus p and q are DISTINCT primes.

Fix p,q and the even gains E_0,E_1<210 and the signs sigma_0,sigma_1. The FIRST TWO high selections imply

    p | 2M-2+E_0+sigma_0,
    q | 2M-2+E_0+(p-1)+E_1+sigma_1.                     (R9)

Because p,q are distinct odd primes, 2 is invertible modulo each, and CRT gives a SINGLE residue class of M modulo pq. It contains at most X/(pq)+1 integers in the source interval. There are at most 105^2*4=44100 choices of E_0,E_1,sigma_0,sigma_1, so for fixed p,q,

    #{M} <=44100*(X/(pq)+1)
          <=44100*(2X/p^2+1)              by (R6).       (R10)

Combining (R8),(R10) and summing p over ALL INTEGERS p between Q and B, not just primes, gives

    N_Q(X) <= (44100*627)
              * sum_{n=Q}^B (B/n+1)(2X/n^2+1)
            << B log(2B) + X/Q + XB/Q^2.

Here sum n^-2 <<1/Q, sum n^-3<<1/Q^2, and sum n^-1<<log(2B). This proves (R4) with an absolute constant. No independence assumption or unproved dynamical mixing estimate is involved.

### What (R4) does not count

- It only handles `p,q,p` when the first p is the FIRST selected HIGH11 label. It does NOT control p that first appears after earlier HIGH events, nor first p followed by two or more distinct HIGH donors before its return.
- It bounds one source per occurrence of this early pattern. It does not bound `A_X`, the small-label second moment, nor `C_X`, the large-label sampled pair count, on ALL adaptive histories.
- The Q=6P specialization is asymptotic; for currently reachable windows the threshold Q>=840 and Q<=B does not yet hold, and this finite checker mostly sees first-three patterns at small p.

## 3. Exact reproducible finite audit

Run:

    python3 research/min_return_frequency_audit.py 256 1024 4096 16384 65536 262144

The script uses the earliest (time,prime) clock event, and for X<=1024 independently compares many full next-event decisions against literal integer-by-integer parity GCD. For p>=5, it tests the unconditional recharge (R1), the three exact short values (R2), and counts actual **second and third occurrences**, not only sampled labels. For HIGH11 it counts the first-three p,q,p patterns. It also re-computes the sampled-prefix `D`, small second moment, small excess and large coincidence pairs using the source's own K(M).

Local finite results (script printout has further fields):

| X | second p-hits (p>=5) | third p-hits | short gains E<=2p | first HIGH11 p,q,p | sum small sampled J^2 | sampled large pairs |
|---:|---:|---:|---:|---:|---:|---:|
|256|206|70|123|17|33|0|
|1024|384|146|217|28|109|0|
|4096|3410|1781|1928|126|2824|0|
|16384|17296|9573|9764|474|21949|0|
|65536|85027|47989|47449|1865|125917|0|
|262144|401451|239318|228442|7809|337482|0|

All short-gain residue differences E-p observed were exactly -1,+1,+3. The first-three-high p,q,p count above B/2 was 3 for X256, 1 for X1024, and 0 for the other listed windows. These are FINITE results and are not used as proofs of (R4) or global asymptotics.

For the same samples, every source terminal at X1024 and above in this table had both neighbours prime; at X256 it was 123 of 128 sources. This does NOT establish any global terminal theorem.

## 4. Next missing analytical estimate

The intended sampled-prefix sufficient criterion remains:

    D(X) < X*P/2 along infinitely many large dyadic windows.

Splitting the sampled excess into small labels p<=W and large collisions p>W leaves:

    A_X = sum_{M,y<p<=W} (J_{M,p}-a)_+,
    C_X = sum_{M,p>W} binom(n_{M,p},2).

The proposed stronger **unproved** small-label moment is

    sum_{M,y<p<=W} J_{M,p}^2 << X*pi(W)*log B.

(R4) proves a sparse initial, one-donor subclass of large-p collisions, but not C_X. The next research stage is either (i) two or more intermediate HIGH donors after the FIRST p; or (ii) one-donor p-return after any number of preceding HIGH labels while maintaining original source weights. The CRT +1 remainder proliferates if arbitrary adaptive histories are summed as if independent.

No result in this note implies twin-prime infinitude.
