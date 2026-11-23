# A166944: low-clock priority, two-root sink renewal, and first-high prime moment

Date: 2026-11-23 JST. Scope `tara-sooo/A166944-Lean`, research Issue #4 (parent #1), branch `research/issue-4-terminal-survivor-positive-budget`. This is a direct continuation of `research/2026-11-23-three-seed-reset-binary-carry-return-barrier.md`. **All new implications below are paper arguments**, using the prior finite 3/5/7/11 reset-state certificate; the complete state/root count and finite statistics were audited with C++17 against the ORIGINAL parity-specific squarefree-clipped GCD. No new Lean-kernel proof, no infinite twin-prime result, and no proof of strict-record A166944.

## 1. Exact setup and low-prime clock priority

For even dyadic scale X, let B=ceil sqrt(7X), original canonical odd start M in [X,2X), s=M+2, C(s)=2M-2, cutoff K(M)=floor((7M-1)/4). For n>s, d(n)=gcd(L_B,g(n,C(n-1))) where L_B contains each odd prime 3<=p<=B once, even n uses g=gcd(n,C-1), odd n uses g=gcd(n-2,C+1), and C'=C+d-1 at the event. At a plateau origin (t,C) let z=2t-C>=0; z remains even.

Let the **restricted low wheel** use only S={3,5,7,11}, product P=1155, period L=2310. At any plateau where an active low prime a<=11 divides (C-1)(C+1), its next parity-correct clock occurs within **2a<=22** steps. Thus the actual next FULL-wheel event must occur within 22 steps; the high prime factor p can win only if its clock distance delta<=2a.

At a canonical initial seed, or at any actual high-RESET (t,z in {0,6}) with no further high event yet, the low-only continuation has **z<=146 at every plateau** by the prior exhaustive 4620-case finite certificate. The initial canonical z=6 obeys the same bound. For p>=59 first high after such a seed has complete increment d=p (prior pair-factor obstruction), and for p>=149 its strong carry has only k=0 or 1:

    even: z+2delta+1=(2k+1)p;
    odd:  z+2delta-5=(2k+1)p;

    k=0 => RESET z'=0 or6; k=1 => CHARGED z'=2p or2p+6.

**NEW PAPER priority lemma:** If an active low prime a<=11 remains at the plateau where the first subsequent high event containing p>=59 occurs, then

    RESET:  p <= z+4a+1 <=191;
    CHARGED: 3p <= z+4a+1 <=191, hence p<=63.

The odd case bounds are stricter. In particular, **(i) every first high event after any high reset with p>=193 occurs at the terminal S-low-only plateau** (all 3,5,7,11 clocks have stopped); **(ii) every CHARGED first high event after reset with p>=67 occurs at that terminal low-only plateau**. This remains valid when the initial state was an EVEN reset; the low-wheel trace starts at its exact even reset (t,z=0), and includes the previously verified 3-step normalization. The finite original-GCD auditor asserts both statements for every canonical trajectory at the tested scales.

The result is one-way: a p-divisibility at the terminal low plateau is NECESSARY, not sufficient, for p to be the first high event, because smaller high primes may have acted earlier.

## 2. EXACT two-root arithmetic representation

For reset seed (t,z), z∈{0,6}, define e_inf(r,z) to be cumulative low-only growth until no S-prime remains active, with r=t mod2310. This is a finite deterministic function of only (r,z), verified by scanning all 4620 residue states; 0<=e_inf<=100. Define its virtual terminal even C-value

    C_inf(t,z)=2t-z+e_inf(t mod 2310,z).

For every prime q>=193, the first high event after reset can contain q only if

    q | (C_inf(t,z)-1)(C_inf(t,z)+1).                (S1)

Since q>=193 is odd and e_inf is constant on each r-cell, S1 says t lies in **EXACTLY TWO distinct roots modulo q**:

    U_sink(q,r,z)={ (z-e_inf(r,z)+1)/2,
                    (z-e_inf(r,z)-1)/2 } mod q.       (S2)

The denominator 2 is a modular inverse, and the two roots differ by 1 mod q. **Unlike the older all-prefix reset-candidate union with 2..31 roots per q>=103, the q>=193 FIRST-ACTUAL-HIGH necessary condition uses only TWO roots**. This is a strong arithmetic simplification, not yet a bound on how many reset epochs occur.

For the actual multiset R_X of high-reset states (t,z), let R_X=|R_X| and

    A_q^sink(X)=sum_(reset visits (t,z)) 1{ q | C_inf(t,z)^2-1 }.

Write J_B=#{primes q:193<=q<=B}. For a fixed r,z and an ARTIFICIALLY uniform residue t mod q, there are exactly 2 roots, hence phase-model expectation E(A_q)=2R_X/q. Thus the following is an EXACT definition/identity for the measured signed discrepancy:

    BOXED: sum_(193<=q<=B prime) q A_q^sink
         = 2 J_B R_X + D_X^sink,
    D_X^sink=sum_q(q A_q^sink-2R_X).                 (S3)

The actual reset origins are highly adaptive, so the model expectation is not an asserted theorem about the canonical distribution. An absolute q-discrepancy may be much larger than the signed D_X^sink.

## 3. A fully UNCONDITIONAL one-wave CRT bound for canonical starts

For the ORIGINAL canonical initial seeds, the restricted low sink is

    C_inf(M+2,6)=2M-2+e_inf((M+2) mod2310,6).

Fix one of the 1155 ODD residues r=M mod2310. Then e_inf is fixed and S1 imposes exactly two residues of M modulo q. As gcd(q,2310)=1, the count over M∈[X,2X) in one r-class is 2*X/(2310q)+O(2). Summing 1155 residue classes gives the effective explicit count bound

    BOXED: |A_q^init(X)-X/q| <=2310,    q>=193,      (S4)

where A_q^init counts all ORIGINAL starts whose **virtual low sink** has q dividing C_inf±1, and |I_X|=X/2.

If the first actual high event at M contains q>=193 then it has d=q and must satisfy this sink condition, so H_(q,first)(X)<=A_q^init(X). Therefore

    BOXED: sum_(193<=q<=B prime) q H_(q,first)(X)
          <= X J_B +2310 sum_(193<=q<=B prime)q
          =O(XB/logB).                                (S5)

This strengthens the previous first-high CRT with a **factor-1** coefficient in the X/q main term and avoids branching on 19 intermediate low plateaus, though it still controls only ONE high wave. The estimate uses standard prime-counting/prime-sum bounds for the final O statement.

## 4. A terminal-sink twin-prime equivalence, and its exact obstacle

When all low primes are inactive at C_inf and ALSO no high prime 13<=q<=B divides C_inf±1, both odd neighbors are coprime to every prime <=B. In the canonical window, any high-reset origin t<=K(M)<3.5X obeys C_inf+1 <=2K+101<7X+101. Because B²>=7X and (B+1)²>=B²+2B+1, for B>=51 we have C_inf+1<(B+1)². Any composite odd C_inf±1 without a prime factor <=B would have at least two factors >B, hence be >=(B+1)², impossible. Therefore

    BOXED: when B>=51 and an actual reset origin t<=K(M)
      has a virtual low-only sink with no prime <=B active,
      C_inf(t,z)-1 and C_inf(t,z)+1 are BOTH PRIME.      (S6)

The sink may be a virtual continuation after the original cutoff or may have been interrupted by another high event; S6 nonetheless produces two ACTUAL integer twin primes. The C++ verifies primality by its independent smallest-prime-factor table at every flagged sink. **S6 is not a proof that such sinks exist at unbounded X**. Lower bounding the occupancy of fully absorbing sinks is itself a twin-prime-level parity-barrier problem. This observation identifies a genuine bottleneck in an attempted proof by a uniformly positive 'absorption probability'.

## 5. Exact full-wheel finite audit

The sibling source `research/renewal_operator_audit.cpp` is standalone C++17, compiled with `g++ -std=c++17 -O3 -Wall -Wextra -Werror`. It independently checks the original parity-specific literal-step clipped-GCD values for ALL odd M from 7 to119 (cap41), all low-only reset sink state maxima, every post-high carry, the charged-to-prime-return barrier from predecessor work, and two NEW sink-priority thresholds. Complete canonical odd-M windows were checked for X=4096,16384,65536,262144,1048576; historical high-event counts 7675,45343,224221,1198498,5516751 were reproduced.

| X | B | high RESET visits R_X | first high-after-reset p>=193 events (all at sinks) | sink candidate weighted sum (q>=193) | 2 J_B R_X phase benchmark | relative signed discrepancy | distinct verified twin centers from reset sinks |
|--:|--:|--:|--:|--:|--:|--:|--:|
| 4096 | 170 | 2865 | 0 | 0 | 0 | n/a | 72 |
| 16384 | 339 | 14422 | 662 | 646475 | 721100 | -10.35% | 238 |
| 65536 | 678 | 73941 | 8299 | 11539147 | 11830560 | -2.46% | 744 |
| 262144 | 1355 | 360413 | 57495 | 127453539 | 125423724 | +1.62% | 2450 |
| 1048576 | 2710 | 1635279 | 289879 | 1150967704 | 1147965858 | +0.26% | 8095 |

At X1048576 the q-wise ABSOLUTE error sum / phase is 16.76%, versus 0.26% signed; this is finite cancellation, not an asymptotic signed discrepancy bound. At initial canonical starts the weighted sink candidate sum, phase=XJ_B, is respectively 405846 vs409600, 5200816 vs5242880, 45529493 vs45613056, 368449028 vs368050176 for X16384,65536,262144,1048576. This agrees with the unconditional CRT-bound (S4).

**HIGH transition obstruction actually measured:** At X262144, all 838085 charged high events split by their *next* high event as charged→charged 662694 (79.1%), charged→reset 96188 (11.5%), and no subsequent high event 79203 (9.5%). At X1048576 the analogous counts are 3104978/446993/329501 of 3881472. Thus the dominant depth mechanism is charged→charged continuation, not reset visits. 96% of high events were pure prime-only at the larger finite scales; composite returns cannot just be declared negligible asymptotically.

The high-depth tail at X1048576: 524288 original starts, 482587 had at least one high event, 212184 had >=10, 85746 >=20, 4813 >=50, 141 >=100; maximum112. Across this finite window the surviving mass ratio for a 10-high-event block is roughly 0.40 for many initial depths but this is NOT a verified uniform-in-B or uniform-depth contraction theorem.

## 6. What would actually close the route

The induced HIGH-EVENT operator is the deterministic map from an event-state (t,C) to its next high event, skipping intervening low-only events and absorbing when no high event precedes the ORIGINAL M-specific deadline K(M). Its pushforward of a multiset of actual canonical source trajectories has layer mass

    N_k(X)=#{M odd in [X,2X): T_B(M)>=k}.

Exactly,

    sum_M T_B(M)=sum_(k>=1)N_k(X).                    (S7)

A block contraction for some 0<theta<1 and rho<1,

    N_(k+ceil(B^theta))(X) <=rho N_k(X)  for all k>=1,

would imply sum_M T_B(M)=O(X B^theta)=o(XB), hence the existing squarefree-wheel terminal certificate implies infinitely many twins. This is **OPEN**; uniform source weights or independent CRT phases do not follow from the deterministic map. Even the weaker single tail #{M:T_B(M)>B^theta}=o(X) for some theta<1 is sufficient via old E<=22+23T and G<=3X on exceptional starts.

The new sink priority gives a sharper place to analyze the induced operator: large first-high p>=193 transitions depend only on **the two B-rough affine neighbor forms at the low sink**, while small high p<=191 may interrupt the low chain, and most very long high paths are CHARGED chains. The arithmetic difficulty is to prove decay of occupancy of these nonterminal high transitions across dynamically selected reset/charged states. Showing abundant exact full-sink absorption by an elementary lower-bound sieve alone would run into the twin-prime parity problem. No asymptotic result or Lean verification is claimed.

### Reproduce

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/renewal_operator_audit.cpp -o /tmp/renewal_operator_audit
/tmp/renewal_operator_audit 4096 16384 65536 262144 1048576
```
