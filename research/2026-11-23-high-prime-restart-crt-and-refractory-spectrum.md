# A166944 squarefree wheel: high-prime restarts, an exact finite low-wheel spectrum, and a second-wave CRT estimate

Date: 2026-11-23 JST. Assigned research Issue #4, parent Issue #1; branch `research/issue-4-terminal-survivor-positive-budget`. This extends the earlier 11-low-prime finite-state and high-prime interruption notes. **All algebraic implications are paper arguments; the finite finite-state certificates are exhaustive C++17 calculations, not Lean kernel proofs. The full repeated-restart asymptotic estimate, twin-prime infinitude, and the stronger A166944 conjecture remain OPEN.**

## Setup

As before, let even X>=256, B=ceil(sqrt(7X)), I_X={odd M:X<=M<2X}, s=M+2, K=floor((7M-1)/4), C(s)=2M-2. At step n>s the squarefree clipped increment is `d(n)=gcd(L_B,g(n,C(n-1)))` with even `g=gcd(n,C-1)` and odd `g=gcd(n-2,C+1)`. A *high event* has at least one prime factor >=13. Other events involve only S={3,5,7,11}, whose product is P=1155, period 2P=2310. `T(M)` counts high events for M.

For a frozen plateau `(t,C)`, `z=2t-C` is the nonnegative horizon deficit. If two distinct prime factors `u<v` of a next event increment fire together, then necessarily `z >= u(v-4)-1`: indeed the waiting time delta to that event is <=2u, while uv divides `z+2delta+1` at even clocks, or the positive `z+2delta-5` at odd clocks. This bound applies to ANY chosen pair of factors, even if other smaller factors are present.

## 1. Two new exhaustive restricted-wheel finite-state invariants

`research/refractory_state_audit.cpp` exhaustively enumerates ALL `(t mod 2310,C even mod 2310)` (2,668,050 states), computes the original restricted next-prime-clock successor, confirms zero directed cycles by topological elimination, and computes both maximum event count and cumulative growth to the terminal sink. For every state it additionally walks all event prefixes, collecting possible even cumulative low growth `e`.

* All-state maximum: **22 nonunit low-only events**, and **1156 cumulative low-only growth** (the earlier crude estimate was 22*(1155-1)=25,388). This gives 0<=e<=1156 for EVERY low-only prefix, starting from any event origin/state.
* The exact union of all prefix growths across all states has **138 distinct even values**; its largest value is 1156. There are **58 primes q>=13** dividing at least one nonzero integer in `{e-3,e-1,e+1}` for those 138 values; the largest is q=1153. These are only *potential* immediate refiring primes, not 58 proven realizable paths.
* A second independent enumeration of the **1155 odd canonical residue classes M mod 2310**, starting always with `t=M+2,C=2M-2`, yields **4940 plateau visits**, maximum 18 low-only events, maximum total low-only growth **98**, and, crucially, **z<=146 at EVERY canonical low-only plateau**. The orbit and the offset `C-(2M-2)` depend only on M mod 2310, so these 1155 classes cover all canonical starts at all sizes. Initial z=6.

The finite 11-low results are bounded exhaustive computational certificates: all 2,668,050 states are checked by a compiled finite program. They do not assert Lean-kernel verification. The known 11-low event maximum F=22 is reproduced independently of previous files.

## 2. Stronger FIRST high-event facts (paper consequences of the canonical finite z certificate)

Before the first high event, the FULL B-wheel follows a prefix of the canonical 11-low-only trajectory. Hence every preceding plateau has `z<=146`.

1. **No two high primes at the first high event.** Two distinct primes >=13 would include some `u<v` with u>=13,v>=17; the pair obstruction yields `z>=13*(17-4)-1=168`, contradicting z<=146. The first high event has a UNIQUE high prime p>=13.
2. **For p>=59 the complete increment is exactly d=p.** If any additional low prime u in {3,5,7,11} co-fired, the pair obstruction gives `z>=u(p-4)-1 >= 3*(59-4)-1=164`, again impossible.
3. **Uniform first-high increment bound** `d <= max(B,191)`. When d=p it is <=B. If d also contains a low factor u<=11, the next-clock time delta<=2u and the original parity-GCD divisibility gives `d<=z+4u+1<=146+44+1=191` (the odd-clock bound is smaller).

The first high event need not be the *first nonunit event*: canonical small-only events can precede it. The results hold for ANY finite cutoff K at which that first high event occurs.

## 3. An all-restart REFRACTORY lemma (paper plus complete low-wheel enumeration)

Consider any two **consecutive high events**, and let q>=13 divide BOTH high increments. The intervening events, if any, use only {3,5,7,11}, with total added growth e>=0. The previous q event has d=0 mod q and q divides one of its two prior neighbors. Immediately afterwards the state is `C'=0 or -2 (mod q)`; after low-only growth e, the state is `e or e-2 (mod q)`. For q to divide a neighbor again before the next high event, necessarily

    BOXED: q | (e-3)(e-1)(e+1).                      (R1)

The exceptional integer e=3 cannot occur, because all increments d-1 and their sum e are even. Since `0<=e<=1156`, the bound

    BOXED: consecutive high events sharing a factor q>=13 force q<=1157.   (R2)

follows. The exhaustive **138-value low-prefix set** strengthens this: q must be in one of the **58 fixed prime candidates**, none greater than 1153. It does not claim every such q is realizable. Thus a prime q>1157 cannot fire in two successive high events, regardless of X or the other high-prime factors. It CAN reappear after an *intervening high event with another prime*, which is why R2 does not bound the total high-event count.

## 4. Exact affine restart cells and the FIRST TWO high-wave CRT estimates

Denote by `j` the index of a low-only plateau before the first high event; there are at most `J0=19` possibilities. Fix an odd canonical residue `r=M mod 2310`, `j`, the unique first high prime p>=13, and the parity/side sigma of this p clock. At that low-only plateau,

    C_j(M)=2M-2+h_j(r),    t_j(M)=M+2+tau_j(r)

with h_j,tau_j independent of M inside residue class r. The constraint `p | C_j(M) +/- 1` fixes ONE residue M mod p. The first shared p clock is thereby fixed relative to M on the CRT cell modulo `2310*p`; the simultaneous small-factor component of the first increment d is also fixed there. Following the event, every later **low-only** plateau before the second high event has

    C'_k(M)=2M-2+h'_(r,j,p,sigma,k),   k=0,...,22,

with a fixed shift on that same CRT cell. These are **candidate cells**; possible earlier competing high clocks may remove starts, which only strengthens counting upper bounds.

Let `N=X/2`, `J_B=# {13<=p<=B, p prime}`, and let `H_{q,1}`, `H_{q,2}` count starts whose first/second high event, respectively, contains prime q. Because the first high event has exactly one high factor,

    H_(p,1)(X) <= 2*J0*(N/p+P).

Consequently, with V_j= sum_(q>=13) q H_(q,j),

    BOXED: V_1(X) <= 2*J0*(N J_B+P sum_(p in J_B) p)
                     = O(X B/log B)=o(XB).                 (CRT-H1)

For SECOND-high primes q != p, the extra condition `q|C'_k(M) +/- 1` fixes one further residue mod q, since gcd(pq,2310)=1. The count within one fixed (r,j,p,sigma,k,second-side) cell is at most `N/(P*p*q)+1`. Sum over P residues and at most `J0*2*23*2` choices. Put `K0=4*19*23=1748`. This yields

    H_(q,2)(X) <= K0 * sum_(13<=p<=B, p!=q) (N/(p*q)+P)
                    + 1_(q<=1157)*K0*(N/q+P).            (CRT-H2)

The last term handles q=p: CRT gives no new q residue, but R2 excludes q>1157. The bound counts q among factors even if the second high increment has several high factors. Summing weights q gives

    V_2(X) <= K0*[ N*J_B*sum_(13<=p<=B) 1/p
                 + P*J_B*sum_(13<=q<=B) q
                 + N*#{13<=q<=min(B,1157)}
                 + P*sum_(13<=q<=min(B,1157))q ].

Using `J_B=O(B/log B)`, `sum_(p<=B) 1/p=O(log log B)`, `sum_(p<=B)p=O(B^2/log B)`, and `B^2=Theta(X)`,

    BOXED: V_2(X)=O(X B loglog B/log B + P X B/log^2 B + X)
                  = o(XB).                                  (CRT-H3)

These are **unconditional paper derivations using the finite 11-wheel certificate**, with no equidistribution assumption for adaptive states. The modulo-`p` restart cell is justified because the FIRST high event has exactly one large factor; without that fact, a product of several distinct high primes would have to be included in the cell modulus.

**What this does NOT achieve:** fixed first/second high events already contribute at most O(XB) even without CRT (one high event per source), and O(XB)=o(X²). These estimates are informative arithmetic dispersion checkpoints, not a proof of the UNBOUNDED total `T_X=o(XB)` or `W_X=o(X²)`. At the third and subsequent high waves, residue moduli multiply with past high primes; for typical p1,p2~B, `2310*p1*p2` can exceed X, and the `+1` boundary error per CRT history dominates. No uniform history-count/dispersion estimate has been proved.

## 5. Independent finite original-GCD epoch audit

`research/restart_epoch_audit.cpp` compiles with `g++ -std=c++17 -O3 -Wall -Wextra -Werror`. It scans every odd canonical M in each specified X interval using the original parity-specific prime-clock recurrence and checks historic full event/growth regressions, independent literal stepwise-GCD M7..119, first-high unique p, first-high p>=59 purity, first-high canonical z bound, small-only prefix growth<=1156, consecutive high q repeat (R1/R2), and affine first-restart signatures `(M mod 2310, j, p, side)` whenever multiple starts occupy the same signature.

| X | B | high events total T_X | mean T per M | largest T(M) | first-high weight V_1 | second-high weight V_2 | repeats of q in consecutive high events | largest observed repeated q |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 4,096 | 170 | 7,675 | 3.7476 | 18 | 57,085 | 49,596 | 163 | 59 |
| 16,384 | 339 | 45,343 | 5.5350 | 45 | 314,495 | 292,875 | 710 | 47 |
| 65,536 | 678 | 224,221 | 6.8427 | 47 | 1,828,325 | 1,785,072 | 4,089 | 47 |
| 262,144 | 1,355 | 1,198,498 | 9.1438 | 79 | 10,106,029 | 10,331,097 | 21,415 | 89 |
| 1,048,576 | 2,710 | 5,516,751 | 10.5224 | 112 | 59,272,237 | 59,836,004 | 102,320 | 61 |

Every first high event has exactly one high factor in these finite scans (also a paper conclusion). Some have simultaneous low factors, with first-high composite counts 16,90,307,1255,5090, respectively; all first-high event increments d<=B for these five scales. The exact shift signatures were independently checked across all occupied repeated history cells (not only one example); X=1,048,576 yielded 348,205 such repeated-cell comparisons and zero mismatches. The observed maximum low-only growth between consecutive high events at the five scales was 80,116,384,384,1154; the universal all-state cap is 1156.

The high-event depth distribution remains substantial: at X1048576, 85,746 of 524,288 starts had at least 20 high events, 4,813 had >=50, 693 had >=75 and 141 had >=100. Its maximum was 112. Therefore limiting the number of waves to two (or any fixed number) does not resolve the dynamic tail.

Extra non-dyadic and small-window full regressions also passed at X=256,512,1024,500000,1000000,1999998. At X=1999998 the original recurrence produced 39,296,118 nonunit events and 11,695,485 high events, with maximum 123 high events on one start; all first-high, CRT-affine and refractory assertions passed. These are further finite tests, not a uniform estimate.

## 6. The remaining analytic lemma and reproducibility

The currently sufficient, UNPROVED goal is `T_X=o(XB)`, equivalent to a sublinear-in-B mean high-event depth. A stronger natural goal `T_X=O(X (log X)^A)` would also suffice. The exact CRT description shows a specific missing ingredient: control the **number, occupancy or total boundary error of adaptive restart-history residue cells**, especially from the third high wave onward. One option is a multi-wave short-history sieve retaining the last few high-prime factors and proving that most occupied histories have controlled modulus; another is a signed or large-sieve discrepancy bound across the many history cells. Neither follows from the first-two-wave counts.

Finite-state evidence comes from `refractory_state_audit.cpp` with all-state graph plus canonical residue enumeration, and `restart_epoch_audit.cpp` with full finite scans. They are reproducible with

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/refractory_state_audit.cpp -o /tmp/refractory_state_audit
/tmp/refractory_state_audit

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/restart_epoch_audit.cpp -o /tmp/restart_epoch_audit
/tmp/restart_epoch_audit 4096 16384 65536 262144 1048576
```

No Lean kernel compilation occurred, Issue #4 remains open, and main was not modified. Twin-prime infinitude and the original `OeisA166944.conjecture` are still open.
