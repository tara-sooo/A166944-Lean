# A166944 Issue #4 — COMPLETE q=17 first-return nilpotence, LOW17 terminal bound, and symbolic q=19 proposal

Date: 2026-11-23 JST. Branch `research/issue-4-terminal-survivor-positive-budget` of `tara-sooo/A166944-Lean` (Issue #4, parent #1). Continues `research/2026-11-23-q13-nilpotent-renewal-and-low-sink-mixing.md`. These are algebraic deductions conditional on complete standalone C++17 finite-state certificates; the q17 certificate has also been checked by an independently implemented Python one-step parity GCD oracle. No new Lean kernel check; twin prime infinitude and the A166944 strict-record conjecture remain OPEN.

## 1. Key arithmetic reduction before enumerating the q-return graph

Let S be a previously proved terminating finite low-prime wheel with odd squarefree product P, and q an odd prime not dividing P. Consider the original parity-specific clipped GCD with primes S union {q}; at a plateau origin t,C with C even, odd squarefree increment d and event time n:

- n even: d|gcd(n,C−1), n even ⇒ n≡0(mod q) and C≡1(mod q) if q|d. Post-event C'=C+d−1≡0(mod q), and q-bearing n≡0(mod 2q).
- n odd: d|gcd(n−2,C+1) ⇒ n≡q+2(mod 2q) and C≡−1(mod q). Post-event C'≡−2(mod q).

Consequently, at ANY q-bearing **post-event** node (t,C), the q residue classes of both t and C are determined entirely by t's parity. Between this q hit and the next q hit, only old S-primes act. Their total clipped growth E=sum(d_S−1) is even, and q may be REACTIVATED ONLY when:

    EVEN q post-event: E≡+1 or −1 (mod q).
    ODD  q post-event: E≡+1 or +3 (mod q).           (ACT)

The q-clock time phase modulo 2q is likewise fixed after q hit: t≡0 (mod 2q) if even, t≡q+2 (mod 2q) if odd. Thus the exact NEXT-q event can be computed solely from the finite old S-only plateau trace (t_j,C_j,E_j) plus (ACT), comparing the next q clock to the next old-prime clock. Ties multiply q by simultaneous lower factors as in the original squarefree clipped GCD. This removes time-by-time scanning; all q tests are at finitely many S-only plateaus. A separate independently structured `q17_return_stats.cpp` implements this and compares it with the direct full-wheel q-jump algorithm on random samples.

Since E is even, the MINIMUM positive reactivation growth is at least q−1 (even q post) or q+1 (odd q post). Hence the separate **UNCONDITIONAL single-prime extension lemma**: if the old S-wheel has total growth <=G from EVERY starting state, then for ANY q>G+1 the wheel S∪{q} has at most ONE q-bearing event from any start, followed by a terminating S-only suffix. The lemma does not apply simultaneously to many q's because q may be reactivated by OTHER newly admitted high primes.

## 2. Exact full q=17 post-event graph: 450,900,450 states, NO CYCLES

Earlier 13-only full finite certificate gives old S={3,5,7,11,13} product P=15015, period L_old=30030 and universal S-only terminal bounds <=63 nonunit events, <=381 elapsed steps, <=17576 total clipped growth.

For new q=17, q-bearing post-event times t are restricted to t even ≡0(mod 17) or t odd ≡2(mod 17), while even post-C is restricted to 0 or −2(mod17). CRT yields exactly

    N=2*P*P = 450,900,450                            (Q17-COUNT)

post-q states modulo L_new=2*P*17=510510. For each state, the successor is the next q=17 post-event state if one exists, otherwise the terminal symbol ⊥. This defines a finite partial functional graph R_17 on N nodes.

`research/q17_full_dfs.cpp` exhaustively checked **EVERY ONE of N states**. It needs O(N) bytes rather than storing all 450m edges: a byte of visit status and a byte of depth per node, computing each state's successor only when needed. The audit was run in three checkpointed portions (0..200000000, 200000000..350000000, 350000000..450900450); checkpoint is disposable LOCAL binary scratch, NOT a reusable artifact or part of the proof statement. Both q13 regression and complete q17 run pass. Full graph summary:

| q17 post-return depth (further q17-bearing events) | number of states |
|---:|---:|
| 0 | 388,987,644 |
| 1 | 56,421,171 |
| 2 | 5,274,358 |
| 3 | 205,002 |
| 4 | 11,748 |
| 5 | 506 |
| 6 | 19 |
| 7 | 2 |

Sum EXACTLY N. There are 61,912,806 successor edges, 388,987,644 terminal states, **zero directed cycles**, and max following 17-hit depth **7**, achieved by a node of index 432334160. Thus R_17^8=⊥ on all nodes. This supplies a *finite-computation-defined* ranking function h(v)∈{0,...,7} with h(v)=0 when R(v)=⊥ and h(v)=1+h(R(v)) otherwise. It is a mathematical finite certificate pending independent Lean checking, **not** a simple algebraic ranking formula valid for every new prime.

A COMPLETELY DIFFERENT O(1)-auxiliary-memory full-space enumeration of the **entire q17 return path for EVERY node** in `research/q17_return_stats.cpp` also checked max following depth7, broken into three disjoint index ranges. This second method reconstructs each q17 path directly rather than relying on a cached DFS status/depth table and independently confirms global path maxima.

### Exact post-q17 max totals (full exhaustiveness)

From any q17 post-event state, through all subsequent S∪{17}-only events to a low sink, the independently enumerated maxima are

    at most 7 further events with q17 factor,
    at most 62 further nonunit events,
    at most 354 elapsed time steps,
    at most 23,224 total clipped growth.             (POST17)

These maxima occur in DIFFERENT initial states. Indexed examples: post-q17 #432334160 has seven future 17 hits; #233618750 has62 events; #64504807 elapsed354; #81973026 growth23224.

`research/q17_literal_oracle.py` independently computes the ORIGINAL parity-specific stepwise gcd(n,C−1) and gcd(n−2,C+1) at these four extreme state representatives and at 3000 other q17 post states plus1500 arbitrary states. It agrees with its own independent event-jump implementation and the full graph extrema, with no reliance on C++ event-clock code. q13 regression also matches its already-committed complete finite graph (2,668,050 nodes, q13 max return depth5, max following events40/time222/growth1406).

## 3. NEW universal restricted LOW17 theorem, and a sufficient HIGH19 condition

For an ARBITRARY even state (t,C) running the original clipped GCD restricted to S17={3,5,7,11,13,17}, there is an initial S13-only run (<=63 events/381 steps/17576 growth). If q17 occurs, its first q clock waits <=34 steps after its preceding S13 plateau, and its squarefree clipped increment is <=P*17=255255, so first17 event adds at most255254 growth. Thereafter POST17 applies. Consequently

    BOXED: each arbitrary S17-only orbit terminates in
      <=8 q17-bearing events,
      <=63+1+62 = 126 total nonunit events,
      <=381+34+354 = 769 elapsed steps,
      <=17576+255254+23224 = 296054 total growth.    (LOW17)

This generalizes the previous finite LOW13 <=63 events/381 steps/17576 growth. The growth cap is conservative; the event/time bounds are likewise proved from separately achieved maxima rather than being asserted sharp for all initial states.

In the ORIGINAL full B-wheel, every maximal segment with NO prime factor >=19 is a prefix of an S17-only trajectory; let T_19(M) be the number of original full-wheel events whose increment has at least one prime factor>=19. Then

    E_B(M)<=126+127*T_19(M).

If the canonical orbit M never reaches a full-wheel sink (actual C±1 have no p<=B factor) by K(M), then its high19-to-high19 or initial/final blocks are at most (769+2B) steps, by LOW17 plus a high-q clock of delay <=2q<=2B. Hence

    BOXED: K(M)−(M+2) <= (T_19(M)+1)*(769+2B)           (HI19)

for every such non-sink M. The exact dyadic aggregate horizon 9X²/16−5X/4 from earlier work implies the STILL OPEN but now weaker-in-prime-scope sufficient criterion

    BOXED: liminf_(X=2^k→∞) [Σ_(odd M∈[X,2X)) T_19(M)]/(X*B) <9/224

for infinitely many twin primes. The threshold9/224 is unchanged because any fixed low-only time bound contributes only lower-order O(B) versus X~B². **The needed asymptotic first-moment bound has not been proved.**

A complete ORIGINAL full-wheel clock+literal-small-M regression checker `research/low17_fullwheel_audit.cpp` yields:

| X | B | high factor>=13 | high factor>=17 | high factor>=19 | T19/(XB) |
|--:|--:|--:|--:|--:|--:|
| 4096 | 170 | 7675 | 6131 | 5391 | 0.007742 |
| 16384 | 339 | 45343 | 37272 | 30946 | 0.005572 |
| 65536 | 678 | 224221 | 187142 | 160568 | 0.003614 |
| 262144 | 1355 | 1198498 | 1001099 | 867049 | 0.002441 |
| 1048576 | 2710 | 5516751 | 4612625 | 4026703 | 0.001417 |

At X1048576, the new low17 wheel absorbs 585922 more events compared with treating17 as high; it removes 1,490,048 events from the original >=13 class. These are finite observations, not the asymptotic open criterion.

## 4. Q19 next: symbolic forbidden-path certificate instead of 130 billion enumerations

If one appends q19 to S17, the possible q19 post-event states number 2*(255255)^2=130,310,230,050, a factor289 larger than q17. Full direct enumeration is not a scalable proof method as q grows. Two complementary paths:

1. **Symbolic return activation**. For q19 post state, E of cumulative S17-only growth must reach E≡±1 mod19 (even post state) or E≡1,3 mod19 (odd). The q19 event clock has a fixed phase modulo38. Represent the lower-wheel trace as a finite-state transducer whose transitions track time delta mod38, growth E mod19, and old-prime CRT classes. A BDD/SAT/SMT-style search for length>=k q19 return paths can symbolically detect or exclude long paths, avoiding materializing all 130b states. Merely exhibiting an algebraic candidate rank without proving every edge decreases it would not suffice.
2. **Image pruning and a short-rank certificate**. For q17 the max depth7, but only 217,277 of450,900,450 states have depth>=3, only527 have depth>=5 and only2 depth>=7. This suggests solving the deeply returning exceptional sets S_k={v:R_q^k(v)≠⊥} by CRT constraint propagation (rather than storing all states). If a high-k set becomes empty, the rank function h(v)=max remaining q-return count is certified. The q17 depth frequencies are PROVED by finite scan; the q19 frequency extrapolation is only a possible algorithmic advantage.

An exploratory `research/q19_return_sample.cpp` (using 64-bit q19 post-state indices) sampled 10,000,000 of 130,310,230,050 possible states; 1,347,113 had immediate q19 returns, and the maximum observed following q19 depth was6, with no sampled cycles. **This is a sample only, not a q19 nilpotence or even q19 no-cycle certificate.**

An additional unconditional tail lemma from (ACT): after a high q post-event, if only the previous S17 wheel acts before any next q event, reactivation needs at least E>=q−1 low-only growth. LOW17 gives E<=296054; thus for any single new q>296055, q cannot recur at all. This covers single-prime extensions with sufficiently large q, but not several new primes interacting and reactivating each other. It is a useful proof boundary for a future induction.

## Verification and status

- Full q13 re-execution: 2,668,050 states, terminal2,216,514, max depth5. PASS.
- Full q17 DFS: 450,900,450 states, 61,912,806 edges, all path states visited, NO cycles, max q17 depth7. PASS across three verified checkpointed phases; peak RAM ~864 MiB (not a 4GiB edge table). Checkpoint file is local/transient and not part of committed source.
- Full independent q17 path enumeration: all 450,900,450 states, max post17 events62, elapsed354, growth23224, q17 depth7; three disjoint ranges. PASS.
- Independent one-step Python original parity GCD: four q17 extreme states,3000 other q17 post-event states,1500 arbitrary states. PASS.
- Original canonical full B-wheel for X4096/16384/65536/262144/1048576, including historical high13 and high17 regressions plus small literal M7..119: PASS.
- q19 ten-million-state exploratory sample: no sampled cycles, max following q19 depth6. Does NOT certify q19.
- These complete finite scans establish a **computational certificate**, not a Lean kernel proof. The actual twin prime infinitude/strict-record A166944 statement and the requisite adaptive high>=19 average event bound remain OPEN. The default repository branch remains unchanged.

### Reproduction

```sh
# Exhaustive q17 DFS in three resumable chunks (scratch checkpoint requires ~902 MB disk)
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q17_full_dfs.cpp -o /tmp/q17_full_dfs
/tmp/q17_full_dfs 13
/tmp/q17_full_dfs 17 200000000 /tmp/q17_checkpoint.bin
/tmp/q17_full_dfs 17 350000000 /tmp/q17_checkpoint.bin
/tmp/q17_full_dfs 17 450900450 /tmp/q17_checkpoint.bin

# Independent complete O(1)-auxiliary-memory maximum-stat scan
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q17_return_stats.cpp -o /tmp/q17_return_stats
/tmp/q17_return_stats 13 range 0 2668050
/tmp/q17_return_stats 17 range 0 150000000
/tmp/q17_return_stats 17 range 150000000 300000000
/tmp/q17_return_stats 17 range 300000000 450900450

python3 research/q17_literal_oracle.py

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low17_fullwheel_audit.cpp -o /tmp/low17_fullwheel_audit
/tmp/low17_fullwheel_audit 4096 16384 65536 262144 1048576

# Exploratory only
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q19_return_sample.cpp -o /tmp/q19_return_sample
/tmp/q19_return_sample 10000000
```
