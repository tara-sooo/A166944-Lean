# Hypothetical infinite MIN worlds IV: finite low-label relays, mixed runs and canonical entry strata

2026-11-26 JST. Continuation of [ae36ba7](https://github.com/tara-sooo/A166944-Lean/commit/ae36ba7e6002e69244233f89fbd810c04a68bbea). Independent research branch. Sources: [III exact clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), direct [47a1442 uniform pinned gaps](https://github.com/tara-sooo/A166944-Lean/blob/47a14426499afbaacaadb11114dac7caccdb4fdf/research/2026-11-26-min-direct-variable-order-sieve-and-uniform-pinned-gaps.md). Paper deductions and finite computation, no Lean kernel verification or external novelty claim. The main target remains open. This note asks whether the long/high deep-bypass model can be repaired by inserting small-label events.

## 1. Low-only dynamics is a terminating finite-state transducer

Fix an integer R>=3; let S be the odd primes <=R and K=2 prod_(q in S) q. At a standard even horizon H with H+1>=R^2, all factors q in S of H+-1 are eligible. Define the *restricted low-only* rule: ignore all labels >R, take the earliest future clock among S, least label at a tie, add p-1 to H, and stop when no S clock exists. This is NOT a new actual MIN definition; it is an auxiliary transducer.

For every restricted step H<=J<H+p-1, where J is an even multiple of K, the even distance J-H lies in [0,p-3]. But H=+-1 mod p and J=0 mod p, so the distance must be +-1 mod p. Neither residue is possible in that even interval. Thus no low-only step crosses the next multiple J>=H of K in the half-open sense. A state at J has no low label. Strict positive even gains imply termination at or before J, in at most (K-2)/2 events, with total gain E<K. Its elapsed time B<=3E follows from each w<=2p<=3(p-1), and its ordinary deficit change is 2B-E in [-E,5E]. These bounds also hold for any prefix of the restricted evolution.

The initial even residue h=H mod K and time residue r=t mod K determine every label and wait, since each period 2q divides K. Store the exact terminal displacement E(h,r), time B(h,r), and event count N(h,r). Define M_R=max E(h,r)<K, D_R=max_(all prefixes)(2B-E)<=5M_R. The restricted terminal horizon is R-rough in the two-neighbor sense: H+-1 avoid every q in S. The number of table states is K^2/2. For R fixed this is an exact finite-state reduction, not a stochastic transition. M_R can be far smaller than K.

Any actual contiguous run with all labels <=R agrees with this restricted rule up to its end: if a low label wins the full competition, it also wins among low labels. Consequently such a run cannot exceed M_R, and its entire time/deficit budget is bounded as above. It may end earlier if an outside label wins.

## 2. Exact mixed high/low decomposition

In an actual standard window [X,lambda X], fix a band [T,B_hi] with T>2R+2 and B_hi<=sqrt X, T=Theta(sqrt X). Call a high event good if its label is in the band and w>=p-2, with an optional independent endpoint-safety condition as in III. If any low factor is eligible at its prehorizon, some low clock arrives within 2R, contradicting the good wait. Thus every good high event starts at an R-rough horizon.

Consider a word consisting of good highs separated ONLY by labels <=R. Between two successive good highs, the low-only relay must run to its restricted terminal state. Proof: the actual low events agree with the transducer, and if they end before the restricted terminal, a low factor remains eligible at the next high start. This rules out its long wait. Conversely, running the transducer to completion is not sufficient for a good next high: an actual outside label could win earlier, or the subsequent high could have a bad wait, label or endpoints.

If a high event at (H,t) uses p on side s and arrives at n=t+w, its post state is (H+p-1,n). Its next candidate high start (if the relay is not interrupted) is exactly
    J=H+p-1+E((H+p-1) mod K,n mod K),
    u=n+B((H+p-1) mod K,n mod K).
The side s fixes n mod2. Forgetting n but retaining its parity yields a finite set of candidate relay displacements. Locally every residue n mod K of that parity can coexist with a selected long high p whenever W(H,p)>=p-2, by the CRT attainment proof in III: no eligible factor at H belongs to S, so the odd primes in K are coprime to the high-start clock moduli. This is only local arbitrary-time feasibility, not bounded-phase or actual relay feasibility.

If K<T-3, no successive good highs joined by such a relay can use the same p. Indeed H=+-1 mod p and J=H+p-1+E. If p divides a neighbor of J, E=1+e2-e1 mod p with e1,e2 in {+1,-1}, so E is congruent to -1,1,3. But E is even and 0<=E<K<p-3, impossible. The more precise sufficient condition is M_R<p-3. This applies even without endpoint safety.

## 3. Aggregate low-relay budget and the surviving large-deficit regime

For any physical block with n_out events of labels >R, the intervening low-only runs (including leading/trailing) have
    G_low <= M_R(n_out+1),
    N_low <= (M_R/2)(n_out+1),
    W_low <= 3G_low.                                   (1)
No assumption of long waits or lack of twins enters this bound. It is a per-ray physical-event budget, not a source-weighted mass bound.

In particular, if ALL outside labels are >=T, then n_out<=G_out/(T-1) and
    G_low <= M_R[1+G_out/(T-1)].
For R fixed, or R=R(X)=o(log X) with K=X^o(1) (by the prime asymptotics used in direct), T=Theta(sqrt X), G=Theta(X), this gives G_low=o(X) and N_low=O(K sqrt X). If all outside events are also good longs, their ordinary deficit increments are >=p-3=g-2; low increments are >=-g. Thus
    d_b-d_a >= G_out-2n_out-G_low = G-o(X).             (2)
The upper bound <=5G is automatic. This shows that small relays alone cannot change the macroscopic positive-deficit regime of II. It is NOT a contradiction: the direct logarithmic lower bound permits macroscopic variation. The current direct uniform-cut theorem has threshold exp(O(S)) rather than sqrt X; when S=R and K=X^o(1), its surviving cuts cannot be crossed by the low labels. Good square-root events supply deep bypass mass at that scale as predicted by direct's section 4. No new upper supply result for that population follows just from the low-relay budget.

Let L_R be the maximum span of any mixed run consisting of good highs with only low relays between them, beginning at a good high and ending immediately after a good high. G_good is bounded by L_R times the number of such runs (their spans may include low gain). Call any event that is neither a good high nor low an interruption; split it into medium R<p<T and bad high p>=T. With medium count b_mid and bad-high gain U_bad,
    G_good <= L_R(1+b_mid+U_bad/(T-1)).                (3)
This replaces III's small-label interruption count by a stronger medium/short-high resource condition, because arbitrarily many low-only relay events inside a run are now allowed. If L_R=O(sqrt X) uniformly for a fixed R, G_good=Omega(X) would force Omega(sqrt X) medium interruptions or Omega(X) bad-high gain. This uniform bound is OPEN. It is not inferred from the finite table.

## 4. Canonical initial entry: sparse sources and the first nonreset stratum

Take odd canonical root M, H0=2M-2, t0=M+2, d0=6. Consider the actual initial low prefix up to the first event p>R (if it exists). By section 1, H-H0<=M_R and 0<=d<=6+D_R at the prehorizon H of this first outside event. If it is a long high p>=eta sqrt X, H0 in [X,lambda X], then every prime q<(p-1)/2 is excluded from dividing either neighbor, by the exact maximum wait in III. In particular H belongs to a set of o(X) possible physical prehorizons (fixed-y CRT sieve as in III). Each such H receives at most floor(M_R/4)+1 canonical starting horizons, since H0=0 mod4 and lies in [H-M_R,H]. Hence for fixed R only o(X) canonical odd roots can have a good high as their first outside event. This includes the case of an empty low prefix.

Quantitatively the elementary sieve in III gives O(X/(loglog X)^2) possible prehorizons by taking y=c log X with fixed 0<c<1 and using PNT/Mertens. Thus the count of such canonical sources is O((M_R+1) X/(loglog X)^2), valid also for a growing R with K=o((loglog X)^2) (and T>2R+2). For instance R=o(logloglog X) suffices via log K~R. For a dense original family of Theta(X) distinct odd canonical roots, only o(X) can follow the low/good-high pattern from the start. Under finite twins and sufficiently large roots the first outside event must exist, since actual trajectories are infinite and the low prefix has bounded gain; the remaining roots must start with some medium or bad high event. This is an initial-entry statement, not a later transport mass theorem. It does not give a relative density result for prime-root source sets of smaller cardinality without stronger sieve estimates.

There is also a precise first-high deficit restriction. If the first outside event is long with label p>max(9,d+1) and side s in {0,1}, its post-deficit satisfies
    d'=d+2w-(p-1),
    d'-6s = 0 mod 2p.
The congruence follows from H'=0 mod p and n=0 mod p on side 0; H'=-2 mod p and n=2 mod p on side 1; both d' and 6s are even. Now
    d'-6s >= p-9 > 0,
    d'-6s <= d+3p+1 <4p.
Therefore exactly
    d'=2p+6s,    w=(3p-1+6s-d)/2.                   (4)
In particular p>max(9,7+D_R) guarantees this after ANY canonical initial low prefix. For fixed R and sufficiently large square-root labels the condition is automatic. This is the first nonreset adjusted-deficit multiplier h=1, not an assertion about arbitrary later high events. The finite audit below also checks the more general pointwise p>max(9,d+1) condition. For the next finitely many good highs separated by low relays, d is bounded by 6+D_R + 5j(B_hi-1+M_R) after j highs and their relays; hence adjusted multipliers are O(j+1) for the first j+1 high events at a comparable scale. This identifies a bounded-multiplier entry regime compatible with prior direct cofactor sieves, without asserting that the regime persists over an entire window.

## 5. Compressed graph and exact phases

Build a DAG whose vertices are actual standard even prehorizons of locally possible good highs. A candidate first high edge uses the actual H+-1 factors, adaptive eligibility, W(H,p)>=p-2 and both endpoints safe. Add a transition to each J given by the possible low relay displacements from section 2 with the required arrival parity, if J has an outgoing good edge. The terminal edge consists of the high jump only (no trailing low relay). For a high at H of gain g and candidate J=H+g+E, dynamic programming maximizes g+E+L_R(J), or g if terminal. Max high count is optimized separately. J>H so this is exact for the projected DAG, an overapproximation of actual words. For actual bounded phases, enumerate first high arrivals exactly as in III (canonical envelope H/2<=t<=3H+3). The starting time can be any feasible t for that arrival, because post-state is fixed. Execute the unique restricted relay, checking every step against the full MIN competition; reject if interrupted. At the terminal R-rough state take the actual next event and require good. Continue deterministically. All runs with >=2 highs have a projected continuation and are covered; singletons checked separately. As in III no canonical ancestry is assumed for these arbitrary intermediate-state maxima.

Finite diagnostic endpoints use K_safe=210,V=12, fixed across windows and across R, with distance >V from multiples of K_safe for each high jump's two endpoints. Low relay intermediate horizons need not be safe. This is an intentional choice of the relaxed mixed class, not a claim that all of its physical cuts are bypass for arbitrary R. In the reported R=3,5,7 experiments all low labels divide K_safe, so they cannot cross that lattice. The largest high count and gain can come from different words.

## 6. Reproducible finite audits

[mixed_relay_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/6c1ec97659963dd647732c5933da3b4aee974a27/research/infinite-orbit/mixed_relay_audit.mjs), blob280ae48372575330f815c10f16d99f76ed9d1bcf. Run node research/infinite-orbit/mixed_relay_audit.mjs. Actual ECMAScript function executed in available runtime, not separate Node. All assertions pass. Complete low-only residue tables:
| R | K | maximum gain | maximum event count | maximum elapsed ticks |
|---:|---:|---:|---:|---:|
|3|6|4|2|7|
|5|30|14|5|19|
|7|210|34|9|56|
22,518 residue states, checked termination, barrier, rough terminal and time budget. The maxima need not share a state. Nine mixed graphs (band [ceil(sqrt X/2),floor sqrt X]):
| X | R | projected max span / high count | exact max span / high count |
|---:|---:|---:|---:|
|4096|3|114 / 2|114 / 2|
|4096|5|136 / 3|136 / 3|
|4096|7|180 / 3|180 / 3|
|16384|3|208 / 2|208 / 2|
|16384|5|288 / 3|246 / 3|
|16384|7|342 / 4|342 / 4|
|65536|3|526 / 3|526 / 3|
|65536|5|526 / 3|526 / 3|
|65536|7|640 / 4|640 / 3|
Positive exact 4-high word at X=16384,R=7, from intermediate state (H,t)=(50442,62200):
    labels 73,5,3,7,5,3,7,97,5,3,79,67
    waits  71,6,3,6,4,2,3,173,9,1,90,79
    H_end=50784, span342.
This is actual MIN from the specified state, with envelope, not established canonical ancestry. 51 representative events in maximum words checked independently by literal gcd tick scan. For each R,X, 1024 actual canonical initial horizons in [X,X+4096) followed to terminal or window boundary (all stopped in these finite scans); 2181 good-high incidences checked against the graph bounds across the 9 nested configurations; max mixed high count from these sampled sources was 1. These are separate from the arbitrary-state exact maxima. A projected 4-high possibility at X=65536,R=7 is NOT phase-realizable (exact max count3), despite equal optimized span640. No full-window mixed path in any tested window; this follows already from the projected max span, not from a sample of times. Finite diagnostics are not a uniform bound.

[first_exit_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/c6ec712f4dcef5cc6fb16c70ea7284c4f40c3602/research/infinite-orbit/first_exit_audit.mjs), blob681623951b9cefd5f4a6c452924abd6bb51ce960. Run node research/infinite-orbit/first_exit_audit.mjs. Actual ECMAScript, all assertions pass. R=3,5,7,11; X=4096,16384,65536,262144. Every canonical H0=0 mod4 in [X,16X) considered; 1,305,600 source incidences for each R, 5,222,400 in total (same roots reused across R). Follow exact initial low prefix, classify first outside event or true terminal. Verify restricted/full low-step match and bound, and first-long roughness and deficit congruence. 84,731 first outside events in the square-root band with w>=p-2; 84,643 satisfy p>max(9,d+1), all yield adjusted d'=2p+6s. The other 88 are outside the sufficient condition, not asserted to fail or satisfy (4). At the largest X:
| R | source incidences | first long band | distinct long prehorizons | max actual initial low gain | max pre-deficit |
|---:|---:|---:|---:|---:|---:|
|3|983040|7697|5949|4|12|
|5|983040|12374|5949|10|30|
|7|983040|16627|5949|28|76|
|11|983040|20006|5949|70|146|
Source multiplicity differs from physical horizon counts, illustrating why physical scarcity alone cannot bound later source-weighted transport. This audit contains actual finite twin stops and does not instantiate the global finite-twin assumption. No asymptotic constant verified by finite computation.

## 7. Next exact target

The pure high survivor of II can be locally repaired with low relays, and longer actual mixed segments exist. The relay compression shows that if the medium and bad-high populations were absent, the low labels still could not change the macroscopic deficit regime, and dense canonical starts would almost all fail that restricted pattern at initial entry. A finite canonical prefix of exceptional labels is nevertheless allowed, so this does not exclude eventual mixed infinite survival. Next: upper bound L_R (or produce arbitrarily long mixed segments), use first-high bounded multipliers to count early high descendants, and extend (3) to genuine medium relays rather than treating them as arbitrary interruptions. For unified dense-source transport, carry source multiplicities through the exact low transducer and actual interruptions; do not identify physical rarity with missing mass. No full all-constraint model, no Lean verification, no finite-twin contradiction.
