# Canonical reentry in seven ticks and a global root/nonreset alternative

Continuation of [395e9ea](https://github.com/tara-sooo/A166944-Lean/commit/395e9ea55ba318ac9f44d653c7920cd1193e8c9a), independent direct-arithmetic branch. The new elementary argument couples the adjusted deficit to recurrence of the original canonical starting states. It does not need factor-count classification, a sieve, short-return words, or the historical cost framework. No proof of twin infinitude or A166944; no Lean kernel verification.

## 1. Definitions

At a plateau (t,H), H even, use adaptive MIN: at each future tick n, even side requires p|n and p|H-1; odd side p|n-2 and p|H+1; odd prime p eligible iff p^2<=H+1. First tick wins, least p on ties. At event e=+1 even or -1 odd, I=(1-e)/2, post Z=H+p-1, ordinary post deficit d=2n-Z>=0, adjusted D=d-6I. The prior identity gives D divisible by 2p. For p>=5, D>=0 since d>=0 and D>=-6. Consequently if D!=0, d>=2p+6I>=2p. For all p>=3, d cannot be 2 or4: on even side neither is divisible by 2p; on odd side d-6 is -4 or-2, likewise impossible.

A canonical state is a state (t,H) with H=0 mod4, H>=8, t=H/2+3. It is exactly the ordinary root M=H/2+1 odd>=5, H=2M-2,t=M+2. A reentry can occur at an event tick or at a unit/quiet tick. We count visits only while the trajectory continues; in a stopped terminal plateau one can extend the formal unit ticks, but this is not counted as an actual reentry of the stopped event process. Starting at a reentry and continuing gives exactly the trajectory from that new root by determinism. Distinct reentries along a path have strictly increasing H and M since each plateau has at most one canonical tick.

## 2. Seven-tick normalization theorem

If an event has D=0 on the odd side, its post state is canonical immediately: 2n-Z=6 and n odd implies Z=0 mod4.

If D=0 on the even side, the post state satisfies t=H/2 even, H=0 mod4. Assume H>=24. The following exact rule applies, independently of the factorization of any larger numbers. At first future tick t+1 odd, gcd(t-1,H+1) divides3 since 2(t-1)-(H+1)=-3. Thus p=3 fires iff H=2 mod3. It is eligible. In that case at tick t+2 even the new horizon H+2 gives gcd(t+2,H+1) divisible3 and dividing3, so a second 3 fires. The resulting state is (t+2,H+4), again an even reset.

If first tick is quiet, at t+2 even gcd(t+2,H-1) divides5. Thus p=5 fires iff H=1 mod5, and is eligible since H>=24. Again resulting state (t+2,H+4) is an even reset. If both first two ticks quiet, at t+3 odd gcd(t+1,H+1)=1 because 2(t+1)-(H+1)=1. This is the canonical tick for unchanged H.

Call the two-tick gain4 blocks type3 (3,3) and type5 (unit,5). They are selected at current H by H=2 mod3, else H=1 mod5, respectively. If neither holds, three quiet ticks normalize to the canonical state. Three successive gain4 blocks are impossible: among H,H+4,H+8 exactly one is 2 mod3, so two of the three would have to be 1 mod5, which cannot happen. Therefore after at most TWO blocks and three quiet ticks there is a canonical state, within 7 ticks and total gain <=8. If the adaptive event process terminates on a twin center during normalization, the alternative is termination; the same rule holds if formally continued with unit ticks. On an infinite path termination cannot occur.

Exact table by starting H mod60 (H divisible4):
    H mod60 : blocks
    0:[], 4:[], 8:[3], 12:[], 16:[5,3],
    20:[3], 24:[], 28:[], 32:[3,5], 36:[5],
    40:[], 44:[3], 48:[], 52:[], 56:[3].
The canonical horizon after normalization is H+4*(number of blocks). No p>=7 event occurs between an even reset and its normalized root. For a reset with p>=7, the resulting canonical state is reached before any next event with p>=7, so each such reset on an infinite path has a distinct associated root. This is a deterministic short reentry result, not a statistical probability of reaching a root.

## 3. Root-free interval obstruction

Consider a finite contiguous interval on an infinite adaptive ray, with initial horizon>=24. It may start/end at quiet ticks as well as events. Let G be its horizon gain, Y any upper bound on its pre-horizons, C=floor sqrt(Y+1) so individual gain<=C-1. Let L be maximum ordinary POST-event deficit in the interval (0 if no events), and R=max(5,floor(L/2)). Every event with p>R must have D=0, since any nonreset p>=5 would give d>=2p>L. Here R>=5 ensures all such high events are >=7, and their normalization uses only labels3,5.

For any integer R>=3 let K_R=2 product of all odd primes<=R. As in the square-band note, a consecutive run of labels<=R has gain<=K_R: it cannot cross the first multiple J of K_R at or above its starting horizon. For H<J with H=e mod p and p<=R, the even positive J-H congruent to -e modp is >=p-1, so H+p-1<=J; at J no such label is eligible. This bound needs no finite-support length result.

Suppose the interval has no canonical tick in its strict interior (endpoints may be canonical). It can contain at most one high event p>R, since every such event is a reset with its associated canonical state before the next high event. If there is a high event, all subsequent gains up to the next canonical state are <=8, by normalization, and the interval must end at or before that state. Before the high event all labels are <=R. Thus the exact bound
    G <= K_R + (C-1) + 8.                          (1)
If no high event occurs, G<=K_R. This works on arbitrary infinite rays, not just canonical starts.

For a root-free crossed window [X,lambda X] with fixed lambda>1, Y=lambda X, first crossing overshoot <=sqrt(X+1), so G>=(lambda-1)X-O(sqrt X). Equation (1) forces K_R>=Omega(X). Elementary Chebyshev theta(R)<=4 log(2)*R gives K_R<=2 exp(4 log(2) R). For large X, R=floor(L/2), so
    L >= (log X)/(2 log 2) - O_lambda(1).           (2)
The same bound holds if one uses a larger maximum over all ordinary deficits (including quiet ticks). In particular an infinite ray with only finitely many canonical reentries cannot keep its post-event deficit bounded, or even o(log H), on its tail. Consecutive canonical reentries on a ray with globally bounded deficit L have horizon spacing <=K_R+sqrt(Y+1)+8; root-free terminal prefixes obey the same bound as long as they actually continue through the interval. No inference that every ray has a bounded deficit.

## 4. Count and gain alternatives without any global deficit assumption

Let R>=5 be arbitrary; do not define it using L. In an interval with initial horizon>=24 on an infinite ray, let N be the number of canonical visits in (t_start,t_end] (not counting initial state). Let m0 be the count of events p>R with D=0, m1 the count of events p>R with D!=0, V0,V1 their respective total gains, and U total low-label gain. All high reset events have distinct associated canonical reentries; at most one such reset has its reentry after the interval's end, so m0<=N+1. Each high nonreset event has ordinary post-deficit d>=2p>2R. The low runs are separated by high events, hence U<=K_R(m0+m1+1). With C as above, this gives the exact count inequality
    G <= K_R+(K_R+C-1)(N+1+m1),
    N+m1 >= (G-K_R)/(K_R+C-1)-1.                   (3)
Also V0<=(C-1)m0, m1<=V1/(R-1), so
    G <= K_R+(K_R+C-1)(N+1)
                    +(1+K_R/(R-1))*V1.            (4)
These are necessary conditions on actual successive states of one path, not independently realizable CRT phases. In (4) negative lower bounds on V1 are simply vacuous.

For crossed [X,lambda X] on an infinite ray, choose fixed 0<eta<1/2 and R=floor(eta log X/(4 log2)) (>=5 eventually). Then K_R<=2X^eta=o(sqrt X), C=O(sqrt X), G>=Omega_lambda(X). Equation (3) implies
    N+m1 >= Omega_lambda(sqrt X).
Thus in EVERY sufficiently large crossed window there are either Omega(sqrt X) distinct canonical reentries, or Omega(sqrt X) nonreset events with p>R and ordinary post-deficit d>=2p. The latter is more than a single deficit maximum. Constants may be chosen depending on lambda,eta, not on the root. If N=o(sqrt X) along any subsequence of windows, (4) further gives
    V1 >= Omega_(lambda,eta)(X^(1-eta) log X)
in those windows. If R is fixed and N=o(sqrt X), the stronger V1>=Omega_(lambda,R)(X) holds, from the same formula. So a root-sparse tail must carry significant gain on nonreset large-label events, not merely on arbitrary long waits.

Conversely, if throughout the window L<= (log X)/(4 log2), choose R=max(5,floor(L/2)); then m1=0 and K_R<=O(sqrt X). Equation (3) forces N>=Omega_lambda(sqrt X). In particular a globally bounded-deficit infinite ray visits Omega(sqrt X) canonical states in every sufficiently large crossed window. This is an unconditional implication on any actual ray satisfying the deficit bound. Such visits do not alone give a twin: the reentry root is a new canonical starting point, not a terminal horizon.

Under finite twins all sufficiently large canonical roots have infinite adaptive trajectories (first note). The two alternatives above must then hold on each of those rays. Neither alternative is presently contradicted by finite twins. In particular the theorem does not assert that small ordinary deficit is forced, nor that a large number of reentries is impossible. It supplies a new global reduction independent of the previous roughness trichotomy.

## 5. Diagnostics

[Audit fb1ccc9](https://github.com/tara-sooo/A166944-Lean/blob/fb1ccc9acf1edd36bb6eacb9e238b95894851f60/research/min_direct_canonical_reentry_audit.mjs), blob fa44de2484114c7d723cda9aa55e6e0ce9e7ebaf, exact remote readback. Run node research/min_direct_canonical_reentry_audit.mjs 150000 180. Actual ECMAScript function executed in tool runtime, not a separate Node process. Abstract even-reset states H=24..200000 step4: 49995 states, 209979 literal GCD ticks; 26664 require zero blocks, 16665 one, 6666 two. All reach the predicted canonical state when including formal unit ticks on terminal plateaus. 15 exact mod60 table checks separately.

Canonical roots all odd M=5..150000, up to180 nonunit events: 1,630,951 events, 73479 nonempty paths, 74951 terminal roots (including roots with zero events), no range truncation. 185119 actual canonical reentry incidences across sources (116251 at event ticks, 68868 quiet); 1884 further potential canonical ticks on stopped terminal plateaus not counted as actual reentries. 91740 even and 116251 odd D=0 events. 800999 p>=5 nonreset deficit checks and all 1630951 post-deficit exclusion checks. 254176 root-free or successive-root interval checks of (1), 829554 general interval/R count and weighted inequalities, 236768 bounded-deficit interval checks. 138714 high reset incidences p>7,Z>=24, 136830 followed by verified actual canonical reentry within the scanned process. Others were not asserted to reach an actual reentry after its endpoint. All final checks passed.

Initial diagnostic mistakenly excluded resets exactly seven ticks before the right endpoint of a root-to-root interval (the endpoint itself is permitted to be the associated root); corrected the old coarse check to n<t_end-7 and included at most8 late event ticks, before deriving the sharper bound (1). Small H<24 blocks excluded from the normalization-based bound. Example M229 visits (t,H)=(231,456),(237,468),(249,492),(257,508),(261,516), with 8 events before termination. Largest sampled root-free gain4670, H256348->261018, 180 events, max post deficit4308; this is a finite prefix, not a claim of infinite continuation. Counts across roots/windows overlap. No full macroscopic crossed window is claimed from these bounded runs.

No Lean executable/kernel verification, no web literature novelty claim, main and sibling branches unchanged. Next: exploit the canonical reentry map on increasing roots (first-return segments are deterministic), or control the nonreset large-deficit branch. This addresses global reachability rather than just local competing-clock availability.
