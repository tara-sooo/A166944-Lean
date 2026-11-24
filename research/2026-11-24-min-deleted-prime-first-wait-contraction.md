# Deleted-prime first-selection clock contraction and repeated-wait tail criterion

2026-11-24 JST. Continues 447acd0cd16414a86c0dead5938415eae63266c5 on the SAME research/min-cycle-forest-2026-11-24 branch. New elementary leave-one-prime-out coupling and asymptotic first-wait contraction, exact finite CRT checks, and larger fixed-seed diagnostics. No Lean compilation. The new repeat-wait premise and physical far-coalescence deficit remain open; no twin-prime proof.

## 1. Probability space and time truncation

Use the complete LOW-only deterministic ghost on the uniform residue rectangle of even C modulo L and t modulo L, where L=2 product_(3<=p<Y prime)p. Equivalently choose independent uniform C mod p and t mod p over odd primes p<Y, and an independent common t parity. The ghost selects the earliest strict next eligible parity clock, ties by smaller prime, and increases C by p-1. It terminates within the LOW barrier. The initial state need not be canonical or have nonnegative height; signed height increments are relative to the initial state. No assumption of stationarity or uniform distribution of later attained states is made.

For a real cutoff T>0 (integer below), let A_Y(T) be the elapsed time of the last event whose relative clock is <=T, or 0 if none. Thus A_Y(T)<=T. Let F_Y(T) be the sum of the inter-event waits for those events which are the FIRST selected occurrence of their prime on that path. Let R_Y(T) be the sum for all REPEATED selections. These are waits of executed events only, not time spent in the terminal infinite plateau or an unfinished waiting interval. Exactly A_Y(T)=F_Y(T)+R_Y(T). Write A,F,R for these random variables when Y,T are fixed. Let tau be the complete finite elapsed time to the last LOW event, D_Y the previous maximum nonnegative signed height gain over prefixes. D_Y<=2 tau because the horizon gain is nonnegative. Every event wait is <=2p<2Y. Hence if tau>T, A_Y(T)>=T-2Y, and for T>2Y
    Pr(D_Y>2T) <= Pr(tau>T) <= E A_Y(T)/(T-2Y).
This explicitly accounts for the overshoot of the next event. The new criterion concerns the truncated repeated WAIT time, not the number of repeated labels or the previous source-weighted canonical repeat count.

## 2. Delete a prime: exact first-hit coupling

Fix a prime p<Y. Run the same ghost from the same initial CRT state but with p removed from the eligible alphabet. Let A_-p(T) be its last-event time by T; extend its final plateau indefinitely for candidate counting only. Conditional on the initial residues for every other prime and the initial time parity, this entire deleted path (relative event times and horizon gains) is deterministic, independently of C mod p and t mod p. This remains true at its terminal plateau. Before the first actual selection of p the original path and the deleted path coincide, by induction on the events, including the tie-break rule. If p is never selected by T, A=A_-p. At a first selection exactly tied with another eligible clock, use the deleted PRE-event horizon at that clock; counting all such candidate ties is an upper bound.

For each relative integer clock n in [1,T], the deleted pre-horizon is C+g(n), and actual event time is t+n. The parity of t+n is fixed under the conditioning. If even, the p event requires C+g(n)=1 mod p and t+n=0 mod p. If odd, it requires C+g(n)=-1 mod p and t+n=2 mod p. Exactly one ordered residue pair (C mod p,t mod p) satisfies these two conditions. Its conditional probability is exactly 1/p^2. We do NOT claim that the first hit events at different clocks are independent, and an eligible p event need not be selected. The first selected p must occur at one of these candidate clocks, so a union bound gives
    Pr(p first selected by T) <= min(1,T/p^2).
Consequently
    E A_-p(T) <= E A_Y(T)+ T Pr(p first selected by T)
               <= E A + T^2/p^2.
The comparison uses only the equality of the prefixes on the complement of the first-hit event and 0<=A,A_-p<=T. This is an actual coupling, not a fresh-randomness model for repeated p events.

## 3. Weighted candidate waits and a strict contraction

Let F_p(T) be the wait of the first selected p event by T, zero if none. On the deleted path partition the integer clocks up to T into plateau intervals (previous event clock, next event clock], using time0 for the initial state; include the unfinished nonterminal plateau if any, or the final terminal plateau. For the first selected p, its actual preceding attained state is the start of the corresponding deleted plateau. Its wait w is the number of relative clocks from that start, and must satisfy 1<=w<=2p by its own strict periodic clock. Within a plateau of length ell truncated at T, candidate waits are 1..m with m=min(ell,2p). Their sum m(m+1)/2 <=(p+1/2) ell. The nonterminal plateau lengths up to T sum to at most A_-p+2Y: all completed intervals sum to A_-p, and an unfinished interval if nonterminal has length <2Y by the deleted ghost clock bound. The final terminal plateau contributes candidate wait sum at most p(2p+1), regardless of its length. This latter contribution is necessary: deleting p may make the path terminate while the original p path continues.

By the exact conditional candidate probability 1/p^2 at each time from section2, overcounting all first-hit candidates gives
    E F_p <= (1/p+1/(2p^2))(E A_-p+2Y)+2+1/p
            <= (1/p+1/(2p^2))(E A+T^2/p^2+2Y)+2+1/p.
This uses the full deleted path to form candidates; it is not obtained by assuming uniformity along the actual selected path. In particular the average factor for a plateau is p+1/2, not the coarser maximum wait 2p. The factor of two saved here is essential for the following contraction.

Take any T=T(Y) with Y=o(T), T=o(Y log Y) (e.g. T=floor(Y sqrt(log Y))), and z=ceil(sqrt(T) log^(1/4) T). For small p<z use the deterministic F_p<=2p, so
    sum_(p<z prime) E F_p <= O(z^2/log z)=o(T).
For z<=p<Y sum the displayed weighted estimate. Mertens' reciprocal-prime theorem gives
    sum_(z<=p<Y prime) (1/p+1/(2p^2))
      = log log Y-log log z+o(1)=log 2+o(1),
since log T/log Y->1 and log z/log Y->1/2. The standard elementary upper prime-count estimate by partial summation gives sum_(p>=z) p^-3=O(1/(z^2 log z)). Hence the error from the deletion comparison is O(T^2/(z^2 log z))=o(T); the unfinished interval cost is O(Y)=o(T); and the terminal contribution O(pi(Y))=o(T). Thus rigorously
    E F_Y(T) <= (log 2+o(1)) E A_Y(T)+o(T).
Combining with A=F+R,
    (1-log 2-o(1)) E A_Y(T) <= E R_Y(T)+o(T).
Equivalently
    E A_Y(T)/T <= (1/(1-log 2)+o(1)) E R_Y(T)/T+o(1).
The constant 1/(1-log 2) is about 3.259. All errors are deterministic asymptotic prime-sum bounds, independent of actual path distributions. This is a genuine contraction: counting initial selections alone, even with their full adaptive history, cannot sustain a nonnegligible fraction of the time scale T without some repeated waits. No upper bound on R itself is claimed. The proof does not use the conjecture that long paths behave like a Markov chain.

For a useful finite inequality without asymptotic notation, for ANY 3<=z<=Y and integer T>=1,
    E F <= 2 sum_(p<z odd prime)p
      + sum_(z<=p<Y prime) [(1/p+1/(2p^2))(E A+T^2/p^2+2Y)+2+1/p],
with all primes in the LOW alphabet. This follows from the same coupling even in very small Y windows.

## 4. New sufficient repeat-wait condition

For T=floor(Y sqrt(log Y)), it suffices along a diverging sequence of Y to show
    E R_Y(T)=o(T).
By the contraction E A=o(T), so Pr(tau>T)=o(1) and Pr(D_Y>2T)=o(1). In particular D_Y/(Y log Y)->0 in probability on that sequence. Since 0<=R<=T, the premise is equivalent to R_Y(T)/T->0 in probability, not to a bound on the expectation of untruncated full repeat waits. No uniform integrability for full path times is needed. More generally for Y<<T<<Y log Y, the same implication holds. One can split repeats into bands as needed, but the displayed theorem requires the sum of their waits. The first-selection estimate applies to all primes; it cannot be reused for repeat occurrences after p's CRT coordinates have been fixed.

The previous clipped-potential first-passage theorem therefore conditionally removes the high-height, small-terminal-class cell-stop population: choose K=2T=o(Y log Y), P and a growing sufficiently slowly so a[P Pr(D_Y>K)+1/log^2 P+K/(Y log Y)]->0, and choose Y(B) sufficiently slowly that the earlier LOW period constraints hold. Then the previous landing-divisor and clock-height deletions, inverse prime-stop moments, and physical forest harmonic near deletion give 2 P_phys,far>=N-o(X) in hypothetical no-twin windows. This is the same end reduction as before, with the new repeat-wait premise replacing the ghost probability-tail premise. The physical far-coalescence upper bound is still independently necessary. In particular the new contraction is not a proof of twin primes.

A useful target for further work is a uniform bound on E R_Y(T), e.g. O(T/log^epsilon Y) for fixed epsilon>0, or a decomposition with separately negligible repeated waits in growing prime bands. The deterministic fact that between repeated selections of p the intervening gain must be at least p-3 (as in earlier reactivation congruences) does not alone give such a bound. Repeats at small primes can be numerous. It is not valid to treat their coordinates as independent anew.

## 5. Exact finite verification and large samples

Saved research/min_deleted_prime_first_wait_audit.mjs and research/min_deleted_prime_first_wait_results.json, exact remote readback at 829dc97fb9e0659d0067fefa9867d25ee010c52b. The script has two independent diagnostic functions.

Exhaustive exact computation for Y=5,7,11, all L^2/2 residue states, T in {floor(Y sqrt(log Y)),2Y,8Y}. For every start and each deleted prime, replay the full and deleted ghosts. Verify equality of last clock if p not selected by T, per-deleted-path weighted candidate bound, exact aggregate CRT inequalities p^2 sum F_p <= sum of deleted candidate waits and p^2 times first-hit count <= sum of candidate times, aggregate deleted-path clock comparison, A=F+R and the terminal overshoot implication. Include terminal plateau in candidate counts. At Y11, 22050 states and 66150 deleted-path comparisons per T, 198450 across three T. At T17: E A=7.65868481, E F=6.40875283, E R=1.24993197. For p7 E F_p=1.56126984 vs exact candidate upper bound1.73065760, p7 first-hit frequency0.28027211. For p3 E F_p=2.55179138 vs candidate upper3.32916100. At T88 all ghosts complete (E tau=10.69011338). These exact checks validate finite inequalities, not the asymptotic coefficient numerically at small Y.

Fixed-seed CRT samples of 8192 complete LOW ghost paths for each Y=13,53,101,199,397,797,1597,3203, with T=floor(Y sqrt(log Y)). Simulate each path to its actual end, compute A,F,R for events at clocks <=T, complete elapsed tau and D, repeat counts and waits split by prime thresholds, and check exact per-path identities and overshoot. All terminate before 20000-event guard (maximum observed305 across these particular samples, distinct from earlier seeds). No high-prime summation truncation: alphabet is all primes <Y, and each sampled path is complete; only F,R,A are intentionally time truncated as in the theorem. Samples are not rigorous upper bounds on the full CRT population.

Selected empirical results:
    Y     T     E[A]/T   E[R]/T   Pr(tau>T)   Pr(D>2T)
    13    20    .464258  .086273  .259521     .124390
    53    105   .406813  .111995  .163818     .037842
    101   216   .360348  .097222  .122314     .020752
    199   457   .311866  .076703  .085083     .009033
    397   971   .257519  .053678  .051025     .005371
    797   2060  .213604  .036395  .027100     .001831
    1597  4337  .181942  .024939  .018066     .000977
    3203  9100  .144855  .014087  .009155     .000488
At Y3203, sample mean A1318.17944, F1189.98755, R128.19189, first waits90.2751% of A; 93.31% of samples have at least one repeated selection by T, so rarity of ANY repeat is not the useful criterion. No sampled repeat wait total exceeds T/4 at that Y; this does not imply such states do not exist. Mean repeat waits for p>=31 are17.37463, p>=57 are9.22546, p>=801 are0.41187; p>=z166 are2.63672. Thus small labels contribute most of the repeat-wait mean in this sample. Mean complete elapsed1353.34729, D1210.71826. The sample's normalized repeat mean is not monotone at every tested Y (13 to53 rises), though decreases at the subsequent tested cutoffs. The asymptotic premise remains unproved.

## 6. Next task

The proof now separates adaptive first selection, handled by an exact deletion coupling with strict log2 contraction, from repeated selection. The latter is the specific remaining ghost tail problem. Analyze repeated waits after a prior use of the same label, especially accumulated waits of small primes between fresh larger selections; use the reactivation congruences and deterministic LOW blocks rather than assuming the original p residues become independent again. An upper bound on the full truncated repeat-wait mean is still needed. No new branch, no main edits, no Lean compilation.
