# First-discovery factorial bounds, exact cutoff coupling, and infinite frozen-terminal clock law

2026-11-24 JST. Continues 447acd0cd16414a86c0dead5938415eae63266c5 on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions in the uniform CRT phase model of the LOW-only deterministic ghost; exact small finite rectangle checks and numerical product diagnostics. No Lean compilation. The required long-path probability estimate, full stopping deficit and twin-prime conjecture remain open.

## 1. Uniform phase model and first-discovery lemma

Let Y be a finite cutoff and let the ghost use all odd primes p<Y, with the canonical MIN clocks, no other labels. The starting horizon C0 is even. Use relative cumulative gain G (initial 0) and relative elapsed integer time s (initial 0). Fix the common parity of starting time t0. The even horizon residues C0 mod p and clock residues t0 mod p are independent uniform residues for the different odd primes, and independent of each other, under the complete CRT rectangle conditional on this parity. The next clock of p occurs at absolute n=0 mod2p if p divides C-1, and n=p+2 mod2p if p divides C+1. The earliest next clock wins, ties by the smaller label. Every event increases G by p-1 and s by at least 1. The LOW barrier ensures finite termination for every finite cutoff. As before D_Y is max(0, max over attained event prefixes of 2s-G), and E_Y is complete executed elapsed time (zero on an initially terminal phase). In particular D_Y<=2E_Y. We use a new time-budget variable T, not the earlier cell-admission threshold.

For a set S of k distinct primes in the alphabet, condition on common parity and on all initial residues outside S. Fix an ordering q1,...,qk of S and strictly increasing proposed first-selection elapsed times 1<=s1<...<sk<=T. There is at most one assignment of the two initial residues mod q_i for every q_i in S that realizes these first selections in this order at these times.

Proof by induction: until s1 the trajectory must agree with the trajectory using the complement of S. This also holds after a complement terminal, treating its state as a stationary horizon until an inserted event. At the proposed time s1, the pre-horizon gain G is uniquely determined by this complement trajectory prior to s1. The parity of t0+s1 is fixed. If even, the two required residues are
    C0=1-G mod q1,       t0=-s1 mod q1.
If odd they are
    C0=-1-G mod q1,      t0=2-s1 mod q1.
There is exactly one candidate pair; reject it if it fails full event selection or any earlier-time condition. For an upper bound it is unnecessary to check that it produces no earlier q1 event, so it is also possible to reconstruct by forcing the proposed event at s1. Then add q1 with its fixed residues to the available alphabet. Up to s2 the true trajectory must use this enlarged alphabet, since no other member of S has yet been selected. The same argument fixes q2 uniquely. Iterate. Other primes, including primes larger than any member of S, may be selected or repeated arbitrarily in the intervening segments; their residues are already fixed and their trajectories deterministic. This is a uniqueness argument for actual successful assignments, not an assertion that the forced sequence is valid or that actual first-selection times are independent.

Thus the conditional probability of the specified first-selection order and times is at most product_(q in S) q^-2. Summing over k! orders and binom(floor T,k) choices of times gives
    Pr(all primes of S selected by T | complement residues, parity)
       <= (floor T)_k product_(q in S) q^-2,
where (T)_k=T(T-1)...(T-k+1) for integer T. The statement remains valid with arbitrary fixed conditioning on a disjoint lower alphabet (average over other complement residues), with no stochastic independence assumption on the chosen event labels.

Let J_{Z,Y}(T) count distinct labels Z<=q<Y selected by elapsed T. Let W(Z,Y)=sum_(Z<=q<Y prime) q^-2. Sum over unordered subsets S of size k. Then
    E[binom(J_{Z,Y}(T),k) | lower residues and parity]
       <= (floor T)_k e_k({q^-2 : Z<=q<Y prime})
       <= (T W(Z,Y))^k/k!,
where e_k is the elementary symmetric sum. Hence the same bound applies to Pr(J>=k). For any u>=0,
    E[(1+u)^J | lower residues and parity] <= (1+u W)^floor T <= exp(u T W).
The first inequality uses (floor T)_k/k! = binom(floor T,k). In particular Pr(J>=k)<=(e T W/k)^k. These are bounds on DISTINCT selected primes, not total event counts; a previously selected prime is no longer fresh and may repeat.

Since W(Z,Y)<=O(1/(Z log Z)) by the elementary prime-count upper bound, choose T=floor(Y(log Y)^beta), Z=ceil(Y/(log Y)^alpha) for fixed alpha,beta>=0 with alpha+beta<1. Then
    Pr(any label >=Z selected by T) <= O((log Y)^(alpha+beta-1))=o(1).
More generally at T=O(Y log Y) and Z=cY for fixed c>0, the number of distinct such labels is bounded in probability, with the displayed factorial tails. This is unconditional, uniform in all initial lower residues. It does not exclude long paths using only smaller labels, nor does it bound repeats of the already exposed labels. Therefore it does not prove D_Y/(Y log Y)->0 in probability.

## 2. Exact conditional probability of agreeing with a lower-cutoff ghost

Couple the Y and Z ghosts, Z<Y, by restricting the same initial CRT residues. Condition on all primes p<Z and the common parity. The complete lower ghost path is now fixed. Write its events as (pre-gain G, pre-time s, wait w, label p<Z), with final gain G_* and elapsed E_Z. For each extra prime q in [Z,Y), construct the following set B_q of bad initial residue pairs (C0 mod q, t0 mod q):
* at every integer relative time j with s<j<s+w on each lower-path plateau, include the pair (1-G,-j) mod q if t0+j is even, or (-1-G,2-j) mod q if odd;
* at the lower terminal horizon include all pairs with C0=1-G_* or -1-G_* mod q and arbitrary t0 mod q.

Deduplicate these pairs. There is no need to include a time tied with a lower event, because the lower prime wins. A full higher-cutoff path agrees with the lower path, including its terminal and all event times, IF AND ONLY IF every extra prime avoids its bad set. Necessity follows from the first high selection or the continued nonterminal status. Sufficiency follows inductively along the lower path and then at terminal. Given the lower residues the bad sets are deterministic and the extra primes' two-residue pairs are independent. Thus
    Pr(complete agreement | lower residues, parity)
       = product_(Z<=q<Y prime)(1-|B_q|/q^2).
The sets obey |B_q|<=min(q^2,E_Z+2q). A sharper plateau bound is
    |B_q| <= min(q^2, sum_(lower events) min(w-1,2q) + 2q).
Within a fixed plateau each parity supplies at most q distinct residues, so this improvement does not assume different plateaus are independent.

For agreement only of the event sequence up to integer time T, restrict the preterminal bad times to j<=T, and after the lower terminal include only j in (E_Z,T], instead of the full terminal eligibility set. Then |B_q(T)|<=min(T,q^2); the corresponding exact product is the probability of no extra prime selected by T. The stationary plateau after a lower terminal is needed even though the lower path has ended. This proof is an exact coupling of adaptive paths until their FIRST differing event, not independent selection at each step.

Put V(Z,Y)=sum_(Z<=q<Y prime)1/q. Conditional complete disagreement is at most min(1,E_Z W+2V), by the union bound. For any T>=0,
    Pr(full disagreement) <= Pr(E_Z>T)+T W+2V.
In particular
    |Pr(D_Y>K)-Pr(D_Z>K)| <= Pr(E_Z>T)+T W+2V
and the same comparison holds for elapsed-time tails. A more exact two-sided bound is given by retaining the conditional product b on lower phases: E[1_{D_Z>K} b] <= Pr(D_Y>K) <= 1-E[1_{D_Z<=K} b]. The comparison provides a certified way to extend finite lower-cutoff calculations to a new band using exact residue coverage, without assuming monotonicity of D or E in the alphabet.

For the near-top choice Z=ceil(Y/(log Y)^alpha), T=floor(Y(log Y)^beta), alpha+beta<1, the additional terms T W+2V are o(1). Indeed V=O(log log Y/log Y) for fixed alpha using prime counting upper bounds in the short multiplicative band (or summing dyadic intervals each O(1/log Z)); alpha=0 gives an empty band. Therefore all remaining error in this comparison can be bounded by the lower ghost's elapsed tail at T. This is a reduction/continuity estimate, not an asymptotic upper bound on that remaining tail.

## 3. Infinite-alphabet local limit

Take a countable product of independent uniform C0 mod p and t0 mod p residues for all odd primes, with one independent common time parity. Every finite-cutoff marginal is exactly its uniform CRT rectangle. There is no need for a single finite integer realizing all these infinite residues. For any fixed even relative horizon gain G and positive integer elapsed j, the probability that a prime p has a valid clock at that state and time is 1/p^2 (conditional on parity). Since sum 1/p^2 converges, almost surely only finitely many primes can be valid at that pair (G,j). Countably many such pairs are simultaneous. Conversely for each fixed even G, infinitely many primes are eligible at that horizon almost surely, by independence and divergence of sum 1/p; use the second Borel-Cantelli lemma and a countable intersection over G. Thus from any attained state there exists a next finite integer clock, and at the earliest such time one may choose the smallest valid prime. The infinite MIN ghost is well-defined almost surely and never terminates. There is no finite-time explosion because time advances by at least 1 at each event.

For each fixed integer T, the event sequence up to T of the finite-cutoff ghosts stabilizes almost surely as Y tends to infinity. One proof compares adjacent cutoffs differing by one prime q: by section1 the chance that the larger ghost selects this new q by T is <=T/q^2, and otherwise the two truncated sequences coincide. Sum over all q and use the first Borel-Cantelli lemma. More quantitatively,
    Pr(any finite cutoff >=Z disagrees with the Z ghost through T)
       <= T sum_(q>=Z prime) q^-2
       = O(T/(Z log Z)).
All cutoffs here mean alphabets with p<cutoff; the adjacent comparison includes insertion of each q>=Z exactly once. The stabilized path equals the infinite path up to T, by its local deterministic clock definition (or induction over event times using finite candidate sets). Thus the same error bound holds for coupling the infinite path and every finite larger cutoff simultaneously. The factorial bounds also pass to infinite first-discovery counts for labels >=Z on a fixed time window. This gives a genuine uniform local limit, but NOT a limit for complete finite paths at elapsed times of order Y log Y.

## 4. Exact distribution of the next high clock at a frozen lower terminal

Condition only on the complete lower alphabet p<Y and parity; do not condition on absence of high events along its path. At its terminal attained state (G_*,E_Y), hold the horizon fixed and consider the next valid clock among all q>=Y. Call this waiting time W_Y^term. Because the lower terminal is a function of lower residues, the two residues of each q>=Y remain independent uniform. This is true for every lower terminal state, including E_Y=0. This random variable is a hypothetical next clock at the frozen state; it is the actual infinite ghost next wait only when the infinite trajectory followed the lower trajectory to terminal.

For S>=0 integer, the number of distinct initial residue pairs for q realizing a valid clock in the next S integer times is exactly
    b_q(S)=min(q,floor(S/2))+min(q,ceil(S/2)).
Proof: for each parity the horizon residue is fixed, and the successive times of that parity give distinct clock residues until q occurrences. The two parities use different horizon residues. It is independent of the starting parity and absolute starting offsets. Therefore
    Pr(W_Y^term>S | lower residues, parity)
       = product_(q>=Y prime)(1-b_q(S)/q^2).
The infinite product converges for each finite S, since b_q(S)<=S and sum q^-2 converges. W_Y^term is finite almost surely, since infinitely many high primes are eligible at the lower terminal.

Use the classical Mertens reciprocal-prime asymptotic sum_(p<=x)1/p=log log x+constant+o(1), and the elementary prime-count upper bound. For fixed u>1 and S=floor(Y^u), primes Y<=q<=S/2 have b_q=2q and contribute logarithm
    sum log(1-2/q) = -2 log u + o(1)
since the sum of squared reciprocal errors tends to zero. Primes q>S/2 contribute absolute logarithm O(S sum_(q>S/2)q^-2)=O(1/log S)=o(1) (for the finite boundary floor/ceiling the same estimate applies). For u<=1 and positive fixed u, total logarithm tends to zero by S sum_(q>=Y)q^-2=O(1/log Y). Hence
    lim_(Y->infinity) Pr(W_Y^term>Y^u) =
        1       for 0<u<=1,
        u^-2    for fixed u>1.
Equivalently log W_Y^term/log Y converges in distribution to the Pareto law supported on [1,infinity) with tail u^-2. For any fixed A>=0, Pr(W_Y^term<=Y(log Y)^A)=O((1+log log Y)/log Y)=o(1); apply the same product split, using a reciprocal prime sum over the near-top band and the large-prime clock tail. This is much longer than the typical local spacing suggested by summing the single-time clock probabilities: repeated clocks at a frozen horizon do not give independent new chances of horizon divisibility.

Relating this frozen-state law to the actual infinite path requires control of previous interference. Conditional on lower path, the probability any extra high label interrupts before or at its last executed event is <=min(1,E_Y sum_(q>=Y)q^-2) (ties with lower events lose). This is the preterminal part of section2, and no terminal eligibility term is needed for it. Hence if E_Y<=T, discrepancy costs at most O(T/(Y log Y)) in probability. In particular if E_Y=o_p(Y log Y), then the frozen-terminal law would describe the actual next infinite event with probability 1-o(1). This hypothesis is not established; the product law is exact for the frozen terminal unconditionally, not for the next event at an arbitrary adaptive high-exposed state. It cannot be used circularly to assert that finite lower ghost durations are small. This makes the distinction between late first discovery, postterminal waiting, and repeated selection explicit.

## 5. Exact finite tests

Saved research/min_ghost_first_discovery_coupling_audit.mjs and research/min_ghost_first_discovery_coupling_results.json, exact remote readback at 81eb5ba076f5d825d92aa49de9cb08c10b6073d7. Exhaustive full rectangles for (Y,Z)=(7,5),(11,5),(11,7),(13,5),(13,7),(13,11), with largest Y13 rectangle 2668050 phases, relative time cutoffs 4,8,16,32,64,128. For each lower phase calculate exact bad-pair sets by enumeration, multiply integer numbers of good assignments, and compare sums to actual complete path equality and no-high-by-T frequencies in the full rectangles. Verify full agreement implies equal E,G,D, per-prime bad-set cardinalities, time coupling bound and actual factorial moments and tails against the elementary-symmetric bound. Counts are exact integers; derived probability comparisons use floating point tolerance. No original full MIN source population is resimulated in these audits; they concern the uniform finite ghost model.

Examples at Y13, Z5 (extra labels 5,7,11):
    complete agreement = 0.3110949945;
    by T=4 Pr(J>=1)=0.2151290, bound0.2746905;
           Pr(J>=2)=0.0109893, bound0.0157868;
           Pr(J>=3)=0.000100823, bound0.000161916.
    by T=8 Pr(J>=3)=0.00125485, bound0.00226682.
At Y13,Z11 (only added11), complete agreement0.7621926126, no-extra-selection by T16=0.8882371020. Complete agreement products equal the full-rectangle counts in every tested pair. These finite cases do not test the asymptotic near-top scale.

Saved research/min_ghost_terminal_clock_gap_audit.mjs and research/min_ghost_terminal_clock_gap_results.json, exact remote readback at 7e32b6f65abe098a8508df5a3e07547c626a642a. Verify b_q(S) against exact enumeration of q^2 residue pairs at both parities for q=3,5,7,11,13,17,19,23 and ten choices of S around q and 2q (160 checks). Numerically evaluate the frozen-state product through prime cutoff Q=10^7. For the omitted factors use union bound S sum_(q>Q)q^-2, dominated by the coprime-to-30 integer sum, <= (8S/900)(1/b0^2+1/b0) with b0=floor(Q/30). Proof: each block [30b,30b+30) contains eight coprime residues, denominators >=30b, and sum_(b>=b0)b^-2<=b0^-2+b0^-1. Thus if P_Q is the finite product, the infinite product is between P_Q max(0,1-tailBound) and P_Q. The analytic omitted-factor bound is rigorous; the displayed numerical endpoints use ordinary floating point, not interval arithmetic with directed rounding.

Examples: Y1597, S=11779=floor(Y log Y), product approx [0.5883400,0.5885249]; at S63820=floor(Y^1.5), approx [0.4254030,0.4261282], limiting4/9. At Y10007,S92174=floor(Y log Y), approx [0.6197653,0.6212924]; at S1001050=floor(Y^1.5), approx [0.4192645,0.4307637]. These are frozen-terminal probabilities, not actual path-duration tails. In particular convergence to 1 at the Y log Y wait scale is very slow in these finite examples. No claim of numerical certification of a complete ghost tail via the product.

## 6. Remaining target

The preceding clipped-potential theorem needs D_Y/(Y log Y)->0 in probability along a diverging sequence (or a smaller leakage condition). A sufficient stronger condition is E_Y=o_p(Y log Y), since D_Y<=2E_Y. New first-discovery factorial bounds control fresh large labels on a prescribed elapsed window and give a uniform infinite-alphabet local coupling; the exact frozen-terminal waiting law isolates the next high clock when lower termination has occurred. Neither proves the needed elapsed or signed-drift tail, because a long path may repeatedly select known smaller primes. A concrete continuation is to control the time spent by such paths with a small number of fresh labels in each upper band, using exact recharge congruences and the existing LOW-block bounds rather than treating every event as a fresh independent trial. The separate far physical merge upper bound remains necessary. No new branch, no main edit, no Lean compilation, no claim of twin-prime proof.
