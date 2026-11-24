# Discovery cylinders, uniform finite-palette theorem, and finite-window early discovery bounds

2026-11-24 JST. Continues eb350115d5fe904b7b034b6871a1c3e68a76602e. New paper theorems and finite audits; no new Lean compilation. Twin-prime infinitude and the aggregate full-length return/occupation estimate remain OPEN.

## 1. A discovery key reconstructs the whole prefix

Use the canonical MIN with original odd roots M in [X,2X), B=ceil(sqrt(7X)), initial t=M+2,C=2M-2, K(M)=floor((7M-1)/4). The relative state is (s,G) with t=M+2+s,C=2M-2+G. Fix LOW S={3,5,7}, L=2 product(S)=210; the arguments work with any fixed finite set S of odd primes. Regard the residues at all primes in S as known even if not selected. A discovery is the first occurrence of a prime outside S. A key records M mod L and the ordered sequence (p_i,M mod p_i) of discoveries, without their times or intermediate repeated labels.

For a key realized by an actual trajectory, reconstruct its prefix by adding p_i to the previous known pool and following that restricted MIN until p_i first wins. Before this discovery no other unseen label can win; removing all such labels therefore leaves the actual choices unchanged. The known-pool candidate clocks depend only on the known residues and relative (s,G), so a key uniquely fixes the whole relative transcript through its last discovery. Each original cutoff still has to permit the transcript. This is not a claim that arbitrary keys are consistent; the competition exclusions in the preceding transcript note still enforce consistency.

From this prefix let the known-only shadow run (without the original cutoff, or with a chosen common relative horizon T). At each shadow plateau and unseen p, only two residues of M mod p can make p eligible. If the candidate pair (relative time,p) is earlier than the next known-only pair (lexicographic, including ties), record the earliest such pair for that residue. At the final plateau allow the candidate within T, if a cutoff is used. Write R_p for the residue set of recorded interventions and b_p(a) for the first pair. The next real discovery is exactly the minimum of the recorded b_p(M mod p), restricted to the original cutoff. This follows by the first departure from the known-only shadow. The shadow terminates by the even-multiple barrier, so its final plateau is included even without a time cutoff.

Let A_p be the allowed residue sets of the previous transcript, with the initial low residues also fixed. Conditional on the realized key and a uniform complete CRT period, the exact probability of NO further discovery before a common relative time T is
    product_(p unseen) (1 - |A_p intersect R_p|/|A_p|).
No probability independence on the actual short interval is claimed. On an actual cell with selected modulus D=product of known primes (including S), the number of roots for which a particular p can intervene is at most
    |A_p intersect R_p| * (1 + X/(2 D p)).
This counts compatible odd residue classes modulo 2Dp, irrespective of additional exclusions; division by the actual cell size is not generally justified by the complete-period probability.

## 2. Explicit two-high-label obstruction (new elementary theorem)

Consider any consecutive admissible horizon segment, with arbitrary initial even horizon, not necessarily the MIN clock. Its labels outside S are drawn from two distinct primes p<q, both >4L+10. Between consecutive outside-S labels the low gain is even and <L by the fixed-prime barrier. No adjacent outside-S occurrences of the same prime are possible: a return to p after its own gain p-1 and low-only gain e<L would require p | p-1+e+sigma'-sigma, an even positive multiple of p (hence >=2p) while the expression is <2p. The same for q. Thus the high word alternates.

If at least four high events occur, both a p-return and a q-return occur. For consecutive occurrences of q the intervening total including the two high gains and the two low blocks is
    p+q-2+e_q+sigma'_q-sigma_q,
with 0<=e_q<2L, an even positive multiple of q smaller than 4q, hence equal to 2q. This gives q-p<=2L. The analogous p-return expression is consequently smaller than 4p (p>4L+10), hence equals 2p. For every successive return of either label,
    e_p = 2-(q-p)+sigma_p-sigma'_p,
    e_q = 2+(q-p)+sigma_q-sigma'_q.
Nonnegative e_p forces q-p<=4. The even difference is either 2 or 4.

If q-p=4, summing across m consecutive p-gaps yields sum e_p=-2m+sigma_first-sigma_last>=0, so m<=1. There are at most two occurrences of p, hence at most five high events. If q-p=2, the low gain in the entire interval from first to last p is <=2 by the same telescoping identity. Every q-gap has low gain >=2; two successive q-gaps have total >=6. If that p-span contained three q occurrences, their two successive gaps would contradict its total low gain <=2. Therefore at most seven high events; if seven occur, the word starts and ends with q. In particular six or more high events force q=p+2, which themselves are twins. Eight or more are impossible.

This is a contiguous high subword with all intervening events in S, not a subsequence obtained by deleting arbitrary other primes. For fixed S and arbitrary two high primes the total number of events is also uniformly bounded: if one p is <=4L+10, fold it into S; the new low modulus is one of finitely many constants. A second high q above that modulus+1 occurs at most once; if smaller then all labels belong to a fixed finite set and the barrier bounds total length. No claim that seven applies to that small-prime case.

## 3. NEW uniform finite-palette theorem (arbitrary fixed number of distinct labels)

The explicit two-label theorem above suggests a more general structural property. We prove:

**Theorem.** For every fixed finite set S of odd primes and every fixed k>=0, there exists H(S,k)<infinity such that EVERY admissible consecutive horizon segment using at most k distinct odd primes outside S has at most H(S,k) outside-S events, independently of the sizes of those primes, the initial even horizon, and all clock choices. In addition its total number of events is bounded by a constant depending only on S,k.

Eligibility means p|(C+sigma), sigma in {-1,+1}, with the exact update C<-C+p-1. Only these conditions are used. The low-only barrier for any fixed S gives gain <L(S)=2 product(S), and at most L(S)/2 low events between high events. For S empty the barrier statement is trivial.

Proof by induction on k, simultaneously for all fixed finite S. k=0 is immediate; k=1 follows from the fixed-low barrier and the return condition: when the one outside prime p>L(S)+1 it cannot recur, otherwise fold p into one of finitely many enlarged low sets. Suppose the theorem holds for k-1 for every fixed finite S, and counterexamples of unbounded high length exist for fixed S,k, k>=2. They must use exactly k outside primes. Sort them p_{1,n}<...<p_{k,n}. If some p_{i,n} is bounded along an infinite subsequence, pass to a fixed prime q outside S, and fold it into S'=S union {q}. The inductive bound H(S',k-1) bounds the number of other high events. Between them, S'-only blocks have bounded gain and number of events, contradicting unbounded high length. Hence, after taking a subsequence, every p_{i,n} tends to infinity.

Let h=H(S,k-1). In every high word, each block of h+1 consecutive high positions must contain every one of the k labels; otherwise the corresponding admissible segment would use at most k-1 outside primes. Encode high positions by their label i in {1,...,k}, eligibility sign sigma, and the low gain immediately preceding them (even in [0,L(S))). This is a finite alphabet, since no low-only block can gain L(S). Diagonal extraction yields an infinite abstract word all of whose finite prefixes occur in the counterexamples for arbitrarily large n. Its labels satisfy the same bounded-gap property.

At high position a let n_j(a) count previous high occurrences of label j, g(a) be cumulative low gain up to the pre-horizon at a, and define the integer vector
    v(a)=(n_1(a),...,n_k(a),g(a)+sigma_a).
For each label i, fix its first occurrence a_i. Let V_i be the real linear span in R^(k+1) of all v(a)-v(a_i) with label(a)=i. These are rational subspaces generated by integer vectors, each with a finite integer basis from the defining set. For any finite such difference vector u and every sufficiently late counterexample containing that abstract prefix, eligibility at both positions implies
    p_{i,n} divides sum_j u_j (p_{j,n}-1) + u_(k+1).        (1)

The sequence v(a)/a is bounded because high counts sum to a-1 and each low block contributes <L(S). Choose a convergent subsequence with limit f. By bounded gaps every first-k coordinate of f is strictly positive (at least 1/(h+1)). For each i, choose occurrence b_i(a) within h+1 high positions of a. The coordinates of v(b_i(a))-v(a) are bounded in terms of S,h (including the sign difference). Thus along the chosen subsequence (v(b_i(a))-v(a_i))/a tends to the SAME f. Since V_i is closed, f belongs to every V_i.

The intersection V of these rational subspaces is rational. It contains f with all first-k coordinates strictly positive, so it contains a rational vector with the same strict positivity, by density of rational points in a rational basis. Scale it to an integer vector u with u_j>0 for j<=k. Express u in each finite defining basis of V_i over Q and clear the denominators d_i. The integer vectors d_i u are fixed finite combinations of differences appearing in one sufficiently long prefix. For all sufficiently late counterexamples, (1) gives
    p_{i,n} | d_i F_n,   F_n=sum_j u_j(p_{j,n}-1)+u_(k+1).
Since p_{i,n}->infinity and d_i are fixed nonzero integers, p_{i,n} does not divide d_i eventually. Thus product_i p_{i,n} divides F_n. But F_n is positive eventually and O_u(max_i p_{i,n}), while product_i p_{i,n}/max_i p_{i,n}->infinity for k>=2. Contradiction. This proves the uniform high bound, and the low-block barrier supplies a total-event bound. QED.

The proof can be made effective in principle: assuming the preceding inductive constant h, enumerate finite abstract words with the bounded-gap condition. At each prefix compute the rational spaces and test whether their intersection contains a vector with first k coordinates positive (scale to >=1, a rational linear feasibility problem). Any infinite bounded-gap word has a finite such certificate by the same limit proof and finite-dimensionality. The finitely branching tree of prefixes without a certificate is therefore finite by Koenig's lemma. For each certificate the denominator and positive-vector bounds above give a computable finite threshold beyond which all primes cannot lie. Take the maximum over certificates and handle the finitely many smaller primes by folding into S and invoking the k-1 bound. This is an existence/effectivity argument, NOT a practical estimate for growing k.

For a MIN segment with B as prime cap the total gain of a fixed-palette segment is O_(S,k)(B), its elapsed time through its last event is at most three times gain, and its known-only shadow has a uniformly bounded NUMBER of plateaus. A non-twin terminal needs elapsed time of order X (except at most 2B for the final quiet tail), so for every fixed k and all sufficiently large X, a non-twin original source must discover more than k distinct outside-S primes. This is not a uniform lower bound of the necessary order B/log B on discoveries; k must grow to solve the main problem.

## 4. Finite-window aggregate CRT bound without conditioning on sparse cells

The uniform theorem gives, for fixed k, a constant bound on both the number of events in any history with <=k known outside-S labels and the number of plateaus of its known-only shadow. For any fixed ordered distinct discovery labels p_1,...,p_k and initial low residue class, each extension adds at most a constant C_(S,k) possible residues mod its next prime: there are at most two per shadow plateau. Each chosen residue determines its first intervention through the prior shadow. Thus the number of original sources realizing this sequence is bounded uniformly in the prime values by
    O_(S,k)( X/(p_1 ... p_k) + 1).                         (2)
Proof: bounded number of compatible residue classes mod L(S)*p_1*...*p_k; count roots in the interval in each class. Actual competition and cutoffs can only reduce this upper count. This is a direct aggregate finite-window estimate, not a conditional probability estimate.

Take Q=ceil(B/log^(2/3) B), B comparable to sqrt(X). Prime counting and partial summation give sum_(Q<=p<=B)1/p=O(log log B/log B), sum_(p<=B)1/p=O(log log B), pi(B)^2=O(X/log^2 B). Sum (2) for k=1,2. The number of original roots for which EITHER of the first two outside-S discoveries (if present) lies in [Q,B] is
    O_S( X (log log B)^2/log B + X/log^2 B ) = o(X).
Here for roots with only one discovery we use the k=1 bound. No lower bound on the size of any actual history cell is used. More generally for fixed k>=2, if the first k-1 outside-S discovery primes are <= Z=B^(1/(k-1)) and the kth lies in [Q,B], summing (2) gives
    O_(S,k)( X (log log B)^k/log B + pi(B) pi(Z)^(k-1) ) = o(X).
The unrestricted +1 term for k>=3 cannot be summed trivially over pi(B)^k sequences. The theorem's constants are not controlled when k grows. For the complete CRT period the same uniform shadow bound strengthens the prior per-event fresh-large hazard to O_(S,k)(log log B/log B) over the ENTIRE next known-only shadow when at most k outside-S labels have been discovered: the current transcript excludes only O_(S,k)(1) residues of each unseen p, and the shadow tests only O_(S,k)(1) further residues. This does not transfer unconditionally to all sparse actual cells.

## 5. Finite tests, actually executed

C++17:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_discovery_shadow_audit.cpp -o /tmp/min_discovery_shadow_audit
    /tmp/min_discovery_shadow_audit 256 1024 4096 16384 65536 262144 1048576
All seven full original windows and original cutoffs checked. The code independently reconstructs each prefix through up to the first three outside-S discoveries using the successive restricted pools; verifies the explicit two-large-label theorem for every maximal two-label high subword starting at each high position; checks the finite non-twin counts. Tested blob de778ad4811adcb9616340302c479f7c709f47e6, exact remote readback at c7872f899d70daf3032bc589480d5ab0b1ae12d7.

| X | full events | replayed prefix events | two-label start checks | both labels >850 |
|--:|--:|--:|--:|--:|
|256|1354|772|391|0|
|1024|4146|2367|1148|0|
|4096|30191|13156|9399|0|
|16384|161096|55727|50097|0|
|65536|796161|236179|262555|0|
|262144|3946588|976027|1337561|27|
|1048576|19219036|4027515|6565420|7535|

Maximum two-label subword length over all labels at these windows: 4,3,5,5,5,6,7. For both labels >850, maximum length in both applicable windows was only 2; no six-event case. At X=256 five non-twin sources, all had >=3 outside-S labels; all other sources end at twins. At largest X: 4,273,096 discoveries across all sources, max 41 distinct outside-S labels. These diagnostics do NOT show the long-trajectory regime or the uniform theorem's constants.

Python 3 (independent relative-clock implementation):
    python3 research/min_discovery_cylinder_audit.py 256 1024 4096 full
In the three finite windows use common relative cutoff T=3X/4-3, a little earlier than the earliest original cutoff, solely to isolate CRT distribution from variable cutoff. Group every root at discovery depths k=0,1,2. Reconstruct prefixes, check complete actual membership against allowed residue cylinders, enumerate per-prime earliest shadow interruptions, check next actual discovery, and compute the full-period product. The full-period test uses all odd residues modulo 30030 (primes through 13), common T=300. For every cell, actual cell size equals product of allowed set sizes and actual count of no new discovery equals the exact rational product prediction. All checks pass. Tested blob 25151102256a17136d79d9457d9812022321cc81, exact remote readback at a369ed61f20f1fe005b326343460fccc14d58de6.

| X | k | root count | cells | singleton cells | actual no next discovery | CRT conditional no-next sum |
|--:|--:|--:|--:|--:|--:|--:|
|256|0|128|105|82|27|37.938759|
|256|1|101|101|101|20|35.000178|
|256|2|81|81|81|27|32.034929|
|1024|0|512|105|0|131|114.972132|
|1024|1|381|381|381|106|99.524034|
|1024|2|275|275|275|95|78.399620|
|4096|0|2048|105|0|313|352.265629|
|4096|1|1735|1519|1303|296|340.155540|
|4096|2|1439|1439|1439|310|306.318378|
|30030 full|0|15015|105|0|9041|9041|
|30030 full|1|5974|565|0|4663|4663|
|30030 full|2|1311|1311|1311|1311|1311|

CRT conditional no-next sum weights the model's conditional probability at each cell by the observed finite-window mass of that cell; it is not an unconditional full-period model prediction. In X=4096 depth two every modulus 2D>=X and all 1439 cells are singletons. The explicit discrepancies illustrate why one cannot simply use conditional product probabilities on finite windows.

## 6. Next proof task

The uniform finite-palette theorem controls repeats only for a FIXED number of labels; the finite-window aggregate CRT argument handles initial discoveries only up to bounded depth or restricted products. Neither gives the required full clock budget R=o(X^2) or the energy estimate. The concrete follow-on is to seek usable growth bounds on H(S,k) (starting with k=3,4, and a quantitative rational-space certificate), and aggregate the actual discovery-cylinder residues across stages where Dp exceeds the interval length. In parallel test whether grouping by bounded sets of recurring labels rather than the entire historical set permits a uniform return-tail estimate. First-discovery weighted cost alone was already o(X^2); a successful proof must control many repeats in long trajectories, not simply prove the early large discoveries are rare. Main unchanged.
