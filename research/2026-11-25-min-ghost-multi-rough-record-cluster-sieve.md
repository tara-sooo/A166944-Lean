# Multi-position rough-return sieve and local clusters of corrected-height records

2026-11-25 JST. Continues e98dc88d4b1612b78178062488d5032eb2340b61 on the SAME research/min-cycle-forest-2026-11-24 branch. New fixed-order multidimensional upper-bound sieve for repeated rough positions of the SAME selected label, including nearby strict corrected-height records arbitrarily far from its first selection. Finite exact local residue and path ticket diagnostics. No external literature search or Lean compilation. This deletes another class of positive record surplus, not all remaining repeats. A separate sparse-cluster count explains why this estimate alone does not improve the global b<3 threshold. No twin-prime proof.

## 1. Ticket definition and record-time consequence

Use the common CRT ghost (infinite alphabet or finite initial segment of odd primes), gain g increasing by p-1 at an event of p, completed wait w<=2p. Let U be the time horizon, z>=ceil(sqrt(2U)), and K>=1 an integer. Consider repeated events of a fixed p>=z through U, with pre-gain <=2U and w>p/4; call these long returns. Their pre-gains relative to its FIRST pre-gain g0 have the unique representations
    g_j=g0+m_j p+a_j, a_j in {-2,0,2}, m_j>=1.
All m_j<=(2U+2)/p. For p>=7, distinct actual return positions in order have strictly increasing m_j: the pre-gain gap is >=p-1, whereas at equal m the maximum offset difference is 4. Every such g_j has no eligible odd prime ell<=p/8, since otherwise its matching clock would arrive within 2ell<=p/4. All arguments are on the original trajectory, without restarting freshness.

Fix integer k>=2 independent of U. A local k-cluster endpoint is a long return whose preceding k-1 long returns of its own label form with it a consecutive sequence of k long returns with
    1<=m_(j+1)-m_j<=K.
Count each endpoint once, with weight p, and sum over p>=z to obtain W_(k,z,K)(U). A second version takes the consecutive sequence only in the SUBSEQUENCE of long returns which are strict same-label records of the corrected post-height J=2s-g_post-6chi (as in the preceding note). In either version, every counted endpoint injects into a distinct ticket (p,m_1,...,m_k,a_1,...,a_k) assigned when p is first selected. Different endpoints have different final actual pre-gain. The ticket is merely a necessary-condition tuple; we do not ask it to correspond to a legal clock-selected path. The sum of all realized endpoint weights is <=4U because w>p/4 and the completed waits are disjoint.

The record version also treats bounded ELAPSED gaps. If consecutive long record returns of p occur at times s_1<s_2, the lattice of the preceding note gives J_2-J_1>=2p. Let e=chi_2-chi_1, |e|<=1. Since p is unchanged, post-gain difference equals pre-gain difference, and
    g_2-g_1=2(s_2-s_1)-6e-(J_2-J_1).
In particular s_2-s_1<=H p implies g_2-g_1<=2Hp+6-2p. As g_2-g_1=(m_2-m_1)p+a_2-a_1, for p>=11 this implies m_2-m_1<=2H+1 (a loose integer bound). Thus the weight of endpoints of k consecutive long strict-record returns with each elapsed gap <=H p is bounded by the record-cluster version with K=ceil(2H+1). This uses a strict record to convert time locality into gain locality; no such conversion is asserted for arbitrary nonrecord returns.

## 2. Uniform (2k+1)-residue local sieve

Use the earlier weighted-return proof with L0=ceil(log^2 U), D=floor(U^(1/20)), R=U^kappa for sufficiently small positive kappa depending only on fixed k. Reveal initially all low coordinates for ell<=R and the common time parity. The claimed weights vanish for finite initial alphabets lacking labels >=z; otherwise all sieve primes are available. For large U, R<z/8.

For fixed g0 in [0,2U], m_j in [1,2U+2] distinct, offsets a_j in {-2,0,2}, and candidate integer label x in [Q,2Q), Q>=z, impose the necessary simultaneous rough conditions
    c_ell+g0+a_j+m_j x != +/-1 mod ell (j=1,...,k)
for all sieve primes L0<ell<=R. Also x mod ell !=0 (candidate x is a prime >R).

Omit primes dividing any m_j or m_i-m_j. For fixed k the sum of their reciprocals with ell>L0 is O_k(log U/(L0 log L0))=o(1): each nonzero factor has absolute value <=2U+2, so has at most log(2U+2)/log L0 prime factors in this range. For remaining ell each pair of neighbor conditions has two distinct roots in x; together with zero there are up to 2k+1 forbidden residues. A collision with zero is an equation c_ell+g0+a_j==+/-1 mod ell, restricting c_ell to one value. A collision between roots for distinct j,i is the equation
    m_i(sigma_j-c_ell-g0-a_j)
      == m_j(sigma_i-c_ell-g0-a_i) mod ell,
with signs sigma_i,sigma_j in {-1,+1}. Since m_i-m_j is invertible, this also restricts c_ell to exactly one residue. Thus for each fixed parameter tuple, the independent local horizon coordinates have collision probabilities <=C_k/ell, uniformly over nonomitted ell. The mean number of collision primes is O_k(log log U).

Using the elementary exponential-moment estimate for sums of independent Bernoulli variables, the probability of >=ceil(log U) collision primes is <=exp(-Omega_k(log U log log U)). There are at most O_k(U^(k+1)) tuples (g0, all m_j, all offsets); we may ignore gap restrictions in this union. Hence with probability 1-exp(-Omega_k(log U log log U)), the initially revealed low coordinates satisfy the collision bound for EVERY tuple. Call this event Good. It is independent of future selection success in the sense of being measurable at time zero; we do not assert independence from the actual path. On Good the total reciprocal mass of collision primes exceeds neither ceil(log U)/L0 nor o(1). Together with omitted factors this costs a bounded multiplicative factor in the local sieve product. We can discard collision primes completely for this upper bound.

The remaining forbidden residue count at each sieve prime is 2k+1, which is strictly less than ell for all large U. By the elementary Mertens harmonic-prime estimate,
    product_(remaining ell)(1-(2k+1)/ell)
       = O_k((log L0/log R)^(2k+1))
       = O_k(lambda_k(U)),
    lambda_k(U)=(log log U/log U)^(2k+1).
Apply exactly the Selberg quadratic majorant of research/2026-11-25-min-ghost-gain-capped-top-repeat-rough-sieve.md, section 3. The unrestricted divisor weights have expected log d <=(2k+1) sum_(ell<=R) log ell/ell=O_k(log R), so choose kappa small enough that at least half their mass lies at d<=D. The quadratic bound is at most twice the above product, and the remainder is O(D^6) (the proof only uses nu(d)<=d). As D^6<=U^0.3 and Q>=sqrt(2U), it is absorbed. Consequently, on Good, for every tuple and dyadic candidate band [Q,2Q) the count of candidate primes satisfies
    # candidates <= O_k(Q lambda_k(U)).
The dimension is five when k=2 and seven when k=3. Noninvertible slopes and equal slopes modulo ell cannot simply be treated as independent roots; their explicit omission and uniform control of collisions are needed for this estimate.

## 3. Expected local cluster weights

At a first-selection tick s, condition on the initially revealed low coordinates, parity and all previous tick history. Good and current g0 are measurable. For unused p>=z, conditional fresh hazard <=2/p^2, by the exact history law. If g0>2U, no relevant tickets are assigned. In candidate band [Q,2Q), Q>=z, there are at most O_k((U/Q) K^(k-1)) choices of (m_1,...,m_k) and offsets: m_1<= (2U+2)/Q and each later stride increases by 1,...,K; the offsets have 3^k choices. We may overcount invalid endpoints or excess last stride. There are no actual returns with p>2U+1. For each fixed tuple the preceding uniform sieve gives O_k(Q lambda_k(U)) candidate labels. Weight p times its first-selection hazard is <=2/Q. Thus conditional expected new ticket weight at tick s in this band, on Good, is at most
    O_k((U/Q) K^(k-1) lambda_k(U)).
Sum over the dyadic bands Q=z,2z,... through 2U+1, then U ticks. The geometric sum is O(U/z). By the pathwise ticket injection, and using realized weight<=4U on Good^c, this proves for BOTH the all-long-return and long-strict-record versions
    E W_(k,z,K)(U)
       <= O_k(U^2 K^(k-1) lambda_k(U)/z)
           +4U exp(-Omega_k(log U log log U)).
For z>2U+1 the realized weights vanish. There is no restriction on the first-selection-to-cluster span except the pre-gain cap, and no recovery of an unused-label hazard at a late return. This is a weighted estimate; it does not exclude occurrence of all clusters with probability tending to one.

In particular for fixed positive b,c satisfying b+c(k-1)<2k+1, choose
    z=ceil(U/log^b U), K=floor(log^c U).
Then E W/U=O_k((log log U)^(2k+1)/log^(2k+1-b-c(k-1)) U)=o(1), where the denominator means (log U) to the displayed exponent. Specific choices:
    k=2, b=4, c=1/2: normalized rate O((log log U)^5/sqrt(log U)).
    k=3, b=6, c=1/4: normalized rate O((log log U)^7/sqrt(log U)).
Both z eventually exceed sqrt(2U), despite the reverse ordering in small numerical windows. The result for elapsed-local strict records holds with H=floor((K-1)/2). Compared with the earlier weighted single-position result b<3, this reaches smaller labels for local MULTIPLE-return clusters only. It applies equally if every return in the cluster lies far beyond the earlier first-span cutoff.

## 4. Additional deletion in the signed record-erasure inequality

Use the prior high-poststate backward scan with LOW cutoff A slowly increasing, L_A<=log^(1/8) U. Its retained positive repeated steps have strict same-label corrected-height records and a_i^+<=2w_i<=4p whenever p>=10L_A+14, and positive a_i requires w_i>p/4. Every positive peak prefix has pre-gain<=2U. Thus the total retained positive repeated increment at endpoints of the above clusters (classify using original full-path history before each endpoint) is bounded by 4 W in the applicable range, and has expectation o(U) for the displayed parameters. Earlier record occurrences need not themselves have been retained by the backward scan; they are actual occurrences and certify the necessary rough conditions.

Let R_old be the residual after the previous deletions, and R_new remove additionally these local cluster endpoints (take the union, not a duplicate charge). For C,Nminus the unchanged disjoint negative credits,
    E[(D(U)-[R_new-C-Nminus]_+)_+]=o(U).
In the two-return choice, a remaining positive record repeat of p>=U/log^4 U must, unless already deleted, either have no earlier long strict-record repeat of that label or be separated from its preceding such repeat by a first-gain stride difference >K. Alternatively use the elapsed-local version: a remaining endpoint is the first long record return or has elapsed gap >floor((K-1)/2)p. In the three-return choice it must lack a previous chain of two long record returns with both local gaps. These are new necessary restrictions on the residual, not sufficient conditions for its contribution to be large. Smaller p and long-gap or short-chain residuals remain uncontrolled.

## 5. Sparse-cluster obstruction to a complete cost bound by this counting alone

There is a simple accompanying bound, useful for judging the scale of this approach. For each selected p>=z through the gain cap, the number of long-return endpoints NOT in a local k-cluster is <=(k-1)(1+(2U+2)/(Kp)): divide its ordered long-return list into runs separated by stride gaps >K, then only the first k-1 occurrences of each run are uncharged. There are at most 1+(2U+2)/(Kp) runs. This applies separately to the record subsequence. Therefore the remaining weight outside the clusters is <=
    O_k(sum_(p selected in [z,2U+1]) p
                  +(U/K) # {selected p in [z,2U+1]}).
Using the first-selection hazard, E of the first sum is <=2U sum_(z<=p<=2U+1) 1/p, and E of the count is O(U/(z log z)). For z=ceil(U/log^b U) with b fixed, prime counting by partial summation gives sum 1/p=O_b(log log U/log U). Thus the normalized sparse bound is
    O_(b,k)(log log U/log U + log^(b-1) U / K).
For power-log K=log^c U, making this latter term vanish requires c>b-1 (or more generally K/log^(b-1) U->infinity). Combining with b+c(k-1)<2k+1 for the dense cluster part yields b<3. Consequently the simultaneous rough-position sieve plus this unrestricted per-label sparse-gap bound does NOT by itself improve the old b<3 full deletion threshold. The newly controlled local clusters at b>=3 are genuine, but to control the remaining sparse records requires a sharper allocation of their time gaps or negative credit, not just taking more simultaneous rough conditions. No global sum of the narrow-band off-band resources has been proved. This is the specific missing step in using this method to establish the whole peak limit.

## 6. Finite audit and persistence

Saved research/min_ghost_multi_rough_record_clusters_audit.mjs and research/min_ghost_multi_rough_record_clusters_results.json; exact remote content readback at e646256de09c95f61d84467a5ce3990225f4afad. Run node research/min_ghost_multi_rough_record_clusters_audit.mjs 256 1024 4096 16384 65536. Fixed pseudorandom common CRT phases, finite initial alphabet <=4U; 256 paths per U except 128 at largest U. Diagnostic Q=max(7,floor(ceil(sqrt(2U))/8)), K=3, and rough tests at primes <=min(47,p/8). Also separately count at analytic minimum z0=ceil(sqrt(2U)). Diagnostic Q is deliberately below z0 to exercise structural cluster checks. These finite cutoffs and gap choices are not the asymptotic parameter sequence; the previous finite-to-infinite coupling error is asymptotic, not a calibrated sample error.

For sampled distinct slope tuples of size2 or3 enumerate forbidden residues x mod every odd prime ell<=47, check unique roots at invertible slopes, union size, and the exact linear collision equation between different slopes, separating noninvertible/equal mod ell cases. At each gain-capped first selection p>=Q enumerate all admissible rough pre-gains g0+mp+a, storing distinct positions and stride indices. Count all k-ticket tuples with successive stride gaps <=K. At actual long repeats check roughness and membership in the assigned positions; count endpoints of consecutive k-clusters in the complete long-return list and strict-record sublist. Verify per-path realized weighted endpoint sums <= candidate ticket budgets (also at z0), and <=4U. Check strict-record height gap >=2p, elapsed gap>=2p, and time-local implies gain-local stride bound. The code checks actual aggregate injection inequalities rather than explicitly storing/deleting every k-tuple. Distinctness follows analytically from endpoint and actual previous k-1 list positions. No numerical verification of the asymptotic sieve constant.

At U65536,N128: 7635 executed events, 37 long returns at diagnostic Q45 (29 strict long records), zero at z0=363; no local cluster endpoints at either threshold. 43008 local residue checks, 10425 noninvertible/equal-slope cases,12260 collision cases,20323 full-residue cases. At U1024,Q7, 611 long returns (409 strict records),48 two-cluster endpoints (21 strict-record endpoints),3 three-cluster endpoints (zero strict-record endpoints). At U4096,Q11,16 two-cluster endpoints (7 strict-record endpoints). Across the entire suite at z0 there were no observed local cluster endpoints, so nonvacuous injection diagnostics come from the lower thresholds and local residue tests. The conservative candidate tickets overcount heavily; e.g. at U65536 two-ticket weight at z0 is322764 while realized endpoint weight is zero. All checks pass. No Lean compilation.

## 7. Remaining work

The exact record lattice supports a multiple-rough-position sieve for local record runs even after long first-selection spans. The new proof controls that class at smaller label scales (b=4 and b=6 examples) and explains the obstruction in bounding sparse clusters by the total per-label span. Further work should control overlapping long record intervals jointly with the existing disjoint negative credits, or use different clock-history estimates for sparse long-return endpoints. Neither the full signed peak convergence eta->0 nor the separate actual physical far-coalescence upper bound is established. No main edit or new branch.
