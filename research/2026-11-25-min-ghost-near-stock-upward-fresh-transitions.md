# Near-eligibility stock and upward fresh-to-known transitions without a ratio bound

2026-11-25 JST. Continues 8ac29afa535a1fae379ef9d97053177aa79a4760 on the SAME research/min-cycle-forest-2026-11-24 branch. Original uniform selected-stock concentration and upward transition estimate. Uses the established exact CRT tick-history law, elementary prime counting, and earlier comparable-transition and weighted rough-return bounds. Exact finite path diagnostics. No external search, no Lean compilation. This removes positive repeat steps immediately following sufficiently large fresh labels irrespective of their upward ratio, but does not settle arbitrary known-only runs or the long-gap record residual. No twin-prime proof.

## 1. Setup and a fixed-target stock counting lemma

Use the common CRT ghost, infinite alphabet or finite initial segment of odd primes. At each executed event p, the relative even horizon gain g increases by p-1, elapsed wait w<=2p, and signed attained height is 2s-g. Fresh means first selection since original time zero. The exact tick-history law implies that at any tick through U, every unused prime p>=z0=ceil(sqrt(2U)) has conditional first-selection hazard <=2/p^2. All probability statements below refer to this ghost, not the actual integer weighted forest.

Choose LOW cutoff A>=5 with L=L_A=2 product_(3<=ell<A)ell<=log^(1/8) U for all sufficiently large U, tending slowly to infinity. In the HIGH subsequence, consecutive labels have intervening LOW gain d even, 0<=d<L, regardless of their waits or number. For positive peak analysis use the prefix with POST-gain<=2U (truncate before first event whose post-gain exceeds it). Since g is nondecreasing, every positive attained peak lies in this prefix. A known label appearing before or in that prefix is <=2U+1. Every event weight p is <=1.5(p-1), so the sum of p in the gain-capped prefix is <=3U. This is useful on exceptional events and avoids needing an expectation of unrestricted gain.

For each fixed integer G in [0,2U] and real dyadic bands [P,2P), [R,2R) starting at z0, with lower endpoints <=2U+1, define K_s(G,P,R) to count distinct primes p in [P,2P) first selected at ticks strictly before s, with first pre-gain u_p satisfying
    u_p <= G-P+1,
    p divides G-u_p+a for at least one integer a in [R-3,2R+L+1].
The shift a here is an integer containing a candidate fresh label plus LOW gain and sign correction; it is not the earlier {-2,0,2} offset itself. All u_p are nonnegative integers. The stock count is monotone in s for fixed targets. The separation condition is essential.

At a tick with pre-gain u, a new ticket for this fixed stock must satisfy u<=G-P+1. For every permitted a, the integer G-u+a is strictly positive (P>=z0, R>=z0) and O(U) uniformly, since G<=2U, a<=2R+L+1 and u>=0. It has O(1) distinct prime divisors >=P>=sqrt(2U), by the product bound on its prime factors. Thus at most O(R+L+1) candidate primes can add a ticket at this tick. The candidate set is measurable from the past and the fixed target. Their total conditional first-selection probability is <=C(R+L+1)/P^2, with absolute C, even if this upper bound exceeds one. At most one label can be selected at a tick.

For completeness, write I_s for the indicator of a stock addition. By iterated conditional expectation,
    E exp(sum_(s<=U) I_s)
       <= exp((e-1) C U(R+L+1)/P^2).
Indeed E(exp(I_s)|past)<=1+(e-1)C(R+L+1)/P^2. For fixed G,P,R this proves by exponential Markov
    Pr(K_(U+1)(G,P,R)>B_(P,R)) <= U^-6
for B_(P,R)=C1[log(2U)+U(R+L+1)/P^2] with a sufficiently large absolute C1. There are O(U log^2 U) fixed target triples. Thus, except on an event of probability O(U^-4) (enlarge constants for small U),
    K_s(G,P,R)<=B_(P,R)                         (1)
SIMULTANEOUSLY for all such targets and all s<=U+1. We did not condition on future success of (1) in applying the history hazard. The concentration concerns random first-selected stock, not all primes eligible near G irrespective of selection. In particular the estimate does not require an independence assumption on known-label coordinates.

## 2. Actual upward fresh-to-known pairs and stock containment

Let q,p be consecutive high events (all intervening labels <A). Suppose q is fresh, p repeated, p>F q, q>=z0, where F>=4. Restrict both events to the post-gain-capped prefix. The first selection of p necessarily precedes q: p!=q, and p>=A cannot first appear in the intervening LOW run. Let G be the pre-gain at the q event. Then u_p+p-1<=G. With sigma0 the eligibility sign of p at its first selection, sigma1 its sign at the specified repeat, the fixed horizon coordinate gives
    p | G-u_p+q-1+d+sigma0-sigma1.               (2)
Let q belong to [R,2R) and p to [P,2P). Then P>F R/2, and the offset q-1+d+sigma0-sigma1 is in [R-3,2R+L+1]. Also u_p<=G-P+1. Consequently p belongs to the actual known stock K_s(G,P,R) immediately BEFORE the q first-selection tick s. This is a necessary condition, not a sufficient test that the future p will be chosen.

Condition on the exact history before s. G is now known. For each of the K_s known p, for each possible even d<L and each sign sigma1, (2) fixes a residue for the prospective q modulo p. Since P>F R/2>=2R, the band [R,2R) contains at most one integer candidate q per residue. Even ignoring primality, there are O(L+1) candidate q for each p. Each has hazard <=2/R^2. Giving it a ticket of weight p<=2P yields an expected potential weight at tick s in this pair of bands of at most
    O((L+1) P K_s(G,P,R)/R^2).                  (3)
The next actual high p, if any, consumes at most one ticket. There is no need to regard p as unused again or to limit the time since its first selection. q can initiate at most one actual qualifying pair.

Let z satisfy z0<z<=2U+1. Count W_up(U;F,z), the sum of p over such upward fresh-to-known pairs with p<z, q>=z0 in the capped prefix. For the expectation on histories satisfying their local condition K_s<=B_(P,R), bound (3) by inserting B_(P,R). This is legitimate because the local condition is measurable BEFORE the q selection. In particular we DO NOT condition the hazard on the simultaneous good event (1), which depends on future selections. Every actual pair on that good event is covered by these tickets; on its complement, W_up<=3U by the gain cap. Thus
    E W_up <= O(U (L+1) sum_(R>=z0 dyadic) sum_(F R/2<P<z dyadic)
                          [P log(2U)/R^2 + U(R+L+1)/(P R^2)])
               + O(U^-3).
All actual pair bands are included even if p falls in a band partly above z. Since R>=z0>>L, geometric sums yield
    sum_R 1/R^2 = O(1/U),
    sum_(P<z) P = O(z),
    sum_(P>F R/2) 1/P = O(1/(F R)).
Hence the main new unconditional expectation bound is
    E W_up = O((L+1) z log(2U) + (L+1) U/F) + O(U^-3).     (4)
No lower bound on q beyond sqrt(2U), no upper bound on the upward ratio, and no bound on the first-to-return distance of p is required. We used a post-gain cap and p<z, unlike the earlier comparable-pair theorem, which was uncapped and uniform in p but needed p<=Fq. The term (L+1) z log U comes from the uniform concentration floor. It is not a bound for all p up to 2U when L is growing.

## 3. Combined deletion of positive increments after large fresh labels

Use the high-poststate scan of research/2026-11-25-min-ghost-corrected-height-record-erasure.md (J=2s-g_post-6chi). At a repeated high event p, let a_i=J_i-J_(previous HIGH poststate) be its corrected change, including its preceding LOW run. For any p>=A,
    a_i^+ <= (4+(5L+6)/A)p.
For p>=10L+14, a_i^+<=2w<=4p and a_i^+>0 implies w>p/4. These estimates apply to all actual steps, and therefore to the subset retained by backward record erasure. Define E_next as the sum of a_i^+ over repeated high steps in the capped prefix whose previous high event q is fresh and q>=z0. For the analogous all-fresh predecessor statement restricted to comparable p<=Fq, q may be smaller than z0.

Use three disjoint cases.
* p<=Fq: earlier research/2026-11-25-min-ghost-fresh-to-known-comparable-repeat-chains.md gives expected p-weight O(F(L+1)U/log U), valid at all q. Multiply by O(L+1) to bound positive corrected changes by O(F(L+1)^2 U/log U).
* p>Fq, p<z, q>=z0: theorem (4). Here p>=F z0>>10L+14, so use a_i^+<=4p WITHOUT an extra L factor.
* p>Fq, p>=z: earlier weighted rough-return sieve, research/2026-11-25-min-ghost-weighted-return-sieve-first-span.md. For z eventually >=10L+14, positive a_i requires w>p/4, and its weight is bounded by four times the earlier W_z. This is true regardless of q, including q<z0. The earlier pre-gain cap contains the present post-gain prefix.

Choose F=max(4,log^(1/4) U), z=ceil(U/log^(5/2) U), L<=log^(1/8) U. These choices eventually have z>z0 and L->infinity by slow choice of A. The three contributions divided by U are respectively
    O(log^(-1/2) U),
    O(log^(-11/8) U + log^(-1/8) U),
    O((log log U)^3/log^(1/2) U).
All vanish. Thus
    E E_next = o(U).
More strongly the union of the following sets of repeated high steps has expected positive increment o(U): all with p<=Fq after ANY fresh high q; all with q>=z0 after a fresh high q (NO ratio restriction); and all with p>=z by the weighted long-return bound. The result includes long first-to-return spans and sparse single returns, not just local multi-rough clusters. It does not require the repeated label's corrected height to be a record, so applies to the earlier signed erasure remainder in particular.

Combine with earlier deletions by dropping these additional positive increments once from R_res. The disjoint negative credits C,Nminus are unchanged. The previous inequality E[(D(U)-[R_res-C-Nminus]_+)_+]=o(U) stays valid with this smaller residual, by [x+y]_+<=[x]_++y for y>=0. This controls an upward ratio failure at the first repeated HIGH step of a run anchored at a sufficiently large fresh q. It does not control all later steps of the run: in particular a transition from an already repeated high label is not a fresh-to-known transition, and a later comparable chain after a top p with negative drift cannot be treated as having small total p-weight merely because its first increment is nonpositive. Also q<z0 followed by Fq<p<z is not controlled by (4). These are explicit remaining cases. The full signed peak convergence, long-gap record resource allocation, and independent physical far-coalescence upper bound remain open.

## 4. Finite diagnostics and persistence

Saved research/min_ghost_near_stock_upward_transition_audit.mjs and research/min_ghost_near_stock_upward_transition_results.json; exact remote content readback at 9d54bd65546c0399e10d8e47c0d18f2f438e176a. Run node research/min_ghost_near_stock_upward_transition_audit.mjs 256 1024 4096 16384 65536. Fixed pseudorandom independent CRT coordinates, finite initial alphabet <=4U, A5,L6,F4. 256 paths per U except 128 at largest U. Diagnostic root=ceil(sqrt(2U)), base=max(7,floor(root/8)), z=max(root,ceil(U/log^2.5 U)). The latter equals root at these finite scales, so the analytic upward range with q>=root and p<z is empty in this diagnostic suite. Diagnostic base below root permits nonvacuous arithmetic checks, not an application of the analytic hazard bound at base. The earlier finite-to-infinite coupling error O(1/log U) is asymptotic, not a calibrated sampling error.

For each fresh high q>=base at pre-gain G<=2U, enumerate previously known p>=Fq with p<=2U+1, exact eligibility tickets for all even d<L, and the enclosing near-stock divisor condition at the diagnostic dyadic bands. Check separation u_p<=G-p+1 and positivity of G-u_p+a in the candidate offset interval. Check exact ticket containment in near stock. For actual capped fresh-to-known upward transitions (p>Fq), verify the low gain, divisor condition and ticket containment whenever q>=base. Record actual preceding-LOW uncorrected positive signed change for diagnostics (not the exact parity-corrected a_i of the theorem). Verify LOW-only bounds and partition of upward pairs by predecessor root threshold.

At U16384: 12767 executed events,1625 actual capped fresh-to-known pairs,8 upward pairs (all with q<root182),6 long-wait upward pairs, total upward p-weight782. Two actual upward pairs have q>=diagnostic base22 and pass the full ticket/divisor test. At U65536:8545 events,1045 capped fresh-to-known pairs, no upward pairs,3 exact candidate tickets checked for stock containment,273155 positive-divisor-target checks; max diagnostic stock2 over all five windows. No actual upward pair with q>=root in this sample suite. The tests exercise arithmetic structure but do not numerically estimate the concentration tail, asymptotic constants, or the new expectation in the analytic range. No Lean compilation.

## 5. Next target

This replaces a ratio restriction at a class of actual first-fresh transitions by a uniform selected-stock concentration argument, using the nonzero divisor target forced by the earlier p gain. It does not solve the full sparse-record gap allocation problem: the next useful input would control smaller fresh predecessor q or transitions between already known labels, without falsely restoring their fresh hazards. No main edit, no new branch, no twin-prime proof.
