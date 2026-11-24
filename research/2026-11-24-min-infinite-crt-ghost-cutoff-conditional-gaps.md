# Infinite CRT ghost, finite-time cutoff coupling, and conditional quiet-gap opportunities

2026-11-24 JST. Continues 447acd0cd16414a86c0dead5938415eae63266c5 on the SAME research/min-cycle-forest-2026-11-24 branch. Original probability/elementary arithmetic deductions, exact finite insertion/history audits, shared-residue finite sampling. No Lean compilation. The tail criterion of the clipped-height theorem and the physical far-merge upper bound remain open; no twin-prime proof.

## 1. One probability space for all LOW cutoffs

Choose one common initial time parity epsilon uniformly in {0,1}. Independently for each odd prime p choose (c_p,b_p) uniformly in (Z/pZ)^2; c_p represents the initial even horizon modulo p, b_p represents initial time modulo p. The shared parity specifies the time mod 2p. These are independent across primes; the whole infinite residue family need not be represented by one ordinary integer. At cutoff Y the restricted residues are exactly the uniform rectangle of even C mod L_Y and t mod L_Y used in the previous notes, by CRT. Work with relative integer time s>=0 and relative even horizon gain g>=0.

At each integer tick s>=1, on the currently frozen pre-event horizon g, a prime p matches iff its two coordinates equal the unique pair
    c_p = (+1 if epsilon+s even, -1 otherwise) - g mod p,
    b_p = (0 if epsilon+s even, p+2 otherwise) - s mod p.
Choose the least matching prime, and increase g by p-1; if none match keep g unchanged. With finite alphabet p<Y this is exactly the deterministic LOW ghost's earliest-clock rule, frozen forever once no eligible prime remains. Strict next time and smallest prime tie-break are built in. Let tau_Y be its final event time (0 if no events); finite by the LOW barrier. Its peak signed drift D_Y satisfies D_Y<=2 tau_Y, since gain is nonnegative.

The infinite-alphabet version is also well defined almost surely. For each fixed pair (s,g), the sum of matching probabilities over p is finite, sum 1/p^2<infinity, so only finitely many primes match almost surely. This holds simultaneously at all integer (s,g) by countability. Even without this fact any nonempty subset of primes has a least member. For any fixed g the eligibility events c_p+g=+/-1 are independent with probabilities 2/p and divergent total. By the second Borel-Cantelli lemma infinitely many are eligible almost surely. Again this holds at all possible integer g simultaneously. Every eligible prime has a finite next clock, hence the infinite process has a next event from every attained state and never has a terminal horizon. There is no accumulation of infinitely many events in a finite time, since each tick advances integer time and takes at most one event. This is a random CRT ghost, not a claim about infinite ordinary-integer MIN runs or uniformity of the actual source population.

## 2. Exact cutoff insertion and quantitative finite-time coupling

Fix cutoffs 5<=Y<V<=infinity and positive integer U. Condition on the lower alphabet coordinates and its entire tick-by-tick path up to U, including the frozen tail after natural termination. For an added prime p in [Y,V), form a forbidden set F_p of coordinate pairs from the displayed match rule at each tick s<=U where the lower process has NO event. At a lower event tick an added prime loses the tie, so those ticks are omitted. The horizon used in the match rule is the lower pre-event horizon. At each included tick exactly one pair is forbidden, so |F_p|<=U (and <=p^2). The two coupled paths agree up to U iff no added prime has coordinates in its forbidden set. Proof: first divergence, if any, must be an added prime at a lower no-event tick; until divergence all horizons and all lower candidates are identical. Conversely if a forbidden match occurs along the lower trace, at its earliest such tick it wins (possibly a smaller added prime wins instead) and creates divergence. This remains true after the lower ghost has frozen; restricting to the eventful prefix would incorrectly discard late added clocks.

Since the added coordinates are independent of the lower path and of each other,
    Pr(agreement through U | lower trace, epsilon)
       = product_(Y<=p<V) (1-|F_p|/p^2).
The infinite product is well defined, including the possibility of a zero factor for small p or large U. The formula uses full equality of event records, not just equality of final horizons. Therefore uniformly in V,
    Pr(divergence through U) <= U sum_(p>=Y prime) 1/p^2
                              = O(U/(Y log Y)).
This is a deterministic conditional union bound, with no independence assumption about successive steps of the adaptive lower path. In particular if U=o(Y log Y), the two paths agree with probability 1-o(1). We did NOT derive an analogous bound for their entire uncapped histories; the terminal frozen tail can eventually be interrupted in the infinite process. A related full lower-path formula uses the eventful prefix followed by a terminal eligibility test: at each added p the forbidden set also includes every t_p coordinate at the two eligible terminal horizon residues. Its union bound is O(tau_Y/p^2+1/p) per p; the finite-time version avoids this extra harmonic term and remains valid for infinite V.

For a single prime p in an arbitrary finite or infinite alphabet, delete it and condition on the path of the remaining primes through U. Before the first selection of p the paths agree. Allow all U ticks in the union bound (including ties where the deleted p may be smaller than a remaining label). It follows without independence of selected labels that
    Pr(p selected at least once through U) <= min(1,U/p^2).
Each selected p clock is in one of the two time classes mod 2p, 0 or p+2, so consecutive selected p events are separated in elapsed time by at least p-2 (for p=3 this is 1). The total number N_p(U) of selections of p thus satisfies
    N_p(U) <= 1{p seen}(1+floor(U/(p-2))).
Consequently the expected number of distinct selected primes is
    <= sum_p min(1,U/p^2) = O(sqrt(U)/log(2U)),
for U large, splitting at sqrt U and using the standard upper prime-count bound. For Q>=max(5,sqrt U), the expected total selections with p>=Q, including returns, is
    O(U/(Q log Q)+U^2/(Q^2 log Q)).
These are unconditional finite-time CRT ghost estimates, not uniform bounds on total lifetime or the ordinary canonical source sample. The first-selection inequality remains valid when other primes repeat arbitrarily. The return estimate does not say that all low-prime returns are sparse.

## 3. First long gap of the infinite ghost

Let sigma_Y be the elapsed time of the start of the first inter-event wait STRICTLY greater than 2Y in the infinite ghost, counting the initial time 0 as a possible start; set sigma_Y=infinity if no such wait occurs. The finite ghost whenever it has a next event has wait <=2p<2Y for some eligible p<Y. Couple both ghosts through U=T+2Y. On agreement,
    {tau_Y<=T} = {sigma_Y<=T}.
If finite ghost has stopped at tau<=T, the infinite ghost has no event through tau+2Y, so has a gap >2Y starting there. Conversely a gap >2Y starting at an infinite attained time s<=T implies the finite ghost has already terminated there, otherwise its next event would appear in the coupled window. The time endpoints are included in the coupling; strict >2Y is intentional. Thus
    |Pr(tau_Y>T)-Pr(sigma_Y>T)|
        <= (T+2Y) sum_(p>=Y)1/p^2
        = O((T+2Y)/(Y log Y)).
Since D_Y<=2tau_Y,
    Pr(D_Y>2T) <= Pr(sigma_Y>T)+O((T+2Y)/(Y log Y)).
In particular for T=floor(Y sqrt(log Y)), proving Pr(sigma_Y>T)->0 (along a diverging sequence suffices) proves the preceding clipped-potential probability condition D_Y/(Y log Y)->0 in probability along that sequence. This is a SUFFICIENT reformulation via quiet plateaux, not equivalence of D-tail and gap-tail (D can be small on a long path with negative drift). It is a distributional comparison of different cutoff models on the same probability space, with a rigorously vanishing coupling error. It does not yet show that a long gap occurs by T.

At a fixed, nonadaptive horizon/time the number of distinct forbidden coordinate pairs of p for a frozen interval of w consecutive future ticks is EXACTLY min(w,2p). Indeed a given pair repeats only after 2p ticks: offsets differing by p switch parity and hence the two different horizon residues; offsets not congruent mod p have different time residues. Therefore the unconditional fixed-state gap tail equals
    product_(p odd) (1-min(w,2p)/p^2) asymp 1/log^2(2w)
by the usual Mertens product bound for p<=w/2 and the summable large-prime contribution O(w sum_(p>w/2)1/p^2)=O(1/log w). This computation must NOT be used as an independent gap probability at each adaptively visited state. The next section gives the actual conditional law instead.

## 4. Exact conditional law given the adaptive selected-label history

Reveal epsilon and the whole selected-label sequence q_s (0 if no event) for 1<=s<=t; this includes the quiet ticks, not only event order. Relative horizon at each tick is determined by this sequence. For any compatible fixed history, form A_p subset (Z/pZ)^2 as follows:
- if q_s=0, exclude the unique matching pair at that tick;
- if 0<p<q_s, also exclude that pair;
- if p=q_s>0, require equality to that pair;
- if p>q_s>0, impose no condition at that tick.
Use the actual pre-event horizon along the specified history. This exactly describes the event of that history by induction over ticks. In particular the history event is a product of independent per-prime constraints. In the infinite alphabet each compatible positive-probability finite history has the same conditional product law: only finitely many primes selected, for other primes at most t exclusions, and the infinite product of remaining fractions converges to a positive value once all finitely many exceptional factors are nonzero. Equivalently derive via finite cylinder probabilities. Conditioning on this history, the coordinates remain mutually independent and uniform on A_p (selected coordinates have been determined). One may also reveal all coordinates of any fixed finite low-prime alphabet at time zero; the remaining history constraints still factorize conditional on these. Statements concern the ghost probability space, not the actual canonical sources.

For every previously selected prime |A_p|=1, because one selected tick fixes both coordinates. For every unused prime,
    |A_p|>=p^2-t.
Let F_p(w) be the forbidden pair set in the next w ticks with the CURRENT horizon frozen. The conditional probability of no next event in that whole interval is exactly
    product_p (1-|A_p intersect F_p(w)|/|A_p|),
using the revealed coordinates as singletons where applicable. Absence of all matches implies the horizon stays frozen; if a first match occurs it creates an event. This formula incorporates all correlations created by prior selections and quiet ticks. It is not a claim that A_p are full or uniformly positioned inside their respective rectangles.

For an unused p>=z with z^2>=2t and z>=5,
    Pr(p has a frozen-horizon match within w | history)
       <= min(w,2p)/(p^2-t).
In particular the probability that some UNUSED p>=z matches at a specified next tick is <=sum_(p>=z)1/(p^2-t)=O(1/(z log z)). This bound also holds after revealing all p<z initially. It is a conditional high-prime hazard estimate, unlike the preceding first-insertion union bound from time zero.

Suppose all PREVIOUSLY SELECTED p>=z are known not to match on the frozen horizon in the next w ticks. Then the conditional probability of absence of ALL p>=z in that interval is at least
    product_(p>=z prime) (1-min(w,2p)/(p^2-t))
       >= c exp(-C t/(z^2 log z)) (log z/log(max(z,2w)))^2.
Proof of the second inequality: compare with the product of 1-min(w,2p)/p^2. For z>=11 and t<=z^2/2, both factors bounded away from zero, so the loss in the sum of their logarithms is O(sum_(p>=z) min(w,2p)*t/p^4) <= O(t sum_(p>=z)1/p^3)=O(t/(z^2 log z)). Standard Mertens bounds on the truncated small-prime product and partial summation on the large-prime sum give the displayed lower bound. Including known quiet selected primes in the lower product only decreases it, so the bound is valid independently of their number. For w<2z the same argument gives a positive absolute lower bound. If any known selected high prime is scheduled in the frozen interval, this lower bound for total high quietness is NOT asserted (that conditional probability is zero). For small unused p with p^2<=t, the size bound gives no useful lower bound and their phase constraints cannot be ignored.

## 5. A sufficient opportunity-count target for the quiet-gap criterion

Fix 1/2<theta<1, z=ceil(Y^theta), T=floor(Y sqrt(log Y)), w=2Y. Reveal all coordinates p<z at time zero, and observe the selected labels and quiet ticks of the infinite process. At any integer time s<=T a candidate opportunity is the following pair of history-measurable conditions:
(i) no p<z is eligible at the current horizon (these coordinates are all known);
(ii) every previously selected p>=z has no matching clock in the NEXT w ticks at that frozen horizon (its coordinates are known from its selected tick).
Unselected p>=z are not revealed. These conditions can be checked from the partial history, without knowing whether the future gap really occurs. They apply even if the current time is within an existing quiet plateau rather than an event time. The preceding conditional bound applies with t=s<=T, since T/z^2->0, and log z/log(2w)->theta. Uniformly at such an opportunity the conditional probability of no event for the next w ticks is at least c_theta>0, for sufficiently large Y. If this succeeds, some inter-event wait >2Y starts no later than s<=T (integer tick convention).

Greedily test these opportunities in increasing time, waiting at least w ticks after each test before beginning the next. Let J_Y be the number of such tests with start times <=T, continuing this rule even if a test succeeds. Its success or failure is known by the next test, and each test time is a stopping time for the revealed history. The uniform conditional lower bound, applied successively, yields for every integer m>=1
    Pr(sigma_Y>T) <= Pr(J_Y<m)+(1-c_theta)^m.
To justify the last term, inductively bound the event that the first m tests all exist and all fail, conditioning at the m-th test start; the earlier failures are measurable there. No independence of tests is assumed. Therefore it suffices to prove J_Y->infinity in probability along a diverging sequence, or more generally Pr(J_Y<m(Y))->0 for some m(Y)->infinity. There is room for at most floor(T/w)+1 such tests, which does diverge slowly. This is a concrete conditional opportunity criterion; no estimate proving enough opportunities has been obtained. The known-coordinate conditions may fail because small labels remain eligible or previous high labels reactivate, and the preceding fresh-prime hazard does not eliminate those obstacles. In particular this is NOT a proof of the clipped-height tail condition. If established, it would remove small physical cell-stop residuals via the preceding theorem, with the physical far-merge upper bound still independently open.

## 6. Finite verification

Saved research/min_ghost_cutoff_coupling_audit.mjs and results JSON, exact remote readback at 1ac6de50bc8b6d95c6bff0b098ad5b9017757f3f. Exact single insertion at Y=p=5,7,11 for ALL lower horizon/time phases and ALL p^2 added coordinate pairs, using CRT lifts and independent finite traces. U=2Y+floor(Y sqrt(log Y)). Verify divergence iff the added pair belongs to the forbidden set on the lower trace including frozen tail; exact total divergence equals the sum of forbidden sizes. Results:
    Y=p=5, U16, 450 cases, 200 diverge (0.444444), union bound0.64.
    Y=p=7, U23, 22050 cases, 7265 diverge (0.329478), bound0.469388.
    Y=p=11,U39,2668050 cases,590194 diverge (0.221208), bound0.322314.
Also 2048 fixed-seed pseudorandom shared CRT samples for Y=13,53,199,397,797 and V=8Y, T=floor(Y sqrt(logY)), U=T+2Y. Compare original selected event records through T and U, verify divergence through T iff the larger ghost selects an added prime by T; on agreement through U check exact finite larger-ghost gap/finite lower-ghost terminal equivalence. Check clock spacing bound for every repeated prime count. For the first128 samples at each Y compute the entire conditional forbidden-set product for the finite larger alphabet. This is a finite cutoff comparison, not a sample of infinite CRT trajectories. At Y797,V6376,T2060,U3654: divergence through T531/2048, through U733/2048, agreement1315/2048 (all gap equivalence checks pass), lower tau>T51/2048, larger gap-start>T229/2048; finite union upper bounds0.306813 and0.544221, mean conditional divergence probability over128 lower paths0.360331 through U. The observed difference between the terminal and gap proportions is substantial at these finite scales; the analytic coupling error is only asymptotically small. The test does not prove infinite gap recurrence or a tail estimate.

Saved research/min_ghost_conditional_history_audit.mjs and results JSON, exact remote readback at 234f1ff7013247c6060ddc6b2c79462a69c1980b. Exhaustive full phase rectangles Y=5,7,11 (18,450,22050 states), t=4,10,25 and future frozen windows w=8,16,32. Group all actual finite alphabet initial states by common parity and exact sequence of tick labels including 0; reconstruct each A_p independently. Check product of |A_p| equals the empirical group cardinality, and product of |A_p minus F_p(w)| equals the exact count of continuations with no future event through w. Also check unused loss <=t, selected singleton, exact future forbidden count min(w,2p), and the finite unused-high product lower bound whenever known high primes are quiet. For Y11,t10,w16 there are1267 histories,13454/22050 full phases are quiet in next16 ticks; 504 unused-coordinate checks and3297 selected-coordinate checks,799 histories satisfy the tested known-high quiet condition at z5, min exact high quiet conditional probability 1/3. At t25,w32,5478 histories,19715 quiet continuations. These audits test the finite exact factorization and combinatorics, not the asymptotic Mertens comparison or the opportunity-count hypothesis. No original canonical stop trajectories resimulated in this turn.

## 7. Next task

The new conditional law exposes the actual effect of the adaptive history: every selected prime becomes known exactly, while unused large primes have at most t excluded residue pairs. This removes the need to assume independent low-ghost events. The remaining distributional problem is to count occasions when the known smaller labels and previously selected high labels cannot prevent a long quiet gap, or to bound low-ghost tail by another use of the exact history law. No claim of a complete stopping deficit. No main edit, no new branch, no Lean compilation.
