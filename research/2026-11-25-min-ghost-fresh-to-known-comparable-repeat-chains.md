# Fresh-to-known high transitions and sublinear comparable repeat chains

2026-11-25 JST. Continues 497f8bd8274f97ff2bb2a9f2363882437ba52a0c on the SAME research/min-cycle-forest-2026-11-24 branch. New unconditional probability bounds for actual fresh-to-known high transitions at ALL label scales, independent of first-to-return span. Bounded-depth extension and deterministic initial-repeat deletion at small labels. Finite path audits. No external search, no Lean compilation. Neither the full signed peak limit nor the physical far-coalescence upper bound is proved.

## 1. Setting and the expected number of known labels

Use the common infinite CRT ghost, or any finite initial segment of odd primes, as in the previous notes. At an executed event, elapsed wait w<=2p, the nonnegative even relative gain g increases by p-1, and signed drift is 2w-(p-1). No physical height-nonnegativity assumption is imposed. A fresh event is the FIRST selection of that label on the entire path since time zero. A known label has already been selected. Its horizon/time coordinates are fixed by that selection and the recorded tick history.

Let U>=2 be the integer observation horizon and z0=ceil(sqrt(2U)). Let K_s be the number of distinct labels selected strictly before tick s, 1<=s<=U. The exact conditional history law gives a fresh-selection probability <=2/p^2 at each tick for p>=z0, since there are at least p^2-(s-1) still-allowed coordinate pairs. For p<z0 use the deterministic number of such primes. Summation (elementary prime-count upper bound and reciprocal-square tail) yields, uniformly in s,
    E K_s <= pi(z0)+2U sum_(p>=z0 prime)1/p^2
          = O(sqrt U/log(2U)).
This bound includes arbitrarily large known labels in the infinite alphabet. It neither bounds their total gain nor requires a gain cap on the actual path. In the finite initial segment all sums only decrease. The infinite process has finitely many selected labels by any finite tick.

## 2. Next-high fresh-to-known transition theorem

Choose A>=5 (may depend on U), and L=L_A=2 product_(3<=ell<A prime)ell. Assume z0>L+3. Ignore all executed events of label <A when forming the HIGH event subsequence. For two consecutive events of that subsequence, write q for the earlier label and p for the later label. The interval in between contains only labels <A, hence its total gain d is even with 0<=d<L by the exact low-only barrier. It may contain arbitrarily many low events. This barrier works with the relative CRT phases by choosing a representative of the initial even horizon modulo L; a common multiple of L in absolute horizon cannot be crossed by any eligible low jump.

Call this a comparable fresh-to-known pair if q is globally fresh, p is repeated, and p<=F q, with real F>=2. The pair is counted only if both events are executed by U. Define W_tr(U;A,F) as the sum of p over all such pairs, including those with short waits or negative signed increments. Every fresh q has at most ONE next high event, so is the earlier endpoint of at most one qualifying pair. No gain cap or upper bound on the first-selection-to-return span of p is needed.

For q<z0, the total weight of all qualifying pairs is deterministically <=F sum_(q<z0 prime)q = O(F U/log(2U)). This remains true if q=p.

For q>=z0, a qualifying repeat p must be a label known BEFORE the selection of q. Indeed if p=q, its pre-gain difference since first selection is q-1+d, even and in [q-1,q-1+L). Two eligibility signs for q require that difference to equal m q+a for a in {-2,0,2}. For q>=z0>L+3, the interval lies in [q-1,2q-2); the m=1 possibilities are odd, m<=0 too small, and m>=2 too large. Hence p=q is impossible. Since p>=A and all intervening labels are <A, its first selection cannot occur inside the intervening low run either.

At the first-selection tick s of q, condition on the exact past. The current pre-gain g, all known p and their c_p are known. For every fixed known p>=A, even d in [0,L), and sign sigma in {-1,+1}, a possible later p requires
    c_p+g+q-1+d == sigma (mod p).
This fixes ONE residue of the possible fresh label q modulo p. We do not condition on actual future success, future waits, or any particular low sequence. In a dyadic band [R,2R), R=z0*2^j, the number of integer q candidates for each such d and sign is <=1+R/p (up to an absolute constant for endpoints). We may ignore primality in counting them. Since only p<=F q can contribute, keep p<=2F R. Multiply each candidate by p and its first-selection hazard <=2/q^2<=2/R^2. The sum over q for fixed p,d,sign is bounded by
    O((R+p)/R^2) = O(F/R).
Sum the d and signs, then all known p. Conditional on the past, the expected potential pair weight initiated at this tick by a fresh label in this band is at most
    O(F(L+1) K_s/R).
This is a candidate upper bound: if q is selected, assign one ticket of weight p to each known p meeting at least one congruence. Summing over d and signs can only overcount. The actual qualifying pair, if any, consumes just one ticket. There is no need to recover a fresh hazard for p itself, or to know its actual first-selection span. The infinite sum over bands of 1/R is 2/z0, finite. The theorem then follows by section1 and summing U ticks:
    E W_tr(U;A,F) = O(F(L+1) U/log(2U)).
The constant is uniform in A,F and finite initial-segment alphabet, subject to z0>L+3. This proof does not use the prior rough-return sieve or a positive-peak gain cap. It bounds ALL pair weights, hence also their completed waits (<=2p) and positive increments (<=4p). In particular it includes arbitrarily distant old labels if they are reached through such a fresh event. It does NOT cover p>Fq, or transitions in which q is already known.

## 3. A growing number of consecutive comparable repeat transitions

For each globally fresh high event q, consider its consecutive run of repeated high events before the next globally fresh high event (the LOW events are still ignored). Mark the first at most r repeated high events in this run as long as every successive pair of high labels obeys p_next<=F p_prev. Stop marking for the remainder of that run on the first failure of the ratio, or when r marked repeated events have occurred. A later fresh high event starts a new run. Every run has disjoint high events; the initial high event of the path is necessarily fresh. Let W_chain denote the sum of the marked repeated labels.

Every nonempty marked run starts with a pair counted by W_tr. If its first repeated label is p1, the jth marked label is <=F^(j-1)p1. Hence the deterministic bound
    W_chain <= (1+F+...+F^(r-1)) W_tr <= 2 F^(r-1) W_tr,
and therefore
    E W_chain = O(F^r (L+1) U/log(2U)).
This extends the probabilistic result to a growing number of consecutive known-label transitions WITHOUT applying the fresh hazard to those later transitions. No condition on the time between first selection of each p and its marked repeat is imposed.

Use the existing signed block decomposition: a high event p and the entire subsequent low run up to the next high event constitute a block, with low maximum signed increment d_peak<=5L. The nonnegative maximum signed block surplus is b=[2w-(p-1)+d_peak]_+. For any p>=A, b<=4p+5L<= (4+5L/A)p. For the marked chain blocks the expected total surplus is thus
    O((L+1)^2 F^r U/log(2U)).
Choose A tending to infinity sufficiently slowly with L<=log^(1/8) U (e.g. maximal permissible primorial cutoff). Choose F=max(2,(log log U)^(1/4)) and r=floor(log log U/(4 log F)) for large U, with r>=1. Both F and r tend to infinity, F^r<=log^(1/4) U, and z0>L+3. Then this expected block surplus is O(U/log^(1/2) U), hence o(U). A simpler choice F=2 and r~log log U/(4 log2) works as well.

In particular all repeated high blocks except the following types are controlled by this argument: those after the first ratio failure in their fresh-anchored run (including the failing event), or those beyond the first r comparable repeats. It would be incorrect to claim that all such unmarked blocks individually have a large upward ratio or depth >r; an earlier failure remains a failure of the whole run. The theorem does not say those remaining runs have small cost. No Markov renewal assumption is used.

## 4. Extra deterministic deletion for small-label early repeat ranks

The previous weighted sieve handled early first-selection gain spans for p>=z0. For p<z0 one can instead delete the first k repeated OCCURRENCES of each label, regardless of how late they occur or how large their first-selection span is. Indeed the sum of their p-weights is deterministically bounded by
    k sum_(p<z0 prime)p = O(k U/log(2U)).
The same estimate holds for the first k LONG-WAIT occurrences of each repeated label (w>p/4), which is a different subset. In a high-block calculation for p>=A, the bound on surplus is <=(4+5L/A) times this weight. Thus with the preceding L<=log^(1/8) U and k=floor(sqrt(log U)), the total surplus of the first k repeated high blocks of each p<z0 is O(U/log^(3/8) U)=o(U), deterministically. This includes arbitrary first-to-return distances and does not need any unused-label hazard for these smaller primes. It does not bound the later repeated occurrences of such a p. The first k long-wait version is separately tested in the audit; the all-occurrence version is the same deterministic rank count.

## 5. Combined signed-peak reduction

Take the previous weighted-return theorem with z=ceil(U/log^(5/2) U), K=floor(log^(3/2) U) and pre-gain cap 2U. It bounds the expected positive surplus of repeated high blocks p>=z, or z0<=p with first-to-return stride m<=K, at o(U) with our smaller L. For short waits in these ranges the whole high-block surplus is zero for large U (p>=10L+2). Retain the old unconditional fresh-block bound 5L+2F_wait(U)+O(L^2/log(2L)), where F_wait is the completed fresh wait sum, distinct from the ratio parameter F. Its expectation is O(U/log U)+o(U).

Additionally delete every block marked by section3, and the first k repeated high blocks per small label of section4. Define E_remaining as the sum of b over repeated high blocks with pre-gain<=2U which remain after ALL these deletions. Blocks may satisfy multiple deletion criteria; only the union is removed, and the sum of separate bounds is an upper bound for its nonnegative cost. Truncate at an event attaining any positive peak through U, so all its pre-gains are <=2U, and any last truncated block maximum is bounded by the full observed block maximum. Thus
    E[(D_infty(U)-E_remaining(U))_+] = o(U).
The same conclusion is uniform for finite initial-segment alphabets. More concretely a remaining block must have p<z, and either p<z0 with repeat rank>k, or z0<=p<z with first-selection stride m>K; also its fresh-anchored high run must already have failed a comparable ratio or have exhausted its r marked repeated events. This is a genuine additional deletion across all scales and addresses some long first-to-return spans independently of the old sieve. It is still a positive-block majorant, not a proof that E_remaining or the exact signed repeat bank is o_prob(U). No conclusion eta->0, and the independently unresolved physical far-coalescence estimate remains required.

## 6. Finite path audit and persistence

Saved research/min_ghost_fresh_to_known_chain_audit.mjs and research/min_ghost_fresh_to_known_chain_results.json, exact remote readback at 1df3a86aef44b0a84f35e5ce948ae9415f4a76aa. Finite common CRT alphabet <=4U with fixed pseudorandom seeds, U=256,1024,4096,16384,65536; 256 paths per case except 128 at U65536. A=5,L6 or A=7,L30, omit cases z0<=L+3, F=2, diagnostic r=3 and k=3. These are finite diagnostic parameters rather than the asymptotic growing sequence. The finite-to-infinite coupling error O(1/log U) is not a calibrated finite-sample error. No empirical estimation of the constant in the probability theorem.

At every high fresh q>=z0, enumerate all previously known p>=A,p<=2q and all even d<L and record a p-ticket if the necessary eligibility holds. At the next high repeated p<=2q, check it is known before q, its intervening actual low gain is in [0,L), and its ticket was included. At q<z0 use budget 2q. Verify the accumulated pair-weight budget, all marked chain weights <=(1+2+4) times pair weight, each low suffix gain and signed peak, all repeated high-block surplus = marked plus unmarked, and the marked positive bound. Also count first three long-wait repeats at each p<z0 and check their deterministic rank-weight budget, regardless of first-selection span. All executed waits checked. No gain cap imposed in the transition/chain audit, as in the analytic theorem; the older sieve is not retested here.

At U65536,A5,128 paths: 7923 executed events; 991 comparable fresh-to-known pairs (764 with earlier q<z0=363, 227 with q>=z0), all 227 large-q actual pairs covered by their known-p tickets, none a self-return. Pair sum p=9861, completed wait sum=7816. There are 1675 marked repeated high blocks of chain weight14811. Their signed block surplus17442 out of total repeated-high-block surplus39686 (aggregate over the sample). Unmarked surplus22244. First three long-wait repeated occurrences per small label have weight19896 and their high-block surplus23166; this overlaps with chain marks. At A7,128 paths: 7638 events, 765 qualifying pairs (200 with large q), 1263 marked repeated high blocks, pair weight9733, chain weight15213, marked surplus18774 of total33130. The early-long-wait surplus is23202 and overlaps with chain marks. All structural and ledger assertions pass. These totals demonstrate nonvacuous candidate coverage, not a numerical test of the asymptotic rates or an upper bound on the remaining surplus. No Lean compilation.

## 7. Next target

The previous first-span sieve could not use a new fresh hazard for an old label after an arbitrary restart. This note instead uses the fresh hazard of a DIFFERENT earlier label and exact known-label eligibility, removing comparable fresh-to-known transitions and their initial comparable repeat chains. Further work must bound high runs with ratio failures or very many consecutive repeats, using their actual old-label constraints and signed gain credit. The new small-label early-rank deletion also restricts the smaller label residual to repeatedly used labels. Neither the full repeat peak nor the global physical far-coalescence bound is solved. No new branch, no main edit, no twin-prime proof.
