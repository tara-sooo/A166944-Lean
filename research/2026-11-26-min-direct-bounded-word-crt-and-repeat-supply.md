# Bounded high-word CRT sieve and a repeat-label supply obstruction

Continuation of [1b10c9f](https://github.com/tara-sooo/A166944-Lean/blob/1b10c9f93f06afc11f5cf941f4bb6985d1df14b4/research/2026-11-26-min-direct-causal-exposure-and-bounded-recovery-words.md). First appearances of distinct labels determine a CRT progression. A repeated label confines a non-source label to a short interval. Sieve the upward source on that progression. This yields an upper supply count for sufficiently sub-square-root scales, and a tradeoff between repeated-word supply, source diversity and low relay. It does not exclude general o(T) low relay or all-distinct words.

## 1. First-occurrence CRT and rough source

Fix lambda>1, an actual canonical block of pre-horizons in [X,lambda X], gain G=O_lambda(X). Use established H,p,g=p-1,w,I,e=1-2I,d,d',n=(H+g+d')/2. Fix constants K>=1, integer J>=2, epsilon>0, and T->infinity. For the entire count assume T^(J+epsilon)<=X; for words of exactly d distinct labels it suffices that T^(d+epsilon)<=X. These scale restrictions are essential for the sieve.

A physical word starts and ends at high events; its displayed consecutive high list p_0,...,p_(j-1) includes EVERY event with label >=T in that word, all in [T,KT]. Other physical events are strictly intervening and have labels <T. Assume 2<=j<=J, distinct endpoint labels, and upward first event (2w_0>p_0-1). Each word has weight in [0,K_w T], K_w fixed (e.g. its causal matched height weight). Count actual words on a single ray, not all abstract states across roots. A starting horizon and a fixed high-list length determine at most one actual word.

Let E_i be cumulative low gain before high position i, E_0=0, E_low=E_(j-1). For integer 0<=B<T-3 retain E_low<=B. Set A_i=sum_(k<i)(p_k-1). Then
    H_i=H_0+A_i+E_i,
    H_0=e_i-A_i-E_i mod p_i.                           (1)
Fix the equality pattern, its d distinct prime labels, signs, and the offsets E_i at FIRST appearances only. There are at most (B+1)^(d-1) choices of these offsets (drop monotonicity for an upper bound). CRT gives one class H_0=H_* mod P, P=product of the d labels. Repeated occurrences determine E_i mod p_i, hence at most one value in [0,B]. No factor (B+1) is needed per repeat.

For p=p_0, q=(H_0-e_0)/p is integral, and on the CRT progression H_0=H_*+Pz the two forms are q=q_*+(P/p)z and pq+2e_0. Both avoid zero modulo odd primes f<(p-1)/4: such an eligible competitor would have a strict future clock <=2f<w_0. For f<T both slopes are invertible, and their roots are distinct because 2e_0 is nonzero mod f. Use the elementary dimension-two upper sieve in [global-sieve](https://github.com/tara-sooo/A166944-Lean/blob/1b10c9f93f06afc11f5cf941f4bb6985d1df14b4/research/2026-11-26-min-direct-global-sieve.md). Pad the z interval to N=ceil(lambda X/P)+2; under T^(d+epsilon)<=X, P<=K^d T^d, N>>T^epsilon. Cutoff z_sieve=floor(min(T,N)^(1/12)) is below (p-1)/4 for large T, has z_sieve^6<=sqrt(N) and log z_sieve>>_epsilon log T. The count per fixed tuple is
    O_(lambda,K,J,epsilon)(X/(P log^2 T)).             (2)
Only the upward source is sieved. No roughness is assumed at a downward target.

## 2. Repeat-label linear relation

Adjacent equal high labels are impossible for B<T-3: a same-p return has positive even cofactor difference (H grows by at least p-1>2, e varies by at most2, q odd), so horizon gap >=2p-2, whereas an adjacent high repeat would have gap p-1+E<2p-2.

Fix consecutive appearances i<k of a repeated label p in the high list. There is a nonempty strict high interior containing no p. Let c_r be the multiplicities of its distinct labels r. Write E=E_k-E_i in [0,B], m=(H_k-H_i-e_k+e_i)/(2p)>=1 integer. Summing the actual high jumps and low relay gives
    (2m-1)p - sum_r c_r r = E-(k-i)-e_k+e_i.          (3)
Since the whole high list has bounded length and labels <=KT, m is bounded in terms of J,K. Choose a dependent label NOT equal to p_0: choose p if p!=p_0, otherwise any interior label. Its coefficient in (3) is nonzero. Fix all other labels, m, signs, and equality pattern. As E varies in [0,B], the dependent label lies in an interval of length <=B, so there are at most B+1 possible integers. No additional offset choice is needed for this interval restriction. We can count it independently of the first-appearance offset choices for an upper bound. Multipliers and absolute deficit heights do not enter.

## 3. Supply count

Let S be the number of distinct source labels used by a chosen word collection (or the size of a fixed containing set). For d distinct labels, write F_d(B) for total weight of words with E_low<=B, F_rep,d(B) for the part with any repeat. Word lengths, equality patterns, signs, choices of repeat positions and bounded m cost fixed constants. Apply (2), weight <=K_w T, sum source reciprocals <=S/T, and sum non-source prime reciprocals over [T,KT] <<_K 1/log T by the elementary Chebyshev bound. Thus
    F_d(B) << X S/log^2 T * ((B+1)/log T)^(d-1).       (4)
For repeated words, fix the source and the other d-2 non-source labels, use (3) to replace one harmonic prime sum by <=(B+1)/T. This does not restrict the source count. Hence
    F_rep,d(B) << X S/log^2 T
                      * (B+1)^d/(T log^(d-2) T).       (5)
Since S<<_K T/log T, independently of the actual support,
    F_rep,d(B) << X (B+1)^d/log^(d+1) T.                (6)
All constants depend only on fixed setup parameters. The counts also apply with weight T per word, yielding word number bounds on division by T. A translated start interval of length V>=T^(d+epsilon) can replace X on the right in (4)-(6) using padding N=ceil(V/P)+2. A word starting there may end outside it. This does not justify the same estimates for the earlier short bins of width T log^2 T. No prime cofactor, finite-twins assumption or low total deficit variation is needed.

## 4. Consequences for disjoint causal words

Take a pairwise event-disjoint collection as in 1b10c9f, or any actual collection with the above properties, total weight F>=rho_1 X, rho_1 fixed. The prior fast-gain/narrow-guard/low-label hypotheses were needed for the causal construction, not for (4)-(6). Disjointness implies sum_words E_low<=G_low, the full physical gain of p<T. For integer cutoff B the weight of words with E_low>B is <=K_w T G_low/(B+1). The previous o(T) low relay does NOT imply the smaller budgets below.

(A) Repeat obstruction without a source support bound. Take B_*=floor((log T)^(1+1/(2J))), eventually below T-3. Equation (6) for d<=J gives F_rep,d(B_*)=O(X/log^(1/2) T), since d/(2J)-1<=-1/2. Summing finitely many d and paying the high-relay tail gives
    F_rep <= O(X/log^(1/2) T)+K_w T G_low/(B_*+1).
Consequently macroscopic repeated-word weight forces
    G_low = Omega((X/T)(log T)^(1+1/(2J))).
Conversely, if G_low=o((X/T)(log T)^(1+1/(2J))), all but o(X) of total word weight has pairwise distinct high labels. This refers to repeats inside bounded words, not recurrence between distant words.

(B) Source diversity/low relay. From (4) and the same tail bound, for 0<=B<T-3,
    F <= C_* X S/log^2 T * sum_(d=2)^J ((B+1)/log T)^(d-1)
                     + K_w T G_low/(B+1),
with a fixed count constant C_*. If S=O(log^2 T), choose B=floor(c log T) for fixed sufficiently small c>0 (depending on rho_1, support/count constants). The first term is <=rho_1 X/2 eventually, so
    G_low = Omega((X/T) log T).
If G_low=O(X/T), a sufficiently large fixed B instead makes the tail <=rho_1 X/2, forcing S=Omega(log^3 T). More generally for B+1=o(log T), when the tail is <=rho_1 X/2, S=Omega(log^3 T/(B+1)). If all retained words have at least d0 distinct labels, the corresponding lower bound is Omega(log^(d0+1) T/(B+1)^(d0-1)).

The new inequalities restrict actual low relay and source diversity, not just candidate phases. Neither required low gain contradicts G_low=o(X); the earlier near-minimal LOCAL weighted support does not imply GLOBAL S=O(log^2 T). The longer CRT scale T^(J+epsilon)<=X is not forced. In particular the proof gives no near-square-root count, even for d=2. All-distinct words and larger low relay remain open, as do general upward supply and small/middle crossing branches. Next target a supply restriction for all-distinct bounded words or a count at larger scales without long CRT progressions, rather than treating these conditional obstructions as a final contradiction.

## 5. Diagnostics

[Audit 54772a5](https://github.com/tara-sooo/A166944-Lean/blob/54772a5ebf3263be3c33bf5b312d4360df584ab4/research/min_direct_bounded_word_crt_repeat_sieve_audit.mjs), blob 7457fd5c543aad3cce8518dfab606b636e020dbd, exact remote readback. Run node research/min_direct_bounded_word_crt_repeat_sieve_audit.mjs 60000. Actual ECMAScript execution in tool runtime, not a separate Node process. 29998 canonical odd roots through60000,549085 events,0 unresolved cap180.119992 controls T11/17/31/61, finite K6,J5,B=min(T-4,ceil(log^2 T)).74475 actual consecutive high prefix incidences with upward start and distinct endpoints;54810 length-two,72895 all-distinct,1580 repeated (728 first detected repeat of source,852 repeat of other label).175150 cumulative offsets,1660 repeat-offset checks,74475 BigInt CRT,186577 rough-root checks,1580 each repeat relation/dependent interval capacity,46554 greedy disjoint low-budget checks.25830 positive actual endpoint causal overlaps,209 repeated. Example T11,B6,high list [13,11,13,11], offsets [0,0,2,2], p13 repeats at0,2,m1, dependent11, H768, low gain2.4880 independent integer interval tests. All assertions passed. Counts overlap across controls and prefix choices, not all disjoint. The unused actualRepeat field stays zero; repeatWords is the actual repeat count. Finite audit tests arithmetic, not the asymptotic scale restriction or analytic sieve constants. No Lean executable/kernel verification, external novelty claim or proof of twin infinitude. Main and sibling branches unchanged.
