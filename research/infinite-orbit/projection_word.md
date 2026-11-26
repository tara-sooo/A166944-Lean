# Hypothetical infinite MIN worlds XIX: arbitrary fixed-length projection sieve and strip return toll

2026-11-26 JST. Independent continuation of [XVIII middle projection](https://github.com/tara-sooo/A166944-Lean/blob/7ce4a26a0b42d48a87bbd3685fa73a03bce3ca1b/research/infinite-orbit/middle_projection.md), [XVII clock directions](https://github.com/tara-sooo/A166944-Lean/blob/893d1f8a15b0ea8570395b3dbaffa3ce2e390ece/research/infinite-orbit/clock_direction.md), and [IX rational clock](https://github.com/tara-sooo/A166944-Lean/blob/9733fd234d882609b87ad2cef1fba038f93b5935/research/infinite-orbit/rational_clock.md). Sibling preflight [direct 14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae), [unified bae8cff](https://github.com/tara-sooo/A166944-Lean/commit/bae8cff1ab76a1c9c1fe01e6758d27ba89f51ae4) short-core prime support clustering. New: for any fixed word length m, a single narrow clock/horizon projection anywhere in the word forces all projection coefficients small when total shifts are short. With even reduced denominator there is no degenerate edge. An iterative gcd-weighted progression count makes the dependence on projection width almost linear, while the prime sieve dimension increases to m. Also an exact endpoint clock toll and a one-cut description of odd-denominator degeneracies. Not an unrestricted long-word bound, not Lean or external novelty claim.

## 1. Transport, excursion and residence

Retain a fixed ordered selected high list of actual MIN events in a physical pre-horizon window [X,lambda X), with T>=eta sqrt X, B=floor sqrt(lambda X+1)=O(T), fixed lambda>1, eta>0, T<=p_i<=B. A word consists of consecutive events in this same list and all intervening actual physical relays. Write J_i,n_i for post horizon and arrival tick, s_i for arrival side, a_i=(J_i+2s_i)/p_i=q_i+1 even, c_i=(n_i-2s_i)/p_i. In canonical time envelope the quotient sizes are O(T). Any local intermediate state satisfying the envelope may be tested, without presuming canonical ancestry.

For fixed coprime positive M,N, h_i=N c_i-M a_i, x_i=p_i h_i=N n_i-M J_i-2(N+M)s_i. For transition j>=1 let E_j be local unselected relay gain, V_j=n_j-n_(j-1)>0, sigma_j=s_j-s_(j-1), D_j=E_j-1+2sigma_j odd nonzero, d_j=V_j-2sigma_j, b_j=N d_j-M D_j. By XVIII,
    p_j(h_j+M)=p_(j-1)h_(j-1)+b_j,
    x_j-x_(j-1)=b_j-M p_j.
Hence for any i<j, exactly
    x_j-x_i=sum_(i<k<=j)(b_k-M p_k)
           =N(n_j-n_i)-M(J_j-J_i)-2(N+M)(s_j-s_i).  (1)
No rank, primality of cofactors, or short-shift condition in (1). If both endpoint projections have abs(h)<=A, then
    N(n_j-n_i)>=M(J_j-J_i)-2BA-2(N+M).              (2)
This is a clock cost for RETURN to the same rational strip, even with arbitrarily many intervening events or excursions outside it. It uses the actual total post-horizon growth, not only the selected gain, and can be summed only over disjoint return intervals. If all intervening selected shifts satisfy b_k<=M T/2, then x decreases at least M T/2 per selected step, so
    j-i<=4BA/(M T).                                 (3)
Thus two strip visits cannot be separated by an arbitrarily long sequence of such cheap transitions, even if intermediate projections leave the strip. With M=1,N=2, h_i>=0 for large high labels by the adjusted-deficit identity and ordinary deficit nonnegativity (p_i h_i>=-6, h_i even); an initial h_i<=A suffices for j-i<=2BA/T under the same cheap-step condition, even without a terminal strip assumption. A reset h_i=0 cannot have another cheap step. This is not a new independent mass credit: (2) uses the original elapsed and gain resources.

For a word of m events, assume m>=3 FIXED and sum E_j<=L, sum V_j<=W, L,W bounded by fixed powers of log X. Put P=L+4,Q=W+2,S=P+Q. Each |b_j|=O_M,N(S)=o(T), and sum |b_j|=O_M,N,m(S). If ANY one position has |h|<=A, A polylogarithmic (possibly zero), telescope (1) in both directions to obtain
    max_i |h_i| <= [B(A+M(m-1))+sum_j |b_j|]/T
                 = O_M,N,m,lambda,eta(A+1).          (4)
We can count using the first projection without specifying which position is small. Moreover W<T-2 eventually, so the two-clock repeat spacing (XVI) implies ALL labels in the word are distinct. The size m is fixed independently of X; no asymptotic uniformity in m claimed.

## 2. Degeneracy and affine word reconstruction

For large X, |h_i|, |h_i+M|, |b_j|<T by (4). With two distinct prime labels, the identity
    p_j(h_j+M)=p_(j-1)h_(j-1)+b_j
implies that if ANY of h_(j-1), h_j+M, b_j vanishes then all three vanish. For example b_j=0 implies p_j divides h_(j-1), so h_(j-1)=0, then h_j+M=0. If h_(j-1)=0 then p_j divides small b_j, and similarly the other zero case. This is exactly a degenerate edge 0 -> -M in projection. If N even, b_j=0 would imply N|D_j, impossible since D_j odd. Hence every edge is nondegenerate for even N. For odd N there is at most ONE degenerate edge: x decreases strictly for these short shifts, and a degenerate edge starts at x=0 and ends at -M p_j<0. If it occurs, (1) gives |h_i|=O_m,M,N(1) throughout, using the zero projection as the anchor, regardless of A.

On a nondegenerate word fix all shifts/sides and the projection integers h_0,...,h_(m-1) in [-C(A+1),C(A+1)]. The recurrence expresses every p_j as a nonconstant rational affine function of p_0. Integrality can be imposed recursively. Suppose the previously allowed parameter progression is p_0=u+k t, t integer, and the last label is p_i=a t+c with a,c integers, a nonzero. Start with u=0,k=1,a=1,c=0. Set H=h_i, d=h_(i+1)+M, b=b_(i+1), all nonzero. The next integrality condition is
    d | H a t+H c+b.
If insoluble discard the tuple. Otherwise set g=gcd(|d|,|H a|), k_next=k*|d|/g and restrict t to a single residue modulo |d|/g. On the refined progression the new affine slope has magnitude |H a|/g. All prior label forms remain integral. This gives EXACTLY one allowed residue class of p_0 modulo k_final, or no class, not merely a necessary list of congruences. In particular k_final<=product_(j>=1)|h_j+M|=O((A+1)^(m-1)). The slopes and intercepts of the integer forms, taking residue representatives at each stage, are polylogarithmically bounded (m fixed). Alternatively all original rational affine coefficients have numerators and denominators of that size.

Every valid tuple gives m pairwise nonproportional prime forms. If any pair were proportional, their nonzero rational ratio has numerator and denominator polylogarithmically bounded after reduction, so cannot be the ratio of two distinct primes >=T. If they are proportional with ratio 1, distinctness also fails. Discard such tuples. This argument requires neither distinct cofactor shifts nor prime cofactors. It does not require horizon rank-one or parallel clock directions.

## 3. Summed progression capacity for arbitrary fixed length

For a fixed nondegenerate tuple, use p_0 in [T,B]. The padded integer parameter length is comparable to T/k_final+1, polynomially large in T uniformly for polylog A. The fixed-dimensional translated upper Selberg sieve used in XIII-XVIII, with sufficiently small fixed-power cutoff in the parameter length (depending on m), yields
    # prime label tuples << (T/k_final) (loglog X)^m/log^m X. (5)
All valid prime forms are >=T, and all nonzero pair determinants and leading coefficients polylog-sized. Omitting primes dividing these coefficients or determinants and finitely many small primes costs O((loglog X)^m) by the Euler product up to a fixed power of log X; fixed A,L,W removes this factor. The polynomial sieve remainder is absorbed with the small fixed-power cutoff. No lower sieve bound or independence of actual MIN events used.

Given adjacent distinct labels p_0,p_1 and the first shift/sides, H_0 and n_0 each lie in one compatible CRT class modulo 2p_0 p_1; each has a global range O(X), so O(1) possibilities. All other horizons and clocks follow from fixed shifts and labels. This works at square-root scale because CRT is only a bounded multiplicity upper count, not a prime sieve inside a long CRT progression.

The new summation is over all h tuples with the progression weight 1/k_final. Fix h_0 (O(A+1) choices). At one recursive stage with current integral slope a and fixed nonzero h_i, the sum of factors by which the new inverse progression length changes is at most
    sum_(0<|d|<=C(A+1)) gcd(|d|,|h_i a|)/|d|
       << tau(|h_i a|) log(2+A).                     (6)
This follows by the gcd divisor expansion and harmonic sums. Invalid choices may be dropped. Uniformly |a|<=[C(A+1)]^i from the slope update above. The elementary divisor bound tau(n)<<_epsilon n^epsilon (from prime-power factorization, with finitely many small primes absorbed in a constant) shows that for every fixed epsilon>0 the right side of (6) is O_(m,epsilon)((A+1)^(epsilon/(m-1))), choosing the auxiliary divisor exponent sufficiently small and absorbing the harmonic log. This uniform estimate is valid for every intermediate prefix, regardless of the chosen shift intercepts. Induct over the m-1 edges to obtain
    sum_(h tuples) 1/k_final <<_(m,epsilon) (A+1)^(1+epsilon). (7)
For A fixed all factors are fixed constants. This removes the naive (A+1)^m cost, and is almost linear in the width for any fixed m. XVIII gives an explicit log^6 width bound for m=3; (7) does not assert that stronger explicit log factor for general m.

The number of shift/sides tuples is O_m((PQ)^(m-1)), since each local E_j,V_j is within its respective total cutoff; summing over this larger box only increases the count. For weight <=C_w T per word, C_w fixed, each source horizon determines at most one consecutive m-word on the fixed actual ray. Combining (5)-(7) proves
    F_m,nondeg(A,L,W)
       <<_(m,epsilon) X (PQ)^(m-1) (A+1)^(1+epsilon)
                         (loglog X)^m/log^m X.        (8)
For fixed A,L,W this is O(X/log^m X). This is an absolute full-window estimate; no proportional short-lifetime localization is claimed. The word may have all composite cofactors, all gaps of order T and arbitrary horizon rank. For fixed even denominator it covers the whole short-strip class. No assumption about actual existence of long cheap words is needed for the upper bound.

## 4. Odd-denominator cut estimate

For completeness consider words containing a degenerate edge. The split into two nondegenerate segments has maximum length k>=ceil(m/2)>=2. The degenerate edge fixes a zero projection and all h_i are bounded by a fixed constant by (4) with A=0; only boundedly many projection choices. For the degenerate shift b_j=0 the allowed (D_j,d_j) are integer multiples of (N,M), so O(min(P,Q)) choices. The other m-2 shifts cost O((PQ)^(m-2)). Sieve the longer segment as above, using k distinct prime forms with bounded coefficients. Fix its first two labels and their shift: CRT fixes the two corresponding physical coordinates up to O(1) possibilities. All arrival ticks throughout the word are then known; each missing high label divides its positive corrected arrival tick O(X), which has O(1) high prime divisors. Since m fixed, the remaining labels and then all horizons have only O(1) choices. We can discard candidates failing actual MIN. Bounding the sieve dimension below by ceil(m/2), we obtain
    F_m,cut(L,W)
       << X (PQ)^(m-2) min(P,Q)
              (loglog X)^ceil(m/2)/log^ceil(m/2) X. (9)
Here all shift cutoffs are polylogarithmic, m fixed, and fixed cutoffs remove loglog as usual. The larger segment might be longer than ceil(m/2), which only helps. There is no A factor. Even N makes the cut class empty. This is a paper deduction; the new local census below targets even denominator, not the odd-cut capacity.

## 5. Macroscopic conditional consequence

Take disjoint actual relay/time word intervals in the same fixed selected list of length m, weighted <=C_w T, total weight >=rho X. Suppose summed actual relay U=O(T log^alpha X), summed elapsed Vtot=O(T log^beta X), and summed minimum absolute projection in each word O(T log^gamma X), alpha,beta,gamma>=0. Alternatively assume every word has some |h_i|<=C log^gamma X. Choose cutoffs with slightly larger logarithmic exponents and discard o(X) weight by each Markov tail (each word weighs at most C_w T). For even N, (8) excludes macro weight if
    (m-1)(alpha+beta)+gamma < m.                     (10)
Indeed choose epsilon>0 sufficiently small and then the cutoff inflation small enough for strict inequality with (1+epsilon)gamma and enlarged exponents. This includes the adjusted deficit M/N=1/2, for which h_i is twice the adjusted deficit multiplier. For odd N also require
    (m-2)(alpha+beta)+min(alpha,beta) < ceil(m/2)
to handle (9). These are conditional on macro weight of actual words of the chosen length and small total budgets. If alpha+beta<1, then for ANY fixed gamma there is a sufficiently large FIXED m satisfying (10), so a macro population of such short words of that length cannot have even one small projection per word on average. This is not a claim that the population of long short words is itself forced, or that m may grow with X. A word may have average elapsed time O(T) (ordinary fast condition), larger relay, or larger projection at every position; the result does not exclude those regimes. No duplicated credit with other sibling ledgers.

## 6. Finite diagnostics and preservation

[Audit 563eb9c](https://github.com/tara-sooo/A166944-Lean/blob/563eb9c04567d4173712bf92fb50376535bf1744/research/infinite-orbit/projection_word_audit.mjs), blob a92b046c0b91671532f7dc99cfe46db459c95b7c, exact remote readback. Run node research/infinite-orbit/projection_word_audit.mjs. Actual ECMAScript executed in available tool runtime, not separate Node. All final assertions pass.

Same standard sample as XVIII at X4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1): 64512 canonical roots, 9959 targeted intermediate starts, 1616573 events, 74191 stops,280 exits,0 cap,85254 high visits,162 literal gcd checks. 20368 ordinary length 4..6 word incidences; no word met the stringent finite L<T/4,W<T-2 condition. To exercise the new class, separately enumerate incoming feasible intermediate arrivals in strips of slopes 1/2,3/2,5/2 with first h in [-16,16] even, X4096 and16384. Deduplicate source (H,n,p). 244919 local starts,677740 further physical event incidences,11 short word incidences of length>=4 before the relay or time cap. Four projection incidences also meet explicit finite small-coefficient and anchor<=16 conditions, all length4. 12 exact affine progression extensions on these four. These targeted origins have no established canonical ancestry.

Across ordinary plus targeted words:20379 words,292604 projection/telescoping row checks,81516 anchor spread checks (four slopes),693656 exact physical endpoint identities and strip return bounds,1913 cheap monotone residence/single-cut controls,8 adjusted-deficit residence controls. 12000 independently generated signed integer projection tuples, length3..7, tested exact recursive congruence class against literal successive divisions for every anchor integer1..96:1152000 comparisons,22557 integral candidates; these are synthetic arithmetic tests, not actual MIN or prime supply. 2560 elementary divisor-weight sum controls.

Independent candidate sets: compare arrival-clock factoring and horizon CRT to projection factoring/reconstruction for fixed shift patterns of lengths4..6, even denominator slopes1/2,3/2. 36 deliberately chosen simple patterns at three X gave empty sets on both routes; add four observed short-word patterns with small coefficients, one candidate each, all exact set equalities and local MIN checks pass. 40 exact set comparisons, four necessary candidates, all four locally realized. Patterns are overlapping diagnostics, not a random sample or a count of canonical roots; no asymptotic sieve constant tested.

Example actual local length4 word, X4096,T32:
    H=13376,13482,13578,13618; p=107,97,37,89;
    q=125,139,367,153; n=7276,7277,7291,7298;
    incoming wait1, later waits1,14,1; sides0,1,1,0;
    local E=0,0,4, V=1,14,7; total L=4,W=22.
For M=1,N=2, h=10,10,26,10 and b=-3,29,17. The exact equations are
    11*97=10*107-3,
    27*37=10*97+29,
    11*89=26*37+17.
The integrality recurrence gives one first-label progression modulo 3267 (107 belongs to it). The source initial pretime7275 realizes the first event; all later events follow actual MIN. This illustrates return to the same projection value with changing labels and a larger intermediate projection. It does not establish canonical ancestry or asymptotic abundance.

## 7. Remaining world

The short-word sieve is now arbitrary fixed dimension with nearly linear projection-width dependence. The remaining broad class can have no small fixed rational projection, larger shifts/time, or only short bounded-length sequences of very cheap transitions. The sibling clustered support result does not imply the polylogarithmic shift budgets. Next seek a bridge from actual fast-recovery words with larger waits to the projection residence and sieve bounds, or construct a relaxed survivor satisfying the resource inequalities to determine what exact local constraints must still be imposed. No general simultaneous congruence count outside strips, unrestricted long-word capacity, full all-constraint infinite model, Lean verification or finite-twin contradiction. Main and sibling branches not modified.
