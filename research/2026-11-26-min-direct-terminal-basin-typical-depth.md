# Inverse terminal basins and a density-one lower bound on MIN depth

Continuation of [86e2797](https://github.com/tara-sooo/A166944-Lean/commit/86e2797a2f7654128fa0650aa0c79a9d530852cc) on the independent direct-arithmetic branch. The preceding study ruled out small collision excess and bounded indegree. Here we examine terminal basins and prove a different global result: almost all large canonical roots experience a growing number of nonunit events. Uses the actual adaptive prefix rule, finite CRT and elementary prime-product bounds. No independence assumption for an actual fixed integer trajectory and no twin infinitude or A166944 proof. Paper proof, not Lean kernel verification.

## 1. Inverse horizon tree of a terminal basin

Fix a terminal even horizon Z, so Z-1,Z+1 are prime. At any last event of a trajectory ending at Z, the predecessor horizon is H=Z-p+1. Even side p|H-1 implies p|Z; odd side p|H+1 implies p|Z+2. Eligibility additionally requires p^2<=Z-p+2. This applies also to nonterminal intermediate Z. Define the relaxed inverse horizon tree by these necessary conditions (and H>=8), omitting clock competition and predecessor times. Every actual reverse path belongs to this tree. At a node h<=Z the number of distinct predecessor horizons is <=omega(h)+omega(h+2), where omega counts distinct prime divisors. This is O(log Z/loglog Z) uniformly for large Z: an integer with r distinct prime factors is >=(r+1)!, whose log is >=floor(r/2)*log(r/2) for r>=4. Thus for fixed k the number of canonical roots terminating at Z in at most k nonunit events is
    <= O_k((log Z/loglog Z)^k).
The depth-zero possibility is included (H0=Z). A canonical root is uniquely specified by its initial horizon H0=2M-2, so predecessor times cannot increase the count. This is an upper bound on the bounded-depth subset, not the entire basin. Also such roots have Z-H0<=k sqrt(Z+1), by eligibility at each event. No phase-free reverse condition is asserted sufficient.

## 2. A uniform upper bound on fast termination

At a canonical root M, after relative T ticks the envelope H<=2t implies horizon gain E<=2T+6. If it stops by that time (including an initially terminal root), the terminal center Z has 0<=Z-(2M-2)<=2T+6. For odd M in [X,2X] and 1<=T<=X, Z<=6X+O(1). For each Z there are at most T+4 possible M. The elementary two-residue upper sieve proved in [c27a25f](https://github.com/tara-sooo/A166944-Lean/commit/c27a25fb1572f721928b17793fe47b2914426225), with the shift2, counts twin centers in that range by O(X/log^2 X). Indeed both Z-1 and Z+1 are prime; if either <= the sieve cutoff it contributes only O(X^(1/12)) exceptions, also within the bound. Thus uniformly in T
    #{odd M in [X,2X] stopping within T ticks}
          <= O(X*(T+1)/log^2 X).                        (1)
Consequently for every T=o(log^2 X), all but o(X) roots require more than T ticks to terminate (or never terminate). This bound does not imply many events, since one long quiet interval can consume all those ticks. It does not assume twins infinite.

## 3. Formal residue process and fresh primes

For the uncut rule, relative tick j>=1, pre-gain E, the raw parity gcd is determined by
    gcd(M+j+2,2j+7-E)   j odd,
    gcd(M+j,2j+1-E)     j even.
The second arguments are odd nonzero, with absolute value<=2j+7 by the envelope E<=2j+4. A quiet tick is recorded if gcd=1, otherwise the least prime factor is the selected label and gain p-1. For every fixed T, the entire prefix is determined by the odd root parity and M mod every odd prime <=2T+7. For actual integers M with 2M-1>=(2T+7)^2, all labels in this prefix are adaptive-eligible; hence this is exactly the adaptive prefix, including formal quiet ticks after termination. No full infinite-path equivalence is assumed.

For analysis only, choose one residue R_p uniformly and independently in Z/pZ for every odd prime p. This is the countable product of finite uniform probability spaces. Fix parity odd. Define the uncut formal process tick by tick by the same relative gcd prime-divisibility tests, with M replaced by these residues. Each finite prefix is realizable by ordinary integer roots via CRT, so the envelope and all finite algebraic identities hold. Let F_t be the information of all residues at primes <=2t+7. The event word up to tick t is F_t-measurable. No independence of successive events is claimed.

At time t, conditional on F_t, the gain E is fixed. If no next event occurs through t+L, then for every prime p in (2t+7,L/2], the formal horizon 2M-2+E has neither neighbor divisible by p. Otherwise that p has a clock within 2p<=L, which would preclude a quiet interval (possibly an earlier smaller label fires). The two forbidden residues of R_p are distinct because p odd, and these fresh primes have independent uniform residues even after conditioning on F_t. Hence the conditional tail of the next-event wait W_t satisfies
    Pr(W_t>L | F_t) <= product_{2t+7<p<=L/2}(1-2/p).   (2)
The bound is valid even when the previously revealed residues already force an earlier event. It is an upper bound, not an exact conditional law; small primes may impose extra restrictions. Taking L->infinity implies W_t finite almost surely for every t, by the elementary prime-product bound below. A countable intersection therefore gives infinitely many events almost surely in the formal residue process. This fact does not give an integer root with an infinite trajectory: the product-space points generally do not correspond to any one integer, and integer residue vectors form a countable set of measure zero.

## 4. Uniform logarithmic waiting growth

Write Q(x)=product_{3<=p<=x}(1-2/p). The earlier first-return note [6bdbf35](https://github.com/tara-sooo/A166944-Lean/commit/6bdbf354a5cb13f13abb6493da96acfe08e95531) proved Q(x)=Theta(1/log^2 x), using Chebyshev's bound, the convergent correction to twice log(1-1/p), and elementary Euler-product/harmonic estimates. Thus (2) gives, for L/2>=2t+7,
    Pr(W_t>L | F_t) <= K (log(2t+7)/log(L/2))^2
with one absolute K. This holds for every conditional residue assignment at t.

Let tau_i denote the relative tick of the i-th nonunit event (tau_0=0). Each is a stopping time for F_t and finite almost surely. Apply (2) at tau_i: on {tau_i=t}, conditioning on F_t gives exactly the preceding bound because {tau_i=t} is F_t-measurable. Define
    V_i=log(tau_(i+1)+16)/log(tau_i+16) >=1.
For u>=2, put L=floor((t+16)^u-(t+16)). If V_i>u, then W_t>L. For t>=0, this L satisfies L/2>=2t+7 and log(L/2)>=(u/2)log(t+16), while log(2t+7)<=2log(t+16). Therefore
    Pr(V_i>u | F_(tau_i)) <= K'/u^2
with one absolute K'. The conditional tail integral yields E[V_i|F_(tau_i)]<=2+K'/2=:B>1 (increase B if needed). No independence of V_i is used. Since log(tau_i+16) is F_(tau_i)-measurable, iteration gives
    E log(tau_k+16) <= log(16)*B^k.
Markov's inequality now gives the explicit-in-k bound
    Pr(tau_k>T) <= log(16)*B^k/log(T+16).              (3)
Here B is a finite absolute constant from the elementary prime-product estimates; no numerical optimum is asserted. In particular choosing
    k(T)=floor(log(log(T+16))/(2 log B))
gives Pr(tau_k>T)=O(1/sqrt(log(T+16))). This proves a growing-event-count result despite the very heavy tail of the first waiting time. It is not an estimate for the expected absolute waiting time, which need not be finite.

## 5. Transfer to actual canonical roots

Take X large, T=floor(log X/(32 log2)), and P_T=product_{odd primes<=2T+7} p. The elementary Chebyshev bound theta(x)<=4 log2*x gives P_T=O(X^(1/4)). Also 2X-1>=(2T+7)^2 for large X. In the odd integer enumeration in [X,2X], the event word through T agrees with the formal residue process, and one complete period of P_T odd roots has exactly its product-space distribution, by CRT. For any property of the prefix, the difference between its proportion in [X,2X] and its formal probability is at most O(P_T/X)=O(X^(-3/4)), by splitting into complete periods and one incomplete remainder. Applying this to the event count in (3) proves
    proportion of roots with fewer than k events by tick T
       <= O(B^k/log(T+16) + X^(-3/4)).                (4)
In particular, there is an absolute c>0 such that all but
    O(X/sqrt(loglog X))
odd M in [X,2X] have at least floor(c logloglog X) nonunit adaptive events within the first floor(log X/(32 log2)) ticks. Take any c<1/(2log B), since loglog(T+16)=logloglog X+o(1). Consequently for each fixed k the proportion of roots terminating in <=k nonunit events tends to zero. To avoid off-by-one ambiguity, apply (4) with k+1 to this fixed-depth assertion, since stopping within k cannot produce k+1 events. The exceptional proportion for growing depth is O(1/sqrt(loglog X)); constants absolute. This is an asymptotic theorem about a family of roots, independent of the existence of infinitely many twins. It does not claim the lower bound holds for every root. It also does not convert formal almost-sure nontermination to actual infinite trajectories.

Under finite twins, all sufficiently large actual roots are already known to have infinitely many events. The new density-one theorem is consistent with that hypothesis and does not contradict it. In contrast, if one could prove a uniform fixed upper bound on the number of nonunit events for a positive-density family of arbitrarily large roots, the theorem would rule out that proposed mechanism. To prove twin infinitude through termination one still needs a family of actual terminating roots with unbounded terminal horizons. Neither the relaxed inverse tree nor the finite-prefix density theorem supplies such roots.

## 6. Exact diagnostics

[Audit 8cf3bb0](https://github.com/tara-sooo/A166944-Lean/blob/8cf3bb0c45a024006aa9144a041ce743cba15bf0/research/min_direct_terminal_basin_typical_depth_audit.mjs), blob 90ee3f2f92fe74328d3e89bc6beea7131f3fbddc. Exact remote readback. Run:
    node research/min_direct_terminal_basin_typical_depth_audit.mjs 200000 180
Actual ECMAScript execution in tool runtime, not a separate Node process. All odd M=5..200000, up to180 nonunit events: 99,998 roots, 2,278,154 events, 99,874 terminal, 124 cap-unresolved. Every event checked against inverse horizon rule. Counts of roots stopping within 0,1,2,3,4 events: 1933,5272,9111,13019,17037. Across 3803 terminal centers with a root in this bounded-depth subset, enumerated four relaxed inverse layers (15212 layer checks) and verified all 17037 actual roots in appropriate layers. Largest relaxed candidate count through depth4 was215, largest observed actual depth<=4 basin16. These are finite observed maxima, not universal constants.

Fresh-prime controls: 50 prefixes at T=0,1,2,4,6, using ordinary integer residues and a large lift; 200 fresh-prime residue counts each exactly two forbidden classes; 400 independent CRT lifts preserving the full prefix while forcing some nonunit event in the next 2p ticks. 17170 BigInt literal GCD ticks checked. These test the finite algebra underlying (2), not the asymptotic density bound. No empirical claim of a triple-log growth rate, whose constants need not be useful at the sampled scales. No Lean verification, no external novelty claim. Main and siblings unchanged.

Next: the reverse tree ignores actual time reachability; seek a sharp coupling of inverse time constraints with the abundance of deep forward prefixes, or a different absolute-scale terminal existence argument. The new theorem limits shallow termination schemes rather than furnishing a contradiction with finite twins.
