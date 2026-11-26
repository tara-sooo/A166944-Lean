# Hypothetical infinite MIN worlds XIII: rank-one bounded words at square-root scale

2026-11-26 JST. Continuation of [dfde7f8](https://github.com/tara-sooo/A166944-Lean/commit/dfde7f8c2b3fb63361d25959793931971ad5db95). Sources: [XII affine pair sieve](https://github.com/tara-sooo/A166944-Lean/blob/dfde7f8c2b3fb63361d25959793931971ad5db95/research/infinite-orbit/close_factor_clock.md), [X cofactor support](https://github.com/tara-sooo/A166944-Lean/blob/aef03d14e390358f0b9b0cc1583cd98376e74d61/research/infinite-orbit/cofactor_support.md). Sibling preflight [direct 568cfa4 bounded-word CRT](https://github.com/tara-sooo/A166944-Lean/blob/568cfa484c91708e7e9196731f7a8566b9deda52/research/2026-11-26-min-direct-bounded-word-crt-and-repeat-supply.md), [unified 3d9c7b1 two rough endpoints](https://github.com/tara-sooo/A166944-Lean/blob/3d9c7b19f1e021bdd23f3335e9b3328b016f5356/research/2026-11-26-min-unified-two-rough-word-relay.md). Their general word CRT needs long progressions relative to the product of distinct labels. This note instead assumes small anchor-relative label differences and small total low relay, and reduces the word to one affine parameter even at top scale. No Lean or external novelty claim.

## 1. Exact rows for a bounded word

In a contiguous actual MIN block with pre-horizons in [X,lambda X), lambda fixed, take T>=eta sqrt X, B=floor sqrt(lambda X+1), fixed eta>0. A word consists of m high events (2<=m<=Jmax fixed), all labels >=T, and EVERY intervening physical event; all labels omitted from the displayed high list are <T. More generally a consecutive list of chosen high events with arbitrary unchosen physical relays obeys the same identities. Number the high positions i=0,...,m-1. Write p=p_0, q=q_0, H=H_0, s=s_0, e=1-2s, n=n_0 (arrival tick), c=(n-2s)/p. Each H_i=p_i q_i+e_i, q_i odd >=p_i, e_i=1-2s_i. No primality assumed of q_i unless explicitly stated. Define
    d_i=p_i-p, j_i=q_i-q-i, k_i=c_i-c, c_i=(n_i-2s_i)/p_i,
    E_i=H_i-H-sum_(h<i)(p_h-1), A_i=sum_(h<i)(d_h-1),
    V_i=n_i-n,
    R_i=A_i+E_i+e-e_i-d_i(i+j_i),
    S_i=V_i-2(s_i-s)-d_i k_i.
All E_i are nonnegative even, nondecreasing, and E_0=0. Then the exact equations are
    d_i q+j_i p=R_i,    d_i c+k_i p=S_i.            (1)
In particular d_i even, j_i=i mod2, R_i=i mod2, and k_i=s_i-s mod2. These equations include arbitrary fast clocks and deep deficits. q,c=O(T) in the canonical envelope, all p_i in [T,B].

Assume |d_i|<=K and E_(m-1)<=L, K>=2,L>=0, with K,L bounded by fixed powers of log X. For large X, d_1!=0: a same-label adjacent high return would need E_1>=p-1. The horizon identity prior to expansion gives
    (p+d_i) j_i=A_i+E_i+e-e_i-d_i(q+i).
It implies |j_i|=O_Jmax,lambda,eta(K+1) uniformly because L=o(T). Similarly |k_i|=O(K+1) because V_i<=3L+sum_(h=1)^i 2p_h=O(T). Thus |R_i|=O(K²+L+1), |S_i|=O(V_(m-1)+K²+1). More generally the horizon argument works whenever L=o(T) and K(K²+L+1)=o(T), with constants fixed. These bounds are actual integer bounds, not random phase assumptions.

## 2. Exact rank collapse and primitive parity

Eliminate q between rows 1 and i:
    p(d_1 j_i-d_i j_1)=d_1 R_i-d_i R_1.             (2)
The right side is O(K(K²+L+1))=o(T)<=o(p). Hence it vanishes identically for sufficiently large X, and
    d_1 j_i=d_i j_1,    d_1 R_i=d_i R_1             (3)
at EVERY position. This is the rank-one reduction; no congruence approximation is left. The precise finite sufficient certificate is |d_1 R_i-d_i R_1|<p for all i; a uniform sufficient certificate is 2K max_i |R_i|<p.

Set g=gcd(|d_1|,|j_1|), D=d_1/g, J=j_1/g, R=R_1/g. Since j_1 and R_1 are odd, g is odd and divides R_1 by (1). D is even nonzero, J and R odd, and gcd(|D|,|J|)=1. For every position there is a signed integer ell_i with
    (d_i,j_i,R_i)=ell_i (D,J,R),
    ell_i=i mod2.                                  (4)
The last assertion follows from j_i parity. Equal prime labels can only recur at positions of equal parity. In particular odd-length cycles in the displayed list cannot return to the same label. This is necessary on the close-label rank-one class, not on all bounded MIN words. The primitive equation is D q+J p=R.

The full cumulative relay is now determined by anchor data, all label offsets and sides:
    E_i=(d_i/d_1) R_1+d_i(i+d_i j_1/d_1)-A_i-e+e_i. (5)
There is no independent free E_i for i>=2. Require all reconstructed E_i to be even integers, monotone in [0,L], and satisfy the necessary horizon conditions. This reconstructs candidate products, not actual earliest-selection clocks. If clocks and low events are desired, they must be verified on the actual deterministic MIN sequence.

## 3. More prime forms from the same affine parameter

Fix the length, equality pattern (d distinct high labels, d>=2), sides, the nonzero first gap d_1, odd j_1, E_1 and the d-2 other distinct label offsets. Require (3)-(5), and ignore inconsistent tuples. The anchor linear equation gives one residue class of p modulo |d_1|/g. Write p=p_*+(|d_1|/g)z with q=(R_1-j_1 p)/d_1; all p_i=p+d_i and q_i=q+i+j_i are integer affine forms on it. At valid candidates -j_1/d_1>0 for large X because q,p>=T and R_1 is polylogarithmic. All high label forms are prime, with d distinct forms. Let v be the number of DISTINCT cofactor shifts i+j_i at positions with prime q_i (any designated subset of such positions suffices). Include one prime form per distinct shift. Distinct label forms are nonproportional. Distinct cofactor shifts give distinct parallel forms with nonzero slope. A cross determinant between label p+d_h and cofactor q+i+j_i is nonzero because its vanishing would require
    R_1+d_1(i+j_i)+j_1 d_h=0,
an odd integer. Therefore there are nu=d+v distinct nonproportional prime forms. If the source alone is known prime-cofactor (e.g. positive drift at top scale for large X), v>=1. If none of the cofactors is prime, the d labels alone can still be sieved. No assumption that all intermediate cofactors are prime or distinct; one must use the ACTUAL number of distinct prime cofactor shifts. If d=3 and only the source prime is known, nu=4, as opposed to XII's 3 for a pair.

## 4. Uniform localized word capacity at top scale

Let source pre-horizons lie in any translated interval of length Hspan>=T^(1+epsilon) for fixed epsilon>0, Hspan=O(X). The word need not end inside this interval, but all events in the physical window. Fix the parameters as in section 3 and which positions supply the v distinct prime forms, a bounded combinatorial choice. Product pq is monotone in the affine parameter at valid candidates. Its variation between valid parameters is at least T times the change in p. Thus padded parameter length
    N=O((Hspan/T)*g/|d_1|+1)
can be chosen comparable to that expression; it is polynomially large in T for polylogarithmic K. Leading coefficients and nonzero determinants have polylogarithmic size. Apply the same fixed-dimensional translated upper Selberg bound as XII, now dimension nu<=2Jmax, cutoff floor(min(T,N)^(1/24)), excluding primes <=nu and divisors of coefficients/determinants. The exceptional factor is O((loglog X)^nu) by the product estimate for primes up to a fixed power of log X (bounded factor for fixed K,L). The cutoff error O(cutoff^6) of the fixed-dimensional bound used in the prior notes is absorbed; alternatively use a smaller fixed positive power depending on Jmax. All actual prime forms are >=T; no small-prime false removal. Candidate count << N (loglog X)^nu/log^nu X.

Sum j_1=O(|d_1|+1) (use the first-position identity, since L=o(T)) with gcd weights: sum gcd(|d_1|,|j_1|) << |d_1| tau(|d_1|). Sum d_1 up to K costs O(K log(2K)), as in XII. The d-2 remaining distinct offsets cost O(K^(d-2)), E_1 costs O(L+1), and all other offsets E_i are reconstructed, not separately summed. Weight each word by at most C_w T with fixed C_w, e.g. endpoint gain or retained matched mass, and note that a fixed start and displayed length determine at most one actual word on a ray. Then
    F_(d,v)(Hspan;K,L)
      << Hspan (L+1) K^(d-1) log(2K)
                    (loglog X)^(d+v)/log^(d+v) X.   (6)
Constants depend on fixed Jmax,lambda,eta,epsilon,C_w and polylog powers. For fixed K,L remove the loglog factor. Unlike a first-appearance CRT count, the power of L+1 is ONE even if there are many high labels. The scale condition does not require Hspan>=T^(d+epsilon). On the other hand the small-label-difference hypothesis is essential. The bound is not valid with the same logs on O(T) or T log² T bins; it applies to aggregate top-scale words in a macroscopic window or original lifetime X/polylog X.

In particular, for fixed length and d>=3, source prime cofactor, K,L fixed, weight O(Hspan/log^(d+1) X). More generally a macroscopically weighted collection of such words with pairwise event-disjoint interiors, with fixed d,v and at least C_w T upper weight per word (i.e. weight<=C_w T), cannot have simultaneously total omitted relay gain U=O((Hspan/T) log^alpha X) and summed maximal anchor-relative label displacement M=O((Hspan/T) log^beta X) when
    alpha+(d-1) beta < d+v.
Indeed choose K=ceil(log^(beta+epsilon0) X), L=ceil(log^(alpha+epsilon0) X) with small fixed epsilon0; the discarded weighted tails <=C_w T M/K and <=C_w T U/L are o(Hspan), and (6) is o(Hspan). Same statement for a class with at least v prime cofactor shifts by selecting v. Overlapping words cannot use the same physical relay repeatedly for this tail argument. For original-tag families sum (6) and use actual disjoint relay budgets on each tag, not a new independent mass credit. The sibling bounded recovery words have O(T) span, o(T) low gain, but may have order-T label changes and larger-than-polylog relay, so the conditions above are not automatic.

## 5. Clock rank and no-repeat consequence

Eliminate c from (1):
    p(d_1 k_i-d_i k_1)=d_1 S_i-d_i S_1.              (7)
If in addition K(V_(m-1)+K²+1)=o(T), for example all high waits AFTER the first and total low relay are polylogarithmic, this yields exact clock rank collapse
    d_1 k_i=d_i k_1,    d_1 S_i=d_i S_1.
There is also the exact finite certificate |d_1 S_i-d_i S_1|<p for each row. Together with (3) it implies k_i=ell_i k_1/g; the coefficient need not be integer separately (actual products are integral). No prime cofactor is needed for (7). If any two positions have equal label, they have equal d_i and hence equal k_i. Their corrected arrival times (n_i-2s_i)=p_i(c+k_i) coincide. Their ordinary arrival difference is then 2(s_j-s_i), even, which by arrival parity forces s_j=s_i. This contradicts strictly increasing arrival times. Consequently ALL labels are distinct under simultaneous rank collapse. This last conclusion also follows from the short elapsed time condition directly when V<T-2: distinct arrivals of a given p are separated by at least p-2 across the two side clocks (or 2p for same side). The rank formulation is stronger in scope because it applies whenever the exact determinants vanish, including longer elapsed times. It imposes a common one-parameter change in both quotient coordinates, but does not eliminate all distinct words.

## 6. Reproducible diagnostics

[Audit 089351f](https://github.com/tara-sooo/A166944-Lean/blob/089351faed9ce28b0f7b24a5fc12bb69865e6133/research/infinite-orbit/bounded_affine_word_audit.mjs), blob cc7357cddf8f325296fc20a553e304ae9af5b84b, exact remote readback. Actual ECMAScript executed in tool runtime; not separate Node. Run node research/infinite-orbit/bounded_affine_word_audit.mjs. First draft failed negative-integer parity due to JS signed remainder; normalized mod(j,2), with no mathematical change. Final assertions pass. Same starts as XII: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1); 64512 canonical roots and 9959 targeted valid intermediate clocks (ancestry unverified), 1616573 actual events, 74191 stops, 280 exits, zero cap-unresolved, 85254 high visits, 162 literal tick gcd checks. Every actual consecutive high subword of lengths 3 through 5 inspected (including large label differences and large relays, not assuming the asymptotic small-gap condition). 39205 word incidences and 140745 exact row checks. After nonzero anchor filtering, 100169 horizon elimination rows, 39041 zero determinants and 61128 nonzero; 100169 clock elimination rows, 38666 zero. All 191 fully rank-one word incidences (154 with source prime q) reconstruct every relay exactly. 183 have repeated labels (all even index distance), 8 have three distinct labels, none four or five; 2 words have both horizon and clock rank, each all-distinct. 573 primitive row and reconstructed-offset checks, 1004 cross-form determinant checks, 138796 residual bound checks. The conservative uniform residual certificates 2K Hbound<p and 2K Cbound<p were never triggered in these finite scans; exact row certificates and actual rank words were exercised. Thus the asymptotic rank criterion is a paper deduction, not a claim that all these finite words fall within it.

Actual rank-one three-distinct-label intermediate example (not known canonical ancestry): p_i=67,73,71; q_i=181,167,173; H_i=12126,12192,12282; E_i=0,0,18; d_i=0,6,4; j_i=0,-15,-10; R_i=0,81,54. Primitive D=2,J=-5,R=27, ell_i=0,3,2. All six prime forms distinct; clock rank does not hold. A canonical repeated-label rank example p_i=67,47,67, q_i=71,103,73, H_i=4758,4842,4890, E_i=0,18,20; repeat at index distance two. Joint-rank example from intermediate state: p_i=257,263,269, q_i=319,313,307, H_i=81984,82320,82584, E_i=0,80,82, c_i=826,808,790; d_i=0,6,12; j_i=0,-7,-14; k_i=0,-18,-36. Actual waits 1,138,2; not asserted asymptotically fast or prime-cofactor at the source. Both rank statements hold exactly.

Independent necessary-product census for length 3, source q prime, K=4,8,16, L=0,4,16, distinct adjacent labels: enumerate products and cumulative relay offsets independently, compare the rank-one subset to reconstruction from the first affine row with E2 derived rather than looped. 27 exact set equalities, 16772 total candidates and 11202 rank-one candidates (overlapping configs). At X=65536,K=4,L=0 all 36 candidates rank-one; at K=16,L=16, 2922 of 3828. These are necessary product candidates, not actual MIN histories. Non-rank finite candidates are not contradictions because the sufficient asymptotic bound is not imposed. No test of analytic sieve constants or Lean kernel.

## 7. Remaining world

The close-label bounded-word class now has one affine parameter and one independent relay offset at square-root scale, including composite intermediate cofactors, repeated labels and additional clock rank for fast words. The general bounded recovery words from the other lanes can still make large label changes and use o(T) rather than polylog relay; all-distinct unrestricted words are not excluded. Next seek a count for larger label differences using the exact nonzero integer rank determinants (or construct a relaxed diverse-label survivor), and check the relation to actual recovery-word transport with no duplicate charges. No full all-constraint model, uncapped arbitrary run bound, Lean proof or finite-twin contradiction. Main and siblings not modified.
