# Hypothetical infinite MIN worlds XIV: primitive relay toll and polynomial rank escape

2026-11-26 JST. Continuation of [e840e0d](https://github.com/tara-sooo/A166944-Lean/commit/e840e0d8140aede2d7b23c7968034fe4a94c5bdd), especially [XIII bounded affine words](https://github.com/tara-sooo/A166944-Lean/blob/e840e0d8140aede2d7b23c7968034fe4a94c5bdd/research/infinite-orbit/bounded_affine_word.md). Sibling preflight [direct 0782bd1 first-pair gap](https://github.com/tara-sooo/A166944-Lean/blob/0782bd1a321319f7de58dfa1ba15fd10382029fd/research/2026-11-26-min-direct-first-pair-gap-and-direct-recovery.md), [unified 20f444e alphabet escape](https://github.com/tara-sooo/A166944-Lean/blob/20f444ec5796970cde7e6cb4dedb93b619f47d23/research/2026-11-26-min-unified-alphabet-escape-budget.md). Here we obtain a new relay-only bound for the rank-one class and a polynomial gap alternative; the alphabet or label-support assumptions of the siblings are not used. All statements are paper deductions with finite arithmetic tests, not Lean proofs or external novelty claims.

## 1. Setup and nonzero determinant toll

Use the exact word notation of XIII. Pre-horizons H_i in [X,lambda X), fixed lambda>1, T>=eta sqrt X, B=floor sqrt(lambda X+1), eta fixed, 3<=m<=m_max fixed displayed high events with T<=p_i<=B. All physical relays between displayed events are retained; if the displayed list contains every high event, their gains are precisely the low gains. Write p_i=p+d_i, q_i=q+i+j_i, H_i=p_i q_i+e_i, e_i=1-2s_i. All p_i are odd primes, all q_i odd integers >=p_i, not necessarily primes. E_i is cumulative intervening gain, E_0=0, L=E_(m-1). Set K=max_i |d_i|. The exact rows are
    A_i=sum_(h<i)(d_h-1),
    R_i=A_i+E_i+e_0-e_i-d_i(i+j_i),
    d_i q+j_i p=R_i.
Here d_i even, j_i and R_i have parity i. If L=o(T), consecutive equal labels are impossible by the same-label toll E_gap>=p_i-1. In particular d_1!=0, K>=2. Directly from the row before expansion,
    (p+d_i)j_i=A_i+E_i+e_0-e_i-d_i(q+i),
so |j_i|<=C(K+1), |R_i|<=C'(K²+L+1), with fixed constants. Eliminating q gives
    p(d_1 j_i-d_i j_1)=d_1 R_i-d_i R_1.
The determinant on the left is even. If any such determinant is nonzero, its magnitude is at least 2, so the right side has magnitude >=2p. Consequently every nonrank word satisfies
    K(K²+L+1)>=c T.                                  (1)
This makes XIII's sufficient rank-collapse bound a necessary quantitative toll for the complementary class. The constants only depend on fixed m_max,lambda,eta. For polylogarithmic L, (1) implies K>=c' T^(1/3), equivalently Omega(X^(1/6)). More generally (1) is a tradeoff in K and L, not a universal T^(1/3) bound when L is large.

## 2. Exact factorization of each rank-one relay

In the rank-one class set g=gcd(|d_1|,|j_1|), D=d_1/g, J=j_1/g, R=R_1/g. As in XIII, D is even nonzero, J,R odd, and
    d_i=D ell_i, j_i=J ell_i, R_i=R ell_i,
    ell_i congruent i mod2, ell_0=0.
Write b_i=R+D(i+1)+DJ(ell_(i+1)+ell_i), h_i=ell_(i+1)-ell_i, L_i=E_(i+1)-E_i, for i=0,...,m-2. Subtract consecutive reconstructed relay formulas from XIII:
    L_i-1+e_i-e_(i+1)=h_i b_i.                       (2)
Both h_i and b_i are odd nonzero integers, so each absolute value is <=L_i+3. This is a divisor constraint on the LABEL displacement itself, not just a restriction on the number of offsets. The actual relay gain is nonnegative even. For adjacent triples,
    b_(i+1)-b_i=D[1+J(ell_(i+2)-ell_i)].              (3)
The bracket is odd since the two ell have equal parity; in particular it cannot vanish. Thus
    |D| <= |b_i|+|b_(i+1)|
         <= (L_i+3)/|h_i|+(L_(i+1)+3)/|h_(i+1)|.
It follows for EACH triple that
    |D| <= L_i+L_(i+1)+6,
    min(|p_(i+1)-p_i|,|p_(i+2)-p_(i+1)|)
        <= L_i+L_(i+1)+6.                            (4)
For a word of length >=3,
    |D|<=L+6, sum |h_i|<=L+3(m-1),
    K <= sum |p_(i+1)-p_i|
      <= (L+6)(L+3(m-1)).                            (5)
Unlike the original rank-one criterion, (2)-(5) assume exact rank, not small K. No clock or primality condition on q_i is used. The triple hypothesis is essential; the difference of consecutive b_i does not exist for a pair.

If a triple has different first and last labels, then |ell_(i+2)-ell_i|>=2. Equation (3) strengthens the first bound in (4) to
    |D|(2|J|-1) <= L_i+L_(i+1)+6.                    (6)
If the word has at least three distinct labels, some such triple exists: otherwise ell_(i+2)=ell_i everywhere and the entire word alternates between just two labels. Under L polylogarithmic, (5) gives K polylogarithmic, and the first row bound gives |J|=O(|D|) (use j_1=O(|d_1|+1) since L=o(T)). By (2) at i=0, R=b_0-D-DJ ell_1, hence |R|=O((L+1)^3)=o(T). From Dq+Jp=R, q>=p, |R|<p and the distinct parity of D,J, one has |J|>=|D|+1. Indeed |J|<=|D|-1 would imply |Dq+Jp|>=p, and equality of absolute values is impossible by parity. Combining (6) with this gives
    |D|(2|D|+1)<=L+6,
    K <= sqrt((L+6)/2) (L+3(m-1))                   (7)
for at least three distinct labels. In particular such a rank-one word with L=0 cannot exist at sufficiently large X: even |D|>=2 demands L+6>=10. This is only for rank-one words; a nonrank word can have zero relay and large label jumps.

## 3. Forbidden intermediate label scale

For L polylogarithmic and fixed length >=3, either the word is rank-one, with K=O((L+1)^2) (or O((L+1)^(3/2)) for >=3 distinct labels), or it is nonrank, with K>=c' T^(1/3) by (1). In particular there are no such words with K growing faster than the stated relay bound but K=o(T^(1/3)). This rules out an intermediate range of LABEL displacements, not all close transitions. It does not imply that the original ray must have polylogarithmic relay or a bounded high-word length. The exact toll (4) also implies that at least one of any two consecutive label jumps in a rank-one word is bounded by the two local relay gains plus 6. This stronger local fact does not require small total L.

## 4. Relay-only localized affine sieve

Let the source pre-horizon lie in any translated interval of length Hspan>=T^(1+epsilon), Hspan=O(X), epsilon fixed. Retain rank-one words of length 3..m_max, cumulative relay <=L for L bounded by a fixed power of log X. Let d be the actual number of distinct label offsets and v the actual number of distinct cofactor shifts i+j_i whose q_i are prime. Thus d>=2, 0<=v<=m. As in XIII there are nu=d+v nonproportional affine prime forms; the cross determinant is nonzero by parity of R and D, or equivalently by the original first row. We now count primitive tuples directly with NO separate K parameter.

Fix length, equality pattern, sides and the positions supplying the prime cofactor forms; boundedly many choices. For signed even D with 0<|D|<=L+6, |J|=O(|D|) by the first-row estimate. If d>=3, (7) restricts |D|=O(sqrt(L+1)). Fix D,J coprime, with J odd. The first step h_0=ell_1 and b_0 satisfy 0<|h_0 b_0|<=L+3. The number of signed integer pairs is O((L+1)log(2+L)), by the divisor sum (parity and actual sides can only reduce this). Then R=b_0-D-DJ ell_1 is fixed. Each remaining distinct ell is in [-L-3(m-1),L+3(m-1)] from (2), so the d-2 remaining distinct values have O((L+1)^(d-2)) choices. All other cumulative relays are reconstructed from these choices and the sides; no extra offset alphabet. Check integrality and validity, and discard inconsistent tuples.

The primitive congruence Dq+Jp=R fixes p to one residue class modulo |D|. On it q is an affine function of p, with positive slope at valid candidates (because |R|=o(T), p,q>=T). Product pq is monotone and changes by >=T times the change in p. Parameter interval length can be padded to N comparable to Hspan/(T |D|)+1, polynomially large uniformly for polylog L. As in XIII, the nu-dimensional translated upper sieve with sufficiently small fixed-power cutoff gives O(N (loglog X)^nu/log^nu X) candidates. All coefficients/determinants are polylogarithmic and the forms have no proportional pairs; fixed L removes the loglog factor. Weight <=C_w T per actual word. Each source and word length gives at most one actual word on the ray. The summation over D,J costs
    sum_(D) sum_(J) 1/|D| = O(L+1) if d=2,
                         = O(sqrt(L+1)) if d>=3.
The +1 in N is uniformly absorbed by Hspan/(T|D|). Consequently
    F_rank,d,v(Hspan;L)
       << Hspan (L+1)^a_d log(2+L)
                   (loglog X)^(d+v)/log^(d+v) X,    (8)
    a_2=2, a_d=d-1/2 for d>=3.
For fixed L this is O(Hspan/log^(d+v) X). This replaces XIII's separate (L+1)K^(d-1) log K count by a relay-only bound for the rank class, with an improved exponent compared with naively inserting (5) or (7) into that earlier formula. It is valid at top scale and short original lifetimes X/polylog, not at O(T) recycling-bin lengths with the same logarithms. It counts necessary candidates, not a lower bound or independence statement about actual MIN.

## 5. Macroscopic alternative, with polynomial rather than logarithmic label variation

Take a collection of actual words of the above fixed d,v class, length 3..m_max, whose source horizons are in Hspan and whose strict relay interiors are disjoint. Weight each by <=C_w T, assume total weight F>=rho Hspan, rho fixed. Let U be the sum of actual relay gains (bounded by full complementary gain when all displayed high events are retained); no extra charges to other ledgers. Suppose
    U=O((Hspan/T) log^alpha X), alpha>=0,
    alpha < (d+v)/a_d.                               (9)
Choose L=ceil(log^(alpha+epsilon0) X), small fixed epsilon0 with a_d(alpha+epsilon0)<d+v. By the relay tail, total weight of words with cumulative gain >L is <=C_w T U/(L+1)=o(Hspan). Equation (8) bounds the remaining rank-one words by o(Hspan). Therefore F-o(Hspan) weight consists of nonrank words with L_word<=L and K>=c T^(1/3) by (1). In particular
    sum_(words) K >= c'' (Hspan/T) T^(1/3).          (10)
At Hspan=Theta(X), T=Theta(sqrt X), this gives Omega(X^(2/3)) summed maximal anchor-relative displacements, substantially larger than the logarithmic variation obstruction of XIII. The result covers d=2 (alternating or other repeated-label words) as well as d>=3, and v=0 if no cofactor is known prime. For d=3,v=1, (9) allows alpha<8/5. For d=3,v=3, alpha<12/5. For d=2,v=1, alpha<3/2. These are conditional on macro weight of this fixed class and a quantitative small relay budget; the currently extracted sibling words need only have o(T) low relay per word, which is much weaker. There is no contradiction with freely varying labels of order T. Sum (8) over original tag-bins of admissible lengths and use actual disjoint relays for a tagged analogue; no independent omitted-wait implication. If a collection mixes finitely many d,v classes one can use the minimum permitted exponent or stratify, not assume a single cofactor count.

## 6. Finite controls

[Audit a654a1f](https://github.com/tara-sooo/A166944-Lean/blob/a654a1fc55d377444f2d451a81fc37a3729f110b/research/infinite-orbit/rank_escape_audit.mjs), blob 6bd2e01fc13f0e6a56fc37d2977e5de8f82feb50, exact remote readback. Actual ECMAScript in tool runtime, not separate Node. Run node research/infinite-orbit/rank_escape_audit.mjs. Extended XIII audit, deliberately reuses its canonical/targeted start corpus so comparison is exact. All assertions passed. X=4096,16384,65536; [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1). 64512 canonical roots,9959 valid targeted intermediate starts (no established ancestry),1616573 actual events,39205 words of lengths3..5,140745 exact rows,162 literal gcd checks, no unresolved cap. 61128 nonzero horizon determinant rows checked even and >=2p in elimination magnitude. 191 exact rank words,382 adjacent relay factorizations,191 triple bounds and 191 total-width bounds. Eight rank words with three distinct labels satisfy (6); twelve rank words have |R|<p, including six with >=3 distinct labels, all satisfy (7). 238688 independently enumerated synthetic integer rank triples with nonnegative even relay checked (2)-(4) through direct formulas; these are NOT actual MIN or prime-product states. Previous 27 product/affine exact census comparisons retained. No rank word of length 4 or 5 in this actual sample; no asymptotic sieve constant test. These checks do not establish the occurrence of the macro hypotheses.

Example from XIII: intermediate p_i=67,73,71; q_i=181,167,173; E_i=0,0,18; primitive D=2,J=-5,R=27, ell=0,3,2, sides e=-1,+1,-1. Then h_0=3,h_1=-1,b_0=-1,b_1=-19. The two products are -3 and 19, exactly L_i-1+e_i-e_(i+1). The actual first-to-last low gain is 18, and (6) demands at least |D|(2|J|-1)-6=12. The smaller adjacent label jump is 2. This is a true MIN intermediate-origin word, not canonical ancestry. The example satisfies |R|<p; its exact labels are consistent with the stronger width bound.

## 7. Remaining world

New exact rank-one relay toll and forbidden intermediate label scale exclude a further class of cheap bounded words, including a polynomial variation alternative under (9). But the finite-twin survivor can use nonrank jumps >=T^(1/3), broader low relay budgets, short-scale bins, or other unselected supply. Next investigate the integer nonrank class with large label jumps, or build an explicit relaxed diverse-label model to test whether the new resource constraints can be simultaneously satisfied; compare with the siblings' actual source/consumer extraction without identifying the two budgets. No full all-constraint infinite model, general uncapped run bound, Lean verification or finite-twin contradiction. Main and sibling branches unchanged by this work.
