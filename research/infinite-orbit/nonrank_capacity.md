# Hypothetical infinite MIN worlds XV: nonrank determinant lattice and polynomial variation capacity

2026-11-26 JST. Independent continuation of [51c7805](https://github.com/tara-sooo/A166944-Lean/commit/51c7805e03354e16e53662fed5e66aa9278fcc41), [XIII bounded affine words](https://github.com/tara-sooo/A166944-Lean/blob/e840e0d8140aede2d7b23c7968034fe4a94c5bdd/research/infinite-orbit/bounded_affine_word.md) and [XIV primitive relay toll](https://github.com/tara-sooo/A166944-Lean/blob/51c7805e03354e16e53662fed5e66aa9278fcc41/research/infinite-orbit/rank_escape.md). Sibling preflight [direct 240e3de fast pair odd shift](https://github.com/tara-sooo/A166944-Lean/blob/240e3dea344526cac575e612ba4d538f42bd2a57/research/2026-11-26-min-direct-fast-pair-odd-shift-and-quadratic-escape.md) and [unified 20f444e alphabet escape](https://github.com/tara-sooo/A166944-Lean/blob/20f444ec5796970cde7e6cb4dedb93b619f47d23/research/2026-11-26-min-unified-alphabet-escape-budget.md). The nonrank class left by XIV is now counted by a small integer determinant lattice rather than by a prime sieve. The argument covers even composite cofactors and arbitrary waits, uses no alphabet or support assumption, and works at square-root scale. Paper deductions and finite diagnostics, not Lean or an external novelty claim.

## 1. Exact reconstruction for a nonrank triple

Take a physical block with pre-horizons H in [X,lambda X), fixed lambda>1; T>=eta sqrt X, B=floor sqrt(lambda X+1), eta>0 fixed; select a FIXED list of complete actual events with T<=p_i<=B. In particular this can be the list of all high events. A word is consecutive in that list, retaining all actual physical relays. Use the notation of XIII/XIV. For a triple based at index zero let p=p_0,q=q_0,H=pq+e_0, e_i=1-2s_i, p_1=p+a,p_2=p+b, q_1=q+1+j,q_2=q+2+k. The q_i are odd integers >=p_i; no primality restriction on them. E_1,E_2 are cumulative relay gains before the second and third displayed event, excluding preceding displayed high gains, so 0<=E_1<=E_2 and both even. Define
    R_1=-1+E_1+e_0-e_1-a(1+j),
    R_2=a-2+E_2+e_0-e_2-b(2+k).
The exact horizon rows are a q+j p=R_1, b q+k p=R_2. Write Delta=a k-b j. If Delta!=0, Cramer's rule gives
    p=(a R_2-b R_1)/Delta,
    q=(k R_1-j R_2)/Delta.                            (1)
Thus the coefficient tuple (a,b,j,k,E_1,E_2,e_0,e_1,e_2) determines at most one physical triple of pre-horizons and labels; it does NOT determine its clock phase or establish that it is an actual MIN triple. On one strictly increasing physical ray a given first horizon can occur at most once; hence this also gives at most one consecutive selected triple occurrence there. Candidate validation requires all reconstructed integers, primes, horizons and eligibility, and actual clock competition if desired. We need only a necessary count.

## 2. Thin nonzero determinant lattice

Suppose |a|,|b|<=K, K>=2, and E_2<=L with 0<=L<T-1 (we can take K=O(T) since labels are comparable). Consecutive equal labels are impossible by the same-label toll, so a!=0 and b!=a. In particular b=0 is allowed a priori. From the pre-expansion rows, with q<=C T and p_i>=T, we obtain uniformly
    |j|<=C_1(|a|+1),  |k|<=C_1(|b|+1),
    |R_i|<=C_2(K²+L+1).
For example (p+a)j=-1+E_1+e_0-e_1-a(q+1), and (p+b)k=a-2+E_2+e_0-e_2-b(q+2). The term |a|/T in the second row is bounded. Constants depend only on lambda,eta and the allowed fixed comparison bound B/T. Since p>=T, (1) implies
    0<|Delta|<=M=C_3 K(K²+L+1)/T.                   (2)
Delta is even, but it has a further divisibility: for fixed (a,b), g=gcd(|a|,|b|)>0 divides Delta. For each fixed nonzero multiple Delta of g, solutions to a k-b j=Delta form an affine integer lattice with j-step |a|/g. In the allowed j interval of length O(|a|+1), there are O(g) solutions (using a!=0). There are at most 2 floor(M/g) admissible NONZERO determinant values. Thus for each fixed (a,b), the number of admissible (j,k) is
    O(g floor(M/g))=O(M),                            (3)
even when M is small; if M<g the count is zero. No extra +1 term is necessary. The zero determinant class would instead contribute O(g) and cannot be treated by (1); XIV treats it separately.

There are O(K²) choices of a,b, O((L+1)²) choices of even E_1,E_2, and eight signs. By (1)-(3), the count of nonrank consecutive triples on a single ray is at most
    C_nr (L+1)² K³(K²+L+1)/T.                      (4)
This counts all prime labels but uses no distribution of primes, no cofactor primality, no waits, and no independence. It holds in any translated source subinterval as an absolute bound for the surrounding physical scale, not a bound proportional to the subinterval length. If M is large, (4) may exceed the total physical gain; it is intended for small-to-intermediate K.

## 3. From triples to bounded nonrank words

For a word with length 3<=m<=m_max fixed, regard the points (p_i,q_i-i) in the plane. Horizon rank one is exactly collinearity of these points when the first pair has different labels. If every consecutive triple is collinear and consecutive labels differ, the nonvertical line through each consecutive pair agrees with the previous line; by induction all the points are collinear. Therefore every nonrank word with L_word<T-1 contains a consecutive nonrank triple. This is a LOCAL witness, without any need to enumerate the other m-3 labels or relay offsets. Changing the origin from the word start to the witness start changes the label width by at most a factor two. The triple cumulative relay is <=L_word. A fixed witness triple can be contained in only O(m_max²) words of length <=m_max consecutive in the SAME fixed list. This does not hold for arbitrary independently chosen subsequences; the same-list condition is used in the count.

For each such word assign weight W<=C_w T with a fixed C_w. Count it via any one witness triple (or overcount by all witnesses). From (4), total weight of nonrank words with anchor-relative width K_word<=K and relay L_word<=L satisfies
    F_nonrank(K,L) << (L+1)² K³(K²+L+1).            (5)
Constant depends on m_max,lambda,eta,C_w. There is no log factor and no source-prime condition. This improves the merely pointwise rank-escape criterion in XIV into a count of the small-width part of the nonrank population. In particular with polylog L and K<=T^(2/5-epsilon), fixed epsilon>0, (5)=o(X), since T=Theta(sqrt X) and K^5 is at most T^(2-5epsilon). (For a very small K use the full K³(K²+L+1) expression.) XIV's per-word lower bound was only Omega(T^(1/3)). Most of a macroscopic nonrank population must escape farther than that.

## 4. Aggregate quantitative variation

Consider an actual collection of consecutive words in the fixed list, length 3..m_max, with strict relay interiors pairwise disjoint, W<=C_w T, total weight F>=rho X for fixed rho>0. Let U=sum_word L_word be the actual relay gain (bounded by full complementary gain if disjoint and the fixed high list contains all high labels). Suppose
    U<=C_U T (log X)^alpha, alpha>=0 fixed.
For a nonrank-only collection, choose L_*=ceil(C_* (log X)^alpha) with C_* sufficiently large depending on C_U,C_w,rho. The weight of words with L_word>L_* is <=C_w T U/(L_*+1), at most rho X/4. Let
    K_*=floor(c_* T^(2/5)/(log X)^(2alpha/5))
with c_*>0 sufficiently small depending on fixed parameters and C_*. For large X, K_*² dominates L_*+1. The count (5) gives weight O((L_*+1)² K_*^5)<=rho X/4 of nonrank words within BOTH cutoffs. Consequently at least rho X/2 weight has K_word>K_*, so
    sum_word K_word >> X^(7/10)/(log X)^(2alpha/5).  (6)
This follows because there are at least (rho X/2)/(C_w T) such words, each with width >K_*. No use of sign of ordinary deficit variation; it is the actual label displacement summed on words, not a signed gain or new resource. In particular, for any fixed epsilon>0, choosing L=log^(alpha+epsilon0) with epsilon0>0 and K=T^(2/5-epsilon) also shows all but o(X) nonrank weight has width >K (including the relay tail). This applies without any rank-sieve restriction on alpha if the macro population is already nonrank.

For a mixed rank/nonrank population with fixed d distinct labels and v distinct prime cofactor shifts as in XIV, additionally assume alpha<(d+v)/a_d where a_2=2 and a_d=d-1/2 for d>=3. Then the XIV rank-only estimate at L_* gives o(X) rank weight, and the same proof, with constants chosen to leave a positive fraction, gives (6) for the full collection. For example d=3,v=1 allows alpha<8/5. More generally one can stratify a finite mixture of these classes. This improves XIV's sum_word K=Omega(X^(2/3)) to (6), under the SAME quantitative small-relay hypothesis. It does not prove that any specific physical population has that budget, or imply a contradiction from the upper bound O(X) on possible summed displacement for event-disjoint words.

For source span Hspan between T^(1+epsilon) and O(X), (5) is absolute rather than O(Hspan) times a normalized ratio. If F>=rho Hspan and U=O((Hspan/T)log^alpha X), replace K_* by floor(c_*(Hspan/(log X)^(2alpha))^(1/5)). Provided Hspan is polynomially large, K_*²>>L_*; the conclusion is sum K >> Hspan^(6/5)/(T (log X)^(2alpha/5)). In particular for short original lifetimes Hspan=X/polylog X this retains the same polynomial exponent with extra logarithms. For N tags of equal such span, sum (5) once per actual list; use their actual tagged U and weights, and multiply the last lower bound by N for macro total weight. The XIV rank term may be included on its stated admissible spans. This does NOT supply the long-progression hypothesis at arbitrary tiny recycling bins or an omitted-wait lower bound. Source span refers to first horizons of words; witnesses may be within O(m_max T+L) later, but remain in the original physical window. No repeated resource charge.

## 5. Finite diagnostics and preservation

[Audit b47bb26](https://github.com/tara-sooo/A166944-Lean/blob/b47bb26d957632b5d2d4fe1d07765be2f6d1010e/research/infinite-orbit/nonrank_capacity_audit.mjs), blob 307980599cdd6f4484f3a653501d389f57cb1512, exact remote readback. Actual ECMAScript in tool runtime, not separate Node. Run node research/infinite-orbit/nonrank_capacity_audit.mjs. First broader combined census attempt timed out before any repository write; verified HEAD unchanged. Final narrower independent census and full actual-ray checks passed.

Same start construction as XIII/XIV: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1), all 64512 canonical roots and 9959 targeted feasible intermediate starts (not established canonical ancestry), 1616573 actual events,74191 finite stops,280 exits, zero cap unresolved,85254 high visits. All consecutive high triples (not restricted to small K,L): 21921 triples,21722 nonrank Cramer reconstructions,199 rank triples. 2752 nonrank triples have composite source cofactor. 37559 actual words of lengths 3..5 with no consecutive equal labels checked for exact equivalence between anchor rank and the local consecutive-triple rank; 37368 nonrank words all have local nonrank witness. 162 independent literal tick gcd controls. These tests include long relays and do not claim the asymptotic small-budget condition.

Independent necessary triple census: for each X and (K,L)=(4,0),(8,0),(8,4),(16,0), enumerate source products p q (q any odd integer >=p), both first signs and cumulative relay gains, factor the two later neighbor products to obtain eligible labels. Compare the set of nonrank triples to a separate enumeration of coefficient tuples (a,b,j,k), discarding determinants outside an explicit finite residual bound and reconstructing p,q by (1). 12 exact set equalities; 678 total necessary nonrank candidates over overlapping configurations, 239 prime source cofactor,439 composite source cofactor. 12,571,440 coefficient tuple incidences in the determinant-filtered census, 1200 fixed-(a,b) lattice capacity checks. Candidates are NOT actual MIN selections; this tests the algebraic enumeration and finite lattice bound, not the macro hypothesis or a uniform numerical asymptotic constant. Selected census totals (prime/composite source):
| X | K=4,L=0 | K=8,L=0 | K=8,L=4 | K=16,L=0 |
|---:|---:|---:|---:|---:|
|4096|1/1|13/18|59/82|41/54|
|16384|1/0|8/18|54/103|24/64|
|65536|0/0|2/9|12/42|24/48|

Actual canonical example with composite source cofactor: H=8694,8778,8850; labels 37,67,53; cofactors 235,131,167; waits 7,110,53; sides e=-1,+1,-1; cumulative relay E=0,48,54. Then a=30,b=16,j=-105,k=-70, R_1=3165,R_2=1170, Delta=-420. Formula (1) returns p=37,q=235 exactly. This illustrates the composite-cofactor scope, not a polylog-relay asymptotic instance. Previous canonical prime-source example p=61,67,41, q=79,73,121, E=0,12,18 has Delta=100 and R_1=47,R_2=860. All events actual MIN, not an assumed independent phase.

## 6. Remaining world

The medium label-displacement range of nonrank triples is now capacity-limited even above the pointwise T^(1/3) escape scale. A macro nonrank population with polylog average relay needs almost all its weight beyond T^(2/5-epsilon) and summed displacement at least (6). A population with order-T jumps, larger relay budgets or words too short for triple witnesses remains possible. The sibling lanes currently allow o(T) relays and do not force the quantitative log budget used here. Next: exploit prime and clock conditions in the nonrank lattice for wider displacements, or construct a relaxed diverse-label survivor and explicitly test the accumulated scalar restrictions. No full all-constraint model, general uncapped mixed-run bound, Lean proof or finite-twin contradiction. Main and sibling branches not modified by this work.
