# Hypothetical infinite MIN worlds XVI: asymmetric nonrank capacity, repeated-label affine sieve and clock phases

2026-11-26 JST. Independent continuation of [XV nonrank capacity](https://github.com/tara-sooo/A166944-Lean/blob/eadacc275f0200ddb1c184035b8b2ed0f6227c68/research/infinite-orbit/nonrank_capacity.md), [XIV rank escape](https://github.com/tara-sooo/A166944-Lean/blob/51c7805e03354e16e53662fed5e66aa9278fcc41/research/infinite-orbit/rank_escape.md), and [XI factor reuse](https://github.com/tara-sooo/A166944-Lean/blob/fe66ed306ed73aa7ae91658fb98882eecf8c526c/research/infinite-orbit/factor_pair.md). Sibling preflight [direct 14c6176 modular hyperbola](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md), [unified fb20d9c localized ratio](https://github.com/tara-sooo/A166944-Lean/blob/fb20d9c5f20b7f13f242f9e672c485c04d34a9f9/research/2026-11-26-min-unified-local-hyperbola-ratio.md), and earlier [direct 568cfa4 bounded repeat CRT](https://github.com/tara-sooo/A166944-Lean/blob/568cfa484c91708e7e9196731f7a8566b9deda52/research/2026-11-26-min-direct-bounded-word-crt-and-repeat-supply.md). The latter uses general repeat relations and long CRT progressions; here the three-event return admits an affine prime sieve at the square-root scale even for large nonrank label jumps. The asymmetric estimate is a refinement of XV. The clock section is an exact local feasibility filter, not an extra saving in the one-ray horizon count. Paper deductions and finite diagnostics, not Lean proof or external novelty claim.

## 1. Exact determinant with all three label differences

Use a fixed selected list of high events of an actual physical MIN ray, T<=p_i<=B, T>=eta sqrt X, B=floor sqrt(lambda X+1), fixed eta>0,lambda>1, pre-horizons in [X,lambda X). All actual intervening physical events are retained in the relay gains. For a consecutive triple in the list write
    labels p,r=p+a,v=p+b;
    cofactors q,u=q+1+j,z=q+2+k;
    pre-horizons H_i=p_i q_i+e_i, e_i=1-2s_i;
    cumulative relay gains E_1,E_2, 0<=E_1<=E_2 even.
All labels prime and cofactors odd >= their labels; cofactors need not be prime. Put C_1=E_1-1+e_0-e_1, C_2=E_2-2+e_0-e_2 and Delta=a k-b j. The exact equations are
    (p+a)j=-a(q+1)+C_1,
    (p+b)k=-b(q+2)+a+C_2.
Subtract after multiplying by b,a respectively and rearrange:
    Delta*r*v =
       a(b-a)[b(q+1)-(p+a)]
       +a C_2(p+a)-b C_1(p+b).                      (1)
This isolates the curvature contribution from relay contributions. For three DISTINCT labels, all three gaps are nonzero even, and with K=max(|a|,|b|,2), L=E_2,
    |Delta| << (|a b(b-a)|+K(L+1))/T.               (2)
Indeed q,p,r,v=O(T), r,v>=T, |C_i|<=L+4; |b|>=2 lets the lower-degree term a(b-a)(p+a) be absorbed. The determinant is an even integer. Thus nonrank triples with three distinct labels, min(|a|,|b|,|b-a|)<=A, |a|,|b|<=K satisfy
    A K²+K(L+1) >> T.                              (3)
Here A>=2 and A<=K (if the given upper cutoff is larger than K, use K). For polylogarithmic A,L, (3) requires K>>sqrt(T/A) at large T (the second term cannot supply T while K is below a sufficiently small multiple of sqrt(T/A)). If both gaps are of order K this reduces to XIV's cubic toll. No clock or prime-cofactor restriction in (1)-(3).

## 2. Asymmetric nonrank candidate count

Assume L<T-1, integer cutoffs A,K>=2, A<=K=O(T). For fixed a,b, |j|=O(|a|+1), as in XV. Given nonzero Delta, g=gcd(|a|,|b|) divides Delta, and j lies on one progression of step |a|/g. Thus there are O(g) possible (j,k) for this Delta and O(M/g) possible nonzero Delta with magnitude <=M, with no additive term when M<g. Using (2) with the small-gap condition, take M=C(A K²+K(L+1))/T. There are O(A K) gap pairs: split into |a|<=A, |b|<=A, or |b-a|<=A and count the free other gap in [-2K,2K]. Count E_1,E_2 and signs by O((L+1)²). Cramer's rule from XV reconstructs p,q uniquely for each nonrank tuple, so each tuple gives at most one consecutive triple on a strictly increasing actual ray. For weight <=C_w T per distinct triple,
    F_nonrank,distinct(A,K,L)
       << (L+1)² [A² K³ + A K²(L+1)].              (4)
All constants fixed in lambda,eta,C_w. This bound is absolute, not normalized to the length of a translated subinterval. Unlike (5) of XV it can be useful even for K well above T^(2/5). If A,L are polylogarithmic and K<=T^(2/3-eps), any fixed eps>0, (4)=o(X).

For an actual collection of such nonrank triples of total weight F>=rho X, rho>0 fixed, with disjoint strict relay interiors and
    U=sum E_2=O(T log^alpha X),
    V_min=sum min(|a|,|b|,|b-a|)=O(T log^beta X),
    alpha,beta>=0 fixed,
take cutoffs L*=ceil(C log^alpha X), A*=max(2,ceil(C log^beta X)), choosing the constants to discard at most rho X/4 total weight by the two tails. Then choose
    K*=floor(c T^(2/3)/log^(2(alpha+beta)/3) X)
for a sufficiently small positive fixed c. Equation (4) bounds the small-K part by <=rho X/4 for large X: the first term is O(c³ X) with fixed other constants, and the second is smaller by O((L*+1)/(A* K*))=o(1). At least rho X/2 weight thus has K>K*. Since each triple weighs at most C_w T,
    sum K >> X^(5/6)/log^(2(alpha+beta)/3) X.       (5)
This is stronger than XV's X^(7/10) when the additional small-minimum-gap budget holds. Equivalently with slowly increased polylogarithmic cutoffs, all but o(X) nonrank weight lies beyond K=T^(2/3-eps). The minimum includes the nonadjacent gap, not just the first or second jump. If exact rank triples are also present, apply XIV separately for d=3 and the fixed actual prime-cofactor count v_c when alpha<(3+v_c)/(5/2). None of the current hypotheses forces small V_min. This is a conditional asymmetric result on distinct triples, not an unconditional improvement of XV for all words. In particular the sibling near-saturation condition r~3p is a LARGE first gap, and need not yield a small minimum gap among three labels. No new gain credit is created by label displacement.

## 3. A repeated label gives an exact affine factor system

Now allow p_0=p_2=p and p_1=r!=p. No assumption of rank or of small label difference. Monotonicity of pre-horizons, T>=5, implies q_2=q+2m with integer m>=1. From the horizon gain,
    p(2m)+e_2-e_0=p+r-2+E_2,
    r=M p+h,
    M=2m-1 positive odd, h=2-E_2-e_0+e_2.         (6)
At comparable scale and E_2=O(T), M=O(1). h is even and nonzero: if h=0, primality would force M=1,r=p. The determinant is Delta=(r-p)*2(m-1); thus rank is equivalent to M=1. The exact alternatives are:
    rank: r=p+h, |h|<=E_2+4;
    nonrank: M>=3, r>=3p-E_2.
In a band B<3T-L, no nonrank repeat can have E_2<=L. This is an exact label-scale desert for the p,r,p class without the small K hypothesis. For elapsed arrival span V=n_2-n_0, the same label p has its two side clocks at 0 and p+2 modulo 2p, so any two different arrivals are separated by at least p-2; hence V>=p-2, even if both later individual waits are fast. A fully short elapsed return is impossible.

The first product relation is r u=p(q+1)+C_1. Combining with (6), define the integer l=q+1-Mu. Then
    h(q+1)=M C_1+l r,
    h u=l p+C_1,
    q=M u+l-1, q_2=q+M+1.                         (7)
Here l is odd (q+1 even, Mu odd), and |l|=O(|h|+1) uniformly for E_2<=L=o(T): use the first equation and r>=T, q=O(T), M=O(1), |C_1|<=L+3. The equations are exact even when all cofactors are composite. Fix E_1,E_2, signs, M and l. The integrality condition h|l p+C_1 fixes p to at most one residue class modulo |h|/gcd(|h|,|l|), or has no solutions. Every label and cofactor in the triple is an affine form in the remaining parameter p. This is a special repeat reduction at top scale, not the long-progression general repeat sieve of direct 568cfa4.

## 4. Prime-cofactor sieve for returns, including the nonrank ratio 3

Assume L bounded by a fixed power of log X, so L<T-1 eventually. Fix the tuple above and choose any v_c of the three cofactor positions which are prime. Sieve the two distinct label forms p,r and those v_c cofactor forms, dimension nu=2+v_c. All included forms are nonconstant. In fact u=(l p+C_1)/h has nonzero slope since l odd, and the slope is positive on a valid tuple for large X: |C_1|=o(T), u,p>=T imply l/h>0. q and q_2 have slope M l/h>0. For checking determinants, multiply cofactor forms by h (a nonzero constant), retaining their integer affine parametrization on the congruence class. With respect to p, the coefficients/intercepts are:
    p: (1,0);
    r: (M,h);
    h u: (l,C_1);
    h q: (M l, l h+M C_1-h);
    h q_2: (M l, l h+M C_1+M h).
The determinants between label forms and cofactor forms are nonzero by parity: h is nonzero even and M,l,C_1 odd. The two endpoint cofactor forms have nonzero determinant since q_2-q=M+1>0. The only remaining proportional possibilities are between u and q (l=1), or between u and q_2 (l=-M). In those cases q=M u or q_2=M u respectively. If M>1 both cannot be prime, and if M=1 equal cofactors would make consecutive products differ by at least 2u, since distinct odd labels are used. The corresponding horizon gap is >=2u-2, whereas the earlier selected label is <=u and its gain plus the local relay is <2u-2 when relay<T-1. Thus equal cofactors impossible at the short relay cut. Consequently any designated PRIME cofactor forms are pairwise nonproportional together with p,r, in both rank and nonrank cases. We do not require primality of the undesignated cofactors.

For source pre-horizon in any translated interval of length Hspan>=T^(1+eps), Hspan=O(X), the product pq is monotone along this progression and changes by >=T times the change in p between valid candidates. Padded parameter length is N comparable to Hspan/T *gcd(|h|,|l|)/|h|+1, polynomially large in T for polylog L. As in XIII/XIV, apply the fixed-dimensional translated upper Selberg bound with sufficiently small fixed-power cutoff in min(T,N); coefficients and nonzero determinants polylogarithmic, exceptional Euler factor O((loglog X)^nu). All prime forms >=T. Each tuple count is << N (loglog X)^nu/log^nu X. For fixed h, sum over l in O(|h|+1) range; the normalized gcd sum is O(tau(|h|)) by the divisor identity. For fixed signs, E_2 determines h uniquely, with |h|<=L+4 and h nonzero; sum tau(|h|) over E_2 costs O((L+1) log(2+L)). E_1 has O(L+1) choices; M and signs bounded. Weight by O(T) and use distinct source horizons on the actual ray. This proves
    F_return,v_c(Hspan;L)
       << Hspan (L+1)² log(2+L)
                 (loglog X)^(2+v_c)/log^(2+v_c) X.  (8)
For fixed L remove loglog. The +1 in N is absorbed by the polynomial Hspan/T and polylog h. A macro disjoint return population of fixed v_c (or at least v_c designated prime cofactors), with total relay O(Hspan/T log^alpha X), is excluded when alpha<(2+v_c)/2, by a slightly enlarged polylog cutoff and the relay tail. In particular v_c>=1 for an upward source at top scale eventually by roughness/cube exclusion; alpha<3/2 then suffices even if the other two cofactors are composite. For all three prime, alpha<5/2. The estimate includes repeated-label nonrank triples with r=3p+O(L), an important class not covered by XIV's small-gap rank sieve. It does not exclude a general nonreturn triple or a population with broader relay costs.

For v_c=0 on the full macroscopic block there is a simpler slightly sharper log-factor bound. At fixed M,h, sieve p and M p+h for O(T J_2(|h|)/log² X) prime pairs, fixed M, h!=0, J_2 as in XI. Each E_1 and signs gives one horizon class modulo pr, so O(1) possible H in [X,lambda X) at top scale. Averaging J_2 over h yields
    F_return,0(X;L) << X(L+1)²/log² X.
This includes all return triples irrespective of cofactor primality and gives alpha<1. The localized (8) is needed when one wants proportional Hspan, not merely the absolute full-block bound. Both are upper counts, not an assumed lower supply or independence. Tagged sums require actual original-list relay budgets. The sibling near-saturation r~3p and source-support constraints do not force p_2=p nor the small-relay exponent alpha required here.

## 5. Exact short-elapsed clock filter for fixed physical triples

The Cramer reconstruction of XV fixes horizon/label/sign data, not the arrival phase. A separate filter applies to any fixed necessary physical triple with p!=r (including repeats p_2=p). Put clocks A_s(l)=0 for s=0, A_s(l)=l+2 for s=1, modulo 2l. In the canonical envelope the first arrival n lies in
    I=[H_0/2+1, 3H_0+3+2p].
Consider all compatible arrival triples n,n+V_1,n+V_2 with 1<=V_1<V_2<=W<2T. For each V_1, its parity must be s_1-s_0 modulo 2, and
    n=A_(s_0)(p)+2p t,
    t=(2s_1-V_1-A_(s_0)(p))*(2p)^(-1) mod r.
Thus n is in one progression modulo 2pr and I has O(X) length; at most 1+floor(|I|/(2pr))=O(1) values per V_1 (take |I| as interval endpoint difference). For each such n,V_1, V_2 is uniquely determined, if it exists, as the next third-label clock after n+V_1 inside n+[V_1+1,W]; the interval length is <2v. Hence
    # compatible (n,V_1,V_2)
        <= (W-1)(1+floor(|I|/(2pr)))=O(W).         (9)
No assumption of cofactor primality or rank. The same enumeration permits exact local MIN feasibility: first require that n is reachable by an incoming event with label p from some pre-time in the envelope, checking every eligible competing clock and smallest-prime tie as in VII. Then run actual deterministic MIN from the post-state (H_0+p-1,n) until the next two selected highs (for the audit the fixed list is all p>=T), requiring their exact horizons, labels, sides and times. For any other fixed selection rule, use that same rule in the simulation. For a label/side/product-only candidate this is a genuine additional restriction; it does not assert canonical ancestry of any resulting source state. Relative to O(T) possible arrival phases at a fixed source, W=o(T) reduces physical phase capacity to O(W). On a single actual ray, the earlier candidate counts already charged at most one visit per source horizon, so (9) cannot be multiplied as a further saving there. No deduction on tag multiplicity or missing mass without an ancestry bound.

## 6. Finite diagnostics

[Audit abf8d60](https://github.com/tara-sooo/A166944-Lean/blob/abf8d6070edd22fe954ccfdd354a8f48af6782f3/research/infinite-orbit/asymmetric_repeat_audit.mjs), blob 27f50ae15bdaf81e595644f734771dbcab66260a, exact remote readback. Run node research/infinite-orbit/asymmetric_repeat_audit.mjs. Actual ECMAScript in tool runtime, not separate Node. All assertions passed. Same deterministic corpus as XV: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1); 64,512 canonical roots and 9,959 targeted intermediate starts (valid envelope and clocks, not established canonical ancestry). 1,616,573 actual events, 74,191 finite stops, 280 exits, 0 cap-unresolved, 85,254 high visits, 162 independent literal tick gcd tests. 21,921 consecutive high triples, 21,921 exact (1) controls, 20,739 distinct-label (2) controls, 21,722 nonrank triples overall.

413 p,r,p triples, 230 nonrank, 191 with E_2<T-1 of which 41 nonrank. All 413 exact (6)-(7) checks, all 1,620 designated prime-form determinant checks on short repeats; no same-label return with elapsed time <p-2. Example nonrank short repeat from targeted intermediate state, X=4096,T=32:
    H=11358,11412,11520; p_i=41,101,41;
    q_i=277,113,281; w_i=4,56,33;
    E_i=0,14,22; e_i=+1,-1,-1;
    M=3,h=-22,l=-61,Delta=120.
This exhibits the genuine nonrank repeated-label ratio, not canonical ancestry or an asymptotic small-L claim. Actual canonical rank return p_i=67,47,67,q_i=71,103,73,E_i=0,18,20 has M=1,h=-20,l=-31.

Independent necessary product census for p,r,p with q arbitrary odd and L=0,4,8,16, at all three X. Enumerate p,q, signs and relay offsets and factor the middle neighbor; require last p divides its selected neighbor. Compare to affine reconstruction (6)-(7) using E_1,E_2, signs,M,l and the congruence for p. 12 exact set equalities; 27,752 candidate incidences over overlapping cutoffs, 8,803 prime source cofactors, 1,543 nonrank. At X=65536,L=0: 140 necessary candidates including 37 with prime source cofactor and 8 nonrank; L=16: 10,487/3,077/586. Necessary product candidates are not actual MIN histories. No asymptotic sieve test.

500 sampled actual horizon triples with distinct first labels, W=min(T,64). Independently enumerate first clock over I and later clock gaps, compare exact set to (9)'s CRT route. 8,935 compatible phases across sample incidences, 95 controls containing the observed arrival triple, all passed. Incoming feasibility and actual deterministic continuation accepted 732 phases and rejected 8,203 (necessary only). These counts are not independent samples or counts of canonical roots; no inference about asymptotic rejection probability. One accepted example at X=4096, H_0=5208,p_i=41,59,47, n=8200,V_1=3,V_2=27,W=32. The sample was capped at 500 triples (165,322,13 at increasing X), not balanced across scales.

## 7. Remaining world

Asymmetric triples with one small label difference now have a stronger conditional X^(5/6) summed-width obstruction; p,r,p repeats have a top-scale affine sieve even when the middle label is near a larger odd multiple. The short-clock filter excludes many local phase candidates without claiming an additional one-ray resource bound. General all-distinct triples with all gaps of order T, large total relay and longer return patterns remain. Next useful target is the broad all-distinct fast-recovery population, or a relaxed integer model satisfying the accumulated resource restrictions to see which exact clock or horizon constraints fail. The quantitative relay and small-minimum-gap hypotheses are not forced by the present siblings. No full all-constraint infinite model, general uncapped run bound, Lean verification or finite-twin contradiction. Main and sibling branches not modified by this work.
