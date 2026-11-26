# Hypothetical infinite MIN worlds XX: rational wait templates and odd-intercept return toll

2026-11-26 JST. Continuation of [XIX fixed projection words](https://github.com/tara-sooo/A166944-Lean/blob/a1812c45be742497d469eca9a091d81be7929374/research/infinite-orbit/projection_word.md) and [XVIII middle projection](https://github.com/tara-sooo/A166944-Lean/blob/7ce4a26a0b42d48a87bbd3685fa73a03bce3ca1b/research/infinite-orbit/middle_projection.md). Sibling preflight [direct 14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae), [unified XL 26942a9](https://github.com/tara-sooo/A166944-Lean/blob/26942a9c628149f15f521260a49b0059d84794d8/research/2026-11-26-min-unified-odd-multiplier-budget.md). The new assumption is small distance from a finite alphabet of rational wait templates, not short elapsed time. Even-denominator clock projection and odd-denominator wait templates force every composed intercept odd, excluding repeats for narrow projection and sufficiently small residuals, even with long elapsed time. The fixed-dimensional sieve consequently extends to mixed long/short words, including near-maximal waits. This is independent of the sibling's near-3p saturation inequality; we do not claim that near-saturation forces the polylogarithmic hypotheses here. Paper deductions and finite arithmetic tests, not Lean proof or external novelty claim.

## 1. Templated transport

Use a fixed selected list of high events in the actual physical MIN sequence, T>=eta sqrt X, T<=p_i<=B=floor sqrt(lambda X+1), prehorizons in [X,lambda X), fixed eta,lambda. A word consists of m consecutive events of this SAME list, including all physical relay events. The length m is fixed independently of X. Let J_i,n_i,s_i be post horizon, arrival tick and side; a_i=(J_i+2s_i)/p_i=q_i+1, c_i=(n_i-2s_i)/p_i, as in XVIII. For fixed coprime positive M,N with N EVEN (hence M odd), h_i=N c_i-M a_i is even. In particular h_i=2 times the adjusted deficit multiplier when M=1,N=2. Put x_i=p_i h_i. All quotients are in the usual canonical necessary envelope; no cofactor primality is imposed.

At edge j, let E_j be gain of all intervening unselected events (even, nonnegative), V_j=n_j-n_(j-1)>0, sigma_j=s_j-s_(j-1). XIX gives
    p_j(h_j+M)=p_(j-1)h_(j-1)+N(V_j-2sigma_j)-M(E_j-1+2sigma_j).
Fix any finite alphabet of nonnegative rational elapsed-time/label templates with ODD reduced denominators. Take one fixed positive odd common denominator d; write each allowed template u/d, u a bounded nonnegative integer. Choose u_j from this alphabet on every edge. Set
    tau_j=d V_j-u_j p_j,
    A_j=d h_(j-1),
    C_j=d(h_j+M)-N u_j,
    xi_j=N(tau_j-2d sigma_j)-M d(E_j-1+2sigma_j).
Exactly,
    C_j p_j=A_j p_(j-1)+xi_j.                       (1)
A_j is even, C_j and xi_j odd, so C_j and xi_j never vanish. The latter is not a claim that xi_j is small. For total relay L=sum E_j and template error R=sum |tau_j|, each |xi_j|<=C_*(L+R+1) with a fixed constant. The bound no longer involves total elapsed V directly, which can be Theta(T) per edge. If a source h_(j-1)=0, (1) requires |xi_j|>=p_j>=T, an exact local reset toll. Thus an edge departing a zero projected state cannot have simultaneously sublinear relay and template residual. This does not apply to wait templates with even denominator (e.g. 1/2).

The previous telescoping endpoint identity still holds:
    x_j-x_i=N(n_j-n_i)-M(J_j-J_i)-2(N+M)(s_j-s_i).
Since V_j=(u_j p_j+tau_j)/d, fixed length and alphabet imply total elapsed O_m(T+R). The total post-horizon gain in the word is O_m(T+L). If ANY one position satisfies |h|<=A, then
    max |h_i| <= C_m(A+1+(L+R)/T).                   (2)
This uses both directions of the endpoint identity, not a short elapsed hypothesis. In particular for L+R=o(T), all h_i=O_m(A+1).

## 2. Odd composed intercept, same-label return and reset costs

Compose (1) over k>=1 consecutive edges from position i to i+k. With A=product A_j, C=product C_j, we obtain
    C p_(i+k)=A p_i+F,
    F_next=A_next F+xi_next C_previous,
where the initial products are 1 and initial intercept is 0. For every nonempty span, A even, C odd, F odd. In particular F!=0, even if an intermediate A_j vanishes. With H=max(1, all |A_j|,|C_j| in span), Z=max |xi_j|, induction gives
    |F|<=k Z H^(k-1).                                (3)
If the endpoint labels repeat then F=(C-A)p_i, C-A odd nonzero, hence
    T<=p_i<=|F|<=k Z H^(k-1).                        (4)
This is independent of the elapsed time between the repeated labels; it is stronger in scope than the short-clock spacing p-2. In particular all labels in the m-word are distinct whenever m Z H^(m-2)<T, with a harmless m factor. Exact parity also gives nonproportionality of every pair of affine prime forms in a nondegenerate word: solving (1) with all A_j nonzero makes every label a nonconstant affine function of p_0; proportionality of any pair would force the composed intercept between them to vanish. In addition their affine slopes have strictly increasing 2-adic valuations in order, since every multiplier A_j/C_j has even numerator and odd denominator. These statements are exact, not approximate independent-prime hypotheses.

For a repeated-label word with some |h|<=A, if L+R>=T there is already a large toll. Otherwise (2) bounds H by O_m(A+1), so (4) implies the necessary bound
    L+R+1 >= c_m T/(A+1)^(m-2).                      (5)
It holds for m>=2 (with constants depending on the fixed alphabet, projection and physical scale). For fixed m and polylog A, the right side grows, so the +1 may be absorbed. Consequently for a collection of actual repeated-label words with disjoint relay and elapsed intervals, total weight >=rho X, weights <=C_w T and each word some |h|<=A (A polylogarithmic), summing gives
    sum_word (L+R) >> X/(A+1)^(m-2).                 (6)
The number of positive-weight words is at least rho X/(C_w T). If only a mean bound on minimum |h| is known, discard the large-anchor tail by enlarging the cutoff by a sufficiently large fixed factor, retaining a positive fraction of weight. Thus even without a sieve, macroscopic repeat supply under bounded normalized projection costs almost macroscopic relay or template deviation. This is a return theorem for a designated actual list and chosen templates, not an upper bound on all repeat supply. It does not assume p_j distinct or source cofactors prime. Nonconsecutive repeats with long waits are genuinely included.

## 3. Fixed-dimensional prime sieve with large elapsed times

Fix m>=3, L,R,A polylogarithmically bounded (nonnegative), total relay <=L, sum |tau|<=R, some |h_i|<=A. By (2) all h=O_m(A+1). Since xi=O(L+R+1), no A_j can vanish for large X, and (3)-(4) exclude ALL repeats. All C_j are nonzero by parity without any asymptotic assumption. This is why a short elapsed restriction is unnecessary.

Fix sides, E_j, u_j, tau_j, and the projection sequence. Then each p_i is a nonconstant rational affine form in p_0, all m forms pairwise nonproportional by the odd intercept argument. Recursively impose integer label constraints exactly as XIX. If the current first-label progression is p_0=u+k t, p_i=a t+c with integer a,c, a!=0, then the next condition is
    C_(i+1) | A_(i+1) a t+A_(i+1)c+xi_(i+1).
It is inconsistent or gives a single t residue modulo |C_(i+1)|/gcd(|C_(i+1)|,|A_(i+1)a|). Update the modulus k by this factor and the absolute slope to |A_(i+1)a|/gcd. Thus the final modulus is at most product |C_j|, polylog for fixed m. Given fixed h_0 (O(A+1) choices), at each step sum the new inverse-modulus factor over h_(i+1) (equivalently distinct integers C_(i+1) of size O(A+1) in a fixed progression). Enlarging to all nonzero such integers gives
    sum_c gcd(|c|,|A_(i+1)a|)/|c|
      << tau_div(|A_(i+1)a|) log(2+A).
Here tau_div is the ordinary divisor count, not the template error. Since |A_(i+1)a|<=C_m(A+1)^(i+1) at each stage, the elementary divisor bound with sufficiently small exponent yields, for any fixed eps>0,
    sum_(h tuples) 1/k_final <<_(m,eps) (A+1)^(1+eps). (7)
This is the same exact weighted-modulus technique as XIX, now with possibly large elapsed times.

For fixed tuple the integer parameter runs over a padded interval of length comparable to T/k_final+1, polynomially large. All relevant affine coefficients and nonzero pair determinants are polylog; use the translated fixed-dimensional upper Selberg sieve as in XIX, omitting primes dividing those coefficients/determinants and the finitely many small primes. The exceptional Euler-product factor is O((loglog X)^m) and the polynomial cutoff error can be absorbed by taking sufficiently small fixed power of the padded length. Count at most
    O(T/k_final * (loglog X)^m/log^m X)
prime label tuples. Given the first two distinct labels p_0,p_1, the fixed first relay, sides and first tau/template determine V_1=(u_1 p_1+tau_1)/d exactly. Thus the two initial horizon and clock congruences each determine one residue class modulo 2p_0 p_1 or no class. Each global range is O(X), giving O(1) possible initial horizon/time pairs. All later elapsed times and relays are fixed by the labels and template data, so the entire necessary state word follows. Exact MIN/ancestry can only reduce the count. This step is a bounded CRT multiplicity count, not a sieve on a long CRT progression.

Each E_j and tau_j is individually bounded by the respective total cutoff; the number of shift tuples is O_m(((L+1)(R+1))^(m-1)), including the fixed alphabet and sides. For weights <=C_w T per word and one increasing actual ray, obtain
    F_template,m(A,L,R)
      <<_(m,eps) X [(L+1)(R+1)]^(m-1) (A+1)^(1+eps)
                      (loglog X)^m/log^m X.           (8)
Fixed cutoffs remove the loglog factor. This extends XIX's O(X/log^m X) to genuinely long waits near finitely many odd-denominator rational ratios, without rank, cofactor primality, or narrow label gaps. There is no claim of uniformity in growing m, no proportional short-bin localization, and no lower sieve bound. The bound counts necessary candidates on one ray. No multiplication by empirical rejection rates.

## 4. Actual wait templates and macroscopic conditions

If instead the template is imposed on the actual incoming wait w_j at selected event j, then the actual elapsed V_j=w_j+W_j where W_j is intervening relay time, W_j<=3E_j by w<=2p<=3(p-1). Hence
    |tau_j|=|dV_j-u_j p_j|<=|d w_j-u_j p_j|+3d E_j.
Thus the theorem can be used with actual source/consumer wait patterns, e.g. alphabet {0,2} (d=1), residuals w_j near zero or 2p_j-w_j near zero, or {0,1/3,2/3,1,4/3,5/3,2} (d=3). Positive fixed ratios can have Theta(T) elapsed even with residual O(1). Zero template means small wait, not an actual zero tick. The residual need not be one-sided. No reason is supplied here why a broad population of usual fast events 4w<=p-1 must be near a finite template to polylog accuracy, or why arbitrary saturated words have that small absolute error.

Take actual disjoint m-word intervals in the fixed list, total weight >=rho X, weights <=C_w T. Suppose actual sums U=sum L_word=O(T log^alpha X), Rtot=sum R_word=O(T log^beta X), summed minimum |h| over words O(T log^gamma X), with nonnegative exponents. By Markov tails with slightly enlarged log cutoffs and eps chosen small enough, (8) makes weight o(X) if
    (m-1)(alpha+beta)+gamma < m.                     (9)
This is XIX's same threshold but with total TEMPLATE DEVIATION replacing total elapsed time. If the budget is for actual wait residual Rw=O(T log^beta_w X), use beta=max(alpha,beta_w) in (9). For repeats (6) alone excludes macro repeat weight under any fixed polylog exponent assumptions on those three budgets, even without (9). All charges are to actual disjoint intervals; no independent resource or missing-mass credit is created. Under near-saturation for ordered pairs the upward and downward wait deviations can be charged to the actual slack, but between-pair relays must also be charged, and the sibling XL lower bound already forces super-polylog absolute slack at top scale for a macro near-saturated ordered pair population. The present theorem does not improve XL's unconditional-in-relay saturation gap or force the remaining population into a finite rational template alphabet.

## 5. Reproducible diagnostics

[Audit 5568272](https://github.com/tara-sooo/A166944-Lean/blob/5568272a2cb4fb4a77a7bcb85f8b48acba3c757a/research/infinite-orbit/templated_clock_audit.mjs), blob 6bb17bc06660674ab943070d148c30b06242ffdc, exact remote readback. Run node research/infinite-orbit/templated_clock_audit.mjs. Actual ECMAScript executed in available tool runtime (not a separate Node invocation), all assertions passed, including a final rerun asserting odd composed intercept and pairwise nonproportionality directly.

Standard corpus reused: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1), 64512 canonical roots,9959 targeted feasible intermediate starts (not certified canonical ancestry),1616573 actual events,74191 stops,280 exits,zero unresolved cap,85254 high visits,162 independent literal gcd checks. 39205 consecutive high word incidences lengths3..5. For each of two projections M/N=1/2,3/2 and common denominators d=1,3, choose nearest allowed template u/d from u=0..2d (clipped when elapsed exceeds 2p). All 406160 transport rows,771404 composed-span parity/identity/size controls,13504 repeat toll checks,31128 zero-source toll checks pass. 110580 spans meet the finite sufficient bound for no repeats and all are distinct at their two endpoints. For nonzero A_j words,354186 exact BigInt affine progression extensions and672966 pairwise affine slope/nonproportionality controls pass.

232 projection/template incidences have L<=24, R<=24 and min |h|<=16 with all A_j nonzero, of which214 contain at least one transition V_j>=p_j/2. These are FINITE illustrative cutoffs, not assertions that the uniform sufficient condition for all labels distinct holds throughout this sample. Ten observed long-wait patterns independently enumerated by (i) source horizon and later neighbor factorization plus clock checks, and (ii) projection factorization, initial horizon CRT and clock reconstruction. Ten exact set equalities, one candidate each, all ten validated by actual incoming feasibility and deterministic forward MIN. At X4096/16384/65536, 6/3/1 patterns respectively. The patterns are chosen from observed words; no independent asymptotic supply or rejection rate is inferred. No analytic sieve constant tested.

Actual canonical example X4096,T32:
    p=61,67,41; q=79,73,121; H=4818,4890,4962;
    arrivals n=2503,2615,2624; actual waits91,95,2;
    sides1,1,0; E=12,6; V=112,9.
For projection 1/2, h=2,4,6. With d=3, templates 5/3,1/3, tau=1,-14, L=18,R=15. Equations:
    5*67=6*61-31,
    19*41=12*67-25.
Composition gives 95*41=72*61-497, the first-label integrality progression has modulus95. The long elapsed112 is greater than T and greater than its corresponding label67. This is outside XIX's stringent short elapsed hypothesis; original sample event sequence from a canonical start is observed. Independent pattern reconstruction finds the same horizon/arrival word with feasible incoming wait1 (not the original canonical incoming wait91). This distinction does not alter the later deterministic events. Final cofactor121 is composite.

Actual canonical return example p=67,47,67, h=0,0,0 for M/N=1/2 and d=1, template1 on both edges; E=18,2; V=32,37; tau=-15,-30. Rows have A=0, C=-1, xi=-47,-67. The composed intercept is67, odd and divisible by the returning label, attaining the basic |F|>=p_i condition. It illustrates the large-error escape and is not a cheap template word.

## 6. Remaining world

The short-elapsed sieve now handles long waits near a finite alphabet of odd-denominator ratios and yields a separate strong repeated-label toll for arbitrary elapsed times. General fast-recovery words can still have broad normalized waits, large projection multipliers or larger relays; no mechanism yet forces a polylogarithmic template residual. The sibling XL near-saturation baseline cost is a useful support-free obstruction but does not close this gap. Next investigate a relaxed model with broad normalized waits and growing projection multipliers satisfying the accumulated scalar restrictions, or an arithmetic relation controlling the template deviation without imposing it. No full all-constraint infinite model, uncapped arbitrary-word bound, Lean proof or finite-twin contradiction. Main and sibling branches not modified.
