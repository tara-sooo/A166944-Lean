# Hypothetical infinite MIN worlds XII: close-label affine sieve and joint factor-clock coordinates

2026-11-26 JST. Continuation of [fe66ed3](https://github.com/tara-sooo/A166944-Lean/commit/fe66ed306ed73aa7ae91658fb98882eecf8c526c), independently of the two sibling lanes. Sources: [V entry sieve](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md), [IX rational clock](https://github.com/tara-sooo/A166944-Lean/blob/9733fd234d882609b87ad2cef1fba038f93b5935/research/infinite-orbit/rational_clock.md), [X cofactor capacity](https://github.com/tara-sooo/A166944-Lean/blob/aef03d14e390358f0b9b0cc1583cd98376e74d61/research/infinite-orbit/cofactor_support.md), [XI factor graph](https://github.com/tara-sooo/A166944-Lean/blob/fe66ed306ed73aa7ae91658fb98882eecf8c526c/research/infinite-orbit/factor_pair.md). Sibling preflight [direct 1b10c9f bounded recovery words](https://github.com/tara-sooo/A166944-Lean/blob/1b10c9f93f06afc11f5cf941f4bb6985d1df14b4/research/2026-11-26-min-direct-causal-exposure-and-bounded-recovery-words.md) and [unified 2b7fa7d rough-source transition graph](https://github.com/tara-sooo/A166944-Lean/blob/2b7fa7d8083ff8798756215e1fe3c242ea33bd19/research/2026-11-26-min-unified-source-transition-graph.md). The new sieve counts close LABEL transitions rather than fixed labels over a long horizon interval. This allows the square-root scale, and the weaker version does not require a prime or rough cofactor at the downstream event. Paper deductions and finite arithmetic diagnostics, not Lean verification or an external novelty claim.

## 1. Setting and simultaneous exact identities

Consider an actual physical contiguous MIN block with pre-horizons in [X,lambda X), lambda>1 fixed, T>=eta sqrt X, B=floor sqrt(lambda X+1), fixed eta>0. Select any ordered list of complete events with T<=p<=B, retaining actual intervening physical events. Each selected event has H=pq+e, e=1-2s, q odd >=p, g=p-1, post (J,n)=(H+g,t+w). The selected p is prime but q may be composite. As in X and IX define a=q+1=(J+2s)/p (even), c=(n-2s)/p (integer of parity s). Both q,a,c are Theta(T) uniformly in the canonical envelope H/2<=t<=3H+3; arbitrary intermediate states satisfying this envelope may also be considered for local feasibility, without ancestry. The envelope holds for canonical rays.

For two consecutive selected events let the downstream label, cofactor, side and clock quotient be r,u,t_side,c2, with f=1-2t_side. Write
    delta=r-p, j=u-q, k=c2-c, sigma=t_side-s,
    E=H2-J (all intervening unselected gain), V=n2-n (actual elapsed time),
    D=E-1+2sigma, R=V-2sigma.
Then E is even >=0, j and delta are even, D odd nonzero, and V=W+w2 with 0<=W<=3E. Direct subtraction of horizon and corrected clock identities gives
    delta*a+(j-1)*r=D,
    delta*c+k*r=R.                                  (1)
The equivalent prime-factor equations are
    delta*q=(1-j)*p+D-delta*j,
    delta*u=(1-j)*p+D.                             (2)
These identities hold even for composite q,u and any waits, with no independence of phase.

If delta=0 then q and u differ by a positive even integer because H2-H>=p-1 and T>=5. Thus E>=p-1 (the same-label toll holds even without prime cofactors). Assume now delta!=0, and put A=1-j, C=D-delta*j. Both A and C are odd nonzero. If E=o(T), then |j|<=1+(|delta|*a+E+3)/T=O(|delta|+1). Since V<=3E+2r, also |k|=O(|delta|+1). All constants here may depend on lambda,eta. In particular these bounds are uniform if |delta|,E are polylogarithmic.

## 2. Nondegenerate three or four prime forms

Fix nonzero even delta, even j, even E>=0 and the two sides. Equation (2) requires A p+C=0 mod delta. If d=gcd(|delta|,|A|) does not divide C there is no candidate; otherwise p is one residue class modulo |delta|/d. Write p=p0+(|delta|/d)z with 0<=p0<|delta|/d. Equations (2) give integer affine forms for q,u on this progression, alongside p,r=p+delta. For K,L bounded by fixed powers of log X and 0<|delta|<=K, E<=L, all affine coefficients and intercepts are bounded by a fixed polynomial in log X. For any actual candidate the sign of A is the sign of delta for sufficiently large X: delta*q=A*p+C and |C| is polylogarithmic while |delta|q>=2T. Thus q grows with p along the progression. This observation is only used for localization.

If the first cofactor q is prime, sieve the three forms p,r,q. All pair determinants are nonzero: before scaling by the progression and delta their nonvanishing is equivalent to
    delta !=0, C=D-delta*j !=0, C-A*delta=D-delta !=0.
The last two are odd, so no zero determinant can hide in a short relay. The target cofactor u need NOT be prime or rough. In particular a positive ordinary drift source (2w>p-1) at square-root scale has prime q eventually by X's cube exclusion, and this three-form sieve applies even to a fast downward target with composite u.

If both q and u are prime, add the fourth form u. Its determinants with p,r are D and D-A*delta, odd nonzero; the q,u determinant is nonzero if j!=0 (their common nonzero slope and distinct constants). The remaining case j=0 cannot occur in an actual selected semiprime pair with E<=L<T-1: XI's shared-factor toll gives E>=p-1. Thus the fourth form is nondegenerate for all actual pairs in the short-relay population. The integer candidate census can also omit j=0 in this four-prime case by the same arithmetic horizon bound. Square events need no separate error term here: the sieve counts them as particular parameter values, not identical forms. This is a dimension-three or dimension-four upper sieve on affine forms, NOT a four-form roughness assumption about an actual downward consumer.

## 3. Localized sieve with summed label-gap and relay alphabets

Let the source pre-horizons be in any translated interval of length Hspan, contained in the physical window, with Hspan>=T^(1+epsilon) for fixed epsilon>0 and Hspan=O(X). We do not require the target to lie in the same subinterval, only in the physical window; imposing that condition reduces the count. For fixed tuple (delta,j,E,s,t_side), valid z have span O((Hspan/T)*d/|delta|+1) because p,q both increase along the progression, q>=T, and product pq increases by at least T times the change in p. Pad to parameter length N comparable to this quantity. Since K,L are polylogarithmic, N is polynomially large in T uniformly over the tuples. The dimension-nu (nu=3 or 4) translated upper Selberg bound used in V and the sibling lanes, with cutoff floor(min(T,N)^(1/24)), gives
    # candidate source horizons
       << N * (log log X)^nu / (log X)^nu.            (3)
Indeed all primes larger than nu outside the nonzero product of leading coefficients and pair determinants have nu distinct forbidden roots; omit the finitely many small primes and the exceptional divisors of that product. Its magnitude is polylogarithmic in X, so the exceptional Euler factor is at most the product over all primes up to a fixed power of log X of (1-nu/f)^(-1), which is O((log log X)^nu) by Mertens. The cutoff is below all actual prime values, and the fixed-dimensional sieve error O(cutoff^6) is absorbed in N/log^nu X. Constants may depend on lambda,eta,epsilon and the fixed powers bounding K,L. For fixed K,L the exceptional factor is bounded by a constant, so the loglog factor is unnecessary. All tuple constraints are necessary only; no lower bound on actual MIN choices follows from candidate counts.

There are O(L+1) choices of E and four side choices. At a given delta, |j|=O(|delta|+1), so using gcd(n,m)=sum_{d|n,d|m} phi(d) gives
    sum_j gcd(|delta|,|1-j|) << |delta| tau(|delta|).
Dropping the even-parity condition on j only enlarges the upper bound. Divide by |delta| and sum over 0<|delta|<=K; sum_{n<=K}tau(n)<<K log(2K), by the elementary divisor hyperbola bound. The additive 1 in the padded length is absorbed uniformly by (Hspan/T)*d/|delta|, since Hspan/T is polynomial and K polylog. Sum (3), weight every pair by at most O(T) (either endpoint gain or actual matched mass <=O(T)), and use that each candidate source pre-horizon identifies at most one occurrence of a consecutive selected pair on the actual ray. We obtain
    F_nu(Hspan;K,L)
      << Hspan (L+1) K log(2K)
                  (log log X)^nu / (log X)^nu,       (4)
where K>=2, L>=0, both at most fixed powers of log X, and F_nu is the total such weight on pairs with 0<|r-p|<=K and E<=L. For nu=3 the source alone has prime cofactor; for nu=4 both do. For fixed K,L the bound is O(Hspan/log^nu X). With the same-label population included, add its actual weight O(U) by the same-label toll (for endpoint gain at r=p this is exactly <=U; matched weights may have a constant factor). For L<T-1 there are no same-label pairs at all.

This gives a joint small-alphabet obstruction, not a bound on the whole four-distinct-prime class. For example K,L=O((log X)^a) with 2a<nu gives o(Hspan) gain. Unlike XI's fixed factor-ratio strip, these are differences between successive SELECTED labels, with the cofactor differences determined by the horizon equation. The proof needs no long-bin length greater than the product of the two labels: it is valid at square-root-scale labels in Hspan=X/polylog X. It does NOT give the same logarithmic saving on Hspan=O(T) or on the logarithmic recycling bins; there the number of affine parameters is too small. It also does not cover label shifts of order T.

## 4. A macroscopic relay-versus-label-variation alternative

Take Hspan=Theta(X). Suppose a population of consecutive selected transitions carries source (or ending) gain F>=rho X, rho>0, with source prime cofactor (nu=3), or both prime cofactors (nu=4). Define V_p=sum |r-p| on that population and U the full complementary gain of the selected list. Each transition's source and target have gain Theta(T). Its relay is disjoint from the other relays of that list. Consequently the total gain with |delta|>K is O(T V_p/K); with E>L it is O(T U/L) for L>0. If U=o(X), same-label pairs carry o(X) gain. Thus, for fixed nonnegative alpha,beta with alpha+beta<nu, the three conditions
    F>=rho X, U=O(T (log X)^alpha),
    V_p=O(T (log X)^beta)
are incompatible for sufficiently large X. Proof: choose epsilon0>0 with alpha+beta+2epsilon0<nu, K=ceil(log^(beta+epsilon0) X), L=ceil(log^(alpha+epsilon0) X). Both tails are o(X), and (4) makes the remaining positive-gap part o(X). This is a paid variation alternative for the ACTUAL prime labels, not ordinary deficit variation. In particular bounded average relay and bounded average prime-label jump cannot sustain a macro semiprime population, even with varying deep multipliers and times. For alpha=0 the exponent on average label variation must reach at least nu in the sense that no fixed beta<nu suffices; this statement is an exclusion of simultaneous upper bounds, not a pointwise lower at exactly log^nu including secondary factors. If U can grow faster than any polylog times T, or V_p=Theta(X), the argument leaves the regime open.

Original-tag extension: apply (4) to actual source horizons in each original lifetime of length Hspan (or to disjoint source bins with admissible length); arbitrary shared trajectories are counted separately per tag. If a macro tagged weight population at scale N Hspan is supported on disjoint successive transitions on each tag, the same tail argument uses summed U and V_p with T in the numerator and N Hspan in the denominator. For example U_tag=O(N Hspan/T log^alpha X), Vp_tag=O(N Hspan/T log^beta X) with alpha+beta<nu cannot support macro tagged weight. No independent source ensemble or core-only missing-wait conclusion. For arbitrary overlapping causal source-consumer words one must use their actual non-reuse/exposure or disjoint packing before charging relay budgets. The physical interval E in (1) may include ANY intervening high events, but small low gain alone is not small E. In particular the bounded words extracted by direct 1b10c9f have E=O(T), not necessarily polylogarithmic; the present sieve does not automatically exclude them.

## 5. Clock alignment in the complementary large-denominator regime

Eliminate r from (1):
    delta * [(j-1)c-k*a] = (j-1)R-k*D.             (5)
Since a=q+1, the source corrected slope is mu=c/a. The integer j-1 is odd nonzero. If E=o(T), delta!=0, and V<=3E+2r, the bounds in section 1 give
    |(j-1)c-k*a| << E+V+1,
    |mu-k/(j-1)| << (E+V+1)/(T |j-1|).              (6)
For close-label, very fast-ending transitions with E+w2=o(T), this is a genuine narrow rational strip for the source slope, even if the actual reduced denominator of mu is of order T. The approximating ratio has denominator <=O(|delta|+1), potentially much smaller than the actual denominator. This is not IX's small-denominator equality: the approximation can be off-line, and the window width is on the quotient coordinate (a,c), not directly the original (J,n). For sufficiently large T in this fast regime the approximating ratio is positive since mu>=1/2 and the error tends to zero. If source side s=1 then c is odd and a even, hence (j-1)c-k*a is odd nonzero. So equality in (6) is impossible, and (5) enforces
    |(j-1)R-k*D| >= |delta|.
For s=0 a zero determinant is not generally excluded. If it occurs, the source slope equals k/(j-1) exactly and its reduced denominator divides the odd number |j-1|. Neither outcome alone yields a bound on the total fast population. A further restriction on the number of admissible offsets or on the source slopes would be needed to turn (6) into a new macroscopic exclusion.

This is an exact simultaneous product/clock relation with a prime-cofactor-free clock part. It leaves arbitrary large label jumps and O(T) elapsed time unconstrained by a narrow tube. It also complements rather than adds to the earlier rational clock budget: the actual gains/relays are the same physical resource.

## 6. Reproducible finite checks

[Audit 3206a1b](https://github.com/tara-sooo/A166944-Lean/blob/3206a1b180f81bbb5ddda517ffa23f92d46815cb/research/infinite-orbit/close_factor_clock_audit.mjs), blob 0461473599263a232e54fcbbae8b7fd399ae983b, exact remote readback. Run node research/infinite-orbit/close_factor_clock_audit.mjs. Actual ECMAScript executed in available tool runtime; not a separate Node invocation. All final assertions passed.

The same canonical and targeted start construction as XI at X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1): 64,512 canonical roots, 9,959 targeted feasible intermediate starts (not necessarily canonical ancestry), 1,616,573 actual MIN events, 74,191 finite stops, 280 upper exits, zero cap-unresolved. 85,254 high visits, 43,275 consecutive high-pair joint clock controls including 42,529 distinct-label affine determinant controls. 162 independent literal tick gcd controls. The high list includes ALL p>=T, without requiring semiprime status or positive drift.

| X | all high pairs | 0<abs(delta)<=16,E<=16 | source prime q | both cofactors prime | composite target cofactor with prime source q |
|---:|---:|---:|---:|---:|---:|
|4096|4308|772|650|571|79|
|16384|9326|644|588|584|4|
|65536|29641|277|180|180|0|

Across those close pairs, 310 have fast ending 4w<=g (whether or not source q prime); 83 have prime source and composite target, so the three-form class strictly extends the four-form class in this finite scan. No zero clock determinant in the close-pair sample. This does not establish the asymptotic absence of that case.

Actual canonical fast composite-target example:
    H=8850,t=4560,p=53,q=167,s=1,w=53,J=8902,n=4613,
    H2=8910,t2=4620,r=67,u=133=7*19,t_side=1,w2=5,
    J2=8976,n2=4625.
Here delta=14,j=-34,k=-18,E=8,V=12,D=7,R=12, a=168,c=87. Equation (5) has LHS 14*(-21)=-294 and RHS (-35)*12-(-18)*7=-294. The downstream clock is fast, the source ordinary drift positive. The first cofactor is prime but the target cofactor composite, so no sieve treating all four as prime is justified on this example. The approximating ratio k/(j-1)=18/35, actual mu=29/56.

Independent candidate census (not actual MIN selection): at each X and K=2,4,8,16, L=0,4,16 enumerate ALL source prime products p q, both sides and even E<=L, factor the target H2-f for eligible distinct r within K, and compare exact sets with the affine congruence construction from (2). 36 global set equalities, 25,528 three-form candidates and 7,992 four-form candidates on each route (overlapping configurations). 72 localized count equalities in translated bins of length ceil(X^.75) at two offsets. This tests the parametrization, not the asymptotic sieve bound. For X=65536, K=2,L=0 counts 63/18; K=16,L=16 counts 4611/1330. Actual time competition and roughness can further reduce these candidates. No Lean kernel verification.

## 7. Remaining world

A macro square-root-scale population sourced at actual semiprime events cannot have simultaneously polylogarithmically small average complementary relay and average prime-label variation with exponent sum below 3 (or 4 when both endpoints are semiprime). At very fast close-label transitions the clock equation additionally ties the source slope to the cofactor/clock quotient jumps. These restrictions still allow large jumps, diverse labels, relay gain on the order of T, and the general composite-cofactor fast population. The current sibling bounded-recovery-word regime allows O(T) spans with o(T) low gain, which does not force the small E or delta hypotheses. Next: analyze bounded words allowing intermediate high labels, or construct a relaxed diverse-label model meeting these and earlier scalar constraints to identify what exact MIN arithmetic still obstructs. No full all-constraint infinite survivor, general uncapped mixed-run bound, Lean proof or finite-twin contradiction. Main and sibling branches not modified.
