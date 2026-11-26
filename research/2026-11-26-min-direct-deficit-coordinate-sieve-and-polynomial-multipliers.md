# Deficit-coordinate sieve and polynomial multiplier range at the square-root scale

Continuation of [f456b05](https://github.com/tara-sooo/A166944-Lean/blob/f456b056875e54e1948ccc74c1792a4816a08385/research/2026-11-26-min-direct-uncapped-transition-minors-and-zero-supply.md). Instead of summing all multiplier lines over the entire label range, sieve in a short interval of adjusted deficits. At square-root scale each selected label is the unique large prime divisor of a sublinear positive adjusted deficit, and a pair of labels gives only O(1) horizon candidates by CRT. In a polynomial subrange of the canonical deficit envelope, a uniform one- or two-dimensional sieve is possible without any fixed or polylogarithmic multiplier cap. The resulting range-sensitive supply bounds include nonzero-minor transitions, but do not handle all deficits of order X. Paper deductions, finite arithmetic audit; no Lean kernel verification or twin-infinitude contradiction.

## 1. Setup and uniqueness in the deficit coordinate

Fix lambda>1, eta>0, K>0, Y=lambda X, T=ceil(eta sqrt X), C=floor sqrt(Y+1), and a contiguous physical block of actual MIN events with pre-horizons in [X,Y]. For an event p, wait w, side I, e=1-2I, gain g=p-1, ordinary post-deficit d', write adjusted D=d'-6I=2hp and x=D/2=hp. Select ANY subset of the nonreset events with T<=p<=C, so x is a positive integer. Initially impose x<=K X^beta for fixed 1/2<=beta<1. This is a bound on the absolute deficit scale, not a fixed multiplier cap. The results are vacuous if the label band is empty.

For successive selected events p,h,I,e,H,x and r,k,J,f,H2,x2, define E=H2-H-(p-1), v=d2'-d1', c=x2-x=v/2-3(J-I). Call a pair close if E<=B and |v|<=A, with nonnegative integer A,B satisfying B<T-1 and Q=floor(A/2)+3<=T/2. Then |c|<=Q. The same-label spacing identity from earlier work implies p!=r, since a same-p return requires E>=p-1. Moreover x,x2<T^2 for sufficiently large X, because beta<1 and eta,K fixed. Each x has AT MOST ONE prime factor >=T, with multiplicity one (two such factors would give x>=T^2). Thus the selected prime p is uniquely determined by x and similarly r by x+c. In particular c=0 is impossible on a close edge: uniqueness would imply p=r. This handles the zero-displacement class automatically within this sublinear range. No long-clock condition, prime cofactor hypothesis, actual crossing restriction or finite-twins hypothesis is used.

For fixed x,c,E,I,J there is at most one possible p,r and they satisfy
    H=e mod p, H+p-1+E=f mod r.
Since p,r are distinct primes, this is one residue modulo pr. As pr>=eta^2 X, there are O_(lambda,eta)(1) candidate H in [X,Y]. Each H gives at most one actual starting event on a fixed monotone ray, and a fixed selected list gives at most one successor. Thus to bound the total ENDING gain of close edges it suffices to count x for which BOTH x and x+c admit a prime divisor in [T,C], then sum over c,E and the four side lists, and multiply by C times a fixed constant. We may count necessary arithmetic candidates without assuming their reachability.

Let R_x=max_selected x-min_selected x (zero if at most one selected), and let W=max(ceil sqrt X,R_x+1). The set of selected x is contained in an integer interval of length W. We shall use a general interval [L,L+W-1] with L>=T and W>=ceil sqrt X, with x,x+c both capped by K X^beta. The proof also applies to the actual smaller interval by enlarging it to W. The parameter W measures range, not accumulated variation.

## 2. Two-dimensional sieve in the deficit interval

Assume 1/2<=beta<3/4. We prove, for each nonzero signed c with |c|<=Q<=T/2, that the number of eligible x in the interval is
    <<_(lambda,eta,K,beta) W / log^2 X *
              sum_{g|abs(c)} J(abs(c)/g)/g,              (1)
where J(n)=prod_{odd primes f|n} f/(f-2).

First suppose L>=W, so x is in [L,2L) and x+c is between L/2 and 3L. With h=x/p, k=(x+c)/r the two multipliers are in [L/(2C),3L/T], each at least 1, and each at most K X^beta/T. For fixed h,k, put g=gcd(h,k), a=h/g, b=k/g. If g does not divide c there is no solution. Otherwise write c0=c/g; the congruences x=0 mod h, x=-c mod k determine one residue x0 modulo hk/g. Write
    x=x0+(hk/g) z,
    p=x0/h+b z, r=(x0+c)/k+a z.
The two linear forms are integral, and their determinant is nonzero with absolute value |c0|. Since a,b are coprime, each odd prime not dividing ab c0 forbids two distinct residues in z. Use the earlier dimension-two upper sieve, omitting the primes dividing ab c0; their loss is bounded by J(a)J(b)J(abs(c0)). The progression parameter interval can be padded to length N=ceil(Wg/(hk))+1. For every possible h,k,
    Wg/(hk) >= W/(K X^beta/T)^2
               >> X^(3/2-2beta).
Thus N is polynomially large, and log(2N)>>_beta log X uniformly. The earlier sieve cutoff floor N^(1/12) is below T for large X: W can be assumed O(X), since the actual canonical deficit envelope and W=max(ceil sqrt X,R_x+1) imply this (and larger W gives a trivial bound after replacing it by O(X)). Also the two prime labels are >=T, so their primality implies avoidance of these small prime factors. The translated-interval sieve yields
    #x for fixed h,k,c << Wg/(hk) *
                 J(a)J(b)J(abs(c0))/log^2 X.
This uses the actual length W in the deficit coordinate, rather than the full label range in the previous growing-cap proof.

Now sum over g|abs(c). For fixed g the admissible a,b lie in [L/(2Cg),3L/(Tg)], positive integers in an interval with bounded endpoint ratio (depending only on lambda,eta). From sum_{n<=z}J(n)=O(z), partial summation gives sum J(n)/n=O_(lambda,eta)(1) on such an interval, including when the lower endpoint is <1 (then upper endpoint is bounded). Drop the coprimality restriction in the positive upper sum. As g/(hk)=1/(g a b), the contribution is
    << W/log^2 X * sum_{g|abs(c)} J(abs(c)/g)/g.
This proves (1) away from the origin.

If L<W, every selected x is <2W, and x>=T. Cover [T, min(2W,K X^beta)] by dyadic shells [U,2U), U=T*2^i, padding the last shell to full length U if needed. Their total lengths are O(W). In a shell h,k are in [U/(2C),3U/T], so the same bounded-ratio harmonic summation applies. The progression length U g/(hk) is >=T^2/(9U) >> X^(1-beta), since U<=K X^beta. It again has log comparable to log X. The same proof with U in place of W gives (1) after summing shell lengths. No extra factor log X is needed. The constants in (1) may diverge as beta approaches 3/4; the exponent is fixed.

The signed-shift sum has bounded mean:
    sum_{1<=c<=Q} sum_{g|c} J(c/g)/g
       = sum_{g<=Q} (1/g) sum_{n<=Q/g} J(n)
       << Q sum_{g>=1} g^(-2) << Q.                    (2)
Thus the possible close ENDING gain, using the horizon CRT of section 1, satisfies
    F_close << C W (A+1)(B+1)/log^2 X.                  (3)
No multiplicative number of slopes or support size appears. The polynomial cap on the actual deficit x<=K X^beta permits h,k up to O(X^(beta-1/2)); for beta=3/4-epsilon with 0<epsilon<1/4 this is the power X^(1/4-epsilon), well beyond the previous polylogarithmic range. This is a range-sensitive theorem, so it does not assert that the old full-window bound with no W factor holds for such caps.

## 3. One-dimensional extension up to any strictly sublinear deficit scale

For fixed 1/2<=beta<1, count only the first prime condition x=hp. The other prime r, when it exists, is still uniquely determined by x+c, and the horizon CRT still gives O(1) candidates. If L>=W, h lies in [L/C,2L/T] and h<=K X^beta/T. For fixed h the prime p lies in a translated interval padded to length N=ceil(W/h)+1, with W/h>>X^(1-beta). The elementary one-dimensional upper sieve gives O(N/log(2N)) uniformly on translated intervals (the same Selberg proof as the preceding fixed-dimensional sieve with one forbidden residue; its z^6 error is absorbed at z=floor N^(1/12)). The cutoff is below p. Summation of 1/h on the bounded-ratio multiplier range costs O(1). Therefore the count of x is O(W/log X). For L<W use the same dyadic shells [U,2U), where U/h>=T/2, and sum shell lengths O(W). This gives the weaker but wider-range result
    F_close << C W (A+1)(B+1)/log X.                    (4)
In particular no long-clock hypothesis is required in either (3) or (4). This covers nonzero cofactor-multiplier minors regardless of their magnitude. Within these caps the previous zero-minor case with integer slope m=1,2 cannot occur when its prime-cofactor hypothesis holds, since it requires x>=p(q+1)=Theta(X). We do not need that exclusion for the counting proof.

## 4. Range-sensitive product obstruction

Let F be the total selected gain, U_out=G-F the entire complementary gain, V_d=sum physical |d'-d|. For successive selected edges, the relay intervals are disjoint and sum E<=U_out, while the post-to-post intervals are disjoint and sum |v|<=V_d. The first chosen event contributes <=C. Consequently for nu=2 in the range beta<3/4 or nu=1 in beta<1,
    F <= C + O(C W (A+1)(B+1)/log^nu X)
              + C U_out/(B+1)+C V_d/(A+1).              (5)
Use z=C U_out/X, y=C V_d/X, u=C R_x/X. Since C=Theta(sqrt X), C W=O(X(1+u)). Also R_x<=V_d/2+3, so u<=y/2+O(C/X). If F>=rho X for fixed rho>0, then
    (1+z)(1+y)(1+u) >>_(rho,lambda,eta,K,beta) log^nu X. (6)
Indeed if the product exceeds log^nu X there is nothing to prove. Otherwise A=ceil(K0 y), B=ceil(K0 z) with sufficiently large fixed K0 depending on rho are polylogarithmic and satisfy the close assumptions for large X. The last two terms in (5) are <=2X/K0, and C=o(X); rearrange the close supply bound. The actual range u can be much smaller than the total variation y. In particular
    (1+z)(1+y)^2 >> log^nu X,
    U_out+V_d = Omega(sqrt X log^(nu/3) X).
If U_out=O(sqrt X), then V_d=Omega(sqrt X log^(nu/2) X). If V_d=O(sqrt X), then U_out=Omega(sqrt X log^nu X). These are new necessary restrictions for polynomial multipliers on square-root label populations. They do not improve every fixed-multiplier regime of the earlier theorem: when h is fixed, the older product bound with only one factor of (1+y) is stronger.

## 5. A high-deficit alternative without imposing a cap on the chosen population

Now choose an arbitrary subset of ALL positive-multiplier nonresets p in [T,C], with total F>=rho X, and no deficit cap. Keep z,y,u defined for the full selected list. Fix beta in either range of the corresponding nu above and H_cap=K X^beta. Count only close edges having BOTH endpoint x<=H_cap. Such an edge is consecutive also in the sublist restricted to x<=H_cap. The sublist range is at most R_x, so (3) or (4) bounds those endings with the SAME W from the full list. A close edge not of this type has ending x>H_cap-Q (if only its first x is above the cap, use |c|<=Q). Thus if F_high denotes the total chosen gain with x>H_cap-Q,
    F_high >= F-C-C U_out/(B+1)-C V_d/(A+1)
                   -O(C W (A+1)(B+1)/log^nu X).          (7)
This argument does not require that the omitted high-deficit gain be part of a small outside budget. It is an actual alternative for the uncapped selected population, not an inference from the product theorem applied to a subset with an uncontrolled complement.

In particular suppose (1+z)(1+y)(1+u)=o(log^nu X). Choose a factor L0(X)->infinity sufficiently slowly that L0^2 times that product is still o(log^nu X), and take A=ceil(L0 y), B=ceil(L0 z). They are polylogarithmic, with Q=o(X^beta). The error terms of (7) are o(X). Therefore
    gain of selected events with x>(K-o(1))X^beta
        >= F-o(X).                                     (8)
Taking nu=1 permits every fixed beta<1 (beta>=1/2). For beta>1/2 these same budget hypotheses also give V_d=O(sqrt X polylog X)=o(X^beta). If F>=rho X, (8) then implies throughout the entire physical block ordinary deficit d>=2K X^beta-o(X^beta): there is a high selected post state and no other state can differ by more than V_d. This is a high-baseline-deficit alternative on the actual ray. It is not an absolute exclusion of high deficit. It shows that in a genuinely low-relay, low-variation near-square-root population, the residual mechanism cannot be explained by even polynomial but strictly sublinear deficits. The condition (1+z)(1+y)(1+u)=o(log X) is much stronger than macroscopic smallness U_out=o(X), V_d=o(X), and has not been forced by the crossing argument. No claim of elimination of the overall large-event branch is made.

Remaining directions: the near-linear deficit scale x=X^(1-o(1)), where the short-interval parameter length may be bounded and the above sieve saving fails; or improve the relay/range/variation budgets from the dynamics. The nonzero-minor class at near-linear x remains open. The earlier small/middle crossing alternatives also remain.

## 6. Finite diagnostics and persistence

[Audit 9d2e0bf](https://github.com/tara-sooo/A166944-Lean/blob/9d2e0bf243135234cb95f76df04a47568442b453/research/min_direct_deficit_coordinate_sieve_audit.mjs), blob143f4941fd03df769515973eccbbb38ec46600f3, exact remote readback. Run node research/min_direct_deficit_coordinate_sieve_audit.mjs 60000. Actual ECMAScript execution in tool runtime, not separate Node. 29998 odd canonical roots through60000,549085 events,0 cap180 unresolved. 52152 nonempty block controls with finite thresholds17/31/47/71, cap C=4T and x<T^2-A-4,131265 selected incidences,79113 successive filtered pairs. 3762 close pairs, all with nonzero displacement and nonzero minor in this finite scan; 7524 unique-large-divisor checks,3762 deficit and horizon CRT checks,25824 prime-line residue checks,3762 tuple-capacity checks with no duplicate physical start within a control. 46309 near-origin and5843 away-origin interval controls,108885 shell intervals,52152 range and gain-budget checks. Independent translated interval congruence checks:2310 systems,39664 exact CRT hits,6930 prime-line residue comparisons. 2048 finite J mean checks,12 weighted gcd-mean controls (floating tolerance for the positive singular-factor means). Representative p43,r31,h3,k4,x129->124,c-5,E0,H1848->1890. Counts overlap across roots and finite cutoffs. The scan exercises exact arithmetic and budgets using finite analogues of uniqueness, not asymptotic square-root scale or polynomial cap hypotheses. The earlier analytic Selberg estimate is reused; no numerical proof of its asymptotic constant. All final assertions passed. No Lean kernel verification or external novelty claim. Main and sibling branches not modified.
