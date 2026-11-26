# Uniform growing-multiplier double sieve and zero-stratum twin chains

Continuation of [c508001](https://github.com/tara-sooo/A166944-Lean/blob/c50800116999a2a8d29f3c5bd695145099254126/research/2026-11-26-min-direct-close-transition-double-sieve.md). Make the previous multiplier-cap dependence explicit using primitive slopes, the gcd divisibility of the displacement, and the mean of the singular factor. Separately, remove all multiplier caps for zero-adjusted-displacement close chains at the cube threshold: their two-label support forces a short repeat or a large ratio of labels. Paper deductions and finite diagnostics; no Lean kernel verification or twin-infinitude contradiction.

## 1. Setup and primitive slopes with growing cap

Use the actual MIN model and previous notation. Fix lambda>1,Y=lambda X, C=floor sqrt(Y+1), physical event block with pre-horizons in [X,Y], gain G=O_lambda(X). At an event p, g=p-1, ordinary deficit d=2t-H, wait w, side I, e=1-2I, post d'=d+2w-g, adjusted D=d'-6I=2hp (positive h for nonreset). Fix a>1/14 and 0<epsilon<a, take T>=X^a, T<=C, and allow an integer multiplier cap M=M(X) in
    1<=M<=X^(a-epsilon).
Select any subset of actual nonresets p>=T,1<=h<=M, in physical order. Two successive chosen events p,h,I,H,d1' and r,k,J,H2,d2' have relay gain E=H2-H-(p-1)>=0, ordinary difference v=d2'-d1', c=v/2-3(J-I). As before,
    kr-hp=c.
Close means E<=B, |v|<=A with nonnegative integer A,B satisfying
    B<T-1, A/2+3<=T/2,
    A+5B<=(T-1)/2.                                     (1)
The last condition can be omitted if every selected first event is long (4w>=p-1); otherwise it ensures the second is long because the intervening ordinary drift is <=5E in absolute value. Close pairs have distinct labels p,r (any same-label return requires E>=p-1). Also c!=0 because h,k<=M<T. In contrast to the fixed M proof, the ratio r/p is not bounded by an absolute constant, so it must be kept in the counting.

Let g0=gcd(h,k); g0 divides c. Set a0=h/g0,b0=k/g0,c0=c/g0. The slopes a0,b0 are coprime and positive. The solutions are
    p=p0+b0*z, r=r0+a0*z, b0*r0-a0*p0=c0.
For p in a dyadic band U<=p<2U with U>=T/2, the parameter z lies in at most N_p=ceil(U/b0)+2 consecutive integers. Since |c|<=T/2<=p/2, for each actual solution
    a0*p/(2b0)<=r<=3a0*p/(2b0).
Write V=a0*U/b0, so r is comparable to V with absolute constants; if the band has any admissible pair, V<=2C and V>=T/3. If none, its contribution is zero.

## 2. Uniform sieve for the label line

Let J(n)=prod_{odd primes f|n} f/(f-2) for positive n. In the primitive z line, two distinct roots modulo every odd prime f not dividing a0*b0*c0 are forbidden by primality of p and r. Discard all primes dividing this product (and 2). The previously proved dimension-two sieve with omitted factors gives
    #label pairs << N_p J(a0*b0*abs(c0))/log^2(2N_p).
Indeed for the generic Selberg denominator discard all exceptional primes, and the complete denominator decreases by at most the product J(a0*b0*abs(c0)), by splitting the squarefree divisor sum on those factors. This is uniform even when the slopes grow. The error N_p^(1/2) at sieve cutoff floor N_p^(1/12) is absorbed by the displayed bound. Here N_p>=U/b0>=X^epsilon/2, so log(2N_p)>>_epsilon log X, and N_p<<U/b0 for large X. The sieve cutoff is below the prime labels: N_p=O(C), and a>1/14>1/24. Therefore
    #label pairs <<_epsilon (U/b0)
                    J(a0)J(b0)J(abs(c0))/log^2 X.       (2)
This explicitly retains the reciprocal primitive slope 1/b0 and uses J(xy)<=J(x)J(y). It avoids the crude count of O(M^2) choices each charged at unit weight. All constants in this section are independent of the cap M.

## 3. Horizon sieve and summing the dyadic bands

For fixed p,r,e,f,E, the necessary horizon residues H=e mod p, H+p-1+E=f mod r give one progression of step pr. Its intersection with [X,Y] has length O_lambda(1+X/(pr)) in the integer progression parameter. At least one of the endpoints is long, by (1) or the first-long selection, so both neighbors of that endpoint avoid all primes below (T-1)/8. As in the previous note the horizon progression has two distinct forbidden roots for each odd sieve prime below both p,r, because pr is invertible. The cutoff floor N^(1/12) with N=O_lambda(1+X/T^2) lies below the roughness threshold by a>1/14. Thus the number of candidate horizons is
    <<_lambda (1+X/(pr))/log^2(2+X/(pr)).
We may charge each candidate the ending gain r-1. Since p,r<=C and pr<=Y+1, the numerator after weighting is at most O_lambda(X/U). Choose p bands U comparable to C*2^(-j) for j>=0; throughout such a band pr<=2UC, hence log(2+X/(pr))>>_lambda (j+1). Combining this with (2), the weighted count for fixed h,k,c,e,f,E and one band is
    <<_(lambda,epsilon) X J(a0)J(b0)J(abs(c0))
                  /[b0 log^2 X (j+1)^2].
There is at most one actual pair with a given first H on the fixed ray, and the two bounds are deterministic, not an independence hypothesis. Summing the convergent j series gives the same bound without (j+1)^2. It is valid for noncomparable p,r; the use of r as ending-event weight cancels the r from the horizon density.

Let Q=floor(A/2)+3. The earlier singular-factor mean gives sum_{n<=L}J(n)<=e L, and by partial summation sum_{n<=L}J(n)/n=O(log(2L)). Summing over h,k,c is now done by g0,a0,b0,c0, with g0<=min(M,Q), a0,b0<=M/g0, 0<|c0|<=Q/g0. Dropping coprimality in this positive upper sum yields
    sum J(a0)J(b0)J(abs(c0))/b0
       << sum_{g0<=min(M,Q)}
             (M/g0) log(2M/g0) (Q/g0)
       << M Q log(2M).
The convergence of sum g0^(-2) is the reason that the final bound is linear in M up to one logarithm. There are four side lists and at most B+1 shifts E. Thus we obtain the uniform growing-cap bound
    F_close <<_(lambda,a,epsilon)
            X M log(2M) (B+1)(A+1)/log^2 X.             (3)
F_close is the total ENDING-event gain of close consecutive selected transitions, not count of possible pairs across arbitrary trajectories. This is valid for any selected subset with the stated cap, uniformly in M,A,B, with (1) or its first-long alternative. The case fixed M reproduces the previous theorem. If M log(2M)(A+1)(B+1)=o(log^2 X), this population has o(X) gain. In particular fixed A,B allow M=log^(2-delta) X for every fixed 0<delta<2. No upper bound on h beyond the stated cap has been proved.

## 4. Product obstruction with a growing multiplier cap

Let F be total chosen gain, U_out=G-F and V_d=total ordinary deficit variation on the entire physical block. The disjoint relay and post-to-post budgets from the preceding proof give
    F <= C + O(X M log(2M)(B+1)(A+1)/log^2 X)
                  + C U_out/(B+1)+C V_d/(A+1).           (4)
Suppose F>=rho X for fixed rho>0. Put L_M=log^2 X/[M log(2M)], x=C U_out/X, y=C V_d/X. Then
    (1+x)(1+y) >>_(rho,lambda,a,epsilon) L_M.             (5)
When L_M is bounded the assertion is trivial after adjusting the constant. Otherwise, if the product is <=L_M, take B=ceil(K x), A=ceil(K y) with sufficiently large fixed K depending on rho. Both cutoffs are O_rho(log^2 X), so (1) holds eventually. The last terms in (4) are <=2X/K; the close bound is O(X(1+x)(1+y)/L_M). This proves (5) with uniform constants. If L_M tends to infinity then
    U_out+V_d = Omega(X sqrt(L_M)/C).
For M=floor(log^(2-delta) X) this is Omega(sqrt X log^(delta/2) X /sqrt(loglog X)), for fixed 0<delta<2. If either U_out or V_d is O(X/C) then the other must be Omega(X L_M/C). This extends the fixed-cap relay-variation tradeoff, with the expected weaker lower bound as more multipliers are permitted. As before U_out includes all resets and omitted high-multiplier events, not just events outside the high-crossing population.

## 5. Zero adjusted displacement at the cube threshold: no multiplier cap

Now allow ALL positive multipliers. Use T=T_3 from [crossing-clock hierarchy](https://github.com/tara-sooo/A166944-Lean/blob/c50800116999a2a8d29f3c5bd695145099254126/research/2026-11-26-min-direct-crossing-clock-and-factor-hierarchy.md), so T>=1+ceil(9(Y+1)^(1/3)), and C as before. Select any subset of nonreset events p>=T, in order; initially we assume each is long. Form maximal chains joined by edges between successive selected visits with c=0 (equal adjusted D) and relay gain E<=B<T-1. These edges have ordinary post difference at most6; imposing the previous A bound as well can only shorten the chains. All D are positive multiples of 2p. On a canonical ray ordinary d' is <=6+5(H_post-H_root)=O(Y), more precisely <=5(Y+C)+6, so the common D/2<T^3. Every selected label in one chain divides this same positive integer D/2, hence there are at most TWO distinct labels >=T. Adjacent labels cannot coincide because E<T-1. Every chain of size>=2 therefore has exactly two labels and alternates between them. In particular every edge between distinct p,r needs D>=2pr and multipliers h>=r,k>=p. These are well beyond the cap in (3); no fixed-cap hypothesis is imposed here.

For three consecutive selected visits of one chain with labels p,r,p, let E1,E2 be their two intervening gains. The repeated p has odd cofactors q1,q3, and
    p+r-2+E1+E2 = H3-H1 = 2m p+e3-e1,
    m=(q3-q1)/2>=1.                                     (6)
If p>r, then H3-H1<=2p-2+2B<4p-4, so q3-q1<4 and m=1. Both endpoints are long and above the cube threshold, so q1,q3 are prime: this is a direct twin witness with lower member >=p>=T. It does not use any no-twin assumption or a fixed multiplier.

More generally both repeated endpoints have the SAME adjusted D, so by the previous exact mod3 and parity constraints, if m!=1 then m>=5. Equation (6) then implies
    r >= 9p-2B.                                         (7)
Thus an equal-D close triple avoiding a twin witness must repeat the SMALLER label and have a much larger middle label. In particular if both labels lie in a factor-two band [U,2U) with U>=T and B<T-1, then H3-H1<3p-2+2B<5p-4, implying m<=2 (indeed H span <5p). Since an equal-D long non-twin return needs m>=5, a twin witness follows. The same conclusion holds for arbitrary ratios r/p bounded above by rho0 when rho0+1+2B/T<10. A sufficient condition is (7) violated. No assertion that every allowable large-middle triple is realized.

If there is no twin witness in a chain, it has at most THREE selected visits, since any four alternating visits contain a triple repeating the larger label. In a factor-two band such a chain has at most TWO visits. Even without excluding twins a chain has at most FIVE visits: six alternating visits contain three occurrences of the larger label, and successive returns of this label would both have m=1. But the old mod3 identity requires every m=1 long return to flip the sign representative e*p mod3 from +1 to -1. Two successive m=1 returns cannot occur. These arguments hold for arbitrary intervening unselected events of total gain <=B per edge, not just consecutive physical events.

If the selected events are not required long, each successor in a zero-close edge is automatically long whenever 6+5B<=(T-1)/2, by the earlier ordinary drift identity and |v|<=6. Only the first event of each chain may fail the long condition. Delete it for the preceding arguments; the length bounds become at most FOUR without a twin witness and at most SIX unconditionally (at most THREE without a witness within a factor-two band). Any twin extracted uses two certified long events, not an uncertified first event. We use the all-long selection below for a clean weighted criterion.

## 6. A weighted twin forcing criterion independent of multiplier and deficit movement

Take any selected all-long high nonreset population contained in a factor-two band [U,2U) with U>=T_3, and let F be its total gain. Let Z be the total ending-event gain of the zero-close edges c=0,E<=B<T-1 in its filtered consecutive-visit graph. Each vertex has at most one incoming edge and one outgoing edge, so the zero-edge chains partition the population into components (including singletons).

Without a twin witness every component has at most two vertices by section 5. For a two-vertex component the ending gain is less than 2U-1 while the first gain is at least U-1. Therefore its ending gain is at most (2U-1)/(3U-2) times the total component gain; singletons have no ending charge. Consequently, absent any actual twin witness,
    Z <= [(2U-1)/(3U-2)] F = (2/3+O(1/U)) F.             (8)
This uses NO small variation budget, NO multiplier cap, NO bound on the number of distinct labels overall, NO small-support partition, and NO lower bound on the physical span of an individual chain. It is a condition on the fraction of selected gain supplied by exact equal-adjusted-deficit close transitions. Thus if there are arbitrarily large X with selected populations as stated and Z>(2/3+delta)F for fixed delta>0 and F>0, actual prime cofactors q,q+2 with q>=T_3 are forced, which implies twin infinitude. In fact any three-vertex chain in a factor-two band is already a direct witness. This is a different sufficient forcing target from the previous two-value tube, which did require an endpoint correction and large physical interval length.

For a family of disjoint physical subblocks with band and selected population allowed to vary between them, apply (8) separately and sum; all factors are <=2/3+O(1/T). One may also filter the entire block separately into disjoint dyadic label bands and compute Z for each filtered list, since the selected ending vertices are disjoint across bands; their relay intervals may overlap, but (8) itself does not sum relay budgets. These are upper bounds under absence of the direct witness. We have not shown that the required Z/F fraction or a three-vertex equal-D chain at the cube threshold is forced by MIN. The remaining nonzero displacement pairs with h,k well above log^2 X, and isolated or large-relay high-multiplier transitions, remain open. The earlier small/middle crossing alternatives also remain.

## 7. Finite diagnostics and persistence

[Final audit 259f73f](https://github.com/tara-sooo/A166944-Lean/blob/259f73f0cdcaa2099f6b1a2915f719d5566633b4/research/min_direct_growing_multiplier_zero_chain_audit.mjs), blob 342fe43c36d144d2b9f09ef6aa64ea259d297ea2. Exact remote readback. Run node research/min_direct_growing_multiplier_zero_chain_audit.mjs 60000. Executed actual ECMAScript in tool runtime. 29998 odd canonical roots through60000,549085 events,0 cap180 unresolved. 44844 nonempty block controls at varying finite caps8,16,32,110146 selected incidences,65302 consecutive filtered pairs.3477 close nonzero transitions checked for exact primitive parameter interval, variable ratio, gcd decomposition, CRT, dyadic band and singular-factor submultiplicativity;25421 prime-line residue checks. Example p43,r31,h3,k4,c-5,E0,v-10,H1848->1890. 1024 finite J mean terms,64 gcd-summed weight controls with749 positive summation terms; these aggregate comparisons use floating tolerance and check only finite small parameter ranges, not the asymptotic constant in (3). The previous exact finite Selberg algebra and analytic bound are used in the proof.

Uncapped positive-D chain controls selected w>6,4w>=g, directly SPF-prime q and D/2<T^3 at finite T11/17/31, B2/4/floor(T/2); also within [T,2T). 948 nontrivial chain incidences,1236 zero edges,2184 visits,948 exact product checks,474 factor-two-band chains.288 triple incidences, all produced actual twin gaps; no non-twin large-middle triple in this finite scan. Maximum observed chain length3.330 band chains without a witness all had length2. These counts overlap across control choices and roots. The finite threshold and directly tested cofactors exercise the arithmetic; they are not claimed cube-certified instances. Representative actual root M43817, selected labels19/17/19, D646 throughout, pre-horizons88332/88350/88368, q4649/5197/4651, waits8/8/11, sides+,+,-, total relay gain2, post ordinary deficits646/646/652. Actual twins4649,4651, independently replayed from the canonical root by literal raw parity-GCD rule over 700 ticks and31 events. No positive c=0 case was seen inside the small capped controls, as expected in the asymptotic cap regime; uncapped chain tests explicitly supply those cases. All final assertions passed. No Lean executable/kernel verification, external novelty claim or finite-twins contradiction. Main and sibling branches not modified.
