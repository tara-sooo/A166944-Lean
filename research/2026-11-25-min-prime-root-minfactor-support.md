# Least-factor quotient support: one extra logarithm and a shorter gain-prefix criterion

2026-11-25 JST. Continues feed8962f2d6765b9f85a1b8ea83124e606943cb on research/min-prime-root-repeat-energy-2026-11-25. A new use of the uniform two-form quotient sieve in 32d4185: stratify the ENTIRE horizon support by its least eligible prime, rather than merely sieve both C±1. Improves the support weight by one full logarithm, hence weakens the required energy estimate, improves several previous structural removals and permits an alternative shorter gain prefix. This is an unconditional paper deduction using the earlier proved sieve and standard elementary prime-sum bounds. No Lean compilation, no claim of novelty outside this project, twin-prime infinitude OPEN.

## 1. Uniform least-factor support lemma

Let X be dyadic, B=ceil(sqrt(7X)), u=log B, l=log u. On the even horizon interval V_X=[2X-2,7X] define r(C) to be the least odd prime <=B dividing (C-1)(C+1), with r=0 when none exists. Write
    S(R)=sum_{C in V_X, 0<r(C)<=R} r(C), 3<=R<=B.
The previous hybrid used S(B)=O(XB/u²). The stronger bound is
    S(R) << X R/log²(2+R)/log(2+R) = O(X R/log³(2+R)),
uniformly in 3<=R<=B, with absolute constants.

Proof. Fix an odd prime p<=B. At a horizon with r(C)=p there is a UNIQUE sign sigma in {-1,1} for which p|(C+sigma), since p does not divide 2. Write (C+sigma)/p=2n+1. For each fixed sign, n ranges over an interval of O(X/p+1) consecutive integers. The definition of r=p is exactly that both
    2n+1, p(2n+1)-2sigma
have no odd prime divisor q<p. For every odd q<p the two linear forms exclude precisely two distinct residues. This implication is from minimality, not from the selected event label or from any trajectory distribution. Apply the self-contained upper bound of 32d4185 to z=floor(p^(1/8)), with bounded p absorbed by an absolute constant. The count of n is
    O(X/(p log² p) + p^(3/4)) = O(X/(p log² p)),
uniformly: p<=B, B²=Theta(X), and p^(7/4) log² p / X=O(B^(-1/4)u²)=o(1). Summing both signs only adds a constant factor. Thus the exact least-prime bucket H_p={C:r(C)=p} has cardinality O(X/(p log² p)). No double-counting between p buckets.

For p<=sqrt R use the elementary bound that their entire contribution to S(R) is O(X sqrt R), since each horizon has exactly one r. For sqrt R<p<=R the contribution per prime is O(X/log² R); there are O(R/log R) primes <=R by Chebyshev's bound. Since sqrt R=O(R/log³(2+R)), this proves the claim. In particular
    S_*:=S(B)=O(XB/u³).                          (1)
This also bounds the support weight of ANY retained actual event subset, without expensive-clock or high selected-label conditions. Earlier O(XB/u²) is a valid weaker estimate. No claim about the exact asymptotic constant of S_*.

A related cardinality result: for any fixed a>0, the number of C with B/u^a<=r(C)<=B is
    O(X/u² sum_{p>=B/u^a}1/p)
      = O_a(X(1+l)/u³).                        (2)
The prime sum follows by partial summation of pi(x)<<x/log x. This is for positive finite r, so does NOT count twin horizons with r=0. For relative-expensive events p>=B/u^b and r>p/sqrt(log p), r>=B/u^(b+1/2) up to harmless constants; hence their horizon support obeys (2). The previous rough-set count, which includes twin terminals, is not replaced by (2).

## 2. Relaxed energy target at the existing gain scale

Keep the existing prefix T=floor(X/u^(1/4)), N=#prime roots ~X/log X, per-source total gain<T+B and no-twin lower bound R >= N(T-6)/4. Let W(C) be ANY retained high incidence mass, and E=sum_C r(C)W(C)^2. By (1)
    (sum_C r(C)W(C))² <= S_* E.
Thus sufficient high energy is now
    E=o(T² B u),                               (3)
because S_* T² B u=O(XB² T²/u²)=O(N² T²). This is a full factor log B weaker than the previous o(T² B) target, on the SAME ensemble and marks. The joint sufficient medium bound Z_m=O(N B u³) is unchanged. All prior pair exclusions of o(T²B) are automatically negligible on the relaxed scale. All previous linear deletions retain their original bounds. This is not a proof of (3).

One immediate linear removal: mark all high incidences at C with W(C)<=B u^(3/2). Cost at most B u^(3/2) S_*=O(NT/u^(1/4)). The threshold grows by a full log factor over the comparable old-support threshold B sqrt(u). Hence a residual high horizon can be required to have > B u^(3/2) actual tags. This is a linear deletion, not an energy bound on the deleted portion. It is compatible with earlier source-cell marks if applied LAST at whole horizons (does not change the distribution at surviving horizons).

## 3. Stronger source-cell and anchor exclusions at this same scale

The near-source whole-pair bound of 5b545e4 is O(NT d/log d). With d=floor(B u^(5/2)), it is O(T² B u/u^(1/4)), negligible on (3). This enlarges the old separation cutoff B u^(3/2) by factor u; no restriction on how late the roots meet. For the nested source-cell construction in 758672d use integer widths d_j=B2^j, 0<=j<=floor(log_2(u^(9/4))). For each scale set
    m_j=floor(2^j u^(7/4)),
    K_j=floor(u^(5/2)/2^j).
The same-cell energy is F_d=O(NT+NT d/log d). The number of possible source cells at one high C is <=ceil(T/(2d))+2. With (1) the linear cost of all occupied cells of mass <=m_j is bounded by
    m_j (ceil(T/(2d_j))+2) S_* = O(NT/u^(1/4))
uniformly on the ladder, since d_j=o(T).
After nested increasing-scale thinning, define D_j(C)=W(C)^2/sum_a W_{j,a}(C)^2 on the remaining tags. All horizons with D_j<=K_j have energy <=K_j F_d=O(T² B u/u^(1/4)), hence linear cost O(NT/u^(1/8)) by (1). The sum over O(1+l) scales is o(NT). Nested coarse deletion preserves earlier fine thickness, and subsequent whole-horizon deletion preserves all surviving statistics. At the fine scale d=B every occupied cell now has >floor(u^1.75) tags and effective cell count >floor(u^2.5); the coarse end is order B u^2.25 with mass floor order u^4 and effective count order u^.25. Every retained high horizon can also obey the global mass floor in section 2. The number of extra LOW attachments is controlled by O(NT/Q) high incidences with Q=ceil(B/u), so O(LNT/Q)=o(NT). These stronger conditions concern actual tags, not the number of arithmetic candidate primes.

For the close-anchor classes of feed8962, keep Q=B/u, V=B exp(-sqrt u), A=floor(B^1/4) and replace the old far cutoff by the enlarged d above. The same prefix-filtered min-tail product U_ab and all key-pair counts remain valid (new far product only decreases). Multiply each of the previous normalized weighted caps by u^(3/4). The new caps are
    c_sym=B u²/A,
    c_asym=B u^(3/2)/A,
    c_same=B u^(5/4).
Using the earlier CRT envelope, the ratio of combined class energy to T² B u is O((1+l)^2/u^(3/4)+(1+l)/sqrt u)=o(1). The prior cap ratios relative to T²B were O((1+l)^2/u^.5), O((1+l)/u^.5), O((1+l)/u^.25); multiplying by u^.75 and dividing by u gives the asserted ratios. This includes polynomial-sized groups, with larger log allowances, but still needs the cap on actual weighted products. Apply all pair exclusions to the final thinned subset. The high residual on the existing ensemble now need only satisfy E_bad=o(T² B u), not the old stronger target.

## 4. Alternative shorter-prefix route at unchanged absolute energy scale

There is another tradeoff: choose
    T'=floor(X/u^(3/4)), Q'=ceil(B/u^(5/4)), k'=floor(u^(1/8)).
Asymptotically B=o(T'), T'=o(X), so the per-root gain-crossing argument of a5e1119 works verbatim: absent twins all prime roots cross T' and R'>=N(T'-6)/4. Each total gain<T'+B; linear selected weight O(NT'). Any C has at most O(T'/log T') prime tags. The energy sufficient condition by (1) is
    E'_h=o(T'^2 B u)=o(X²B/u^(1/2)),              (4)
which is the SAME absolute energy scale as the OLD T²B criterion at T=X/u^.25, now on a prefix shorter by sqrt(u). The high threshold is lower, so no assertion of automatic containment of the whole high incidence set. This is a new independent sufficient route, not a claim that all late pair/anchor exclusions already transport.

Here are sufficient elementary deletions, with optional older light support. Mark first k' occurrences per original root and selected label. Their selected weight <=N k' sum_{p<=B}p=O(N X/u^(7/8))=O(NT'/u^(1/8)). Add the inverse-square adaptive cap floor(T'/(p² l²)) to the first-use count if desired; its weight is O(NT'/l) by sum_{p<=B}1/p=O(l). For the LOW boundary y maximal with L=2 product_{3<=p<=y}p<=l^(1/4), the extra LOW charge from all these marks is O(L times selected weight)=o(NT'). Initial LOW blocks cost O(NL). Every contiguous LOW block gains <L, as proved earlier; attach to its preceding non-LOW event or initial root. Thus all high p>=Q' counts incur at most O(LNT'/Q')=o(NT') attachment, and remaining medium events cost at most p+1.5L each, including attached LOW. This argument requires no bound on LOW multiplicities individually.

One may also delete the earlier relaxed light-return horizons for Q' and J=floor(u^1/4): the support calculation of 2d184f3 (valid alpha+2beta<2) yields S_light=O(X l²/u^1/4). Its tag-lift using O(T'/log T') costs O(NT' l²/u^1/4); multiplying event count by L still gives o(NT'). No need for this optional deletion for the criterion below. Previous dense/propagation/halo and root-pair steps are not needed or claimed to be transported here.

For p>=Y=ceil(l), delete relative cheap r<=p/sqrt(log p), clock cost O(NT'/sqrt(log Y)), with extra LOW charge O(LNT'/Y) because all such p>=Y events number O(NT'/Y). If desired remove first and last D=floor(T'/l) gain at clock and selected weight O(N(D+B)), extra LOW charge O(LN(D+B))=o(NT'). For p>=Y the quotient capacity n_rel(M,p)<<T'/(p log² p) still holds using p^.75=o(T'/(p log²p)), so previous logarithmic-band rank deletion costs O(NT'/sqrt(log Y)) selected weight. Optional marks can be made on original lists in the same order as before, not by rerunning the dynamics.

On the residual medium incidences y<p<Q', put Z'_m=sum_{M,p} n_m(M,p)^2. The medium plus LOW budget after all marked classes is bounded by
    o(NT')+sqrt(N sum_{y<p<Q'}(p+1.5L)² Z'_m).
The coefficient sum is O(Q'^3/log Q') by the prime upper bound (L<<Q'). If Z'_m=O(N B u³), this square-root term is O(N X/u^(7/8))=O(NT'/u^(1/8)). Thus the joint OPEN sufficient conditions are
    Z'_m=O(N B u³), E'_h=o(X²B/u^(1/2)).
With (4) they force R'=o(NT') and hence twin infinitude. This alternate route uses a smaller set of accounting reductions than the fully developed existing-scale hybrid; in particular the latter's heavy support/anchor pair estimates have not been transferred here. The shorter horizon alone does not bound either residual. The simpler core is useful for comparing cutoff scales without conflating numerical energy thresholds with incidence-set inclusion.

More generally choose T_a=X/u^a and Q_b=B/u^b, with 0<a<1, b>0, k=u^eta and 0<eta<1-a. The same first-use/LOW/relative-cheap core gives the medium target Z_m=O(N B u³) provided 3b>2+2a (from sqrt(N Q_b³/u * N B u³)=O(N X u^(1-3b/2))), and high energy o(T_a² B u). If including the previous light-return deletion with J=u^beta, use b+2beta<2. The specific a=.75,b=1.25,eta=.125,beta=.25 meets these inequalities. Constants, integer floors and bounded initial X are immaterial to the asymptotic implication.

## 5. Reproducible audit

Standalone ECMAScript research/min_prime_root_minfactor_support_audit.mjs, exact remote readback at 1f166710d32e77bd1daae4092a04bb7ad13127cc, blob 7c6040b75f2f9b258b638b38596c4c212da9bd87. Run:
    node research/min_prime_root_minfactor_support_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node executable. Six dyadic windows. Enumerates ALL even horizons of V_X, exact least eligible odd prime buckets, unique sign and quotient and absence of every smaller odd prime, then independently enumerates each possible odd quotient for every p<=B and both signs and checks the exact converse and bucket cardinalities. Checks complete-period small-prime sieve capacities (q<=7) and aggregates r support, dyadic r bands, high-r support and relaxed relative-expensive support. Separately executes three gain-prefix modes at each X: alternative analytic T',Q',k'; short diagnostic T=B,Q'; four T=4B,Q old. Tests actual SPF MIN, literal parity-GCD comparisons at X256/1024 (analytic1608, short1183, four1707), gain crossing lower and noncrossing non-twin bounds, first-k and relative-cheap partition, full residual medium Z (includes LOW here, not the final theorem moment), actual high horizon support/Cauchy exact BigInt comparison, global small-mass horizon bound and energy partition. It isolates core deletion and global mass test; does not rerun all accumulated previous marks or new multiscale ladder/anchor caps. All finite checks pass. No proof of asymptotic bounds from the measured ratios; section 1 is a paper proof from the earlier sieve.

| X | B | exact S_* | S_* u³/(XB) | S_* u²/(XB) |
|--:|--:|--:|--:|--:|
|256|43|3002|14.5105|3.8579|
|1024|85|14267|14.3728|3.2352|
|4096|170|69858|13.5904|2.6462|
|16384|339|351646|12.5198|2.1490|
|65536|678|1808600|11.2773|1.7299|
|262144|1355|9566479|10.1009|1.4007|

At largest X, 646287 horizons with positive r, independent quotient enumeration 2281092 checks, 215 prime buckets strictly below the crude finite periodic capacity, weighted periodic upper43924063. High-r threshold Q'/sqrt(log Q') counts24300 horizons weight6386166, relative-expensive arithmetic support15075 horizons weight5683575. Analytic shorter prefix T'=59568,Q'=115,k'=1: all20390 prime roots terminate at twins before crossing, full R16687054, events616116, first-use14207764, relative-cheap178890, medium incl LOW2201053, high99347, high E1453091, actual support16843, max mass34, global analytic cap26241.15 deletes all high incidences. This is a vacuous finite residual for the large asymptotic mass threshold. Short diagnostic T=B, Q'=115, mass cap4: 4992 crossings,15398 twin terminal roots, high R33214, E346380; low-mass deletion clock8187, energy23519, residual E322861. Four diagnostic T=4B,Q=188, mass cap4: 170 crossings,20220 twins, high R58838, E650728, mass deletion clock9387, energy19413, residual631315. These finite diagnostics are not cumulative previous reductions or limiting evidence.

## 6. Next target

The stronger support bound applies to both the gain-stopped prime-root and parallel short-clock paths (their own energy normalization differs). For the existing-scale hybrid the next target is the residual energy at the relaxed scale T² B u, with enlarged source separation, stronger multiscale thickness and weighted caps, or a direct bound on the smaller alternative prefix. Neither medium nor high residual criterion has been proved. Main and other branches unchanged.
