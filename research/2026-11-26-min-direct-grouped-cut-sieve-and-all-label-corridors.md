# Grouped Bonferroni extension of the cut sieve and all-label endpoint corridors

Continuation of [3e19d7e](https://github.com/tara-sooo/A166944-Lean/blob/3e19d7e945788d39b12a17744c2139970e90da8d/research/2026-11-26-min-direct-thickened-cut-recovery-and-local-supply.md). Extend the additional roughness sieve from a polynomial cutoff in R to Z=floor(exp(3S)), using logarithmic-prime groups and a pointwise product Bonferroni envelope. Reuse the earlier Fourier entropy certificate with a common frequency cutoff multiplied by exp(o(R)); the smoothing exponent stays 4/11. Exact-anchor mass becomes o(X) even across all labels. Separately extend the preceding forward corridors to all labels, including launches near the cut with arbitrarily large jumps, and quantify the remaining deep-interior bypass population. These are paper deductions and finite audits, not a finite-twins contradiction or Lean kernel verification.

## 1. Base barrier and new extra-prime cutoff

Let R be the largest odd prime with P=P_R<=sqrt X, r=pi_o(R), S=floor(R/loglog R), K=2P_S, ell=ceil(P^(4/11)). We work for sufficiently large X so S>=3. Retain the hybrid base barrier in j=J/2 coordinates: J=0 mod every odd prime <=S, J mod f in {0,2,...,f-3} for S<f<=R. Its density is alpha=P_S^(-1)*prod_(S<f<=R)(f-1)/(2f). Every base cut is an ordinary R barrier, so no event of label <=R crosses it in the half-open convention H<=J<H+p-1.

Replace the former extra sieve cutoff S^2 by
    Z=floor(exp(3S)).
Define E to be the primes R<f<=Z and keep cuts satisfying J!=+/-1 mod f for all f in E. Set
    Q=prod_(f in E)(1-2/f),
    mu=sum_(f in E)2/f,
    f_sv=base indicator/alpha * prod_(f in E)(1-b_f),
    b_f=1_{J=+/-1 mod f}.
The base mean of f_sv is Q on the full CRT period, which we do NOT use to estimate local windows. By the usual Mertens product, the convergent quadratic correction to the two-root factors for f>R, and the reciprocal-prime estimates,
    Q=(1+o(1))(log R/log Z)^2,
    mu=O(log R), exp(mu)=O(R^2).
In particular Q^{-1}=O(R^2). The cutoff Z=X^o(1) grows much faster than K+1, since log P_S=(1+o(1))S. All surviving cuts are Z-rough in the two-neighbor sense. The earlier single global truncation with order r/(10 log Z) cannot be used: log Z is larger than r and the required truncation accuracy worsens. The next section replaces it.

## 2. Grouped pointwise envelope with small support modulus

Partition E into nonempty disjoint groups E_i by successive halving of the logarithmic upper endpoints: f with exp(L_i/2)<f<=exp(L_i), L_i=2^{-i}log Z, intersected with R<f<=Z. Stop when the lower endpoint is below R. There are m=O(log R) groups and sum_i L_i<=2 log Z. By Mertens uniformly for endpoints >=R, each group has mu_i=sum 2/f<=2log 2+o(1) and Q_i=prod(1-2/f)>=c>0 for an absolute fixed c, for large R. The last truncated group satisfies the same upper/lower bounds. We only need bounded mu_i and Q_i bounded away from zero.

Fix a desired error power A>0. Take an even truncation k with k~k0 loglog R/logloglog R for a sufficiently large fixed k0 depending on A, e.g. k0=4A+40. For group i let U_i be the alternating sum of products of b_f through order k, L_i^Bon through order k+1, and D_i=U_i-L_i^Bon=sum_(|F|=k+1,F subset E_i) prod b_f. Write I_i=prod_(f in E_i)(1-b_f). Bonferroni gives U_i>=I_i>=L_i^Bon, U_i>=0, D_i>=0. Missing high-order terms when a group has fewer primes are zero. Do NOT multiply the lower polynomials, since they can be negative. Use instead the two polynomials
    U=prod_i U_i,
    L=prod_i U_i - sum_i D_i prod_(j!=i) U_j.
Then
    L <= prod_i I_i <= U.                             (1)
Proof: the upper bound is immediate; telescope the difference between products U_i and I_i in any fixed group order. Each term is at most D_i prod_(j!=i) U_j by 0<=I_j<=U_j and U_i-I_i<=D_i. This proof holds pointwise for all binary configurations.

For each group the expectation of D_i under its independent CRT residues is
    e_(i,k+1)<=mu_i^(k+1)/(k+1)!.
By the factorial bound and choice of k, this is O((log R)^(-2A-10)), uniformly in groups. If u_i denotes the expectation of U_i then 0<=u_i-Q_i<=e_(i,k+1), so
    0<=prod u_i-Q<=Q O((log R)^(-2A-8)),
    0<=prod u_i-E[L]<=Q O((log R)^(-2A-8)).             (2)
Indeed m=O(log R), Q_i>=c, product relative error <=exp(sum e/Q_i)-1, and the expectation gap is prod u_i times sum e/u_i. In (2) expectation is over the extra prime CRT classes. Independence here is exact because the groups are disjoint primes, also independent of the base modulus P. The absolute coefficient weight after expanding either polynomial into products of b_f, weighted by w_F=prod_(f in F)(2/f), is at most (1+m)exp(mu)=R^O(1). For the lower polynomial, keep correction terms separately if equal monomials combine; the triangle inequality only improves with cancellation.

Crucial support bound: in an upper term at most k primes are used from each group; a lower correction term uses at most k+1 primes in ONE group and at most k in the others. Every monomial therefore has q_F=prod_(f in F)f satisfying
    log q_F <= (k+1) sum L_i <= 2(k+1) log Z =: B_R.
For our choice log Z=3S+o(1), B_R=O_A(R/logloglog R)=o(R). Thus even though the number of extra primes is enormous, every modulus that occurs has log size log P+o(R). This is the advantage of grouping by logarithmic prime sizes over the previous cardinality-only bound.

## 3. Uniform Fourier transfer at the same smoothing exponent

For each F appearing in the expansion let f_F be the base indicator times prod_(f in F)b_f divided by alpha*w_F. Its CRT period is P*q_F, its mean is 1. Reuse the earlier [growing-order Fourier proof](https://github.com/tara-sooo/A166944-Lean/blob/3e19d7e945788d39b12a17744c2139970e90da8d/research/2026-11-26-min-direct-growing-order-sieved-recovery.md) with the COMMON frequency cutoff
    M=ceil(P^(7/11)*exp(r)*P_S*exp(2 B_R)).
This is a different cutoff from the earlier M but log M=(7/11+o(1))log P and M<P/2 eventually. The ambient primes >S, >=R/log R, <=R and their base local intervals are unchanged. The earlier low-frequency certificate uses the shortened projection parameter floor(log M/log b)/n->7/11, with n~r and log b~log R, and all other local factors have magnitude <=1. Thus its uniform positive margin remains valid for every such F; summed symmetric low-frequency energy <=exp(-(.003+o(1))*r). This uses the previous fixed entropy certificate at its same limiting parameter, not a new Fourier exponent or a Parseval argument over the full Z-primorial.

For the high-frequency estimate, q_F<=exp B_R and w_F^{-1}<=q_F, while alpha^{-1}=P_S exp((log 2+o(1))*r). The same moving-average and normalized Parseval bound gives
    (P*q_F/(2 ell (M+1)))^2/(alpha*w_F)
     <= (1/4) exp(-B_R-log P_S+(log 2-2+o(1))*r).
Consequently sigma_F,ell^2<=exp(-.001r) for all the expanded terms. Also P*q_F<=sqrt X exp(B_R)=X^(1/2+o(1))=o(X). On ANY translated interval I of length O(X), by periodicity,
    ||(f_F)_ell-1||_(2,I)<=O(sqrt X exp(-.0005r)),
    |sum_I f_F-|I||<=P*q_F.
Here (f_F)_ell is the forward moving average. Both are uniform in the terms; the coefficient sum is only R^O(1), not the number of terms. Apply (1) after multiplication by the base normalized indicator and averaging; use (2), the triangle inequality in L2, and the absolute weighted coefficient bound. After dividing by Q the errors from the Fourier fluctuations are polynomial in R times exp(-.0005r), and the deterministic expectation errors are O((log R)^(-2A-8)). Thus for any fixed A>0, choosing k as above,
    sum_I |(f_sv)_ell/Q-1|^2 = O(X/(log R)^(2A)),
    sum_I f_sv/Q = |I|+O(X/(log R)^A).                 (3)
The second statement follows in the same way before smoothing, using polynomial in R times sqrt X exp B_R = X^(1/2+o(1)), negligible compared with X/(log R)^A. Constants may depend on A and the fixed interval-length factor. The earlier exponential error in r is NOT asserted here; the grouped truncation provides an arbitrarily fixed power of log R. It is enough for all o(X) mass balances. In particular normalized mass M_cut(Jset)=(2/Q)sum f_sv for sets of integer horizon positions has mass G+o(X) on a physical crossed window. For disjoint event intervals of total gain G_* and count n, the earlier inner/outer smoothing argument gives
    G_*-2(ell-1)n-o(X)<=M_cut(union)<=G_*+2(ell-1)n+o(X). (4)
The error is uniform for any family on that window, with fixed A as above. The exact lattice bound still holds with the NEW weight kappa=2/(alpha Q).

## 4. All exact anchors have negligible normalized mass

At an exact anchor H=J on a surviving cut, every prime <=Z is excluded from dividing H+-1, by the base and the enlarged sieve. Therefore any actual selected event at such a start has label p>Z. An event contains at most one exact anchor (its own start), regardless of how many cuts its jump spans. In any physical window of total gain G=O(X), the count of these anchor incidences is at most G/(Z-1). Since
    log kappa=log P_S+O(r+log R)=(1+o(1))S,
    kappa/Z=exp(-(2+o(1))S)=o(1),
their total normalized mass is <=kappa G/(Z-1)=o(X).  (5)
This is unconditional on finite twins, variation or sparsity, and applies to ALL label scales. In particular no p<=D=K+1 can start exactly at a surviving cut; all small crossers are strict. Nor can any p<=Z be an anchor, including a superpolynomial-in-log-X range of former middle crossers. The weight is changed by the extra sieve (Q is now small); kappa remains X^o(1), so the old small-count exponent is unchanged, but the numerical small-count lower bound uses this new kappa, not the old one. The old weighted three-scale and crossing-clock arguments use only (4), the exact lattice bound, and no-witness exclusion for p<=S^2. With the new Q,kappa and uniform o(X) errors they transfer as stated at the asymptotic exponent level. We do not claim their old exponential error or their precise old finite constants. Since ell is unchanged and kappa=X^o(1), their macroscopic three-scale alternatives remain. This does not itself exclude the strict crossings of the small or middle branch.

## 5. Endpoint corridors for all label scales

Independently of the new extra sieve, take V=4 floor(S^2/4), so V~S^2, K>2V eventually. Consider a finite physical block with H+1>=S^2 and any designated subset of the pinned surviving cuts. Ignore exact anchors for the moment. Each strict crossing has pre-horizon H<J and post H'=H+g>J. Put a=J-H>0,b=H'-J>0, so a+b=g. Classify each strict cut (not the whole event) in this order:
    launch: a<=V;
    landing: a>V and b<=V/2;
    bypass: a>V and b>V/2.
For a launch, start the corridor at the crossing event and continue up to first plateau >=J+V. For a landing start immediately AFTER the crossing, and continue to that endpoint. If incomplete, mark pending, at most one since its cut lies within V of the final horizon. All corridor pre-horizons satisfy 0<|H-J|<=V; a launch can have arbitrarily large p, in which case it immediately completes. The preceding two-sided offset lemma says either a direct twin witness >S occurs, or every event in the corridor has w<=2S. For completed corridors the actual gains satisfy
    G_J>=max(V,g_cross) for launch,
    G_J>=V/2 for landing.                              (6)
No selected label cap is imposed. This includes the old moderate theorem and the earlier small-overshoot extension in a single disjoint family. Distinct corridors have disjoint pre-horizon neighborhoods because K>2V. Even if one large event has a launch near its start and a landing near its end for two DIFFERENT cuts, the latter corridor starts after it, so its gain is not charged twice. At most one launch and at most one landing cut per event because of lattice spacing. A final jump can cross several other cuts but belongs to only its own corridor if its start lies in that corridor. No event is truncated.

For completed witness-free corridors let Q_corr be their physical union and
    D_corr=sum_launch max(V,g_cross)+(V/2)*n_landing.
Take integer low cutoff L0>4S, alpha0=1-4S/L0. In each corridor all events p>L0 decrease ordinary d by at least alpha0*g and all low events can increase it by at most 5g. As in the preceding note, actual disjointness and telescoping give
    D_corr <= G_low(Q_corr)+P_-(Q_corr)/alpha0,
    alpha0 D_corr <= (alpha0+5)G_low(Q_corr)
                      +P_+(outside Q_corr)+d_a.         (7)
This is a gain-sensitive budget, not just the former fixed V cost for each moderate crossing: the entire gain of even a very large near-launch event is charged. In particular for any launch p>L0 the actual crossing event itself satisfies d-d'>=alpha0 g, and its net decrease can be summed once over all launches even without completing the corridors. In a landing with small post-crossing d, the earlier local low-gain bound applies from that new post state. For example if that crossing is a reset, post d<=6 and the landing corridor needs low gain >=(alpha0 V/2-6)/(alpha0+5), independent of the crossing label. These statements require no small initial deficit for the full block. A finite-twins assumption at sufficiently large S makes all corridors witness-free. On disjoint physical windows one may sum their demands with only one initial deficit term by telescoping over the full ray, as before.

For the remaining bypass cuts both endpoints are far from J, so necessarily g>3V/2. All such cuts of an event are contained in the eroded half-open jump interval [H+V,H'-V/2), of length (g-3V/2)_+. Their exact count is bounded by ceil((g-3V/2)_+/K). The erosion intervals are disjoint between distinct events and their endpoints are even (V divisible by four). By the same mixed direct/smoothed bound, for the set of events actually containing bypass cuts,
    M_bypass <= sum_event min(kappa*ceil((g-3V/2)_+/K),
                        g-3V/2+2(ell-1)) + o(X).        (8)
For each event the choice of direct vs smoothed term is arbitrary, and apply the smoothing once to the chosen subfamily, so no per-event o(X) charge. The actual bypass subset need not be all cuts inside that eroded interval; this is an upper bound. More generally replace V/2 by theta V (fixed 0<theta<1, rounded down to even integer) to obtain landing demand (1-theta)V and bypass threshold (1+theta)V up to rounding. The half-radius version suffices here.

With L0=R, alpha0=1-o(1). Under finite twins, (5),(7),(8) yield an all-label classification: normalized exact-anchor mass o(X), endpoint mass controlled by the actual localized resource with V/2 demand per completed cut (and full gain of near launches), and only the eroded bypass interior as the remaining contribution. In particular if those localized resources are o(V X/kappa), with initial d_a included in the second budget if used, then endpoint mass is o(X) (pending <=kappa=o(X)), so essentially ALL normalized cut mass must be deep bypass and must be supplied by labels p-1>3V/2. This is stronger than merely excluding starts exactly at J, but the required resource bound is not forced. We have not shown that bypass cuts or large overshoots are rare, nor that the full small/middle population has an o(X) supply bound. The next substantial task is to control this deep-interior population or derive a comparable upper bound on the localized resources. The grouped construction is a way to remove the exact anchor exception, not a method to change the radius-S^2 twin certificate to radius Z.

## 6. Finite diagnostics and preservation

[Audit a5b2653](https://github.com/tara-sooo/A166944-Lean/blob/a5b2653f5d7553f0139a2f81b8256205ab2e6256/research/min_direct_grouped_cut_sieve_audit.mjs), blob 8535bdf80cfc77ea4c8f0be17e4190bc0d447b36, exact remote readback. Run node research/min_direct_grouped_cut_sieve_audit.mjs 60000. Actual ECMAScript execution in tool runtime, not separate Node. 50000 pointwise grouped envelopes with binary bad counts, 250 independent exact BigInt expectation/expansion systems, 166779 term-support checks (66923 upper,99856 lower), max finite support8; 49 dyadic-log support-bound controls. These test the grouped polynomial identities and finite expectation arithmetic, not the asymptotic Fourier constant or huge prime cutoff; the Fourier transfer above uses the previous analytic certificate.

29998 canonical odd roots through60000,549085 actual MIN events,0 cap180 unresolved. Finite S5/7/11, base R7/11/13, radius14/48/120, extended cutoff97/251/503. 87602 old finite surviving cut incidences,30088 extended;23128 old anchors,3976 extended anchors all with p>Z;18833 old anchors p<=Z removed (remaining old anchors may also be removed by other conditions). 4613 launch,1772 landing,19727 bypass strict extended cuts;3339 launch and1772 landing with p>V.5281 completed endpoint corridors,1104 pending,802 completed without witness (440 launch,362 landing),4479 with witness.8289 actual fast-clock,352 high-drop,5281 disjoint checks,87795 localized budgets and anchor-gain count checks. Representative large clean launch S5,V14,Z97,J1950,H1944->1972,p29,w8,g28,low gain0,negative variation12. Finite radii may differ from asymptotic choice divisible by4; corridor/budget proofs hold with these radii (no smoothing erosion calculation is tested there). Counts overlap across roots/configurations. All assertions passed. No direct audit of asymptotic (3) or (8), no infinite trajectory, external novelty claim, final contradiction or Lean kernel verification. Main and sibling branches not modified.
