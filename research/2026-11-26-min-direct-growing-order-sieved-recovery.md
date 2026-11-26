# Growing-order sieve smoothing and crossing-only A1 recovery alternatives

Continuation of [40a43f6](https://github.com/tara-sooo/A166944-Lean/blob/40a43f624b3f73df3c68b1bf0bcb2b4f665b9713/research/2026-11-26-min-direct-sieved-hybrid-twin-certificates.md). Replace the fixed-order Bonferroni limit by a growing-order, uniformly controlled L2 envelope. This recovers an exponential zero-window bound for the FULL sieved hybrid indicator on actual macroscopic intervals without applying Parseval to its huge period. Use it with the last-exit geometry to remove all noncrossing far B events from the A1 tail exception count. The resulting necessary window alternative counts only actual crossers and confines its A1 term to an explicit finite band. A further recovery dichotomy holds under the weaker crossing-only sparsity. No twin-prime contradiction, no Lean kernel verification or novelty claim.

## 1. Setup and uniform growing-order intersection variance

Retain the previous sieved hybrid family. S,R,V are integers with 3<=S<R<V<=S^2, S->infinity, S=o(R); use for example S=floor(R/loglog R), V=S^2. Let P=P_R be the product of odd primes<=R, r=pi_o(R), ell=ceil(P^(4/11)), and let E be the set of primes R<f<=V. In integer horizon coordinate j=J/2, the base hybrid condition is J=0 mod f for odd f<=S and J mod f in {0,2,...,f-3} for S<f<=R. Its density is alpha=P_S^(-1)*prod_{S<f<=R}(f-1)/(2f). A surviving cut additionally has J!=+/-1 mod every f in E. Every surviving cut is an ordinary R barrier and V-rough.

For F subset E let q_F=prod_{f in F}f, P_F^*=P*q_F, w_F=prod_{f in F}(2/f). Let f_F be the normalized indicator of the base hybrid condition AND the bad residues J=+/-1 at all f in F, with density alpha*w_F and mean1 over period P_F^*. For F empty this is the normalized base indicator. Define
    mu=sum_{f in E}2/f,   Q=prod_{f in E}(1-2/f).
We have mu<=2log2+o(1), Q>=1/4-o(1), by prime Mertens/reciprocal estimates. Define the actual sieved indicator normalized by the BASE density:
    f_sv(j)=f_empty(j)*prod_{f in E}(1-1_{2j=+/-1 mod f}).
Its full-period mean is Q, not1. We will not use its full period.

The previous fixed-order proof of the intersection variance extends uniformly to
    |F| <= K_max=floor(r/(10 log V)).                         (1)
Indeed take the same common frequency cutoff
    M=ceil(P^(7/11)*exp(r)*P_S).
In every period P_F^* the normalized Fourier coefficient factors over local CRT sets. The ambient primes <=R, >S, >=R/log R have number n~r and min b with log b~log R. Their local sets are exactly the old cyclic H intervals; the others have coefficient magnitude <=1. The entire low-frequency estimate of the earlier [4/11 certificate](https://github.com/tara-sooo/A166944-Lean/blob/40a43f624b3f73df3c68b1bf0bcb2b4f665b9713/research/2026-11-26-min-direct-cluster-recovery.md) uses only these ambient primes, the class counts with full-period CRT inverses, and q=floor(log M/log b) with q/n->7/11. Since log P_S=o(R), this q limit and the uniform certificate gaps are unchanged for ALL F, not just fixed |F|. All estimates on omitted local factors are the bound1, independent of their number. M<P/2<=P_F^*/2 eventually. Thus the summed symmetric low-frequency energy is <=exp(-(.003+o(1))*r).

For the high-frequency term, normalized Parseval and the smoothing multiplier give
    (P_F^*/(2 ell (M+1)))^2/(alpha*w_F)
       <= (V^(3|F|)/4)*exp(-log P_S+(log2-2+o(1))*r).
Here q_F<=V^|F|, w_F^(-1)<=V^|F|, and log(1/alpha)=log P_S+(log2+o(1))*r. At (1) the extra cost is <=exp(.3r), so the high-frequency bound is exponentially smaller than exp(-.001r). Uniformly in all F satisfying (1), for sufficiently large R,
    sigma_(F,ell)^2 <= exp(-.001*r),   P_F^*<=P*exp(.1r).      (2)
The sigma is the complete-period variance of the forward average of f_F of length ell. This uses the existing rigorously certified entropy inequalities, not a new Fourier exponent, and no summation of errors over all individual subsets without their weights.

## 2. Growing-order Bonferroni and local L2 for the full sieve

Let R be the largest odd prime with P_R<=sqrt X, so R~.5log X and r~R/log R. The same argument applies with largest P_R<=X^rho for any fixed 0<rho<1. Take
    k=2 floor(r/(40 log V)).
This is even, tends to infinity, and k+1<=K_max eventually. Write
    Q_j=sum_{|F|<=j} (-1)^|F| w_F.
The even/odd Bonferroni inequalities give Q_(k+1)<=Q<=Q_k, and pointwise after forward averaging,
    sum_{|F|<=k+1}(-1)^|F|w_F (f_F)_ell
       <= (f_sv)_ell
       <=sum_{|F|<=k}(-1)^|F|w_F (f_F)_ell.                    (3)
The total coefficient weight in any truncation is <=exp(mu)=O(1). Both expectation gaps are <=e_(k+1), where e_j=sum_{|F|=j}w_F<=mu^j/j!. Since log V<=2log R, log k~log R, k log k >=(.025-o(1))*r. Thus for large R
    e_(k+1)<=exp(-.01r).                                    (4)
For instance this follows from j!>= (j/e)^j, and mu bounded. If there are fewer than k+1 extra primes, the missing elementary sums are zero and the same inequalities hold exactly.

Let I be ANY integer interval of n=O(X) positions, arbitrary translate. By periodicity and nonnegativity, for each |F|<=k+1,
    sum_I |(f_F)_ell-1|^2 <= (n+P_F^*) exp(-.001r)
                             =O(X exp(-.001r)).
The last equality is uniform because P_F^*<=sqrt X exp(.1r)=o(X); for fixed rho<1 use P<=X^rho. By (3), pointwise
    |(f_sv)_ell-Q| <= sum_{|F|<=k+1} w_F |(f_F)_ell-1| + e_(k+1).
Take the Euclidean norm over I and use the triangle inequality, (2), bounded total coefficient weight and (4). We obtain the NEW local mean-square theorem
    sum_{j in I}|(f_sv)_ell(j)-Q|^2 = O(X exp(-.001r)).        (5)
The constant is uniform over arbitrary intervals of length at most a fixed constant times X, including intervals selected from the trajectory. In particular the number Z(I) of zero forward averages on I satisfies
    Z(I) <= Q^(-2)*sum_I |(f_sv)_ell-Q|^2
          = O(X exp(-.001r)).                              (6)
Only the small intersection periods were used. Neither a global variance bound over the full period P_V nor a uniform pointwise gap upper is asserted.

The unsmoothed mass is also controlled quantitatively: by periodicity the sum of each normalized f_F over I differs from n by at most P_F^*. Apply (3) before smoothing, and use (4):
    |sum_I f_sv-Q n| <= exp(mu)*P*exp(.1r) + n exp(-.01r).
At fixed rho<1 the first term is O(X exp(-.01r)), since r=o(log X). Thus the error is O(X exp(-.01r)). Now for any union U of m disjoint integer intervals in I covering ALL surviving cuts in I, let U^- expand each interval left by ell-1, lying in I' of length n+ell-1. Nonnegative smoothing gives sum_I f_sv <= sum_{U^-}(f_sv)_ell. Cauchy-Schwarz from (5) bounds the excess above Q|U^-| by O(X exp(-.0005r)). Consequently
    n <= |U|+(ell-1)m+O(X exp(-.0005r)).                     (7)
This makes the previous o(X) union error explicit. No rate of prime number theorem beyond the asymptotic facts used in the old uniform entropy certificate is needed; the inequalities are for sufficiently large X.

## 3. Zero-run recovery with only actual crossing exceptions

Use canonical MIN and the earlier last-exit corridor extraction [319d42d](https://github.com/tara-sooo/A166944-Lean/blob/40a43f624b3f73df3c68b1bf0bcb2b4f665b9713/research/2026-11-26-min-direct-last-exit-corridors-and-record-support.md). Consider an event block crossing [X,lambda X], lambda>1 fixed, G=(lambda-1)X+O(sqrt X), label cap C=floor sqrt(lambda X+1), N canonical visits. At these large horizons use the same near-square definition and its later-near exclusion.

Define B_cross to be the count of all FAR B events with p>R that ACTUALLY cross at least one surviving sieved hybrid cut. Define A_cross to be the far A1 events with p>R that cross such a cut. Counting events, not incidences with cuts, is essential. There is no hypothesis on the number of noncrossing B. Under absence of the direct primorial-offset twin witness >S (in particular under finite twins and sufficiently large S), every A_cross has p>V. Every moderate B_cross R<p<=V has w<=2S and ordinary decrease >=p-1-4S. Thus B_cross<=B_star<=B_R in the terminology of the previous note.

For any selected subset of marked A1 in bands [T,2T), T=T0*2^j, T0>=47, T<=C, construct cores and last-exit corridors as before: x=d+3, first later plateau x<=.4T, then last preceding plateau x>=1.9T. In each completed corridor:
* no A1 of any size occurs;
* a reset label>=5 can occur only at the end;
* any nonreset has post x<1.9T, and its pre x is in (.4T,2.85T), label <.95T if >=5.
* each such event with p>R is far B (the near label after the mark is >=.96T at sufficiently high H).
The net ordinary drop Delta>=1.5T, and horizon gain g>=Delta. Same-band cores are disjoint, at most one pending per band. A completed corridor is now called CUT-FREE GOOD if it has no reset>=5 and no event crossing a surviving cut. It may contain arbitrarily many labels >R, including labels >V, as long as their actual jump intervals contain no surviving cut. Its entire contiguous half-open horizon interval is free of surviving cuts. This is a weaker condition than the old all-labels<=R requirement. It still has all plateau states in (4T/15,57T/20), and first/last events decreasing nonresets.

Bad completed corridors can be charged to their reset or else to an actual B_cross event; no near nonreset or low label can supply that latter exception. A reset is charged at most once per band, and a B_cross at most three times across the bands by the ratio 2.85/.4<8 for its pre x. Good corridor event intervals likewise split into three disjoint colors j mod3. Consequently, writing L_bands=#bands, m_bad for the count of bad or pending selected marks, W_bad=sum of their labels, we have
    m_bad <= (N+2)L_bands+3 B_cross,
    W_bad <= 4C + 10 sum_{dec resets q}(q+6) +3C B_cross
           <= 4C+10(C+6)(N+1)+3C B_cross.                   (8)
For the reset weight bound, any charged mark has T<(q+6)/.4 by the pre-x reset bound, and the sum of 2T over those dyadic bands is <10(q+6). Pending mark weight <4C. One may restrict reset and B sums to actually charged events, as in the earlier last-exit note. In particular (8) removes ALL far B that never cross a surviving cut from the exception set.

Let I=[H_start/2,H_end/2) and Z=Z(I) as in (6). If T0>=ceil(8ell/3), every cut-free good corridor has length g/2>=2ell in this coordinate. At least half of its positions start length-ell zero windows wholly in the interval. Within each color those starts are disjoint. Therefore, summing over all selected marks and colors,
    sum_good g <=12 Z,
    m_good <=8 Z/T0,
    W_good <=16 Z,                                         (9)
using p<2T<=(4/3)g. No bound on any individual maximum gap is needed, and noncrossing high events inside these corridors do not affect the result. Equations (6),(8),(9) imply for ANY selected subset of A1 p>=T0>=ceil(8ell/3),
    m_tail <= O(X exp(-.001r)/T0)+(N+2)L_bands+3 B_cross,
    W_tail <= O(X exp(-.001r))+4C+10(C+6)(N+1)+3C B_cross.    (10)
This tail theorem itself does NOT require absence of a twin witness: it only uses the definition of B_cross, the R barrier exclusion, and the recovery geometry. It replaces the former sparsity of ALL far B by actual crossing sparsity in both count and weight conclusions. Under N,B_cross=o(sqrt X), W_tail=o(X), m_tail=o(X/ell) at T0=ceil(8ell/3). The actual population can include all A1, not just crossers. At the balanced cutoff ell=O(X^(2/11)), and ell*log X=o(sqrt X).

## 4. A truncated crossing-only window alternative

Assume no direct twin witness >S at surviving cuts. In the proof of the previous window alternative take ONLY actual crossers. Put m_cross=#A_cross, F_cross=sum of their gains. The far-only recovery share holds for any designated A1 subset:
    (1+c)F_cross <= G_far + D_near_reset + 2C,
    c=9/5-o(1).
The union of actual crossing jumps covers all surviving cuts. Their gain is at most G-G_far+F_cross+C(n_A0+B_cross), and count at most n_near+m_cross+n_A0+B_cross, where n_A0 counts far A0 crossers and n_near all near events. Near decreasing resets and these far A0 resets have distinct associated canonical visits except possibly one pending, so their combined count<=N+1. Applying (7) and substituting the far-only share, using G_far>=G/2-O(sqrt X), n_near=O(sqrt X), yields
    9G/28-o(X) <= 2ell*m_cross+(C+2ell)*(N+1+B_cross).        (11)
The leading o(X) includes the explicit smoothing error as well as the earlier near geometry O(X^(3/4)) and boundary O(C+ell sqrt X) terms. The count m_cross is already smaller than the old count of all far A1 p>V.

Now put T0=ceil(8ell/3) and m_mid=#A_cross with V<p<T0. Apply (10) to the crossing A1 tail p>=T0. For L_bands=O(log X),
    2ell*(m_cross-m_mid)
        <= O(X exp(-.001r)) +2ell*(N+2)L_bands+6ell B_cross.
Because ell log X=o(C) at balanced R, absorb the terms proportional to N and B_cross into the coefficient, not the additive error. We obtain the NEW unconditional-on-sparsity alternative (conditional only on no twin witness):
    9G/28-o(X) <= 2ell*m_mid+(C+o(C))*(N+1+B_cross).          (12)
There is no assumption that either count is small in (12). It confines the A1 term to actual crossing far A1 in the finite band V<p<ceil(8ell/3). If no such mid population exists on a sequence of large crossed windows, N+B_cross>= (9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X. More generally under N,B_cross=o(sqrt X),
    m_mid >= (9(lambda-1)/56-o(1))*X/ell
          = Omega(X^(9/11)).                                (13)
In particular choose V=floor(R/loglog R)^2 as before. This retains the prior super-logarithmic lower label threshold and occurrence exponent while using ONLY actual crossing sparsity, and now also imposes an upper threshold on the required counted population. The tail conclusion (10) simultaneously bounds the weight of all exceptionally large A1 under those weaker assumptions. B_cross need not be comparable to B_R; no density or proportionality relation between them is assumed.

## 5. Noncrossing-B versus high-multiplier record recovery

Use all m=m_cross or the mid subset as selected marks, dyadic bands starting T_min=V+1. Under N,B_cross=o(sqrt X), (11) or (13) gives m=Omega(X/ell), and (8) gives n_good=(1-o(1))*m. These are cut-free good corridors, not necessarily all-low ones.

For each corridor, strict running-minimum ordinary-deficit decreases allocate disjoint new record intervals with total Delta>=1.5T, as in 319d42d. Each record of label s>=5 is a nonreset and contributes at most s-3. Separate low record events s<=R and high record events s>R. The latter are all genuine FAR NONCROSSING B, and their contribution is <.95T. If k_L,k_H count those occurrences in the corridor, respectively, then
    (R-3)/T*k_L + .95*k_H >=1.5.
Let J_L,J_H count DISTINCT actual record events in the respective classes across all good corridors. The overlap is <=3, and T>=V+1, giving
    (R-3)/(V+1)*J_L + .95*J_H >= n_good/2.                 (14)
Every low record has multiplier h with
    2s h = x_post-6I-3 > (4/15)T-9,
    h=Omega(V/R).
Thus under the weaker sparsity conditions, either Omega(X^(9/11)*V/R) high-multiplier low record decreases, OR Omega(X^(9/11)) far noncrossing high B record decreases must occur on the actual ray (or both). For example if J_H=o(m), J_L>=(1/2-o(1))*(V+1)/(R-3)*m. This is a tradeoff for the SAME necessary A1 population of actual cut crossers, not for hypothetical independent plateau states.

A second variant uses B_star (ALL far B with p>V, plus those R<p<=V with w<=2S), rather than just actual crossers. Declare an extended good corridor one with no reset>=5 and no B_star. Inside such a corridor no A1 occurs, all labels are <=V, and any label s>R has w>2S. Under no witness these events cannot cross surviving cuts, so each extended good corridor is also cut-free good. The same geometric exception accounting bounds the number excluded by (N+2)L_bands+3B_star. For N,B_star=o(sqrt X), n_ext=(1-o(1))*m_cross. Split the records into low s<=R and moderate slow R<s<=V, with distinct actual counts J_L^*,J_M^*. A moderate record contributes at most s-1-2(2S+1)<=V-3-4S. Hence
    (R-3)J_L^*+(V-3-4S)J_M^* >= (V+1)*n_ext/2.             (15)
All moderate records are far noncrossing B with waits>2S; all low records have h=Omega(V/R). Under these hypotheses either the same growing high-multiplier low supply is necessary, or Omega(X^(9/11)) actual moderate slow B decreases with R<s<=V. The coefficient V-3-4S is positive asymptotically; the finite inequality is applied only when it is positive, or moderate decreases cannot occur. This gives a narrower unresolved population than arbitrary high B, without requiring the former B_R=o(sqrt X).

Neither (14) nor (15) bounds the upper supply of record decreases. Noncrossing high B may remain abundant, and finite twins alone does not imply N,B_cross or B_star sparse. The current unconditional alternative (12) either requires many crossing B/canonical reentries or a large confined population of crossing A1; it does not rule out those possibilities. Next targets are a supply upper for noncrossing B (especially moderate slow decreases) and the high-multiplier low records, or an exclusion of the large crossing-B/canonical-root alternatives. A direct offset twin witness at unbounded S would resolve the problem, but it has not been forced.

## 6. Finite diagnostics and preservation

[Audit 3f70772](https://github.com/tara-sooo/A166944-Lean/blob/3f70772f5fac3845d1a502229503b19ad674ec1b/research/min_direct_sieved_corridor_l2_audit.mjs), blob8496c1eb8f88acc14f179e65cda5e217a82395e9. Exact remote readback. Run node research/min_direct_sieved_corridor_l2_audit.mjs 30000. Actual ECMAScript execution in tool runtime, not a separate Node process. Six small complete sieve periods up to255255, 17 period/length controls, 82 intersection periods, 29 truncation controls, 3108315 period positions, 5450655 exact pointwise envelope comparisons in common integer units, 1015 local L2/Minkowski and exact zero-count checks, 4340 exact periodic squared-sum bounds. Minkowski norm comparisons use floating tolerance; integer envelopes, zero bounds and periodic squared sums use exact BigInt. 340 disjoint zero-run controls, 4103 long zero runs, 293463 zero-start checks. These finite controls verify the analytic envelope and geometry, not the asymptotic exponential variance at large R; (1)-(5) follow from the earlier rational certificate and uniform bounds.

14998 odd canonical roots through30000,243497 actual events,0 cap180 unresolved; reconstructed earlier9962-digit actual CRT witness word7687/5233/3541/2389/1621/1093/733/7369 with22195 literal BigInt gcd ticks and20600 stage residue checks. 9307 corridor/cutoff controls,6153 mark incidences,296 completed,5857 pending,289 reset-bad,2 actual crossing-bad,5 cut-free good including4 with high labels,5 exact record partition checks,72 direct union-cut absence tests. Two extended good witness controls with nine low and one moderate record. At S73,R3600,V5329,T7000, mark7687, its five-event last-exit corridor labels5233/3541/2389/1621/1093 is cut-free and extended good despite its first label5233>R: wait162>2S=146, all other labels<=R. This is actual, not a relaxed path. At S79,R5233,V6241 it is all-low. At S3,R5,V7 a real cut crossing rejects the corridor. The main scan had max good overlap1 and no same-color adjacency, so the previous separately audited relaxed overlapping controls remain the nontrivial test of the color argument. No-witness assumptions in the asymptotic population theorem are not imposed on the finite scan; for extended-good controls actual absence of surviving cuts is checked. Initial audit had zero extended-good and crossing-bad cases; expanded BigInt cutoffs and reran all tests, including actual moderate-slow and crossing cases, all final assertions passed.

No Lean executable/kernel verification. No new Fourier exponent or finite-twins contradiction. Main and sibling branches not modified.
