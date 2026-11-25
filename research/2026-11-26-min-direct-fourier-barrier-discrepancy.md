# Fourier discrepancy for both barrier families and a balanced primorial cutoff

Continuation of [a3f181e](https://github.com/tara-sooo/A166944-Lean/commit/a3f181e92f2b09a5affb63bc48c8fa56ca166ffb). The previous horizon and deficit barrier estimates used the entire primorial period as the discrepancy. Exploiting the contiguous local CRT residue intervals gives a uniform Fourier improvement, not merely a smaller average gap. This simultaneously increases the required A1 count and decreases its permitted large-label tail threshold under the existing root-sparse/high-B-sparse hypotheses. Combining dense deficit cuts with completed ordinary recovery slabs removes the earlier small-primorial restriction for the good-mark weighted theorem. No contradiction with finite twins or Lean kernel verification.

## 1. A common local Fourier bound

For an integer cutoff S>=5 let P=P_S be the product of odd primes <=S. Use integer coordinate j=b/2 for even cuts b, and the periodic extensions to all integer j of the following two barrier families:
* H-family: 2j mod p lies in {0,2,...,p-3} for all odd p<=S. Equivalently j mod p belongs to a contiguous interval of length (p-1)/2.
* d-family of a3f181e: 2j mod 2p belongs to the complement of the two possible downward-crossing intervals. For p>=11 the local allowed residues of j are the cyclic interval {(p+5)/2,...,p-1,0}, of length (p-3)/2. For p=3 all residues are allowed; at 5 and7 the local sets have size3. The d-family excludes any downward crossing by event label<=S (including resets). The H-family excludes upward horizon crossing by label<=S.

Each family is a product of nonempty local sets under CRT, so its density theta in j-coordinate is the product of the local densities. Use alpha_S for the H-family density and theta_S for the d-family density as before. Let mu be the probability measure uniform on its allowed j residues modulo P. For p>=11 define
    kappa_p = 1 / (((p-3)/2) sin(pi/p)).
We have kappa_p<1, since sin(pi/p)>=3/p for p>=11 by the elementary sine bound sin x>=x-x^3/6, and 3(p-3)/(2p)>1. For a cyclic interval of length a, any nonzero local Fourier frequency f has normalized coefficient magnitude
    |sin(pi*a*f/p)|/(a*|sin(pi*f/p)|)
       <= 1/(a*sin(pi/p)).
Thus both families have the common upper bound kappa_p for p>=11 and trivial bound1 at 3,5,7. No assumption on the local CRT inverse or on the distribution of frequencies is required.

Put
    Lambda_S=product_{11<=p<=S, p prime} kappa_p,
    D_S^*=product_{11<=p<=S, p prime} (1+(kappa_p^(-1)-1)/p),
    F_S(k)=product_{11<=p<=S, p prime, p|k} kappa_p^(-1).
CRT represents j modulo P as sum r_p*(P/p)*u_p with u_p the inverse of P/p mod p. The global Fourier coefficient muhat(k) factors into the local coefficients at frequencies k*u_p mod p. The local frequency vanishes exactly when p|k, so for 1<=k<P
    |muhat(k)| <= Lambda_S F_S(k).                    (1)
For all M>=1, writing F_S(k) as a divisor sum with nonnegative coefficients
    F_S(k)=sum_{a|k, a|product_{11<=p<=S}p} c_a,
    c_a=product_{p|a}(kappa_p^(-1)-1),
gives
    sum_{k<=M} F_S(k)/k
      =sum_{a<=M} (c_a/a) H_floor(M/a)
      <= D_S^*(1+log M).                             (2)
This harmonic weighting is important: a bound on every individual low frequency is not enough to control the full interval discrepancy without accounting for the other frequencies.

## 2. Uniform interval discrepancy and maximum gaps

Define the explicit common bound, in j-coordinate,
    E_S=min(P_S, P_S Lambda_S D_S^*(1+log P_S)).       (3)
For either family and EVERY half-open integer interval I of length l in j-coordinate (arbitrary translate and length),
    |#(family intersect I)/theta - l| <= E_S.         (4)
Proof: by periodicity reduce to length <=P. Fourier inversion of the indicator of the interval and measure mu gives discrepancy equal to sum over 1<=k<P of muhat(k) times an interval exponential sum (possibly conjugated). For 1<=k<=P/2 the latter has magnitude <=1/sin(pi*k/P)<=P/(2k). Combine the symmetric frequencies k and P-k, using that the measure is real, and then (1)-(2). This bounds the discrepancy by P Lambda_S D_S^*(1+log P). The elementary period bound P gives the other term of the minimum. These bounds concern the normalized count (the raw count divided by density), not the absolute error in the raw count.

For even absolute endpoints H<=Z the normalized barrier count 2/theta times the number in [H,Z), or (H,Z], differs from Z-H by at most 2E_S. For real endpoints this bound may be enlarged to 2E_S+2 by rounding to the even lattice. Therefore a run of floor(E_S)+1 consecutive j positions cannot be empty. Every next cut in absolute even-coordinate distance is within
    B_S=2 ceil(E_S)+4
of any real target (strictly less than B_S). The extra constant allows rounding up to the even lattice, and is also valid for the shifted x=d+3 coordinate of deficit cuts.

The improvement is asymptotically substantial. As p grows, kappa_p=(2/pi)(1+O(1/p)). Therefore, using the elementary Chebyshev lower bound on pi(S), with pi(S) denoting the number of primes<=S,
    log Lambda_S= -log(pi/2)*pi(S)+O(log S),
    log D_S^*=O(log S), log(1+log P_S)=O(log S),
    E_S/P_S=exp(-(log(pi/2)+o(1))*pi(S)).            (5)
The constant pi inside log(pi/2) is the circle constant; pi(S) is the prime-count function. For large S the second term in (3) is the smaller one. Since P_S Lambda_S>=a fixed constant times product of p*kappa_p over p>=11, E_S grows without bound. Hence B_S=O(E_S). This is a uniform gap upper bound and not an assertion about the typical gap. In particular E_S/P_S is smaller than every fixed negative power of S. No unproved prime-distribution conjecture was used.

The same interval bound can replace the period-size discrepancy in both previous barrier analyses; it does not identify the two different local barrier sets.

## 3. Improved macroscopic A1 lower count

Use the established canonical MIN model and its earlier notation. A1: label p>=47, p>=5d+15, adjusted D=2p. A0: same label/deficit test and D=0. B: failure of the test at p>=47. Far and near use the earlier fixed square-band definition. For an infinite canonical ray and crossed horizon window [X,lambda X], lambda>1 fixed, choose cutoff R of order log X with E_R=o(sqrt X). The block has gain G=(lambda-1)X+O(sqrt X), label bound C=floor sqrt(lambda X+1), near gain<=G/2+O(sqrt X), near count O(sqrt X). Let m count ALL A1 with p>R, N count actual canonical visits, and B_R^count count far B with p>R. (The superscript distinguishes this count from the gap upper bound B_R.)

By (4), total normalized H-barrier coverage in the block is >=G-2E_R. Every jump p<=R covers none, and a jump of gain g covers normalized count <=g+2E_R. Subtracting the high-near coverage, the high-far normalized coverage is >=G/2-o(X), since E_R sqrt X=o(X). The A1 gain ceiling from c14ee7f for any subset gives at most 5G/14+O(C) high-far A1 gain. Their count is <=m. Each high-far A0 has a distinct associated canonical visit except possibly one pending at the endpoint, so their count <=N+1. Each A0 or B contributes at most C+2E_R normalized coverage. Hence
    G/7-o(X) <= 2E_R*m+(C+2E_R)*(N+1+B_R^count).      (6)
All error estimates are uniform over the ray under these cutoff conditions. In particular suppose along a sequence of crossed windows
    N=o(sqrt X), B_R^count=o(sqrt X).
Then
    m >= ((lambda-1)/14-o(1))*X/E_R.                (7)
This improves the earlier bound with P_R in its denominator by P_R/E_R=exp((log(pi/2)+o(1))*pi(R)). The sparse-root/high-far-B conditions are hypotheses, not consequences of finite twins.

One can now use a balanced cutoff R: choose the largest odd prime R such that P_R<=sqrt X. Elementary Chebyshev bounds on log P_R and Bertrand's postulate give R=Theta(log X) (the next prime <=2R, and P_R>sqrt X/(next prime)). By (5),
    E_R (log X)^A=o(sqrt X) for every fixed A>0.
Thus (7) forces
    m >= ((lambda-1)/14-o(1))*sqrt X
                    *exp((log(pi/2)+o(1))*pi(R)).
In particular m dominates sqrt X times every fixed power of log X, even at this substantially larger primorial threshold. Earlier estimates used a strict smaller-power bound P_R<=X^delta, delta<1/2, to make the period-size errors negligible. The condition E_R(log X)^A=o(sqrt X) is the relevant replacement; the balanced choice is a concrete sufficient one.

## 4. Improved upper count on the large-label A1 tail

In x=d+3 coordinate the shifted dense deficit barriers are x=b+3 for b in the d-family. Given any cutoff S>=5, let B=B_S from section2. Round each reference level z_j=3B*2^j, j>=0, up to the first shifted deficit barrier y_j>=z_j. Then
    z_j<=y_j<z_j+B,
    y_(j+1)/y_j >= 2 z_j/(z_j+B)>=3/2.
Every decreasing nonreset has x/x'<3/2, hence crosses at most one of these levels downward. All downward crossings have label>S by the deficit barrier property, unless there are no crossings.

Every marked A1 with p>=2B has a reference level in (p/5,2p-B]. If p/5<z_0 choose z_0=3B; otherwise the first z_j>p/5 is <=2p/5<=2p-B. The rounded level therefore lies in (p/5,2p], and the mark crosses it upward. Retain only the reference levels z_j<=2C, where C bounds marked labels. Assign each such mark just one level and match to its first later downward crossing, by the alternating-crossings proof of 4947f42 and a3f181e. The assignments to nonreset events are globally injective. Let H_S^dec count ordinary-decreasing nonreset events of label>S in the block. At most N+1 decreasing resets and at most one pending slot per level can prevent a nonreset match. Thus for any contiguous canonical event block,
    #marked A1 with p>=2B_S
       <= H_S^dec + (N+2)L_S,                       (8)
where L_S<=1+log_2(2C/(3B_S)) if the level set is nonempty, and L_S=0 otherwise. This is an actual upper count of occurrences on a ray. The earlier threshold P_S/2+4 is replaced by 2B_S=4ceil(E_S)+8, exponentially smaller relative to P_S on the prime-count scale. At small S the new upper threshold can be worse, and one can retain the earlier bound there.

Apply (8) with S=R under the hypotheses and balanced cutoff of section3. Every ordinary-decreasing nonreset p>R is B (A1 increases, A0 resets, and the prior low-deficit criterion exhausts those two cases); the near count O(sqrt X) and far sparsity give H_R^dec=O(sqrt X). Since L_R=O(log X), (7) implies
    #marked A1 with p>=4ceil(E_R)+8=o(m).            (9)
Almost every mark is thus confined to R<p<4ceil(E_R)+8, with a lower count of order X/E_R instead of X/P_R. The exceptional o(m) labels can still carry significant total gain. This upper bound does not cap the number of repeated small-label recoveries.

## 5. Larger lower recovery cutoff and weighted ordinary recovery on good marks

For completeness there are two useful combinations with the earlier matching/slab proofs. First choose the lower cutoff S to be the largest odd prime with P_S<=R (now R can be the balanced choice). The same Chebyshev/Bertrand argument gives S=Theta(log R), and B_S=o(R) by (5). More generally only B_S=o(R) is needed. In section4 of a3f181e replace K_S by the gap bound B_S, and round up to the next dense deficit barrier, not necessarily a multiple of K_S. For fixed T>=47 with B_S<=T/200 use reference grid ratio beta=3/2+10B_S/T and phase a in [1,beta), starting at (T/5)*a. The successive rounded levels have ratio>3/2 because z>=T/5 and (beta-3/2)*z>=2B_S. Select references in (p/5,2p-B_S] for every marked p>T. All five or six levels per mark are crossed upward; the phase average slot count is at least m log_beta(10-5B_S/T). The identical first-downcross pairing gives distinct nonreset recovery events with s>S and s<beta^k*p/10+B_S/2 for rank k, and exceptions <=(N+2)L. At T=R and with the sparsity conditions of section3, discard assignments to s>R (at most H_R^dec by injection). All but o(m) marks receive five distinct later ordinary-decreasing nonreset B with S<s<=R, and at least (log(10)/log(3/2)-5-o(1))*m receive six. This uses a larger lower cutoff than the earlier conservative choice K_S<=o(R); at the balanced S the full primorial P_S can be comparable to R, but its effective gap is much smaller.

Second, use the COMPLETED SLAB proof of 4947f42 to avoid the large exception-weight error in the dense matching theorem of a3f181e. In a finite block with marks p>R, choose any 1<eta<=3/2, geometric x-levels starting at R/5 with ratio eta, and select the complete slabs [a,b] lying strictly above p/5 and ending at or below 2p for each marked p. Their contiguous union has width at least (2/eta-eta/5)p. As in that paper, a slab is good if its recovery interval (from the mark until first x<=a) completes and no positive ordinary downward length allocated in the slab comes from a reset or a nonreset s>R. A mark is good if all its selected slabs are good. The earlier counting proof yields
    #bad <= (N+2)L + (ceil(log_eta(3/2))+2)*H_R^dec,
where L<=1+log_eta(10C/R). This bound does not depend on how big the bad marks' labels are.

Now for a good mark and each selected slab [a,b], take all shifted dense S-deficit barriers in (a,b]. Each is crossed upward by the mark, and its first later downward crossing occurs before or at completion of the slab, hence within the good recovery interval. That event gives positive length inside the slab: its downward interval contains the cut in (a,b] with strict inequality at the post endpoint. Thus it is a nonreset s<=R, and since it crosses a dense S barrier it must have s>S. At each fixed cut the first-downcross pairings are injective; slabs have disjoint interiors and the half-open convention avoids duplicating a shared endpoint. So no event/cut pair is allocated twice, even if different good marks recover overlapping scales.

Let W_good be the sum of labels of the good marks (or any chosen subset of them), m_good their count, F total actual ordinary deficit decreases by nonresets with S<s<=R in the block, and j their count. Every good mark's contiguous slab union contributes at least theta_S/2 times ((2/eta-eta/5)*p-2E_S-2) cut slots by (4) at real endpoints, with the additive2 accounting for lattice rounding. At an event there are at most (d-d')/2 available even cuts, and the normalized dense cut count is <=d-d'+2E_S. Summation proves the two simultaneous finite inequalities
    F >= theta_S * [(2/eta-eta/5)*W_good-(2E_S+2)*m_good],
    F+2E_S*j >= (2/eta-eta/5)*W_good-(2E_S+2)*m_good. (10)
This combines discrete cut matching with good-slab exception counting; it does NOT need to charge all exceptional marks at a common upper label U. For large windows choose eta=1+1/log X. The number of bad marks is O(sqrt X*(log X)^2)=o(m) under (7) and the balanced cutoff. Also E_S=o(R). Thus
    F >= (9/5-o(1))*theta_S*W_good,
    F+2E_S*j >= (9/5-o(1))*W_good,                   (11)
where good marks include all but o(m) marked occurrences. One can intersect this good set with the label restriction (9), still all but o(m). For sufficiently large X every counted recovery event lies far from the square band (s<=R=O(log X)) and satisfies B since s>S>=47 and ordinary d strictly decreases. This proves the weighted lower-band recovery theorem with the balanced cutoff, without the previous delta<1/4 restriction needed to bound the exceptional weight in the earlier all-moderate-marks formula. It still only uses the GOOD marks' weight, not the total weight of an exceptional large-label tail. If j=O(W_good/R), then 2E_S*j=o(W_good) and the second bound yields the full (9/5-o(1))*W_good actual reduction. Otherwise the density-weighted lower bound remains unconditional on j within the sparsity hypotheses.

These are necessary lower and upper bounds for specified populations. They do not show that either sparsity hypothesis must hold on an infinite ray, nor give an upper bound on the supply of low-label ordinary decreases small enough to contradict (7),(11). No contradiction with finite twins.

## 6. Reproducible diagnostics and persistence

[Fourier audit 36feeadd](https://github.com/tara-sooo/A166944-Lean/blob/36feeadd032a1e762762c86d0c4e52ace7425df9/research/min_direct_fourier_barrier_discrepancy_audit.mjs), blob ac430535a0de680b9ca86ddd6e42ca6811e70298. Run node research/min_direct_fourier_barrier_discrepancy_audit.mjs. Actual ECMAScript execution in tool runtime, not a separate Node process. Both families:90 local-set checks through prime199,8,360 local Fourier coefficient checks,428 CRT frequency-factorization checks (direct global comparison at smaller periods),216,290 divisor-average checks,24,000 interval tests. Complete periods S=5,7,11,13,17,19 for both families, including all cyclic gaps and discrepancy extrema. At S19 the period in index-coordinate is 4,849,845; actual maximum gaps are 1,785 (H) and990 (d), normalized discrepancies12690.074... and4504.013..., compared with the formula's min bound E=P at this small cutoff. The audit also verifies 132 rounded grid checks and12,000 tail coverage tests using both the proved upper bound and the smaller observed complete-period maximum gap. All passed. Fourier/trigonometric diagnostics use floating point; full-period counts and gap calculations use integer arithmetic within safe ranges. The analytic inequalities in sections1-2 are the proof, not an inference from finite measured gaps.

For S100/200/500/1000/2000 the computed -log10(E_S/P_S) values are approximately1.198/4.737/13.718/27.573/53.596. These are evaluations of the proved upper-bound formula, using floating arithmetic, NOT enumeration of those huge periods or observations of their actual maximum gaps.

[Combined slab audit a0af473](https://github.com/tara-sooo/A166944-Lean/blob/a0af47386605217fc75c01f12150b5bfcf06a/research/min_direct_dense_good_slab_audit.mjs), blob f501b7a114ac4fa6374b4ea53d10d6d990263c3d. Run node research/min_direct_dense_good_slab_audit.mjs 50000 180. Derived from the earlier exact rational slab audit; same 24,998 roots,452,868 actual events,3,929 A1,all terminated within cap; 407,200 block/cutoff incidences,33,412 nonempty marked blocks,412,800 slabs,161,226 allocation checks. Only the earlier constructed 9,962-digit witness yielded good marks in these finite diagnostics (four beta choices). Added sixteen complete good-mark/cutoff tests S5/7/11/13 and eta3/2,5/4,11/10,101/100,23,711 exact distinct event/cut matches,92 per-event capacity checks; all pass. The audit uses period-size error at its small cutoffs (where E_S=P), not extrapolation to the asymptotic improvement. Reconstructed witness 7687/5233/3541/2389/1621/1093/733/7369 with22,195 literal BigInt gcd ticks,20,600 stage-residue checks. For eta101/100 and S5 the selected good mark7687 receives4109 dense cut matches, normalized length13696.666..., against actual ordinary decrease13908; S13 gives250 matches and normalized length13902.777.... These values may differ from the continuous slab width because the density correction is not exact on an individual interval; the theorem accounts for this through the uniform discrepancy term. All exact assertions passed. Both new audit sources remote-read and verified. Main/sibling branches unchanged, no Lean executable/kernel verification or observation of a macroscopic infinite-ray crossing.

Next: use (1)-(4) to study local barrier density for joint H and deficit restrictions at a fixed event label, or derive a stronger supply upper bound from the low-label high-multiplier clock constraints. This turn changes the effective cutoff scale and tightens both bounds in the sparse branch, but does not establish a stopping invariant.
