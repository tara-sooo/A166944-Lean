# Scale-resolved cluster recovery and refined 4/11 smoothing

Continuation of [ccf79fc](https://github.com/tara-sooo/A166944-Lean/commit/ccf79fc5df279083a1099b0003e37171a4b927e5). Two results: refine the three-class Fourier certificate to exponent4/11; and replace individual recovery-event matching by matching to a high event together with its following low-label run. The latter gives five distinct high far nonreset B precursors per completed large A1, with a logarithmic-in-mark-size lower prime cutoff, and a weighted completed-slab supply bound. This is a scale-resolved necessary condition, not a stopping invariant or contradiction with finite twins.

## 1. Refined three-class certificate

Retain the finite three-class energy inequality of ccf79fc, with full-P CRT inverse and local frequency classes 0,+/-1,other. Its limiting squared coefficient upper bounds in the two nonzero classes are A=4/pi^2 and A/9, and limiting class moment sums are 2A^s and (1 or 1/3)-2A^s for s1 or2 respectively. For both barrier families and sufficiently large primes use strict upper constants
    A1=.40530, A2=.04504,
    m11=.81060, m12=.18950,
    m21=.32860, m22=.00490.
The accompanying exact rational code verifies the strict comparisons using 3.14159<pi<3.14160 and the preceding formulas. The conservative lower bounds on negative logarithms are
    c1=.903, c2=3.100,
    b11=.209, b12=1.660, b21=1.112, b22=5.300.

Use delta=7/11, M=ceil(P^delta exp(r)), ambient primes R/log R..R, n~r, q=floor(log M/log b), q/n=delta+o(1) by PNT. Let v,w,u be the class fractions, v+w+u=1, v<=q/n. For selected fraction H and typical class intersections j_i=H*t_i+O(1), sH<1, the earlier agreement bound has gap/n
    (1-H)*(v^2+w^2/2)-(delta-H)+o(1).
The earlier conditional AM-GM/partial-moment bound has saving exponent/n at least
    (1-sH)*(c1*w+c2*u)+H*(b_s1*w+b_s2*u-E(v,w,u))+o(1),
where E is the entropy. Rounding the selected counts is feasible as in ccf79fc, including bounded-size classes, and all errors are uniform when H ranges in a fixed finite set. Positive gap gives bounded projection fibres (or injection if h>q).

New certificate: Nmesh=1000, i=0..640,j=0..999-i, v in[i,i+1]/1000, w in[j,j+1]/1000, u in[max(0,998-i-j),1000-i-j]/1000. This covers the feasible simplex with v<=.64, including its boundary, and hence all asymptotic divisor classes. Put S=(2i^2+j^2)/(2*1000^2), choose
    H=max(1,ceil(100000*(7/11-S)/(1-S))+1)/100000.
Verify the gap directly in exact integer arithmetic (so the floating ceil used for selection is not relied upon). The entropy upper bound is the sum of the three component suprema bounded outward by interval logarithms at the appropriate endpoints, or .368 when the interval contains the maximum location 1/e in(.367,.368). Lower-bound each positive linear contribution by the lower component endpoints. Choose s1 or2 with sH<1, retaining the larger certified saving. All 435880 cells have saving strictly >.003; observed minimum certified lower value .005810681080419112, min shortening gap .000005067736363636364, max H=.63638. 304878 choices s1,131002 s2. The exact certificate uses 10^30 fixed-point BigInt logs, range reduction by powers of2, 120 terms of atanh series with outward rounding and rigorous remainder, including the log2 interval. The comparison thresholds .003 and zero gap are checked as integer inequalities. No claim is made that delta=7/11 is optimal.

There are O(n^2) classes. Summing the exponentially small energy bounds, using n~r, and bounding high frequencies by (P/(2*l*(M+1)))^2/alpha_P<=exp((log2-2+o(1))*r) for l>=ceil(P^(4/11)), gives for sufficiently large R BOTH families
    sigma_l^2 <= exp(-.001*r), ceil(P_R^(4/11))<=l<=P_R.   (1)
This is a mean-square, not a pointwise gap theorem.

Substitute into the same finite smoothed-horizon union and far-only recovery inequalities of78b1212/850c00f. Crossed [X,lambda X], fixed lambda>1, G=(lambda-1)X+O(sqrt X), C=floor sqrt(lambda X+1), N canonical visits, B_R far B p>R, m_f far A1 p>R. At any fixed 0<rho<1 with largest prime P_R<=X^rho, or the near-X cutoff P_R<=X/log^2 X, l=ceil(P_R^(4/11)) gives P_R=o(X), l log^a X=o(sqrt X) for all fixed a. Therefore
    9G/28-o(X)<=2l*m_f+(C+2l)(N+1+B_R).
Under N,B_R=o(sqrt X), m_f>=(9(lambda-1)/56-o(1))*X/l; balanced P_R<=sqrt X yields Omega(X^(9/11)), improved from X^(4/5); near-X gives Omega(X^(7/11) log^(8/11) X), a different counted population. Previous unconditional-on-sparsity joint count N+B_union>=(9(lambda-1)/(28sqrt(lambda))-o(1))*sqrt X holds at these cutoffs as before. The precursor and long-run bounds give W_T=O_lambda(X exp(-.001*r)+sqrt X(N+B_R+1)) for T>=max(48,20l); sparse T=24l gives o(X) weight and o(m_f) occurrences. Balanced threshold O(X^(2/11)) improves O(X^(1/5)). These are substitutions into established inequalities, not observations of an infinite trajectory.

## 2. New cluster construction

Use actual adaptive MIN on a canonical ray, x=d+3, x'=d'+3, selected prime p, gain p-1, adjusted D=d'-6I. A1 means p>=47, x<=p/5, D=2p. Nonreset labels >=5 have D=2p*h with integer h>=1, post x'>=2p+3 and x/x'<3/2 (the inequality holds for increases as well; a decrease is <=p-1 and x'>=2p+3). A0 is the low-deficit reset; B the remaining high labels. Near/far as in8b30078 and850c00f. Take a contiguous finite block with all pre-horizons >=6250001, label bound C, N canonical visits in (start,end]. The later-near theorem of850c00f now gives for any near label s at or after marked A1 label p the bound s>=(1-eta)p>=.96p, eta=2/floor((A-1)^(1/4))<=.04. This is the only near geometry needed below.

Choose cutoffs 47<=S<=R. Mark A1 events p>R with p>=T>=48 (or any subset, or further upper restriction on p). Write m_T and W_T for count and sum of labels of the marks. Partition the block into clusters: each event with label s>S and its following maximal consecutive run of labels<=S; an initial run without a preceding high event is kept separate. Let K be any upper bound for the gain of each such low run, and require
    K<=T/200.                                           (2)
For example K=K_S=2P_S is valid by the earlier primorial barrier: low runs cannot cross the next multiple of K_S. One can instead use a smaller proved or observed finite-block upper bound K. This flexibility is useful for finite diagnostics. The initial low run cannot contain any marked event or pay any future marked level. No mark occurs inside the low-label part of any cluster. By summing d'-d>=-(p-1), every plateau in a low run is >=its initial x-K. This holds without assuming the run is decreasing.

Use first-downcross allocation for the expanded lower recovery interval
    (p/5,19p/10].                                      (3)
Every A1 crosses it upward. Pending levels for distinct marks have disjoint interiors and each pending level is <=the current x. We claim all payments for (3) occur in clusters whose high precursor is either a reset or a far nonreset B.

- If the high event is the mark itself, x_post>=2p+3, and the subsequent run cannot reach a level y<=1.9p because K<=p/200. The high event increases.
- If the high event is another A1, an older pending level y satisfies y<=x_pre<=s/5. Then x_post>=2s+3>=10y+3. Its following low run cannot reach y, since y>p/5>=T/5 and K<=T/200. New marks are handled by the first case.
- If the high event is a near nonreset, it is at or after the mark and x_post>=2s+3>=1.92p+3. It cannot pay y<=1.9p on the high event or after a low run of gain<=p/200. This also covers any later near nonreset irrespective of its multiplier.
- The initial run cannot pay a marked level since allocation starts only at a mark. Remaining high events are resets or far nonreset B. All reset high labels exceed S>=47 and therefore have distinct associated canonical visits except possibly one pending endpoint, by123bbd4.

This strengthens precursor exclusion f7c6f40: the admissible recovery interval is almost the entire A1 excursion, and the clusters can be assigned injectively at geometric levels.

## 3. Five distinct high-B cluster matches per mark

Use geometric levels y_j=(T/5)*phase*(31/20)^j, j>=0, 1<=phase<31/20, through19C/10; L0 denotes their count (if no marks the bounds are trivial). Each mark p>=T contains at least five levels in (3), since (31/20)^5<19/2=9.5. Match each selected level to its first downward crossing within the block, or leave it pending. At each fixed level successive marked upcrossings must be separated by its downcrossing, so no event/level pair is assigned twice.

Suppose a far nonreset B cluster (high precursor s, pre X0, post X1) pays a level y. No new mark occurs within this cluster, so all its paid levels were pending at its start and are <=X0. A payment by the high event has X1<y, and a payment within the low run implies X1<y+K by the decrease bound. Also X0<(3/2)X1. Therefore if y_min and y_max are two paid levels, then
    y_max<=X0<(3/2)(y_min+K)
           <=(3/2)(1+1/40)*y_min < (31/20)*y_min,
since y_min>T/5. This is impossible for distinct levels of the grid. Nor can one cluster pay two slots at the same level, since no new mark lies in it. Hence each far nonreset B cluster pays at most ONE geometric-level slot globally. A high reset cluster can pay at most L0 slots, and the endpoint leaves at most L0 slots pending. The number of reset clusters is <=N+1. Writing B_S^nr for the count of all far nonreset B with s>S, we obtain the finite bound
    5*m_T <= B_S^nr+(N+2)*L0.                           (4)
For each nonreset match the high precursor need not itself decrease; the actual downcross may occur later within its low run. This is why the counted B population differs from earlier actual-decrease-only level matches.

There are also NEW simultaneous scale restrictions on each matched high precursor. Its post X1=2s*h+6I+3 (h positive integer), with X1<y+K and X1>(2/3)X0>=(2/3)y. Thus
    S<s<(y+K-3)/2 < p,
    s*h>y/3-9/2 > p/15-9/2.                            (5)
The last strict inequality uses y>p/5. In particular all matched precursors of marks p<=U have label<U. If the matched precursor lies in S<s<=R, then h>(T/15-9/2)/R. This is a scale restriction on the post adjusted-deficit multiplier of the high B even when the actual payment is made by a following much smaller label. It does not imply that this precursor itself is an ordinary-decreasing event.

Let B_(S,R]^nr(T,U) denote the count of far nonreset B with S<s<=R, s<U, and s*h>T/15-9/2 (omit s<U when no upper mark bound is imposed). Mark only T<=p<=U,p>R. Since at most B_R high far B with s>R exist in the block, (4)-(5) give
    B_(S,R]^nr(T,U) >=5*m_[T,U] -(N+2)*L0-B_R.           (6)
This is a cumulative band count bound without any trajectory independence.

## 4. Completed slabs and weighted high-B supply

The same cluster exclusion works for arbitrary real levels in (3), not just grid points. Fix 1<beta<=31/20. Use geometric levels starting at (T/5)*phase, 1<=phase<beta, through19C/10. Let L be the number of levels. For each marked p select all FULL slabs (a,b] between consecutive grid levels lying inside (3). Their total width is at least
    c_beta*p, c_beta=19/(10*beta)-beta/5>0.
Indeed the first selected level is <=beta*p/5, the last >=(19p/10)/beta, and all intervening slabs are full. First-downcross allocation of every real level in these slabs uses only the allowed cluster types. Pending portions of slabs at a given time are disjoint; at a fixed slab, another mark cannot add it until the earlier mark has recovered every level in it (the new pre x<=the lower endpoint). No exceptional cluster contains a new mark because its high event is a reset or nonreset B and all following labels<=S.

Call a mark bad if a selected slab is incomplete at the block endpoint, or any positive portion is paid by a high reset cluster or a far B cluster with precursor label>R. Each such cluster can touch at most one marked allocation per grid slab, because there is no new mark within it. There are <=N+1+B_R exceptional clusters; pending at the endpoint affects at most L marks. Therefore
    #bad <= (N+B_R+2)*L.                               (7)
Every good mark has full selected width paid by far nonreset B clusters with S<s<=R, which satisfy (5) for any assigned level. For any chosen subset of good marks, let W_good be their summed labels, and J be the number of distinct band clusters paying any portion of their slabs. A cluster of precursor s contributes at most (s-1)+L_low to total allocated length, where L_low<=K is its actual subsequent low-run gain. This follows from the per-event capacity by actual ordinary drops and the bound drop<=gain; no double payment across marks because pending intervals are disjoint. Thus
    sum_{paying band clusters} [(s-1)+L_low]
        >= c_beta*W_good,
    J >= c_beta*W_good/(R-1+K).                         (8)
The stronger first inequality can use the actual positive drop of the high B in place of s-1. For a marked subset with p>=T, every paying band cluster obeys s*h>T/15-9/2; if also p<=U then s<U. This weighted bound has no additive exceptional weight loss for good marks; the excluded mark count is explicit. The denominator R-1+K is a supply bound for the combined cluster, not for its precursor alone.

## 5. Macroscopic interpretation

In a crossed window [X,lambda X], let R be the balanced or near-X cutoff, or any fixed-power cutoff R~rho log X from section1. For polynomial mark threshold T=X^a with fixed 0<a<rho, choose S largest odd prime with 2P_S<=T/200 (and S>=47 eventually). By PNT and the next-prime bound, S~log T=a log X; for large X S<R. In particular this raises the previous rounded-level lower cutoff of order log log X to order log X for marks at polynomial scale. Equations (6)-(8) apply at this S. Under N,B_R=o(sqrt X), the exception term in (6) is o(sqrt X log X); hence if a polynomial-scale mark subset has m_[T,U]>>sqrt X log X, it needs at least (5-o(1))*m_[T,U] distinct far nonreset B occurrences in S<s<=R. Every such matched occurrence has multiplier h>(X^a/15-9/2)/R, of order at least X^a/log X. This is stronger in scale than the earlier S0~log log X five-slot bound, but only for the indicated large marks; no assertion that the total mark count lower bound guarantees many polynomial-scale marks.

For a stronger good-weight budget choose a fixed 0<b<a and S largest prime with 2P_S<=X^b. Then S~b log X, K<=X^b=o(T), condition (2) holds, and beta=1+1/log X gives L=O(log^2 X), c_beta=1.7-o(1). In the sparse branch, if m_T>>sqrt X log^2 X, all but o(m_T) marks are good by (7). In particular their good weight is >=(1-o(1))*T*m_T. Equation (8) forces
    J >= (1.7-o(1))*W_good/(R-1+K),
and hence J=Omega(X^(a-b)*m_T) under the above mark-count condition. This may require many more than five high B occurrences per mark. This is a count for distinct clusters and high precursor events, not distinct prime values. It holds without assuming good weight is a relative approximation to the full W_T. Neither the existence of many polynomial-scale A1 nor either sparsity hypothesis is forced by finite twins. No contradiction has yet been established.

## 6. Diagnostics and preservation

Refined Fourier certificate [485e6db](https://github.com/tara-sooo/A166944-Lean/blob/485e6db9152cd048ccfd248dd1b710569d3acfbd/research/min_direct_three_class_refined_certificate.mjs), blob 575cdd7e14336084f77a75ce13045e082c4594d0. Exact remote readback. Actual ECMAScript executed, 435880 exact cells, minimum certified saving .005810681080419112, gap .000005067736363636364. Run node research/min_direct_three_class_refined_certificate.mjs. No fresh finite Fourier-period enumeration: the new result uses the same finite three-class inequality already audited in3bea1a4, with new exact constant and entropy certificate. Earlier exploratory nonuniform-subset/four-class choices did not supply a stronger uniform certificate and are not used.

Cluster audit [f7faf20](https://github.com/tara-sooo/A166944-Lean/blob/f7faf20a048150b859cb11b0c7c9344a00ca27c5/research/min_direct_cluster_recovery_audit.mjs), blob c1cc1c207c04e1d15d7abe8a65eec8d13040d23a. Exact remote readback. Run node research/min_direct_cluster_recovery_audit.mjs 30000. Actual ECMAScript: 14998 odd roots through30000,243497 actual events;22796 finite block-cutoff controls,7651 marked blocks,39479 slots,31 nonreset cluster matches incl2 paid by following low run,20 reset-paid and39428 pending slots;8246 clusters,31 point-scale inequalities,31828 slabs,71 positive slab-payment intersections,4 good mark incidences of summed weight30748,7647 bad. Diagnostics use actual maximum low-run gain K (often zero), rather than huge K_S, and small S3/5/7/11 plus S47 control; when S<47 count other nonreset far non-A1 as exceptions, not a p>=47 classification. For small horizons check the later-near label inequality directly on the block (no rejected marked blocks in this run); theorem uses A>=6250001. Exact rational geometric levels and widths, integer allocation. Diagnostic reset-count bound uses actual high reset count (or all resets>=7), independent of inferred canonical visit count; analytic normalization gives N+1.

Reconstructed prior 12979-digit CRT root word10039/6709/4513/7,15140 literal BigInt GCD ticks,13028 CRT checks. At S7/11,R7000,T10000, actual K6, phase chosen to include y9027: final label7 pays that level and matches to far B precursor4513, not to7. Five slots, two matched, three pending; incomplete mark not good. Reconstructed prior9962-digit root word7687/5233/3541/2389/1621/1093/733/7369,22195 literal ticks,20600 CRT checks. At S3/5/7/47,R7500,T7000,K0, first mark7687 all five slots paid by distinct high nonreset B, four full slabs of total width10355.2535625 completed by six band clusters, good mark in each control. All assertions passed. These are previously constructed roots reconstructed and retested, not new roots or macroscopic infinite-ray observations. No Lean kernel verification or historical novelty claim. Main/sibling branches unchanged.

Next investigate whether the high-multiplier band supply (6)-(8) can be upper-bounded using simultaneous H/time congruences, or show sufficiently many large marks must occur. Further improvement of Fourier exponent alone does not resolve either missing implication.
