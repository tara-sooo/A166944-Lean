# Weighted crossing mass, inner smoothing, and a three-scale window alternative

Continuation of [daba226](https://github.com/tara-sooo/A166944-Lean/blob/daba22699bcd9379435764fd65b67f7660fa66ab/research/2026-11-26-min-direct-growing-order-sieved-recovery.md). Two changes: use direct pinned-lattice capacity for small actual crossing jumps instead of the much larger smoothing boundary charge; and use INNER smoothing on reset-free last-exit corridors to transfer the large A1 tail to the ACTUAL B crossing mass, rather than to the coarse count times C or even ell. The resulting weighted alternative does not assume canonical-visit or B sparsity. Under the earlier sparse hypotheses it strengthens the count/size tradeoff and low-record supply. Paper deductions and finite exact audits; no Lean kernel verification or external novelty claim.

## 1. Normalized mass and two-sided interval smoothing

Retain the earlier sieved hybrid barrier family, odd primorial P_R=P, r=pi_o(R), balanced P<=sqrt X, ell=ceil(P^(4/11)), 3<=S<R<V<=S^2 with S->infinity, S=o(R). For the main asymptotic use S=floor(R/loglog R), V=S^2. In even horizon coordinates J=2j the base hybrid indicator pins J=0 mod every odd prime<=S and uses ordinary H-barriers at the remaining primes<=R. Its density is alpha=P_S^(-1)*beta, beta=prod_{S<f<=R, f odd prime}(f-1)/(2f). Further exclude J=+/-1 at all primes R<f<=V; Q=prod_{R<f<=V}(1-2/f)>=1/4-o(1). Let f_sv be the surviving indicator divided by alpha, so mean Q. The earlier growing-order theorem supplies
    sum_I |(f_sv)_ell-Q|^2=O(X exp(-.001r)),
    sum_I f_sv=Q*|I|+O(X exp(-.01r))
for any translated integer interval I of length O(X). Here and below intervals are half-open, in j=H/2 coordinates unless stated otherwise.

For any such integer interval J or disjoint union define its absolute normalized mass
    M(J)=(2/Q)*sum_{j in J} f_sv(j).
It counts surviving cuts with a common weight kappa=2/(alpha Q) each. For a finite event block crossing [X,lambda X], fixed lambda>1, all event jump intervals in j partition I=[H_start/2,H_end/2), and
    M(I)=G+O(X exp(-.01r)), G=H_end-H_start.
The mass of a physical event is the mass of its own jump interval, not an independent sample at its pre-horizon. Mass is additive on disjoint intervals.

Let J_1,...,J_m be ANY pairwise disjoint integer intervals in I, total absolute length G_U=2 sum |J_i|. Expanding each by ell-1 leftward gives the prior upper mass argument (nonnegative moving-average contributions), irrespective of overlaps among expanded intervals. For the LOWER mass use only start positions j such that [j,j+ell) is wholly inside some J_i. There are sum max(0,|J_i|-ell+1) such positions, at least G_U/2-(ell-1)m. A point of J_i contributes to at most ell such windows with coefficient 1/ell, so the sum of moving averages over the inner starts is at most the unsmoothed mass sum on the union. The inner starts are disjoint. Cauchy-Schwarz on I or its ell-left expansion bounds the total absolute moving-average error by O(X exp(-.0005r)). Thus
    G_U-2(ell-1)m-E_X <= M(union J_i)
                          <= G_U+2(ell-1)m+E_X,             (1)
where E_X=O_lambda(X exp(-.0005r)), uniform over all such families (and can be taken nonnegative). The lower bound remains valid if some intervals have length<ell; there is no assertion that those intervals alone contain cuts. This two-sided form is the new tool. Only the preceding local L2 theorem is used, not the full huge sieve period.

## 2. Exact small-crossing capacity and mixed upper bound

Every surviving cut is at an even multiple of P_S, i.e. j=0 mod P_S. An event of label p with gain g=p-1 has interval length g/2 in j. Hence the number of surviving cuts it crosses is <=ceil(g/(2P_S)), with equality possible in the lattice count but not necessarily for the full sieve. Its normalized mass satisfies the exact upper bound
    M(event) <= b(p):=kappa*ceil((p-1)/(2P_S)).              (2)
No endpoint +1 is needed beyond the ceiling: the interval is half-open on integer coordinates. This is especially useful when p-1<=2P_S, in which case a crossing event covers exactly one cut and has mass kappa.

For ANY family of distinct actual events with label p, select individually either (2) or the contribution g+2(ell-1) from the smoothed upper bound in (1), using the smaller. Sum the direct bounds on their subfamily, and apply (1) just once to the disjoint remaining event intervals. Therefore
    sum M(event) <= sum c(p)+E_X,
    c(p)=min(b(p), p-1+2(ell-1)).                          (3)
This is a mixed upper bound on an arbitrary family; c(p) by itself is NOT a pointwise upper bound without the additive E_X when the smoothed option is chosen. The error is independent of the number of events. In particular
    sum M(event) <= sum (p-1)+sum a(p)+E_X,
    a(p)=max(0,min(2(ell-1), b(p)-(p-1)))                  (4)
since c(p)<=g+a(p). We may also use a(p)<=min(2ell,b(p)). This separates actual small crossing capacity from the usual Fourier expansion cost.

Put D=2P_S+1. At the main cutoff S=floor(R/loglog R), V=S^2,
    V<D<ell, log D=(1+o(1))*R/loglog R,
    log kappa=log P_S+(log2+o(1))*r+O(1)
              =(1+o(1))*R/loglog R.                       (5)
Here r~R/log R, R~(log X)/2, ell=X^(2/11+o(1)). The last asymptotic for ell follows from maximality of the balanced primorial and the next prime of size O(R). Thus kappa=X^o(1), D=X^o(1), with D growing faster than every fixed power of R but far smaller than ell. The bound (4) charges at most kappa per A1 with p<=D, rather than 2ell. This use of the pinned lattice is independent of the statistical rarity of actual crossing labels.

## 3. Transferring the large A1 tail by actual B mass

Use the canonical MIN definitions, x=d+3, fixed near geometry, and the previous last-exit corridors. Work on an event block crossing [X,lambda X] with label cap C=floor sqrt(lambda X+1). For ANY designated subset of A1 with p>=T0=ceil(8ell/3), split into bands [T,2T) with T=T0*2^j. The same-band cores are disjoint, at most one pending per band. The completed corridor [a,b) has pre x>.4T, post x<1.9T, net drop >=1.5T and gain g_corr>=1.5T>=4ell; no A1 occurs in it. A reset p>=5 can occur only at its end. In a corridor without such a reset, every nonreset has pre x<2.85T (including label3) and, if p>=5, label <.95T. Any crossing event in it has p>R, hence is nonreset far B, by the preceding near exclusion. This classification does not assume absence of a twin witness. In particular ALL its mass is due to such B events, even if many cuts occur inside one jump.

Let M_B be total actual mass of far NONRESET B crossers in the entire event block. Count every event once; no separate count for each corridor. Nonreset corridors form three disjoint families by band index mod3, since .4T<x_pre<2.85T for every event in them. Their total mass across all three colors is at most 3 M_B, including overlaps. Within one color apply the LOWER inequality (1) to the whole family of corridor intervals. Since g_corr>=4ell,
    g_corr-2(ell-1)>=2ell, and >=g_corr/2.
Summing the three colors, if m_nr is the number of reset-free completed tail corridors,
    2ell*m_nr <= 3 M_B + 3 E_X,
    sum_nr g_corr <= 6 M_B+6 E_X.                         (6)
In the first bound count includes corridors with or without cut crossings. Thus a reset-free recovery cannot be made exempt from the tail estimate just because some B crosses a cut. Its length forces a definite mass that must be paid by actual B. For the label weight W_nr=sum of corresponding A1 labels, p<2T<=4g_corr/3 gives W_nr<=8 M_B+8 E_X.

For completed tail corridors ending in a reset, charge each to its final decreasing reset q>=7. Within a band the charge is unique; that reset has pre x<=q+6, so only bands .4T<q+6 can charge it. Their total marked p weight is <10(q+6), by geometric summation of 2T. Only resets with q+6>.4T0 are charged. Let Z_H be ALL decreasing resets in the block with q+6>.4T0, regardless of crossings. Write W_Z=sum_{q in Z_H}(q+6), counted with event multiplicity. If m_r is the number of these reset-ended tail corridors, then
    W_r<=10 W_Z,   2ell*m_r<= (2ell/T0)*10 W_Z<= (15/2) W_Z.
There are O(log X) pending marks, of total p weight<4C. Their 2ell-count penalty is O(ell log X)=o(X). Thus for any designated tail subset,
    2ell*m_tail <= 3 M_B+(15/2) W_Z+o(X),                 (7)
    W_tail <=8 M_B+10 W_Z+O(E_X+C).                       (8)
The o(X) in (7) is uniform, from E_X and pending count; the formula (8) includes all pending weights. In particular if actual B mass and large-reset gain are o(X), then m_tail=o(X/ell) and W_tail=o(X), even if B_cross or canonical visits are not o(sqrt X). Since q+6>.4T0 implies q>ell for all sufficiently large ell, W_Z<=(1+o(1))*G_Zbig, where G_Zbig is total gain of ALL resets q>=ell in the block. Here a reset means p>=5 with adjusted post deficit zero, not every visit to the canonical state. No small-reset normalization visits are counted as large resets.

## 4. Weighted master inequality without sparsity

Assume absence of the preceding primorial-offset twin witness >S. Under finite twins this holds for all sufficiently large S. Then every crossing A1 with p>R has p>V, since the strict offset certificate and the extra sieve rule out moderate A1 crossers. Let A denote all actual FAR A1 crossers, F_A their gain, and A_mid those with V<p<T0. Write M_Z for the actual mass of all FAR reset crossers p>R (A0 or B). M_B is as above (far nonreset B crossers); these and A exhaust all far crossing events, because A0 is a reset, and low p<=R cannot cross. Let D_nr denote total ordinary deficit decrease of near decreasing resets. All near crossing events together have mass <=G-G_far+2ell*n_near+E_X=G-G_far+o(X) by (1), since the fixed near packing has n_near=O(sqrt X). The total block mass is G+o(X). By (4) applied just once to A,
    G_far <= F_A+sum_{A} a(p)+M_B+M_Z+o(X).
The existing far-only recovery allocation is valid for this designated A1 subset:
    (1+c0)F_A <= G_far+D_nr+2C, c0=9/5-o(1).
Using G_far>=G/2-O(sqrt X) and (7) for the A tail, with a(p)<=2ell, we get
    9G/28-o(X) <= sum_{A_mid} a(p)+4 M_B+M_Z
                        +D_nr/(1+c0)+(15/2) W_Z.          (9)
This is the main weighted alternative. It uses no count N of canonical visits and no sparsity assumption whatsoever. The right-hand quantities are actual mass and gain, not C times the number of B or reentry events. It is stronger in particular when many B crossers have small labels or when many canonical visits arise from small resets. Formula (9) is not a pointwise assertion about each single reset or B. The direct twin witness is the other outcome if the no-witness assumption fails.

Applying (3) to the disjoint families of B and far reset crossers gives the computable upper version
    9G/28-o(X) <= sum_{A_mid} a(p)
          +4 sum_{Bcross,nr} c(p)+sum_{far reset cross} c(p)
          +D_nr/(1+c0)+(15/2) W_Z.                        (10)
Only a constant number of uniform smoothing errors are added. The counts of far reset and near decreasing reset events need not be sparse. The near label geometry gives near p=(1-o(1))*sqrt(H) for H>=X, hence every such near reset has p>=ell for large X; D_nr<=G_Zbig. Also W_Z<=(1+o(1))*G_Zbig as noted. These reductions need only the earlier near-square bounds.

## 5. Explicit three-scale necessary alternative

For S=floor(R/loglog R), V=S^2, D=2P_S+1 and T0=ceil(8ell/3), define three quantities:
* n_small = number of ALL far crossing events with R<p<=D (A1, reset, nonreset B).
* n_middle = number of far crossing events with D<p<T0 (all classes).
* G_large = total gain of far nonreset B crossers with p>=T0, PLUS total gain of ALL resets with p>=ell in the block, whether or not crossing. The two families are disjoint.

For every small p, a(p),c(p)<=kappa. For every middle p, a(p)<=2ell and c(p)<=p-1+2ell< (14/3+o(1))*ell. For every nonreset B crosser p>=T0, c(p)<= (7/4+o(1))*(p-1). Far reset crossers with p>=T0 are in the reset-gain term of G_large and obey the same bound; the additional near and tail reset charges in (10) are also bounded by a constant times G_large. A1 p>=T0 has already been removed by the mass transfer. Thus for example, with deliberately rounded absolute constants, for all sufficiently large X,
    9G/28-o(X) <= 4 kappa*n_small +20 ell*n_middle
                                    +20 G_large.          (11)
The constants do not depend on lambda (the o(X) may). Some of the populations in (11) overlap with the reset-gain class at p in [ell,T0), but only as positive upper-bound terms; their use does not assume disjointness of all three categories. Every counted small/middle crossing has p>R. Under no witness, small crossers with p<=V are fast ordinary decreases with w<=2S (including any reset), by the previous offset certificate; their presence does not imply that all small crossers are fast. In particular all small crossing A1 have p>V.

It follows on EVERY sufficiently large crossed window with no offset twin witness that at least one of the following holds (constants depending on fixed lambda):
    n_small = Omega(X/kappa) = X^(1-o(1)) in lower exponent;
    n_middle = Omega(X/ell) = Omega(X^(9/11));
    G_large = Omega(X).
More precisely this is a disjunction of uniform lower bounds at each window, not a claim that any one holds eventually for all windows. The first two alternatives require many actual crossing events at explicitly disjoint label scales. The third requires a macroscopic gain from actual large B crossers or large resets, not merely many canonical visits. It implies Omega(sqrt X) large-B-or-reset events since p<=C. This addresses the previous nonsparse alternatives quantitatively but does not exclude them. No contradiction is implied by n_small=X^(1-o(1)): the total possible event count is O(X).

## 6. Improved sparse-branch count/size tradeoff and record consequence

Suppose N,B_cross=o(sqrt X) along crossed windows, with the old N counting all actual canonical visits and B_cross counting far B crossers (including resets). Then M_B,M_Z,W_Z,D_nr=o(X) by (3), label cap C=O(sqrt X), and the earlier seven-tick normalization injection for resets of label>=7 into visits except one pending. For far reset crossers p>R this injection applies. It also applies to all resets q+6>.4T0 and near decreasing resets. Equation (9) now gives
    9G/28-o(X) <= kappa*m_small,A1+2ell*m_middle,A1,        (12)
where m_small,A1 counts crossing far A1 V<p<=D and m_middle,A1 counts crossing far A1 D<p<T0. Thus either
    m_small,A1 = Omega(X/kappa),  V<p<=D,
or
    m_middle,A1 = Omega(X/ell),   D<p<T0.                  (13)
In the first alternative the necessary A1 count is X^(1-o(1)), not just X^(9/11). In the second the necessary X^(9/11) population has a label threshold D=exp((1+o(1))*R/loglog R), much larger than R^2. These are alternative outcomes, not simultaneous unconditional improvements. In particular if the small A1 count is o(X/kappa), the second follows with leading count coefficient 9(lambda-1)/56-o(1) as before. If the middle A1 count is o(X/ell), the first has leading coefficient 9(lambda-1)/28-o(1) times X/kappa. No upper bound on the small A1 count at this required scale has been proved.

For the selected population in whichever alternative holds, take dyadic bands starting T_min=V+1 or D+1 respectively. Under N,B_cross=o(sqrt X), the previous crossing-only corridor extraction gives n_good=(1-o(1))*m completed cut-free good corridors: its exception bound O((N+2)log X+B_cross) is o(m) for BOTH counts in (13). If J_L,J_H are distinct low record and high noncrossing far B record events in those corridors, then
    (R-3)/T_min*J_L+.95 J_H >= n_good/2,
and every low record has h=Omega(T_min/R). Therefore in the small-A1 alternative there are either Omega(X V/(kappa R)) low records with h=Omega(V/R), or Omega(X/kappa) high noncrossing B records. In the middle-A1 alternative there are either Omega(X D/(ell R)) low records with h=Omega(D/R), or Omega(X/ell) high noncrossing B records. These use the factor-three overlap, not a loss of log X in a single-band pigeonhole. For the stronger original N,B_R=o(sqrt X), the high B option can be excluded by total count, so in either branch the low-record count is Omega(X D/(ell R)): indeed X V/(kappa R) divided by X D/(ell R) tends to infinity since ell/(kappa D)=X^(2/11+o(1)). This improves the earlier X^(9/11)*V/R record lower bound by a super-polylogarithmic factor, conditional on those original sparsity assumptions. Only the middle branch gives the larger individual multiplier lower bound Omega(D/R); the small branch can have smaller individual multipliers and more occurrences.

Remaining problem: no upper supply theorem excludes either tiny-crossing density or medium-crossing density on a single fixed ray; the macroscopic large-B/reset gain alternative is also still open. The new mass transfer identifies the amount and scale needed from these nonsparse cases, instead of charging every B or canonical reentry at the worst-case sqrt X gain. The direct offset witness at unbounded S would establish twin infinitude, but is not forced by (11) alone. No new Fourier exponent; no Lean proof.

## 7. Finite diagnostics and persistence

[Weighted crossing audit 3fdafd3](https://github.com/tara-sooo/A166944-Lean/blob/3fdafd339d62e983b91abfb759e68c6dae12dd59/research/min_direct_weighted_crossing_mass_audit.mjs), blob 8a3cd4bc17f5fbe4ab2d99b6a1bc425ada1f0bfe, exact remote readback. Run node research/min_direct_weighted_crossing_mass_audit.mjs 30000. Actual ECMAScript execution in tool runtime, not a separate Node process. Six complete small CRT sieve periods up to255255 (1036140 positions), 900 arbitrary translated/disjoint union tests,11496 interval tests incl1809 shorter than smoothing length,293154 inner-window positions,138805 direct pinned-lattice capacity checks,900 mixed min-capacity checks. Integer comparison of normalized masses uses common BigInt units, and exact periodic prefixes for moving-average deviations. The original diagnostic execution timed out because it recomputed rolling arrays for every ray; the final code caches period mass/error prefixes and completed all assertions.

14998 odd canonical roots through30000,243497 actual events,0 unresolved180 cap. 5588 ray/cutoff controls,5713 tail mark incidences,5318 pending,387 reset-ended corridors,8 nonreset corridors all with actual crossing mass,16764 color lower-mass comparisons,5588 tail mass-transfer checks,387 reset weight checks. Reconstructed earlier9962-digit actual canonical witness word7687/5233/3541/2389/1621/1093/733/7369,22195 literal BigInt gcd ticks and20600 stage residue checks. Its five-label last-exit corridor with mark7687,T7000 has gain13872. At S3,R5,V7,L3 it crosses660 surviving cuts; at S5,R7,V17,L6 it crosses121; at S7,R7,V13,L6 it crosses46. These finite controls count all non-A1/nonreset crossing events in place of far nonreset B, so the small-horizon tests do not require the far-exclusion threshold or S=o(R); the asymptotic proof uses the genuine far class and stated hypotheses. They verify inner/outer smoothing mass and the exact charge inequalities, not the earlier asymptotic L2 theorem or the existence of crossed windows of arbitrary size. No new overlap depth>1 claim; use the earlier separately constructed overlap controls for that. All final checks passed. Main and sibling branches not modified.
