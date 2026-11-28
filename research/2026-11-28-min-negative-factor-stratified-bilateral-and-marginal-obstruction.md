# Factor-stratified bilateral sieve, phase gains, and a continuous multistage marginal obstruction

2026-11-28 JST. Issue #10. Round-2 Astra research snapshot b7a38fca82333a66b74aaaab9c82d96918a57dfc. This checkpoint independently reopens its central analytic inputs, improves the bilateral lower at fixed exponents by allowing any source factor as the short unrestricted prime in unfiltered rows, improves the phase-selected supply, strengthens the quantitative near-square twin criterion, and constructs a countermodel for ALL one-sided roughness tail bounds at an ideal level 5/8, including arbitrary source factor-anatomy subdivisions and repeated bilateral switches. This is more than the previous obstruction for a single intermediate threshold. The actual .4 stationary lower, M85, long-distance canonical survival, and twin infinitude remain open. Analytic statements below are paper deductions; no new Lean build or independent human specialist review.

Notation L=log R, Pi_R=2 C2 R/L², C2=prod_(p>2)(1-1/(p-1)^2). Odd n=A-1 in [R-1,2R-1], m=n+2. For fixed c, let C_c indicate least prime factor >=4R^c. U_a indicates least prime factor >=R^a. Define M(t)=omega(1/t)/t, the leading bare mass coefficient of t-rough integers in units R/L. Fixed constants at cutoffs and slab endpoint shifts do not alter the limiting coefficients. Source product rows enumerate ordered prime factors; large squares and equal-exponent boundaries cost o(Pi_R) after the standard fixed-mesh enclosure and limiting argument.

## 1. Independent source/application review of Astra round 2

Reopened the exact saved notes under research/astra-max at b7a38fca82333a66b74aaaab9c82d96918a57dfc, in particular round2-rough-pairs-past-one-third.md, round2-cofactor-phase-high-and-twin-criterion.md and the bilateral coefficient script. Checked original sources:
- J. Wu, Acta Arith. 114 (2004), https://www.impan.pl/shop/publication/transaction/download/product/82961, printed pp220-223, PDF images pp5-8 (zero indexed). Lemma2.2 has z<=sqrt Q; use min(requested z,R^(d/2.1)) for plateau upper estimates, not the invalid larger z directly. Lemma2.5 table and preceding SW/rough-support hypotheses for the short coefficient; Lemmas2.7 and 2.9 give the unrestricted prime and ALL fixed ordered-prime-product row levels 4/7-eps, respectively (not just small short-factor cases). Lemma2.10 gives bare Buchstab mass and upper .561522 for omega(u) at u>=3.5. No short prime restricted to a single mod4 class is asserted SW. Ordinary lower weights must be supported on the correct sifting set and controlled by well-factorability, not upper-only programmable weights.
- Pascadi arXiv:2505.00653v2, https://arxiv.org/html/2505.00653v2#S4, Definition4.3, Proposition4.4, inequalities (4.15), Proposition4.5 proof, §5.1 Definition5.1 and (5.3), Proposition5.2, and §5.2 Lemma5.6 proof. Confirmed arbitrary 1-bounded coefficients of the three modulus factors, short source sequence SW and rough, long coefficient only bounded. Unit third modulus is the dyadic block parameter 1/2 in the paper's strict-lower dyadic convention; the proof of Lemma5.6 explicitly uses d3=1, and Proposition4.5 decomposes factors supported down to 1. This resolves the former review item at the level of checking the original application, not reproving dispersion. For the upper weights only, Prop5.2 gives factorization at exponent 3/5-50delta for x^(2delta)<=N<=x^(1/3+delta). Choose delta=10^-6 and reserve .00005 margin for box and small-component expansion, using .5999. This is a use of Prop4.4+Prop5.2 on a source product row, not applying a final theorem about prime counts directly to products.
- Lichtman arXiv:2109.02851v2, https://arxiv.org/pdf/2109.02851v2, §5, printed pp22-23, PDF images pp21-22, (5.14)-(5.17), Lemma5.3. Ordinary Iwaniec weight construction is a finite sum of outer prime-factor boxes convolved with a small-prime component of level D^epsilon_s, signed bounded coefficients. With fixed boxing parameters and epsilon_s sufficiently small relative to the strict Prop5.2 margins, append the small component to a modulus group and use a fixed grouping for all entries of a box. Same-bin permutations, where relevant, have fixed combinatorial normalization (or boxes of close factor size excluded in the construction); overincluded repeated polynomial primes cost O(R^(1-xi+o(1))) by the square-modulus reciprocal bound. Restriction to odd sifting primes is applied factor by factor. No transfer of upper support to lower weights. The alternative twist squarefree projection in Astra's isolated-semiprime note is consistent with the original well-factorability quantifier (each split). The two-factor fixed-split mask from the previous project note is sufficient for the two-factor bounds here.

On full unrestricted product rows, Lemma2.9 is used with the product lower-endpoint parameter and dyadic intervals, after the short-relative-box localization detailed in Astra's bilateral note. Signed dyadic endpoint expansions have O(L^k) terms, retain a fixed level margin, and truncation costs a power-saving by trivial tuple and divisor bounds. For upper product row boxes, also apply Prop4.4 after dyadic decomposition (or separate interval support directly). Short factor chosen freely only for UNFILTERED rows. For fixed mod4 cofactor conditions choose the least prime as the short unrestricted coefficient and place the cofactor constraint in the long coefficient. Bare reference mass then includes its 1/2 phase weight by fixed-class PNT before shift-sifting. The local main terms use g(p)=1/(p-1) for odd primes, and V(z)~2 C2 exp(-gamma)/log z; coprime-reference corrections from polynomial source primes are negligible with bounded factor count. All cells have fixed positive width, endpoints and level margins before R->infinity; take box approximation and sieve errors arbitrarily small after fixing the finite partition.

Independent coefficient reconstruction on a finer fixed grid (not the original Python script) gives old .334 coefficient >.0064250453, using its ORIGINAL .2062, d_U=.5999 and fallback d0 for all negative rows above 1/3. This agrees in sign with the original .005684586 rational certificate. No flaw found in the inspected central input/application chain. Did not independently reprove the cited published distribution results, audit every Astra note, or rerun Lean. The narrow A1 prime-only numerator remains open. Related literature search on Chen-type rough pairs returned the previously withdrawn Ratliff v3 .3844 and the classical Chen roughness variants; the withdrawn result is not used. No claim of literature priority or exhaustive coverage.

## 2. General factor-stratified bilateral lower

Fix a=.206, d0=4/7-.0001, dU=.5999. Define
    d2(t)=min((2+3t)/5,1-t)-.0001.
For unfiltered rows with a prime factor at exponent t, choose it as N in Prop4.4, other factors as M. If d2(t) improves d0 or dU, take Q1 exponent t-rho and Q2 exponent d2(t)-t+rho, Q3 unit, rho>0 small. The constraints 2t+Q2_exponent<1 and 2t+5Q2_exponent<2 are satisfied with fixed slack. The short factor remains a prime with unrestricted residues. In a rectangular exponent cell [l,r], valid lower bound on the level is min((2+3l)/5,1-r)-.0001. Discard factors of exponent >.5 as candidates for improvement (their cap is <.5 anyway). Upper level .5999 available for every rejected row with least prime t<=1/3 by Prop5.2, and for t in [1/3,.4] by the ordinary two-factor formula. Uniform Wu d0 available for all unfiltered rows, including prime and balanced semiprime rows.

Write B(d,a)=2 log(d/a-1)/d (valid 2<d/a<4, increasing in d in this regime). In normalized units Pi_R:
  lower sieve on a row of bare mass J at R^a: J B(d,a);
  upper on row at requested cutoff R^c (constant multiplier allowed): J 2/d,
using the smaller cutoff as in §1 when the plateau parameter is in [2.1,3). All plateau uses below meet that range.

Take .3<=c<=.3346. Exact bilateral identity
    C_c(n) C_c(m)=C_c(n) U_a(m) - (U_a(m)-C_c(m)) C_c(n).
For positive count, prime row at d0, ordered semiprimes with smaller exponent t in [c,1/2] at max(d0,d2(t)), and if c<1/3, triple rows at d0. Since c>.25, no four-prime rows in the positive term. Denote the lower coefficient
    P_c=B(d0,a)
         + integral_c^(1/2) B(max(d0,d2(t)),a) dt/[t(1-t)]
         + B(d0,a) T(c),
where T(c)=0 for c>=1/3 and otherwise
    T(c)=integral_c^(1/3) log((1-2t)/t) dt/[t(1-t)].
The latter is the ordered triple simplex mass, from integrating the second factor exponent u between t and (1-t)/2. M(c)=1+log((1-c)/c)+T(c) for c>.25.

For negative count begin with the upper 2/dU [M(a)-M(c)]. Now improve the rejected triple rows by considering ALL THREE source factors rather than only the least. With ordered exponents t<=u<=v=1-t-u, a<=t<min(c,1/3), the triple mass is dt du/(t u v). Define d*(t,u)=max(dU,d2(t),d2(u),d2(v)). A row's upper saving is 2/dU-2/d*. Therefore the new saving
    J3(a,c)= integral_a^min(c,1/3) integral_t^((1-t)/2)
                   (2/dU-2/d*(t,u)) dt du/(t u (1-t-u)).
The integrand is nonnegative. Also J2(c)=integral_(1/3)^c [2/dU-2/max(dU,d2(t))] dt/[t(1-t)] if c>1/3, 0 otherwise. Four-prime rejected rows, when present, simply use baseline upper; no improvement needed. Thus a NEW unconditional lower coefficient
    # two-sided 4R^c-rough centers / Pi_R
        >= P_c - 2/dU[M(a)-M(c)] + J3(a,c)+J2(c)-eps-o(1)
for any arbitrarily small fixed sieve approximation eps. It is a count of distinct centers, not divisor incidences. Arithmetic-to-clock as in original note: 6|A, no eligible label before first H=floor(R^c), G=0, each birth distinct.

Exact BigInt outward bounds, using M(a)<=.561522/a, and monotone lower Riemann sums for the triple mass, give (net pre-error lower, then conservative usable coefficient):
    c         net lower >       usable >=
    .3000     .9923140394        .98
    .3125     .6013402621        .59
    .3200     .3851649608        .375
    .3240     .2754134199        .27
    .3340     .0177948381        .015
    .3345     .0054488683        .004
    .3346     .0029808339        .002
Usable coefficients hold for every sufficiently large slab by taking fixed approximation errors and then R large. In particular .324 has 27 times Astra's stated .01 coefficient and .334 has 3 times its .005 coefficient. .3346 is the new fixed exponent (not merely <.3346); both neighbors are P1 or P2. The stronger seed constants at .3-.324 are useful even though those exponents were already within the frontier. This improvement is row stratification, not a new distribution theorem or evidence at .4.

## 3. Apply the refinement to actual HIGH supply

Use Astra's cofactor phase indicator C_s(ell,b) on each neighbor, accepting all 4R^b-rough integers and those with least factor p>=4R^ell, p<4R^b, cofactor u=3 mod4 (plus) or 1 mod4 (minus). Here ell>.25, b in [.35,.4]. Unsifted mass J=(M(ell)+M(b))/2. Exact identity C_- C_+= C_- U_a - (U_a-C_+)C_-. In negative rows drop opposite phase and upper-sieve at 4R^ell; the plateau parameter after reducing cutoff is in [2.1,3). In positive rows, prime and all semiprime t>=b unfiltered; half mass semiprime rows ell<=t<b and triple rows ell<=t<=1/3 carry the phase. Use d_phase(t)=max(d2(t),d_Wu(t)-.0001), where d_Wu is Wu Lemma2.5's piecewise table, with least prime as N, cofactor AP in M. Over a cell use the minimum across endpoints AND any table breakpoints. For phase-restricted rows do NOT use the unrestricted-product Wu 2.9. Lower coefficient:
    P_phase=B(d0,a)+int_b^.5 B(max(d0,d2(t)),a) dt/[t(1-t)]
       + (1/2)int_ell^b B(d_phase(t),a) dt/[t(1-t)]
       + (1/2)int_ell^(1/3) B(d_phase(t),a) log((1-2t)/t)dt/[t(1-t)].
Negative upper baseline is 2/dU[M(a)-J]. All rejected triple rows of least exponent t<ell are unfiltered, so gain J3(a,ell) as in §2. For t>=ell, phase-rejected rows keep least prime as N (do not swap in a phase-constrained cofactor prime). For negative semiprime t∈[1/3,b], half rejected, gain J2(b)/2. Other negative rows remain at baseline. Hence
    lower >= P_phase - 2/dU[M(a)-J] + J3(a,ell)+J2(b)/2 - eps-o(1).
Certified pre-error lower and conservative usable combined coefficient after removing intra-neighbor near ties:
    ell       b       net lower >    usable >=
    .280      .400    .0792806731    .070
    .283      .400    .0224664245    .020
    .284      .400    .0038405264    .002
    .320      .350    .0064156858    .004
    .300      .375    .0134568091    .010
Astra original .28,.4 was .010; new .070 is sevenfold. The .284 exponent is an alternative if stronger minimum label matters, at smaller density. The deletion of ties is O(eta) Pi_R by original unrestricted row upper in a small fixed diagonal strip, then eta chosen small relative to coefficient. Every retained center either reaches H=floor(R^b) with G=0 or has actual HIGH first winner p>=4R^ell, p<=2H/3+O(1) (same clock formulas as Astra). The actual occupied HIGH positions have bounded reverse multiplicity and supply the existing adaptive L²-time continuation theorem. This improves seed density and range, NOT the subsequent polynomial-height lower. In particular the two branches at .4 have not been separated; neither .070 nor .002 is claimed as an actual first-.4 lower.

## 4. Why arbitrary repeated bilateral tail exchanges cannot by themselves reach .4

This is a new continuous countermodel for a precise information class; it is NOT an arithmetic sequence of shifted integers, NOT a counterexample to the conjecture, and does not satisfy arbitrary additional joint congruence or phase restrictions.

Let mu be the bare factor-anatomy measure: atom 1 for primes (least exponent 1), for ordered k>=2 factors with sum exponents1 the density d t1 ... d t_(k-1)/(t1 ... tk), all ti>0. This is locally finite on least exponent >=z>0. Its tail mass is M(z), by ordered prime-product PNT/Buchstab (for fixed z only finitely many k). Consider arbitrary factor-box restrictions in one row and a roughness-tail bound in the other. Even suppose every such row has the IDEAL common linear sieve level d=5/8, so bounds in units Pi_R are its bare mass times
    L_d(z)=exp(-gamma) f(d/z)/z,
    U_d(z)=exp(-gamma) F(d/z)/z,
with L=0 for z>=d/2 and upper 2/d for z>=d/3 (by monotone cutoff reduction if necessary). For z<d/3, U>=2/d, since sF(s) is nondecreasing. In [d/4,d/2], L=2/d log(d/z-1). Standard linear sieve on ordinary integers (g(p)=1/p, trivial remainder at level R^d) proves L_d(z)<=M(z)<=U_d(z) for every fixed z>0; no shifted-pair result is used here.

Take c=.365, m=M(c)=1+log((1-c)/c). There is b0∈(.175,.2) with M(b0)=2m: M is continuous strictly decreasing below1/2, and the certificate bounds M(.175)>=M3(.175)>3.1544 > 2m (2m<3.107456), M(.2)<2.807611 <2m. Let C be anatomy with least exponent>=c, E with b0<=least<c, F with least<b0. Then mu(C)=mu(E)=m. Define a symmetric nonnegative joint measure
    dnu(x,y)=w(x,y) dmu(x)dmu(y),
    w=0 on CxC and ExE, w=2 on CxE and ExC,
    w=1 if either x or y in F.
This is locally finite at every positive pair of thresholds. Each row in F has ordinary tail M(z). Each row in C or E has tail M(z) when z<b0 because the total mass in C union E is preserved. For z>=b0, a C row has tail 2(M(z)-m) for z<c, and 0 at z>=c. An E row has tail 2m for z<=c, and 2M(z) above c. All these tails <=2m<2/d=3.2 <=U_d(z). E rows satisfy the lower because L_d decreases on [b0,d/2] and L_d(b0)<=M(b0)=2m; at z>d/2 it is zero. C rows satisfy lower provided
    2(M(z)-m) >= 2/d log(d/z-1),  b0<=z<=d/2.
This holds on the wider certified interval [.175,.3125]. Use M(z)>=M3(z)=1+log((1-z)/z)+T(z), including only P1/P2/P3. Both M3 and the right side decrease there. For each of 1375 cells width .0001, use lower M3 at right endpoint and upper L at left; right-endpoint quadrature for T. Exact rational bounds give minimum margin >.0350387. Thus EVERY row satisfies the entire one-sided roughness-tail family, for arbitrary anatomy restrictions by integration, in either direction. All exact identities from partitions of this measure (finite sums, subtraction, switching repeatedly, weighted combinations) hold. Nonetheless nu(CxC)=0, and hence the target .4 tail pair mass is ZERO.

Consequence: no deduction using solely these one-sided tail inequalities and exact bilateral counting identities, even with ideal level5/8 on every row, can force a positive joint lower at .365 or .4. This extends Astra's single-threshold ceiling to arbitrary numbers of switches and all factor-anatomy row partitions within this information class. It is not an obstruction to actual arithmetic, additional factor-sensitive bounds in the TARGET variable, mixed congruence statistics, phase selection, or dynamical arguments. Numerically exploratory symmetric finite linear programs with least-exponent bins (not used as proof) also showed no gain at .335-.4 using the uniform baseline row levels; the explicit continuous construction supersedes relying on numerical LP feasibility. No claim of the exact optimal threshold for the full envelope class.

## 5. A real two-stage correction that would go beyond the envelope

For a< b=.4 set E_a=U_a-C_b, on either integer. The exact identity
    C_b(n)C_b(m)=C_b(n)U_a(m)-E_a(m)U_a(n)+E_a(m)E_a(n)
does not require symmetry of actual shifted pairs. The last term is a genuinely simultaneous rejected-rejected count. This is one way to introduce information that the continuous model does not enforce (indeed it has ExE=0 at its chosen b0 and c).

At a=.206, apply §2's positive P_b (no triples), and upper sieve on E_a(m)U_a(n) at cutoff R^a. Retain all row level improvements of J3,J2 but cap the selected exponent by 3a-.0001=.6179. Hence the upper for U_a is still on the plateau in every row. Certified difference (upper minus lower) <1.545850 Pi_R (pre-error). Thus a new explicit sufficient OPEN target for stationary M85 is
    # {both least factors in [R^.206,4R^.4)} >= 1.56 Pi_R
on infinitely many growing slabs. This count must be for the actual adjacent pair; no independence is asserted. At a=.16 a second version uses uniform dU on all rejected rows (least in [.16,1/3] Prop5.2, [1/3,.4] two-factor) and the full upper coefficient
    2/dU [1+int_3^(dU/a) log(s-2)/(s-1) ds]
(3<dU/a<4, the integrand is increasing, right-endpoint upper sum). Positive P_b uses d0/max(d0,d2) as above. Gap <3.014614 Pi_R. A sufficient alternative target is at least 3.03 Pi_R actual pairs with both least factors in [R^.16,4R^.4). Both target counts unproved. This correction is a new concrete lower target, not an assumption that one may count the rejected populations independently. The countermodel shows why further switching based only on the same tail data cannot guarantee it. Smaller-factor joint CRT sieve or new shifted-product correlation might supply a subset; no positive target-scale correction has yet been derived. No claim that these constants are optimal.

## 6. Stronger fixed-power terminal capacity and direct twin criteria

Astra's terminal upper used Wu Lemma2.5 with exponent 1-t on the near-balanced semiprime rows, where t is the smaller prime exponent >=theta>=.4. But these rows are UNFILTERED: Wu Lemma2.9 permits level 4/7-eps for all ordered prime product rows, even t>.4. No short-coefficient phase restriction here. Keep d0=4/7-.0001. For canonical first-H, H=floor(R^theta), theta in [.4,.5), G<=beta H with fixed beta<8/13, inherited mod2310 block bound forces both endpoint neighbors rough to a fixed positive multiple of H. Non-twin means at least one neighbor is semiprime; each orientation's row with smaller exponent t in [theta-o(1),.5+o(1)] is upper-sifted at e.g. R^.25 (plateau s=d0/.25 in (2,3)). Sum across semiprime rows and both orientations:
    # non-twin distinct endpoints <= (K_new(theta)+o(1))Pi_R,
    K_new(theta)=4/d0 * log((1-theta)/theta).
This is smaller than Astra's integral 4 int dt/[t(1-t)^2] for theta>.4. It inherits the mod2310 finite potential certificate, not newly kernel-verified.

Combine the strengthened seeds in §2 with this capacity. For any one of the following routes, if at least 2/3 of a seed family of the indicated size gives distinct actual target first-height endpoints with total gain <=.6H on infinitely many unbounded slabs, then twins are infinite:
    seed exponent c   seed coeff   target theta   certified non-twin coeff <
    .300              .98          .480           .560398
    .324              .27          .494           .168038
    .334              .015         .4997          .008402
The seed sizes here are LOWER bounds; one may select a subfamily of the required size. These improved sufficient conditions do not provide the transport lower. The .324 route is a concrete new alternative with target .494 rather than .4999, because the lower seed density has improved dramatically. The earlier short-record, signed-cost, and HIGH adaptive continuations remain available; none bridges these polynomial distances yet.

## 7. Executable certificate and scope

research/lean/negative_min_stratified_bilateral_and_envelope_audit.mjs @6d2d52f5c2d0c2f7abd996d0bca2eb4f6d5046e2 blob a92f252b53df98b67359be301c323764996bf8b2, executed in ECMAScript; exact pinned and active branch readback verified. All final assertions passed. Exact integer exponent grid units 1/2100000, log and coefficient fixed-point scale 10^25, 64-term positive atanh log expansion with rational geometric tail; all certificate comparisons BigInt. Fixed cell sizes <=.0001 for semiprime integrals, triple mass and countermodel; <=.0005 for two-dimensional upper savings. For each triple rectangle the ordered constraints t_hi<=u_lo and u_hi<=1-t_hi-u_hi guarantee containment; lower cap for each of t,u,v, upper product t_hi u_hi v_hi, positive rectangle contribution rounded down. Static .3346 uses 20485 positive saving rectangles; phase .284,.4 uses 14289; .324 uses 20233. 10855 distinct cached rational log arguments. Original .334 coefficient independently reconstructed >.0064250453. Countermodel all 1375 intervals certified with margin >.0350387. Exact comparisons for all three terminal capacity routes. First attempted final combined certificate failed the overly tight .206 correction target assertion 1.545 (actual upper 1.5458498187 truncated); widened sufficient margin to 1.56 and reran, all assertions passed. An earlier exploratory phase cell min used endpoints only; final code includes all Wu breakpoints, especially 2/7. Printed decimals truncate toward zero; explicit strict comparison margins, not unqualified rounding, are used in the text. No finite trajectory simulation was added in this checkpoint; the exact existing birth/HIGH arithmetic bridge is reused. These certificates check the numeric inequalities, not the proofs of dispersion or the asymptotics themselves.

Source files unchanged besides new note and certificate; no Lean core/main/sibling edits. The Astra round2 stored verification output was inspected, not rerun. Current research status: conditional on paper arguments as above, fixed stationary exponent .3346, significantly stronger seed and .4 phase coefficients; M85 unresolved, target4.85 unmet. Suggested next research: establish a genuine joint rejected-pair correction or different arithmetic correlation beyond the complete marginal-envelope family; use the enlarged .324 or phase-selected seed populations in actual min-plus/ancestor transport. Merely refining a single intermediate cutoff or adding more ordinary one-sided tails will not force .4 within the demonstrated information class.
