# Phase-selective absolute BV, a nonreset first-minus dichotomy, and separated high trajectories

2026-11-28 JST, Issue #10. Base 2eab1ed84472132895a7e21c2599d8f189b1f3ec. User renewed M85 (H=floor(R^.4), >>R/log²R distinct actual first-H sites with gain<=4H) and requested sustained multi-stage research. New paper deductions: an independent below-square-root absolute distribution estimate allowing fixed source congruence classes; its application to rule out the reset-only version of the previous isolated-minus alternative; a common elapsed-time, noncoalescing actual high-trajectory family; and a limiting parameter argument. No M85 or >5/16 unconditional static lower established. The high/rough dichotomy inherits the prior Pascadi two-factor transfer (including Q3=1 review item). The new absolute estimate itself does not depend on that transfer. No Lean run or independent specialist review.

## 1. Why the phase problem requires another input

Write L=log R, n=pv in [R+1,2R+1], p,v primes, R^.374900<=p<=R^.374950, v>p. B_R is the count of this source; M_R=4 C2 B_R/L with C2=product over odd primes ell of (1-1/(ell-1)^2). Thus M_R is comparable to R/L², with a fixed positive band width. S_k(z) counts these n with k|n-2 and P^-(n-2)>=z; S=S_1. In 2eab1ed8 the alternative to a static improvement was an isolated first minus label r, but the postheight could be 3 (reset) or r+3 (HIGH).

For n-2=r u with r odd prime and u odd, canonical A=n-1 has first minus opportunity at age (r-1)/2 if u=3 mod4, and (3r-1)/2 if u=1 mod4. These yield postheights 3 and r+3 respectively if no competitor fires earlier. Reset is equivalent to n=3r+2 mod4. A phase-restricted upper on S_r(r) is therefore needed, not an assumption that both phases are equally frequent among the sifted points.

Rechecked Pascadi arXiv:2505.00653v2, printed pp20-21 (screenshots plus text), Def4.3, Prop4.4 (4.15)-(4.17), Prop4.5 p22-23. Def4.3 demands SW for ALL moduli; a small prime coefficient restricted to one class mod4 does NOT satisfy this at modulus 4. One cannot simply quote Prop4.4 with the restricted small coefficient. The odd-modulus variant might be obtainable by auditing the dispersion proof, but was not established here. Maynard arXiv:2006.07088v1 and Oxford preprint of the same early version were located (old numbering, not the final Prop5.8/7.2 cited by Pascadi); final-version PDF retrieval failed. Yang arXiv:2608.13299v2 pp3-4 (text and p4 screenshot), (1.1),(1.2), Thm1.2, again has a free integer variable, not the needed prime-restricted coefficient. Literature search also located almost-prime shifted correlations averaged over h and Chen-type/weighted switching results; none was used as a fixed-shift lower for our source. We instead use a weaker distribution level for the phase-specific upper; the factor 1/2 in the phase restriction more than compensates for part of the lost level.

## 2. Absolute distribution for phase-restricted semiprime sources

Fix e<1/2, e>0. For i,j in {1,3}, let B_ij and A_ij(k) be the counts of the above source with p=i mod4, v=j mod4, and, in A_ij(k), n=2 mod k. Then for every fixed A>0,
    sum_{k<=R^e, k odd squarefree} | A_ij(k)-B_ij/phi(k) | <<_{e,A} R/L^A.       (1)
In particular the prior polynomial-factor-only absolute estimate at .49 can be extended to all odd squarefree moduli below any fixed exponent 1/2, with arbitrarily large log saving and source congruences. This is a deduction from classical multiplicative large sieve and Siegel-Walfisz, not a new above-square-root theorem.

Proof. Work first in a rectangular product box of prime sizes P,V with PV comparable to R, P>=R^.3749, V<=C R^.6251 and V>>R^e. Let alpha,beta be the prime indicators with the fixed respective residue classes and interval cutoffs, and A(chi),B(chi) their character sums. Character orthogonality applies to residue 2 at odd modulus k. For a primitive character of conductor f|k, the induced B-sum is exactly its primitive sum, since all v>k. The induced A-sum differs by at most one: only primes p dividing k but not f are removed, and k<P². The total nonprincipal error from replacing induced A-sums by primitive sums is bounded by
    sum_{P_min<=k<=R^e} (1/phi(k)) sum_{chi mod k}|B(chi)|
    << R^e ( V/sqrt(P_min) + sqrt(V) )
by character orthogonality and Cauchy, since the number of pairs v1=v2 mod k is O(V(V/k+1)). With P_min=R^.3749, the two exponents are at most .93765 and .81255 even at e=.5; hence this is power-saving. The principal term's removed prime contribution is O(V sum_{k<=R^e}1/phi(k))=O(V L), also negligible. The product box mass is A(1)B(1) before exclusions.

Each nonprincipal induced character is lifted from a unique primitive character of conductor f>1 (f odd). Its weights after summing k multiples of f are bounded by
    sum_{k<=R^e, f|k}1/phi(k) << L/phi(f),
using phi(fm)>=phi(f)phi(m) and sum_{m<=X}1/phi(m)<<log(2X). For f<=L^J, J a fixed large constant, SW on the prime p in the reduced class mod4 gives A(chi*)=O(P/L^C) for any C, uniformly for nonprincipal chi* modulo odd f: use CRT mod4f, PNT in log-power APs and the zero sum of a nonprincipal character over reduced classes. Interval cutoffs are differences of endpoints, so this holds even in short boxes. The trivial B-sum and summation over f give O(R/L^A) with arbitrary log saving by taking C sufficiently large relative to J,A.

For dyadic F<=f<2F with F>=L^J, standard multiplicative large sieve and Cauchy give
    sum_f (1/phi(f)) sum_{chi*}|A(chi*) B(chi*)|
    << sqrt[(F²+P)P (F²+V)V]/F
    << sqrt R [ F+sqrt(P)+sqrt(V)+sqrt(PV)/F ].
For F<=R^e the first term is O(R^(.5+e)), second and third power-saving, last O(R/L^J). Summing dyadic F and the conductor multiplicity factor L preserves arbitrary log savings for J large. This proves the box result with uniform constants, including the induced-character errors. No polynomial moduli AP asymptotic was used.

For the exact slab partition p,v into multiplicative intervals of ratio 1+L^(-K) with K fixed large. O(L^(2K+2)) boxes meet the full exponent ranges; use those wholly inside [R+1,2R+1], with the box error exponent chosen larger than 2K+A+5. Boundary products lie in O(R/L^K)-length intervals adjacent to the two slab endpoints. Unique representation (p<v and disjoint sizes) gives error in the total modulus sum at most
    sum_{n in endpoint intervals} tau(n-2) + O((R/L^K+1)L)
    << R/L^(K-1)+sqrt R,
by the divisor hyperbola method counting multiples of each d<=sqrt(2R+1). This boundary estimate uses the FIXED residue 2, not max over arbitrary residues. Take K>A+3. This proves (1). Also B_ij~B_R/4 by ordinary fixed-AP PNT, using coarse product boxes and then a fine fixed approximation. The prime counts on the two sides need not be jointly independent modulo any polynomial-sized modulus.

## 3. Phase-specific ordinary upper at lower level

Use d=.6246 from the preceding Pascadi transfer and e=.499 from (1). Let a=.300, c=.3128, b=.313. Define
    F_d(t)=log((d-t)/t)/d,
    U_e(a,c)=integral_a^c dt/[t(e-t)]
            =log(c(e-a)/(a(e-c)))/e.
Let Z_reset count source n with least factor r of n-2 in [R^a,R^c) and (n-2)/r=3 mod4 (including multiple low factors). Then for any arbitrarily small fixed error epsilon>0 and R sufficiently large,
    Z_reset/M_R <= (1/2) U_e(a,c)+epsilon.                      (2)

For each of four source classes (i,j), r is in exactly ONE reduced class mod4, determined by ij=3r+2 mod4. Sift the residual quotient of n-2 by primes below a cutoff just smaller than R^(e-t), where t=log_R r. Since e-t<t, this cutoff is below r; every n counted by the true r-rough condition survives it. Use ordinary dimension-one linear upper weights at residual level R^(e-t-small slack), with s just above1, hence s F(s)=2 exp(gamma). Main term per r is (4C2 B_ij/L)/[(r-1)(e-t)] up to arbitrarily small fixed errors (cutoff/level slack). This is the usual Mertens density g(k)=1/phi(k) for odd squarefree k. For rigor partition [a,c] into finitely many fixed narrow exponent bins; use the smaller residual level at the top of a bin and cutoff below that level. For a sufficiently fine fixed mesh the normalized upper is arbitrarily close to the integral. The moduli r*k of the remainder are odd squarefree <=R^e, and have AT MOST ONE prime factor >=R^a since 2a>e, so the aggregate error is bounded by (1) (no multiplicity loss). This also avoids the earlier Q3=1 issue for this upper. PNT in the fixed reduced class mod4 contributes 1/2 to the reciprocal prime integral; sum the four B_ij. The factor 1/2 is an upper-bound main-term computation, NOT an equidistribution assertion for the surviving rough roots.

## 4. A stronger dichotomy: roughness above 5/16 or actual HIGH minus arrivals

Use the variable-cutoff result of 2eab1ed8 (and its original two-factor transfer) with original cutoff .160, a_var(t)=(d-t)/3+.0002, correction incidence count C_R(b). It gives the following four estimates, with independently arbitrarily small fixed epsilon:
    S(R^a)/M_R >= F_d(a)-epsilon;
    S(R^c)/M_R <= S(R^b)/M_R + F_d(c)-F_d(b)+epsilon;
    C_R(b)/M_R <= S(R^b)/M_R-F_d(b)+epsilon;
    Z_reset/M_R <= U_e(a,c)/2+epsilon.
The first three use the previous lower and plateau upper (including the old review item); the fourth is the new independent estimate (2).

Consider n counted by S(R^a)-S(R^c). If n-2 has two distinct prime factors below R^b, let r be its least and q another. q>=r>=R^a, q<R^b, and a_var(log_R q)<a, so this n contributes to C_R(b) as the incidence (q,r,n). If any prime >=R^a repeats, remove it by the elementary upper O(R^(1-a)+sqrt R)=o(M_R) for n-2 divisible by a prime square in that range. The remaining points have exactly one prime factor r<R^b, r in [R^a,R^c). Delete the Z_reset roots. The number N_HIGH remaining is therefore at least
    M_R [ F_d(a)-F_d(c)-U_e(a,c)/2+2 F_d(b)-4 epsilon ]
          -2 S(R^b)-o(M_R).                                   (3)
The bound is valid even if the corrections count incidences with multiplicity; each removed multi-low root contributes at least one. We do not assume that the correction is a distinct-root count.

Exact rational log series audit gives
    .0084688577252784414303 <= F_d(a)-F_d(c)-U_e(a,c)/2+2 F_d(b)
                           <= .0084688577252784414831.
(The interval is displayed at scale 10^22, not a floating estimate.) In particular choose epsilon<=.0002 and the square error <=.0005 M_R. Then for every sufficiently large R either:
  (I) S(R^.313)>=.001 M_R. This gives density-scale stationary first-height sites at every fixed sigma<.313, including .3129>5/16.
  (II) at least .004 M_R actual canonical roots A=n-1 have r in [R^.300,R^.3128), all other factors of n-2 >=R^.313, p,v>=R^.3749, and (n-2)/r=1 mod4. Their actual FIRST winner is r, minus sign, at age (3r-1)/2, and poststate has x0=r(u-1)+2, h0=r+3.

Indeed the roots are multiples of six by odd n, and neither n nor n-2 divisible by3; other candidate factors have first opportunity >=(other-7)/2 by the canonical height bound, while r has its minus opportunity at (3r-1)/2. Fixed power separation makes r strictly first. Its postheight follows from the exact height ledger. This improves 2eab1ed8 by ruling out the possibility that the entire density-scale dynamic alternative consists only of resets. It trades the lower label exponent .310 for .300 to pay for the phase upper; no claim that the earlier .310 family has positive HIGH fraction. In (II) the high arrival is below its earlier maximum height (first prefire height about 1.5r), so it is not a new height record.

## 5. Use the new HIGH population: common time at high height, disjoint true connectors

The modular short-transfer proof of 07503a49 (research/2026-11-28-min-negative-modular-short-transfer-and-canonical-approximation.md) can now be applied to (II), despite the first fired cofactor u possibly being semiprime, rather than the prime v of the earlier HIGH population. Here both u and r u+2=n are R^a-rough; this is enough for every upper sieve below. This section is an explicit adaptation, not a new lower sieve.

Choose z=floor(c0 L) with fixed sufficiently small c0>0, and B=4 product_{3<=ell<=z prime}ell<=R^.01. The low-label trial ignores eligible primes >z, retains the actual minimum of the others. The signed clock n0=r+3-x0/2, and x0=r(u-1)+2. The trial displacement g at elapsed tick w (before firing) is fixed by r,u mod B, because the spatial and clock residues are determined. For w<=T0, g<=z T0, even. An outside eligible prime ell>z necessarily satisfies
    ell | 2(r+3)+2w-g+1-2 b_s,  ell | r(u-1)+2-g+s,
where b_+=0,b_-=3 and s is the firing sign. For T0=O(L log L), the first integer is positive O(r). Also ell!=r: with 0<=g<r-3, even g cannot equal 2+s mod r. A first trial/true discrepancy must be among these outside eligibilities.

In a dyadic box r~P, u~X=R/P, the class-wise elementary upper for prime r is O(P/(phi(B)L)), with an extra reduced residue mod ell<=R^.05 giving O(P/(phi(B)ell L)). For fixed r, the two forms u,ru+2 are R^a-rough; uniform two-form Selberg upper gives O(X/(B L²)*(B/phi(B))²) per reduced u class, with an extra residue mod ell>z, ell!=r, dividing by ell. The parameter length X/(B ell) stays polynomial since ell=O(P), c=.3128, 1-2c-.01>0. The only determinant is 2 and the coefficient r costs a uniformly bounded omitted-prime factor. The admissible (r,u) class pairs are at most phi(B)^2 F_B, F_B=product_{odd ell|B}(1-1/(ell-1)); (B/phi(B))F_B is bounded, since the odd-prime factors are 1-1/(ell-1)^2. No prime lower in the restricted classes is needed.

For ell<=R^.05 the first pin fixes one r residue and the second one u residue. For ell>R^.05 the first pin has O(1) such factors at fixed r and class pair, of total reciprocal O(R^(-.05)). Thus summing the progression uppers over classes, over O(L) dyadic boxes and w<=T0 gives
    # exceptional roots << R/L² * [T0/(z log z)+T0 R^(-.05)].    (4)
Choose T0=floor(c1 z log z) for a sufficiently small FIXED c1>0 relative to the positive lower in (II). Retain >>R/L² actual roots whose entire common elapsed T0 suffix matches the trial. On all of them the height remains >=r+3-z T0/2=(1-o(1))r, and the suffix gain is <=D=z T0. This is a true polynomial HEIGHT and polylogarithmic common TIME result, not a polynomial-time result.

For two connectors to meet at a physical state (x,n) they must have anchor positions differing by <=D and clocks differing by <=T0. Hence their r labels differ by <=T0+D/2. Equal r forces equal anchor (both x0=2 mod r and D<r), hence equal root. For distinct primes r,r', each fixed offset d0 with |d0|<=D gives the CRT x0=2 mod r, x0+d0=2 mod r'; number of possible positions O(R/r²), since r'~r and r²=o(R). Summing over even ALL integer r>=R^a, offsets and possible r', gives O(R^(1-a)(D+1)(T0+D+1))=o(R/L²). Delete both endpoints of such near pairs. The retained connectors are pairwise disjoint in physical state, including different elapsed ticks. All anchors and states lie in [R-O(R^c),2R]. No claim of disjoint spatial positions at differing clocks.

Moreover for fixed 0<alpha<a, every trial visited center y=r(u-1)+2-g with qmin(y)>=R^alpha has four R^alpha-rough forms u,ru+2,y-1,y+1, with distinct rational roots (g=o(r), determinant nonzero). In each fixed r and class pair, the elementary four-form Selberg upper is O(X/B*(log L)^4/L^4); the omitted-prime factor includes B already. Sum using prime r class upper, at most phi(B)^2 F_B classes, O(L) boxes and T0+1 ticks. The total O(R(T0+1)(log L)^4/L^4)=o(R/L²). Therefore after deletion these common-time actual connectors have no twin centers, and indeed qmin<R^alpha at every visited postarrival center. The existence of such a density-scale HIGH dynamic population at polynomial exponent .300 is a new consequence of the phase split, not a substitute for the missing first-H transport to .4.

## 6. Limiting strengthening and next obstacle

The same proof gives a family of dichotomies arbitrarily close to the critical exponent. In the ideal limit d=5/8, e=1/2, b=c=5/16, choose any fixed a<5/16 sufficiently close to it (e.g. a>=.300). Then F_d(b)=0 and
    Delta=integral_a^b [ 1/(t(d-t))-1/(2t(e-t)) ]dt >0,
because 2e-d=3/8 > b. By continuity, choose genuine d<5/8 sufficiently close, e<1/2 sufficiently close, b>5/16, c<b sufficiently close to b, with Delta=F_d(a)-F_d(c)-U_e(a,c)/2+2F_d(b)>0. Choose the source p band sufficiently close to 3/8 from below with two-factor capacities giving d (as in 96859f4/4708dfc), preserving fixed power slack. The cutoff construction still works since a>(d-a)/3+.0002 and c<b<source exponents. The absolute estimate (1) remains valid for the new source band. Use a small fixed threshold in (I) proportional to Delta, and errors smaller than it. Thus for every fixed epsilon>0 (choose a>5/16-epsilon and a>=.300), under the SAME prior analytic transfer, every sufficiently large slab either has density-scale static roughness at some fixed exponent above 5/16, or density-scale HIGH first-minus arrivals of height >=R^(5/16-epsilon) with disjoint actual polylog-time connectors. Constants may depend on epsilon. This is not a claim that the first alternative occurs infinitely often or that either gives M85.

New obstacle: after the common-time suffix in (II), the anchor form with a large pinned r and the two source rough forms no longer gives a uniform polynomial-time error bound. Equation (4) grows linearly in T0, so extending T0 to a polynomial height gap by this same estimate loses the entire density-scale population. Also the high arrival does not exceed the earlier first-wait record. Need a new *iterable* height-section lower or alternative prime-correlation/long-range argument. M85 still requires genuinely new control at H=R^.4, not merely improving the starting exponent or local phase.

## 7. Verification and source ledger

- [S1] prior variable cutoff/dichotomy: 2eab1ed84472132895a7e21c2599d8f189b1f3ec, research/2026-11-28-min-negative-variable-cutoff-and-absolute-marginal.md §§2,4,5. Reopened 2026-11-28.
- [S2] previous HIGH modular transfer: 07503a495c962aeb854ba29e7a20a73e7f6eefe5, research/2026-11-28-min-negative-modular-short-transfer-and-canonical-approximation.md §§1–3, reopened at base. The present adaptation uses the two rough forms instead of requiring a prime first cofactor.
- [S3] Pascadi, On the exponents of distribution of primes and smooth numbers, arXiv:2505.00653v2, 2025-06-29, https://arxiv.org/pdf/2505.00653v2 pp20–23 Def4.3, Prop4.4/4.5; text and screenshots pp20–21 inspected 2026-11-28. Supports distinction between required SW and fixed AP coefficient; prior endpoint review not closed.
- [S4] Yang, arXiv:2608.13299v2, 2026-09-03, https://arxiv.org/pdf/2608.13299 pp3–4 (1.1),(1.2),Thm1.2, rechecked text and p4 screenshot; no new theorem used. Maynard arXiv:2006.07088v1 early version also inspected; final cited numbering unavailable, no claimed proof adaptation.
- Audit: research/lean/negative_min_phase_split_absolute_bv_audit.mjs @ad032514adbe7e9a536e04f891988bc85e3bbbc1 blob 251d61479ee16cf3e6ef4245c1b2f0320f2f0c52, ECMAScript execution, exact commit and branch readback. 70-term rational positive atanh series plus geometric tail, scale 10^22; margin interval above. R=100000,400000,1000000 with intentionally broader p band [.30,.44] and cutoff proxies a=.18,c=.27,b=.34: 59,729 source points, 5,665 phase-class checks, 1,743 isolated high cases, 3,085 literal first-winner checks over 58,150 ticks, 958 induced-exclusion size controls; exact variable-cutoff identities and counting lower all pass. These finite examples are structural tests, not the asymptotic constants or evidence for the asymptotic alternative probabilities.
- No change to verified Lean core b0e26798535b2c997f1383c1dc37bbe560aac938, no new Lean compile or independent human review. Main/siblings unchanged. The analytic upper for the phase split is independent of the old high-level transfer; the combined lower inherits it.
