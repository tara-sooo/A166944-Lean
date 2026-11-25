# Local medium repeat moments indexed by the least eligible factor

2026-11-25 JST. Continuation of d179af254862f3cf24aa064d6c49c6e29b34d579 on research/min-prime-root-repeat-energy-2026-11-25. Redirects the investigation from repeated refinements of synchronous high energy to the independent medium obstruction. Gives a strictly weaker localized version of the old selected-label moment criterion, an alternative least-factor-indexed criterion, and a four-form sieve bound for the low-overlap part of the latter. No proof of the heavy local overlap moment, high residual or twin-prime infinitude. Paper deductions and finite checks; no Lean compilation or external novelty claim.

## 1. Exact LOW attachment and the medium problem

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=log u, T=floor(X/u^(1/4)), H=T+B, N=Theta(X/u) prime starts M in [X,2X), Q=ceil(B/u). The original canonical MIN prefix stops at the first gain crossing >=T, original terminal or cutoff. Each source has total gain <H, total selected weight <=1.5H, and total r-cost <=1.5H. Here p is the actual selected odd prime, and r=r(C) the least eligible odd prime <=B at the pre-event horizon C. In particular r<=p. In the absence of twin terminals the total r-cost is >=N(T-6)/4 for all sufficiently large X.

Take the established LOW boundary y maximal with even primorial L=2 product_{3<=p<=y}p <=ell^(1/4) for sufficiently large X. In particular L grows slowly and L=o(Q). Every contiguous block of actual p<=y has gain <L: the next multiple of L is an impenetrable even-horizon barrier under these selections (the last possible p jump before crossing cannot cross such a multiple). This is the earlier LOW lemma; its proof and earlier cumulative marks are in edffc245/a5e1119. Its total r-cost is <=1.5L. Attach each LOW block to its preceding actual nonLOW event, or to its initial root if no such event exists. Initial LOW blocks together cost O(NL). Attached LOW on all p>=Q anchors costs O(LNH/Q)=o(NT), even without any high-energy estimate.

Freeze a medium incidence list I_m: all actual events y<p<Q, or their subset after any previous accounting deletions whose combined clock and associated LOW cost is already o(NT). We do not rerun MIN. A medium event can have r<=y, which MUST NOT be discarded merely because its minimum is small. Its exact clock plus attached LOW cost is bounded by
    w(r)=r+1.5L.
Alternatively one can use w(p)=p+1.5L. Both are legitimate upper bounds; no assumption that selected p and minimum r agree. All medium counts and blocks below are on the chosen frozen I_m, before the new first-use deletion. The natural high classification p>=Q, r>p/sqrt(log p) is unchanged, with its earlier relative-cheap deletion at o(NT) cost. Thus the alternative criterion below needs no transfer of an r-indexed definition to the high chain/merger proofs.

## 2. Adaptive local gain cells

Let j denote the label of an incidence, using either j=p (selected-label version) or j=r (least-factor version). In either case j is an odd prime <Q. Define
    w_j=j+1.5L,
    A_j=ceil(w_j² u^(3/2)), k=max(1,floor(u^(1/4))).
Use fixed ALIGNED horizon cells of integer width A_j, e.g. [a A_j,(a+1) A_j), independently for each j. Use absolute horizons C, not per-root moving cells. At fixed M,j,a let n(M,j,a) count the frozen medium hits in that cell. Each root visits horizons strictly increasingly over a range of length <H; hence at most ceil(H/A_j)+2 cells can occur for each label on that root. This does not require p=j. Uniformly A_j<<H/u^(1/4) for all j<Q at large X, because Q~B/u and L=o(Q); thus this is genuinely local even at the upper medium boundary. At small j the cells can be much shorter.

Delete the first min(k,n) actual hits in every occupied M,j,a cell, including their attached LOW cost. Their total cost is bounded by
    R_first <= kN sum_{3<=j<Q} w_j (ceil(H/A_j)+2)
      << kN [H/u^(3/2) sum_j 1/w_j + sum_j w_j]
      << kN [H(1+ell)/u^(3/2) + Q²/log Q + L Q/log Q]
      = o(NT).                                             (1)
Here and below sums in j run over odd primes. Use elementary prime reciprocal and counting bounds and H~T. At the chosen k the first term is O(NT(1+ell)/u^(5/4)); the endpoint term is also negligible. This is a clock-plus-LOW accounting deletion, not a selected-gain propagation seed. Every surviving hit now has at least k earlier same-j frozen hits in a gain interval of length <A_j, even for r-indexed hits with different selected primes.

Write
    Z_loc(j-type)=sum_{M,j,a} n(M,j,a)(n(M,j,a)-1),
    Z_trim(j-type)=sum_{M,j,a} (max(0,n(M,j,a)-k))².
The latter is <= the former because k>=1. Thus we require only off-diagonal within-root repeat pairs, not their diagonal count. The remaining medium-plus-LOW cost satisfies
    R_med,rem² <= (N sum_{j<Q} w_j²(ceil(H/A_j)+2)) Z_trim
              <= (N sum_{j<Q} w_j²(ceil(H/A_j)+2)) Z_loc.
The coefficient is
    O(N [H pi(Q)/u^(3/2) + sum_{j<Q} w_j²])
       = O(N [H Q/(u^(3/2) log Q) + Q³/log Q])
       = O(N X B/u^(15/4)).                                (2)
For the middle inequality use L=o(Q) and the ordinary prime counting bound; the lower j<=L contribution is included in the sum. Therefore either of the local moment conditions
    Z_trim=o(N B u^(13/4))   OR   Z_loc=o(N B u^(13/4))      (3)
implies R_med,rem=o(NT), and the simpler O(N B u³) suffices with R_med,rem=O(NT/u^(1/8)). All constants and floors are immaterial asymptotically.

For selected labels the earlier global Z_m=sum_{M,y<p<Q} n_m(M,p)² dominates Z_loc(p-type) on the same I_m. Thus (3) is a weaker sufficient condition than the previous O(N B u³), since it ignores all distant repeats across aligned cells and the diagonal, and even has an extra u^.25 in the little-o threshold. For least-factor labels this is an alternative condition: different selected primes can contribute to the same r, and there is no claimed domination by the old selected-label moment. The local width is determined by w_r and not by the potentially much larger selected p.

An alternative first-moment description: at each label the exact quotient (C+sigma)/r=2n+1, sigma unique, both forms avoid odd primes q<r. For r sufficiently large the local capacity n(M,r,a)<<A_r/(r log²r) follows by the two-form sieve of 32d4185 with z=floor(r^(1/8)); the remainder r^.75 is absorbed because A_r/r>=r u^1.5. Bounded r handled by an absolute constant. The minimum-factor version has this deterministic capacity without a relative-expensive restriction, unlike applying the same bound to selected p. This capacity alone does NOT prove (3).

## 3. Exact local overlap representation

For each r-indexed arithmetic pair of even horizons C<D in the same aligned r-cell, with r(C)=r(D)=r<Q, define
    V_r(C,D)=# original prime starts M having BOTH hits in the frozen medium I_m.
The source tags at either horizon are counted only if their selected p is in the medium set and they survive any earlier marks defining I_m. Strict horizon growth ensures no source can appear twice at either horizon. The width is fixed in absolute C, so the same pair belongs to a single cell, independent of source. Then exactly
    Z_loc(r-type)=2 sum_{r<Q} sum_{C<D same r-cell} V_r(C,D).   (4)
This is an intersection of actual source-tag sets, not a product of their marginal masses. A pair of horizons whose two independent ancestry masses are enormous may still have small V. Every source contributes at most one unit to a fixed V. Only positive r are considered; no r=0 twin horizon enters.

We now bound the contribution of small V to (4), even if there are very many distinct root-specific repeat pairs. Set
    c_r=max(1,floor((log r)^6)).
We prove the unconditional arithmetic bound
    2 sum_{r<Q} sum_{C<D same cell, V_r<=c_r} V_r(C,D)
        = o(N B u³).                                      (5)
It covers every local repeat pair shared by at most its label-dependent polylogarithmic number of roots, regardless of depths, actual selected labels, or repeated physical/projection contacts.

## 4. Four-form arithmetic support for medium repeat pairs

Let K_r count all pairs of even horizons C<D in [2X-2,7X] with r(C)=r(D)=r and D-C<A_r. For an upper bound ignore the aligned-cell condition. If h=D-C, the unique signs sigma,tau in {-1,1} satisfy r|(C+sigma), r|(D+tau), so
    h+tau-sigma=0 mod r.
Thus h lies in at most three classes mod r; the number of positive h<A_r is O(A_r/r) (A_r>=r). For each h the eligible arithmetic C lie in at most two classes mod r and there are O(X/r) of them. The simple bound for every r is
    K_r << X A_r/r².                                      (6)
For r>3, both C and D are multiples of six: otherwise 3 divides one of C±1 or D±1. Hence h>=6; the shift-two degeneracy of the four-form sieve does not occur.

For r>=u² strengthen (6). Uniformly for these r<Q, L=o(r), A_r<<r² u^1.5, log A_r=O(log r) because log r>=2 log u. Fix one admissible h and sign sigma, and write C=r(2n+1)-sigma, with O(X/r) consecutive possible integers n. Both endpoints have least factor r. For sieve primes
    (log r)^2 < q <= z=floor(r^(1/16)),
    q not dividing h(h-2)(h+2),
the four linear forms C-1,C+1,C+h-1,C+h+1 exclude exactly four residues of n modulo q; q<r, q odd and the slope 2r is invertible. The exclusions are necessary, not sufficient for r(D)=r. All omitted exceptional primes q>(log r)^2 have combined reciprocal sum
    O(1/(log r loglog r)),
since |h(h-2)(h+2)| has logarithm O(log r) and each such prime has logarithm >2 loglog r. This is uniform for all admissible nonzero h>=6.

For clarity the dimension-four sieve calculation is the same as in b8fea48, with parameter r rather than B. Allowed squarefree d<=z have g(d)=prod_{q|d}4/q, h_4(d)=prod_{q|d}(q-4)/4. The Selberg quadratic main term diagonalizes as sum_l h_4(l)Y_l² with Y_l=sum_{l|d}lambda_d g(d). The choice Y_l=mu(l)/(h_4(l)G_4(z)), G_4(z)=sum_{d<=z}1/h_4(d), has lambda_1=1, |lambda_d|<=prod_{q|d}(1-4/q)^(-1)<=d for sufficiently large r. The counting error is O(z^6), using 4^omega(lcm(d,e))<=de. To bound G_4, take the product of allowed q<=z^c with sufficiently small fixed c>0. Its total mass prod(1-4/q)^(-1) is >> (log r/(1+loglog r))^4 by Mertens and the bounded reciprocal loss of the exceptional primes. In the normalized product distribution the inclusion probability of q is 4/q, so expected log d=O(log(z^c))<=.5 log z for small c. At least half the mass has d<=z by Markov, giving that same lower bound for G_4. This uses only elementary prime sums and the previously proved quadratic sieve. No independence assumption on trajectories.

The survivor count for n at fixed h,sigma is consequently
    O((X/r)((1+loglog r)/log r)^4 + r^(3/8))
      = O((X/r)((1+loglog r)/log r)^4).
The error is uniformly absorbed, since r<=B, X=Theta(B²), and (r^1.375/X) log^4 r=o(1). Summing both signs and O(A_r/r) admissible shifts gives
    K_r << X (A_r/r²) ((1+loglog r)/log r)^4
         << X u^(3/2) ((1+loglog r)/log r)^4
              for u²<=r<Q.                               (7)
This bound counts arithmetic pairs of horizons, not root pairs, and is independent of the MIN path length or actual multiplicity.

For r<u², (6) and L<=ell^.25 yield
    sum_{r<u²} c_r K_r
      << X u^(3/2) u² (1+L)^2 (1+ell)^6
      = o(X B u²).
The factor u² simply bounds the number of these primes; no primality saving needed there. For u²<=r<Q, (7), c_r<=O(log^6 r), and pi(Q)<<B/u² give
    sum_{u²<=r<Q} c_r K_r
      << X u^(3/2) sum_{u²<=r<Q} (log r)^2(1+loglog r)^4
      << X B u^(3/2)(1+ell)^4
      = o(X B u²)=o(N B u³).
Together these prove (5). In particular the argument does not need to omit small r from I_m; their capped-pair contributions use the simpler congruence bound. The uncapped small-r contributions can still be large.

## 5. New medium sufficient condition and integration

Define the heavy local overlap moment
    Z_heavy = 2 sum_{r<Q} sum_{C<D same r-cell, V_r(C,D)>c_r} V_r(C,D).
By (4)-(5),
    Z_loc(r-type)= Z_heavy + o(N B u³).                  (8)
Thus the following is a new sufficient replacement for the entire old medium requirement:
    Z_heavy=O(N B u³)
or more generally Z_heavy=o(N B u^(13/4)).
This condition no longer contains widely separated repeated labels, the diagonal, or any pair whose overlap is below c_r. It is on actual shared origins of a pair of horizons, not the two separate ancestry masses. It is valid whether the two hits selected the same prime or different primes. It does not assert that all heavy pairs can be eliminated, or that the small-overlap pair contribution represents a disjoint linear deletion of hits. Instead the small pair moment is harmless in Cauchy's estimate (2).

The new first-use deletion (1), LOW accounting and (2)-(8) reduce the entire medium clock burden to this condition. If desired keep the old selected-label moment route independently, or the localized selected-label version (3), whichever can be proved. For an independent simple core take I_m to contain every actual medium event, with no earlier marks; for the cumulative hybrid take its surviving medium subset with already-paid linear and LOW cost. For the high part retain the established natural high labels and previous absolute pair/slice exclusions and relative phase absorption. Joint OPEN conditions on the same unbounded dyadic windows are now, for example,
    Z_heavy=O(N B u³),
    E_phys,admitbad+E_async,bad=o(T² B u).
These would imply total R=o(NT), contradicting the no-twin gain-crossing lower bound. Neither residual condition is proved here. This is a genuinely different target for the medium problem, not a claimed solution of the old global Z_m or an assumption that its r-indexed analogue is small. The old high proofs need no rerun and are independent of the new medium cells. Main and other branches unchanged.

## 6. Reproducible audit

Standalone ECMAScript research/min_prime_root_local_repeat_audit.mjs, exact remote readback at b909083b74b5c9086180361dd68da20e8f83174e, blob ea44378b8cbb3a5b94653b65f82ff4c477b78fac. Run:
    node research/min_prime_root_local_repeat_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node executable. All 18 runs (3 modes x 6 windows) passed. Actual canonical SPF MIN prefixes, independent literal parity-GCD comparisons on X256/1024 (short1183, wide1707, analytic1719), exact LOW block assignment and gain barrier at y3,L6, quotient identity and minimum factor, aligned cell counting in both selected and minimum labels, first k deletion and exact BigInt Cauchy inequalities, global off-diagonal vs local off-diagonal vs trimmed squares. Independently aggregates V per same-cell pair and checks the overlap identity and capped/heavy partition. Enumerates ALL even arithmetic horizons, buckets by actual r and aligned cell, computes exact arithmetic same-cell pair count (not an asymptotic estimate). Checks r-indexed pair congruence for all actual pairs, r>3 spacing six, and finite nonexceptional four-residue counts with q<r among 5..31. No independent asymptotic sieve estimate or cumulative high/medium marks tested; the analytic LOW guard y3,L6 is diagnostic and not the asymptotic primorial rule at these sizes.

Analytic T=X/u^.25,Qm=ceil(B/u) min5, width ceil((r+9)^2 u^1.5), k=max(1,floor(u^.25)), c_r=floor(log^6 r) min1. At finite sizes large windows and small k do NOT exhibit asymptotic cheap-first-use cost. Short T=B,Qm=max(7,ceil(B/8)), k1, diagnostic width ceil((r+9)^2/8), cap2; wide T=4B,Qm=max(7,ceil(B/4)), k2, same width, cap4. The width coefficient in diagnostic modes is deliberately tiny, so most hits are removed by the first k at these finite settings; this is NOT evidence for (1) with those diagnostic widths. All medium events y<p<Qm included, no relative-cheap or previous accounting marks. The selected and r versions use the identical original incidence set but may differ in cell widths and local pair counts.

| X | wide global offdiag r | wide local offdiag r | wide heavy local r | wide trimmed squares r |
|--:|--:|--:|--:|--:|
|256|not tabulated|30|12|0|
|1024|not tabulated|84|36|0|
|4096|not tabulated|596|362|0|
|16384|not tabulated|2444|1538|0|
|65536|not tabulated|11348|8138|1|
|262144|1821790|49418|36890|19|

At largest X262144, B1355,N20390, wide T5420,Qm339: 612685 original events, total R16602377, medium368326 tags clock8413394 plus attached LOW627792 (total9041186). 208359 LOW blocks, max gain4. Initial LOW41988, high-attached19077. Minimum-label local groups343636, global offdiag1821790 vs local49418, trimmed19. Local overlap4937 distinct keys, max V85, heavy1334 keys, capped12528 and heavy36890 ordered pair incidences. Exact arithmetic cell pair envelope1145047, actual keys4937. 24709 unordered same-root local pair incidences, of which1092 same sign and23617 opposite sign; 1860 four-residue tests. Selected-label alternative global offdiag1667998/local49846/trimmed215, max V83. Actual clock+LOW remaining after diagnostic first k: r163, p1551; this cheap-looking finite residual follows from intentionally tiny diagnostic widths, NOT from the asymptotic guarantee.

At largest short T1355,Qm170: medium269330 tags, total clock+LOW4846011; r global offdiag828920/local36336, capped7416/heavy28920, trimmed18186, r remaining182879; p local37548/trimmed18953. Largest analytic T159967,Qm188: medium359795 tags, cost6754565; r global offdiag1874438/local1457802, capped1084478/heavy373324, trimmed1254213, r remaining2053367. 166047 actual r pair keys, max V103, 9874 heavy keys, 32856 residue checks. p global offdiag1718552/local1352972, trimmed1155018, remaining2076048. Thus r and selected label statistics are not ordered uniformly. All empirical magnitudes diagnostic, no limiting inference.

## 7. Next target

The medium obstruction is now local intersection mass on equal-minimum-factor horizon pairs rather than all global repetitions. Investigate r-deleted shadow return paths and actual reverse root histories for those pairs with V>log^6 r. In particular small r and opposite-sign transitions cannot be treated as generic four-form events of a large modulus; the heavy overlap may concentrate on them. A bound on actual common-source overlap (not only arithmetic support or individual horizon masses) would advance the medium criterion. High synchronous and asynchronous residuals remain independent.
