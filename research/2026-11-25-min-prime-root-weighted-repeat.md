# Band-weighted medium repeat moments and unconditional short-gap exclusion

2026-11-25 JST. Continuation of 711a0db7df0d2920f15f6f071718f924ce4938f2 on research/min-prime-root-repeat-energy-2026-11-25. The previous medium criterion counted every local equal-minimum-factor repeat pair with high common-source overlap. Here short-gap pairs are paid unconditionally, even if their common-source overlap is arbitrarily large. Dyadic factor bands give a weighted sufficient moment with less stringent requirements at small r, and allow larger overlap caps there. Neither the residual weighted long-gap overlap nor the high energy is bounded. No Lean compilation or external novelty assertion.

## 1. Inherited local medium ledger

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts, Q=ceil(B/u). Freeze the original actual medium incidences y<p<Q (or any subset after already-paid accounting deletions), where p is the selected odd prime, r=r(C)<=p the least eligible odd prime. Attach each original LOW block to its preceding nonLOW anchor; initial LOW and high-attached LOW are negligible as in 711a0db. The medium incidence clock plus attached LOW is at most w_r=r+1.5L with L the established slow-growing even primorial. In particular r<=y is allowed, and no relative-expensive test on p is required.

Use the same aligned absolute horizon cells of width A_r=ceil(w_r² u^1.5), and delete the first k=max(1,floor(u^.25)) hits per source, r, and cell at o(NT) total clock+LOW cost. All pair counts below refer to the FROZEN list before this deletion. Let n(M,r,a) denote the count in that cell. Residual squared count (n-k)_+²<=n(n-1). For each dyadic band P=2^b, b>=1, P<=r<2P with r<Q, define
    Z_P=sum_{M,r in band,a} n(M,r,a)(n(M,r,a)-1).
Let G_P be the actual sum of selected gains p-1 at these frozen medium events (not all gains between their repeats). The gain budget gives sum_P G_P<=NH and the number of events in band P is <=G_P/(P-1). The previous proof by bandwise Cauchy gives
    R_med,rem <= sum_P sqrt(C_P Z_P),                (1)
    C_P=N sum_{P<=r<min(2P,Q)} w_r² (ceil(H/A_r)+2).
Uniformly in all nonempty bands, including bounded P,
    C_P << (NH/u^1.5) P/log(2P).                    (2)
Indeed w_r²(ceil(H/A_r)+2)<=H/u^1.5+3w_r². Uniformly w_r²=O(Q²)=O(X/u²)=o(H/u^1.5); the number of primes in the band is O(P/log(2P)). Thus there is no separate loss proportional to the number of small r with w_r dominated by L. This uses the actual local cell partition, not a global moment across distant cells.

## 2. Unconditional short-gap repeat pairs

Define an additional distance cutoff (independently of the aligned cell width)
    D_r=max(1,floor(r u^1.5 [log(2+min(r,u))]²/ell^1.5)).
For any fixed arithmetic horizon C of least factor r, the number of other even horizons E in (C,C+D_r] with least factor r satisfies
    #{E} << u^1.5/ell^1.5                          (3)
uniformly for all 3<=r<Q.

Proof: fix one divisibility side sigma in {-1,1}, write E=r(2n+1)-sigma. The interval for n has length O(1+D_r/r). Both forms 2n+1 and r(2n+1)-2sigma avoid all odd primes below r. Use the uniform two-form interval sieve of 32d4185 with z=floor(min(r,Hq)^1/8) for an enclosing integer interval of length Hq=ceil(D_r/(2r))+3. This gives O(Hq/log²(2+min(r,Hq))) survivors for each sign: the error z^6<=Hq^.75 is absorbed, z<r, and the bounded-min cases use the trivial interval bound with an enlarged absolute constant. Both signs add factor two. Since D_r/r >> u^1.5/ell^1.5 >> u, uniformly Hq>=u for sufficiently large X, so log(2+min(r,Hq))>=log(2+min(r,u)). Substitution proves (3). This is a local arithmetic capacity, not a random trajectory model; the next horizons need not be immediate actual events or have the same selected p.

For each band split Z_P into Z_P^short and Z_P^long according to whether the positive gap of the unordered horizon pair in its same aligned r-cell is <=D_r or >D_r. Use factor two for ordered offdiagonal counts. Every frozen medium incidence can be the earlier endpoint of at most the number in (3) such short pairs ON ITS OWN source, because its horizons strictly increase. There is NO restriction on V_r(C,E), the number of different roots sharing a particular pair. Hence
    Z_P^short << (u^1.5/ell^1.5) G_P/P.
Combining (2) with Cauchy across bands and the total gain budget yields
    sum_P sqrt(C_P Z_P^short)
        << sqrt((NH/ell^1.5) * sum_P G_P * sum_P 1/log(2P))
        << NH/ell^.25 = o(NT).                     (4)
The last reciprocal sum over dyadic bands is O(ell), since log(2P)=(b+1)log 2. This is a direct unconditional upper bound on the CLOCK CONTRIBUTION in the split Cauchy inequality, NOT a claim that sum_P Z_P^short=o(NBu³). Small-r short repeat counts may in fact be much larger than that scale. No additional physical ancestry assumption is used.

For r>=u, D_r is of order r u^1.5 sqrt(ell). The exclusion allows all possible actual intervening selected words with total gain <=D_r, including words with different starting/ending selected p. For each such actual word from C to E the sum of selected increments is exactly E-C, so every selected p in the word satisfies p-1<=E-C. The proof of (4) needs only the gain budget and local arithmetic capacities; it does not assert that the actual word is unique or that its labels are independent. This replaces a potentially complicated short-transcript classification by an upper bound valid for all transcripts.

## 3. Weighted long-gap moment

Define the band weight
    lambda_P=sqrt(P/Q) log Q/log(2P)
and weighted long moment
    Z_weight,long=sum_P lambda_P Z_P^long.
These weights are positive, uniformly O(1), comparable to 1 at the top scale and much smaller at small P (the log ratio is offset by the square-root power). More generally any fixed exponent alpha in (0,1) in place of 1/2 works, with a constant depending on alpha; use 1/2 in the audit. Formula (2) yields
    sum_P C_P/lambda_P
        << (NH/u^1.5) (Q/log Q) sum_P sqrt(P/Q)
        = O(N X B/u^3.75).                          (5)
This sum is geometric, rather than a factor proportional to the number of bands.

Use sqrt(Z_P)<=sqrt(Z_P^short)+sqrt(Z_P^long) in (1), then Cauchy with lambda_P on the second sum. From (4)-(5),
    R_med,rem << NT/ell^.25
                 + sqrt((N X B/u^3.75) Z_weight,long).  (6)
Thus Z_weight,long=o(NBu^3.25) suffices; in particular O(NBu³) gives an additional O(NT/u^.125) term. The original unweighted local criterion implies this new one on the same frozen set, up to the bounded weight constant, but the new condition allows more repetitions at smaller r and no requirement on the short part. The old selected-label criterion remains an independent route; no ordering of selected vs least-factor moment is claimed.

## 4. Larger caps for the long common-source overlaps

Recall exact overlap V_r(C,E), the number of original sources with both frozen medium incidences at these two horizons in the same aligned r-cell and r(C)=r(E)=r. A root contributes at most once to any key (r,C,E). Then
    Z_weight,long=2 sum_{r<Q} lambda_{P(r)}
                         sum_{C<E same r-cell,E-C>D_r} V_r(C,E).
For each r define c_r=max(1,floor((log r)^6)), and enlarge the cutoff to
    c'_r=max(1,floor(c_r/lambda_{P(r)})).
Since lambda is bounded, lambda*c'_r<=max(c_r,lambda)=O(c_r). The arithmetic pair count K_r of 711a0db applies to all same-cell pairs, hence also to the long subset. Its previously proved estimate sum_{r<Q} c_r K_r=o(NBu³) therefore gives
    2 sum_{r<Q} lambda_{P(r)}
       sum_{long keys with V_r<=c'_r} V_r=o(NBu³).       (7)
No new arithmetic independence hypothesis. The new cap is of order (log r)^6 sqrt(Q/P) log(2P)/log Q, with floor and min1. At bounded r this is of order sqrt(Q)/log Q, in contrast to the old fixed cap. At r near Q the cap remains of order u^6. It is a cap on actual intersection mass of the two tagged horizon sets, not on a marginal product or on the number of possible word types.

Define
    Z_weight,bad=2 sum_{r<Q} lambda_{P(r)}
        sum_{C<E same r-cell,E-C>D_r,V_r>c'_r} V_r(C,E).
Then (6)-(7) prove
    R_med,rem <= o(NT) + O(sqrt((N X B/u^3.75) Z_weight,bad)).
A new sufficient medium target is Z_weight,bad=O(NBu³), or o(NBu^3.25). All short-gap repeat pairs, even at extremely high overlap, and all long pairs under the enlarged caps are covered. There is no claim that these pairs correspond to disjoint deleted clock incidences: the argument splits a quadratic moment before Cauchy.

## 5. Integration and remaining problems

The high definition p>=Q and relative-expensive r>p/sqrt(log p) and all previously proved high-energy exclusions/phase absorption remain unchanged. Attach LOW exactly once as in section 1; the new medium first-use removal includes its LOW cost. One may use the full original medium I_m or its subset after previously paid linear marks. Combining the medium estimate with the existing high residual gives the joint OPEN sufficient conditions
    Z_weight,bad=O(N B u³),
    E_phys,admitbad+E_async,bad=o(T² B u)
on the same unbounded dyadic windows. If they hold, the earlier gain-prefix lower bound contradicts the total upper bound R=o(NT) on windows without twins. This is a weaker medium requirement than the unweighted local least-factor criterion; it does not prove that the actual residual satisfies it. The exact short-gap count is unconditional, but longer heavily shared paths remain the arithmetic/dynamical obstruction. A future route is to quantify the distribution of the long return gaps within each aligned r-cell using actual r-deleted shadows, or to use the tail-clock/physical merger information to bound intersections on long gaps, without identifying arbitrary projected contacts with physical synchronization. No bound for the high residual or old global selected-label moment is claimed.

## 6. Reproducible audit

Standalone ECMAScript research/min_prime_root_weighted_repeat_audit.mjs, exact remote readback at 131baba095e8d71dfed2305a39694cd4328f3173, blob 641642f283206399b3760a487c70957782574dd7. Run:
    node research/min_prime_root_weighted_repeat_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node invocation. All 18 runs (three modes x six windows) passed. Actual canonical SPF MIN prefixes and independent literal parity-GCD comparisons on X256/1024 (short1183,wide1707,analytic1719), exact LOW assignment, first-use partition, full r-horizon enumeration and binary-search local capacity for each frozen incidence, actual short-word gain identity and bound on every selected increment, exact local overlap identities and band gain budgets, exact BigInt band Cauchy, weighted capped/heavy partition and floating-point split Cauchy checks. The arithmetic capacity audit uses the actual r-horizons, not a numerical proof of the limiting sieve constants. Full frozen original medium, no accumulated earlier marks. Fixed finite LOW y=3,L=6, not the slowly growing asymptotic primorial.

Analytic mode uses T=X/u^.25,Q=ceil(B/u) min5, A_r=ceil((r+9)^2 u^1.5), k=max(1,floor(u^.25)), D_r as above, c'_r as above. Diagnostic short/wide modes use T=B/4B respectively, Qm=max(7,ceil(B/8)) / max(7,ceil(B/4)), A_r=ceil((r+9)^2/8), k=1/2, D_r=3r/6r, base cap2/4 divided by lambda with floor and min1. The tiny diagnostic widths and short cutoffs are chosen to exercise the partition, NOT to justify the asymptotic cheap-first deletion or short-gap bound at those settings.

| X | analytic local offdiag | short | long capped | long heavy |
|--:|--:|--:|--:|--:|
|256|202|90|112|0|
|1024|652|296|348|8|
|4096|9532|3084|6220|228|
|16384|59398|15218|42576|1604|
|65536|279534|68318|199544|11672|
|262144|1457802|303186|1074230|80386|

At largest X262144 analytic B1355,T159967,Q188,N20390, medium359795 tags clock6136787+attached LOW617778. Original first-use cost4701198, remaining2053367, trimmed squared moment1254213. Exact local moment1457802 equals short303186 + long1154616; long equals capped1074230 + heavy80386. Weighted long429851.3586 = capped399269.3005 + heavy30582.0582 (floating-point). Short arithmetic capacity checked at359795 incidences, max9 candidates; 151593 actual short unordered pairs, 144954 with more than one full intervening selected event; 33415 distinct short keys, 132632 long keys, 2974 heavy long keys, max V103. The finite bound from split Cauchy is loose, and the first-use cost is not empirically small in this mode.

Largest wide T5420,Qm339: local49418, short49276, long142=capped76+heavy66, 13 long keys of which2 heavy; weighted heavy34.4335. Largest short T1355,Qm170: local36336, short26220, long10116=capped4676+heavy5440; weighted heavy2183.7911, 262 heavy keys. These finite numbers concern the new independent medium partition and do not estimate limiting saving fractions. Main and other branches unchanged, no Lean compilation.
