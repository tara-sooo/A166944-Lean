# Triple-factor gaps and factor-role capacities

Continuation of [20e23ea](https://github.com/tara-sooo/A166944-Lean/commit/20e23ea0302ca2071f031c318ef5509665a2cda2) on the independent direct-arithmetic branch. New bounds for the fourth-root qualified composite-cofactor branch, using the elementary two-residue and shift upper sieves proved in c27a25f. No prime-pair asymptotic or short-return hypothesis. Twin infinitude and A166944 remain open. Paper proof, not Lean kernel verification.

## 1. Setup and counting injection

Consider one contiguous adaptive event block with pre-horizons <=Y. A fourth-root qualified type-III event has H-e=pab, where a<=b and p,a,b are odd primes, e=+1 even/-1 odd, gain p-1, p>1+floor(8(Y+1)^(1/4)), and 4w>=p-1. All factors of H+-1 exceed (Y+1)^(1/4), and a,b>=(p-1)/8. Also p<=C3=(144(Y+1))^(1/3). These are the previous paper's deductions. A tuple (p,a,b,e) determines H, so it occurs at most once on a strictly increasing path. Upper bounds below may count extra arithmetic candidates; they do not assert clock realizability.

Use the previous uniform two-root sieve: for fixed integer coefficient L coprime to the small sieve primes, the integers v for which v and Lv+2e avoid all those primes have count O(N/log^2(2N)) in a length-N interval, by choosing z=floor(N^(1/12)). Here v is one of the three prime factors, L is the product of the other two, all factors exceed (Y+1)^(1/4), and N<=Y+1. Thus every sieve prime is smaller than all three factors and the roughness threshold for sufficiently large Y. If a variable range [1,N] is nonempty for actual candidates, N>(Y+1)^(1/4), so log N comparable to log Y. For fixed shift h>=1, prime pairs v,v+h with v in a dyadic interval [A,2A) of length A and both > (Y+1)^(1/4) have count O(J(h) A/log^2Y), where J(h)=product of odd prime l|h of l/(l-2), and sum_{h<=D}J(h)<=euler-number*D. Here all dyadic A are at least half (Y+1)^(1/4) and at most Y+1. The square case h=0 has count O(A/logY) by Chebyshev. All constants absolute, and both possible signs cost at most a factor two.

## 2. Co-factor pair gap

Let V_D be total type-III gain on 0<=b-a<=D, integer D>=0. Group a in dyadic bands A<=a<2A. For each fixed a,b, the selected p satisfies
    p <= T_A=min(16A+1,(Y+1)/A^2).
This follows from p<=8a+1 and pab<=Y+1. If T_A is too small there are no candidates. Otherwise the two-root sieve on p and abp+2e, summed over signs, gives gain <=O(T_A^2/log^2Y). The number of cofactor pairs in the band with 1<=b-a<=D is O(A D/log^2Y) by the shift average; a=b contributes O(A/logY). Therefore band gain is
    O(A T_A^2/log^3Y + A D T_A^2/log^4Y).
For dyadic A, sum A T_A^2 <= O(sum min(A^3,(Y+1)^2/A^3)) = O(Y): split at (Y+1)^(1/3), each side a geometric series. Consequently uniformly in D,
    V_D <= O(Y/log^3Y + Y D/log^4Y).                 (1)
In particular square cofactor gain is o(Y), and all cofactor gaps o(log^4Y) collectively carry o(Y) gain. Choose a sufficiently small absolute alpha>0; if total V3>=Y/132 (the previous global type-III branch), discarding b-a<=alpha log^4Y loses at most any prescribed fixed small fraction of Y, for all sufficiently large Y. This is independent of whether p is near a or b.

## 3. Selected factor cannot be too close to either cofactor factor

Let W_D be total type-III gain on min(|p-a|,|p-b|)<=D. For D=0, fix p and choose the other cofactor factor c, allowing p=c too. Its range is c<=N=(Y+1)/p^2; the two-root sieve on c and p^2 c+2e yields gain <=O(Y/(p log^2Y)). Sum over p in [(Y+1)^(1/4), C3], for which sum 1/p=O(1): in each dyadic band [A,2A) there are O(A/logY) primes and there are O(logY) bands. Thus W_0=O(Y/log^2Y).

For D>=1 and D<= (Y+1)^(1/4)/4, use dyadic bands A<=p<2A. Either cofactor factor c at distance h<=D from p lies between p/2 and 2p, so pc>=A^2/2. Count (p,c) using the shift sieve, both directions, O(A D/log^2Y) pairs with h nonzero. Remaining factor v<=2(Y+1)/A^2; sieve v and pcv+2e gives O(Y/(A^2 log^2Y)) possible v, and each gain <=2A. Each band contributes O(Y D/log^4Y). Sum O(logY) bands. Hence
    W_D <= O(Y/log^2Y + Y D/log^3Y).                 (2)
Uniform in this D range. For positive-gain type-III branch, choose small absolute beta>0 and discard min(|p-a|,|p-b|)<=beta log^3Y with arbitrarily small fixed-fraction gain loss eventually. In particular all repeated prime factors can be discarded at o(Y) cost, and the remaining three factors are pairwise distinct. None of (1),(2) excludes locally realizable repeated or close factors.

## 4. Factor-role capacities and polynomial cofactor diversity

For fixed smaller cofactor factor a, and fixed p, the remaining factor b<=N=(Y+1)/(pa). The two-root sieve gives count O(Y/(pa log^2Y)) and gain O(Y/(a log^2Y)). Since p<=8a+1, Chebyshev gives O(a/logY) possible p (also when a is large, since log a comparable to log Y). Summing shows total gain for a specified smaller factor is O(Y/log^3Y). The identical argument fixing the larger factor b uses p<=8b+1 and the variable a, so the same bound applies. Consequently any type-III subset carrying >=delta Y for fixed delta>0 contains Omega_delta(log^3Y) distinct smaller factors and Omega_delta(log^3Y) distinct larger factors. This does not assert high multiplicity of each such factor.

For fixed cofactor pair (a,b), selected p<=min(8a+1,(Y+1)/a^2)=O(Y^(1/3)) uniformly, by splitting a at (Y+1)^(1/3). The same two-root sieve on p gives total gain O(Y^(2/3)/log^2Y) per pair. Thus positive type-III gain requires
    Omega_delta(Y^(1/3) log^2Y)
distinct cofactor pairs (a,b), equivalently distinct semiprime cofactors q=ab by unique prime factorization (a<=b). For fixed (p,a), capacity O(Y/(a log^2Y)) <=O(Y^(3/4)/log^2Y) since a> (Y+1)^(1/4). Hence also Omega_delta(Y^(1/4)log^2Y) distinct ordered (selected p, smaller a) pairs, and same for (p,b). These lower bounds count one path only and hold for any positive-gain subset, including the gap-filtered one.

## 5. Near-upper-band multiplicity refinement

For fixed selected p, use a<=sqrt((Y+1)/p), a>=(p-1)/8, and a>(Y+1)^(1/4). Sum the preceding fixed-(p,a) capacity over these prime a. Dyadic prime counting gives
    V3_p <= O((Y/log^3Y)*(1+log^+((Y+1)/p^3))),
where log^+(x)=max(0,log x). Indeed the number of dyadic bands in the a interval is O(1+log^+((Y+1)/p^3)), and each band has reciprocal prime sum O(1/logY). For p>=Y^(1/3)/(log Y)^K (fixed K>0), this is O_K(Y loglogY/log^3Y), and for p>=gamma Y^(1/3), fixed gamma>0, it is O_gamma(Y/log^3Y).

Therefore if V3>=delta Y, for any fixed K>0 one of two regimes holds: (i) p<=Y^(1/3)/(logY)^K carries >=delta Y/2, in which case using sum(p-1)=O(Y^(2/3)/log^(2K+1)Y) and the previous per-label cap O(Y/log^2Y), there are Omega_delta,K(log^2Y) labels each with Omega_delta,K(Y^(1/3)log^(2K+1)Y) type-III occurrences; or (ii) the complementary labels carry >=delta Y/2, in which case there are Omega_delta,K(log^3Y/loglogY) labels each with Omega_delta(Y^(1/3)logY) visits. Proof in both cases: discard low multiplicities so their gain <=delta Y/4, then divide remaining gain by the corresponding per-label capacity. This sharpens the previous type-III multiplicity/diversity tradeoff but does not bound total label support from above.

## 6. Global consequence

Under finite twins, a canonical adaptive ray beyond the last twin center crosses every sufficiently large [X,16X], Y=16X. In the type-III branch V3>=Y/132, discard the narrow cubes from the previous paper (gain <=Y/264), and apply (1),(2) with sufficiently small alpha,beta to lose at most Y/1056 each. At least Y/528 gain remains, since Y/132-Y/264-2Y/1056=Y/528. On this subset:
    b-a>alpha log^4Y,
    min(|p-a|,|p-b|)>beta log^3Y,
    max(|p-x|,|a-x|,|b-x|)>sqrt(x)/200, x=(p+a+b)/3.
All three primes distinct. There are Omega(Y^(2/3)) such events, Omega(log^2Y) selected labels each Omega(Y^(1/3)logY) visits, Omega(log^3Y) distinct smaller and larger factors each, and Omega(Y^(1/3)log^2Y) distinct semiprime cofactors. The preceding near-upper-band refinement applies to this subset too. These are simultaneous necessary conditions for the composite branch. They do not rule out this branch, the small-prime concentration branch, or the prime-cofactor branch. In particular the previous conditional stopping theorem remains conditional.

## 7. Diagnostics and reproducibility

[Audit d2d59ce](https://github.com/tara-sooo/A166944-Lean/blob/d2d59cebafd2fd2614fd0e193d2b4711bdefe08b/research/min_direct_triple_factor_gap_audit.mjs), blob f81d507a1c0639fa55a922b06bc6ee76cdc48179, exact remote readback. Run node research/min_direct_triple_factor_gap_audit.mjs. Actual ECMAScript execution in tool runtime, not a separate Node process. Enumerated p and sorted (a,b) from first 15 primes >=5003 (last 5113), both signs, Y=133667977898, B=4838. For each candidate chose n first designated clock with n-w>=H/2 and w=ceil((p-1)/4), checked actual literal earliest GCD event. 3600 candidates, 567148 literal ticks, 240 actual qualified events from ABSTRACT plateau starts (not canonical ancestry), 50 independent factor-clock event-jump comparisons, 1088 roughness factor checks, 3360 small sieve-residue checks, 3600 dyadic capacity checks, 680 disjoint relaxed arithmetic jump intervals (not a single actual path). Among 240 actual hits: 43 square cofactors, 44 selected factor repeated, 159 all-distinct (categories overlap), 97 cofactor gap<=20, 139 selected-to-cofactor gap<=20. Example distinct p5003,a5009,b5023,e=-1,H125876515620,t62938264066,n62938265317,w1251, opposite H-1=3457*36412067. These are local witnesses, not counterexamples to the asymptotic gain bounds, which are paper deductions. No new canonical trajectory scan: previous scan found no type III under its bounded scales. No Lean verification or external novelty claim. Main and siblings unchanged.

Next: seek a genuine global obstruction to simultaneously realizing the high multiplicities and the polynomial diversity of cofactor pairs; pure sieve capacities still permit all three branches. The now-excluded near-factor regimes cannot carry positive type-III gain, but the imbalanced distinct-factor branch is open.
