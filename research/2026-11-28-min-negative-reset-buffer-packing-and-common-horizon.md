# Negative MIN: order-free reset-buffer packing, mixed-scale sieve, and separated common square-root age

2026-11-28 JST; Issue #10. Continue from 4f654dfe616a0e0d88048ecf5d67bbe68944d8ef. User goal 4.85, alternate trajectory-distribution route and continued GitHub persistence. Core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a (614 checked declarations) unchanged. This checkpoint removes the growing signed-word penalty from spatial collision bounds by counting full intervals around the first reset positions, improves the uniform logarithmic loss by averaging bad-prime factors, and uses the result at two different time scales. All asymptotic results below are paper deductions, not new kernel theorems or independent specialist verification. No new external literature used; the .295 analytic draft is not used.

## 1. Source population and three goals

Use the unconditional source-composite supply of e51533d section 4: at least a R/L² distinct canonical roots A=pv-1 in [R,2R], L=log R, with p,v primes 1 mod420, R^.198<=p<=R^.199, v>p, and pv-2 p-rough. Thus A+1 composite, qmin(A)=p. The actual first plus event is p at age (p-7)/2, destination x=p(v-1)=A-p+1, followed by 3 idle ticks to exactly birth(x) at age (p-1)/2. Unique factorization fixes p for each A. Denote this population F, N=|F|. Constants a>0 and the two exponents are fixed. The following are the new goals, and are proved below:
(A) retain >>R/L² roots with pairwise disjoint reset neighborhoods of radius J=const*L², all of whose even centers are non-twin, and follow all the actual paths through common age H~L² measured from the reset, with no spatial meetings. Most of this retained population completes a growing number of events during H. Their postreset paths subsequently cross assigned disjoint intervals of length J whose union has positive spatial density.
(B) at common original elapsed age T=ceil(8 sqrt(2R+1)), retain >>sqrt R distinct roots with pairwise disjoint entire actual visited position sets, without any restriction on event count or gain/time. The packing count at this scale is much smaller than R/L². No claim of non-twin endpoints in (B) unless assuming finite twins.
(C) quantify the tradeoff in (B) for all separation distances, rather than only short signed words. This is a different result from the previous k~log L/loglog L event-depth theorem, which retains the larger population but only for individually stopped prefixes.

## 2. Averaged singular factor, with elementary progression upper sieve

For nonzero n,n-2,n+2 integers of magnitude R^O(1), define
    F4(n)=prod_{ell>=11 prime, ell | n(n-2)(n+2)} (1-4/ell)^(-1).
Uniformly for a fixed polynomial-scale prime band Y<=q<=2Y with Y>=R^beta (beta fixed positive), and any integer shift b of polynomial magnitude, we claim
    sum_{q prime in band, q+b not in {0,2,-2}} F4(q+b)
        <<_beta Y/log Y.                                      (1)
The bound is uniform in b; the implied constant can depend on the fixed polynomial magnitude bound. It is an averaged upper bound, not an assumption of independence of prime factors.

For ell>=11, (1-4/ell)^(-1)<=1+8/ell, so expand the product majorant into squarefree d dividing n(n-2)(n+2) with all prime factors >=11, weight 8^omega(d)/d. The sum of terms d>Y^.5 is at most
    Y^(-1/4) prod_{ell|n(n-2)(n+2), ell>=11}(1+8/sqrt ell)
        <= Y^(-1/4) exp(O(sqrt L)).
Indeed the nonzero integer product has O(L) distinct prime factors; ordering them increasingly gives sum 1/sqrt ell=O(sqrt L) even without the PNT. This pointwise tail is polynomially small in R and negligible after summing over at most O(Y) integers q.

For d<=Y^.5, the condition d|(q+b)(q+b-2)(q+b+2) gives at most 3^omega(d) residue classes. A class not coprime to d contains no primes q>=Y>d. Each reduced class contains O(Y/(phi(d) log Y)) primes, uniformly: write q=q0+dm and apply the dimension-one elementary Selberg upper in a parameter interval of length X~Y/d>=sqrt Y. Sieve primes <=D=floor(X^1/12) not dividing d; the full Euler product gives log D, deleting primes dividing d loses at most the factor d/phi(d). The usual restricted-Euler-product argument with inclusion probability 1/ell and small fixed power cutoff produces G(D)>>log D*phi(d)/d. CRT remainder O(D^6) is negligible. This proves the required progression upper without a new prime distribution theorem. The resulting small-d sum is at most
    O(Y/log Y) sum_{d squarefree}24^omega(d)/(d phi(d))
      = O(Y/log Y),
since its Euler factors are 1+24/(ell(ell-1)). This proves (1). Partial summation or simply 1/q<=1/Y, followed by O(L) dyadic bands, gives
    sum_{R^beta<=q<=C R^gamma, q prime, q+b not in {0,±2}}
          F4(q+b)/q <<_(beta,gamma,C) 1.                       (2)
We will apply (2) both with fixed shift depending on another first label and with fixed shift depending on a low word; no dependence of b on the prime being summed is allowed.

## 3. Refined elementary upper sieve for four affine forms

Recall the diagonal Selberg argument of e51533d/4f654df. Suppose X>=R^delta with fixed delta>0 and four integral affine forms in a parameter interval of length X are rough to R^alpha, with fixed alpha>0. Suppose their coefficients and determinants are polynomial in R and nonzero. On primes ell>=11 not dividing their coefficient product or any determinant, density is 4/ell. Use D=floor(min(X^1/12,R^alpha/2)), supported weights |lambda_d|<=d and CRT remainder O(D^6)<=X^.5. Restrict the Euler product for G(D) to ell<=D^epsilon with fixed sufficiently small epsilon; independent inclusion probability 4/ell gives expected log modulus O(epsilon log D), so >=half the product mass has modulus <=D. The unrestricted product is >>L^4. Rather than deleting bad primes with a uniform (log L)^4 loss, retain their actual factor
    B4=prod_{ell>=11 bad prime}(1-4/ell)^(-1).
Thus count <= C X B4/L^4, absorbing X^.5 into X/L^4. All implied constants uniform with the fixed polynomial margins. For our forms the bad primes can be read directly from the slopes and undivided shifts, which is essential for (1)-(2).

A mixed-scale variant: the first two forms are R^theta-rough, and the last two only K0-rough, where K0 is a polylogarithmic power of R up to polyloglog factors, with log K0~log L. Choose D=floor(min(X^1/12,R^theta/2)). For ell<K0 use density 4/ell; for ell>=K0 use density 2/ell (omit all primes bad for any of the four forms in both ranges). Same Selberg diagonalization and remainder apply with these variable local densities. In the restricted Euler product ell<=D^epsilon the entire range ell<K0 is included for large R. By Mertens and (1-j/ell)^(-1)>=(1-1/ell)^(-j), j=2,4, unrestricted product is >> L²(log K0)²; expected log modulus still O(epsilon log D) using density<=4/ell. Deleting bad primes loses at most B4. Consequently
    count << X B4/[L²(log K0)²].                              (3)
This is a two-range elementary upper sieve, not a claim of a new mixed-scale lower bound. The small primes 2,3,5,7 are always omitted, a constant factor.

## 4. All-distance first-reset pair energy without word enumeration

We state this part for any subset of non-twin canonical R^theta-rough roots with actual first event plus and p in [R^theta,R^(.5-rho)], theta,rho fixed positive, theta<.5-rho. This includes F. For first destination x=A-p+1, p|x, and source forms (x+p)/p and x+p-2 are R^theta-rough. Take distinct source roots A,B with destination positions x,x+d, where d is any fixed integer |d|<=D0, D0<=R (positions are necessarily even). Their first labels are p,q.

If p!=q, x=0 modp, x+d=0 modq prescribe one CRT class modulo pq, interval length X~R/(pq)>=R^(2rho) (uniform constant factors). The four source forms, as functions of x on this class, are
    (x+p)/p, x+p-2, (x+d+q)/q, x+d+q-2.
Their undivided shifts are p,p-2,d+q,d+q-2. All are distinct because n=d+q-p=B-A is a nonzero multiple of 6, so n,n±2 are nonzero. In the CRT parameter the slopes divide pq, and all bad primes >=11 divide pq or n(n±2); this follows by multiplying each determinant by its two denominators, giving pq times the difference of its undivided shifts. The first labels are large, so their factors in B4 are bounded by an absolute constant. The refined upper in section 3 gives at most
    O(R/(pq L^4) * F4(d+q-p))
for fixed p,q,d, with uniform constants. Sum over q for each fixed p,d by (2), and sum 1/p=O_theta(1) over the polynomial prime interval. Thus for each fixed d the distinct-label contribution is O(R/L^4), WITHOUT a (log L)^4 loss. This is valid even when d is polynomial in R; the source difference is never assumed small relative to p,q.

For equal labels p=q, necessarily d is a nonzero multiple of p (d=0 would give identical source). Summed over all |d|<=D0, simply count all multiples x of p in the slab, at most O(R/p), and at most 2 floor(D0/p) other multiples. Thus the equal-label contribution is
    O(R D0 sum_{p>=R^theta}1/p²)=O(R D0/R^theta)
       = o(R(D0+1)/L^4).
No sieve needed for this contribution, and it vanishes if D0<R^theta. Therefore the unordered distinct-root near-pair count satisfies
    E(D0) := # {A!=B unordered: |x_A-x_B|<=D0}
             << R(D0+1)/L^4,  0<=D0<=R.                     (4)
Here D0 is a distance parameter, not a sieve level. We count coincident first destinations as pairs even when their arrival clocks differ. The proof ignores later histories entirely and controls their entire future displacement envelopes in section 7.

## 5. Positive-density disjoint non-twin reset neighborhoods

For any fixed 0<alpha<theta, put K=R^alpha. For a fixed even offset d with |d|<=4J, J=O(L²), count roots whose first destination x has qmin(x+d)>=K. The four forms
    (x+p)/p, x+p-2, x+d-1, x+d+1
are all K-rough, in one class x=0 modp. Their distinct shifts are p,p-2,d-1,d+1, since p≫J. Bad primes >=11 divide p or n(n±2) with n=p-d-1. Apply section 3 with X~R/p, then (2) summing over p with fixed shift -d-1. Thus the count for EACH d is O(R/L^4), and the number of roots whose reset neighborhood of radius 4J contains any even K-rough center is
    B(J) << R(J+1)/L^4.                                      (5)
This is an unconditional count for arbitrary rough plus-first sources; we have removed the previous loglog loss from the neighborhood theorem.

Now choose a sufficiently small fixed j0>0, depending on the lower constant a and the fixed constants in (4),(5), and set J=2 floor(j0 L²/2), a positive even integer for large R. Remove both roots of every pair in E(4J) and all roots in (5). The sum of these deletion costs is <=a R/(2L²) by choosing j0 small, then R large. Apply to F from section 1. Remain N1>=aR/(2L²) roots, their reset destinations at pairwise distance >4J, and every even site within radius4J of any such destination has qmin<K and hence is non-twin for large R. In particular NO initial source in F is in any of these neighborhoods, since those sources are R^.198-rough. The initial A is non-twin by forced composite. We need not prove a lower bound on the distance between original source centers: they are distinct and never visited by any of the postreset prefixes inside the clear neighborhoods.

For each retained root continue from its exact birth(x) reset at original age (p-1)/2. The checked canonical gain bound shows that for every common reset-relative age 0<=t<=H, with
    H=floor((J-6)/2),
its position is in [x-J,x]. Thus ALL actual positions visited by different paths (including original sources and their first destination) are disjoint through this common relative H. All these centers are non-twin. The time H~L² has a uniform lower, not merely an upper bound on a stopping time. Relative reset clocks differ, so this is not a common absolute clock. No event count cap has been imposed. In particular the disjoint union has at least N1(H+1)>>R physical-state incidences at these postreset ages, with no multiplicity across different roots or different ages (clock strictly increases).

Next, follow each same path until it first moves below x-J. While it stays within [x-J,x], every phase has full wait <2K and every firing moves at least 2. Hence it crosses below x-J within <=2K(floor(J/2)+1) postreset ticks. All pre-crossing visited centers are non-twin and pairwise disjoint across different roots; the crossing LANDING center is excluded from this claim. Each such actual path crosses every assigned unit spatial cut x-J,...,x-1 (a jump may skip intermediate centers, but it crosses those cuts). These cut sets are disjoint because the reset centers are separated. The union has size exactly N1 J>>R, a positive fraction of the slab, not merely the number of distinct terminal cuts. Take alpha=.1 for F; the original age of each such crossing is <=R^.199 for sufficiently large R, since reset age <=R^.199/2 and O(R^.1 L²)=o(R^.199). This strengthens the previous buffer crossing with J=L^.4 or L^(2-eps), and uses arbitrary subsequent labels, not a word cap. We emphasize that swept CUTS are not visited centers; the number of visited positions is not asserted to be a positive fraction of R.

## 6. Actual growing event count at the common logarithmic relative horizon

The separation theorem alone could leave the entire H idle. Use the mixed sieve (3) to exclude this possibility for most of the reset population. Let l=log L, l2=log l, l3=log l2. Fix 0<c<2 and set k=floor(c l2/l3) (for sufficiently large R), Z0=2H+7, K0=H/(2k). Thus k→infinity, log K0~2 log L, Z0=O(L²), and k is a slowly growing triple-log-scale depth (k~c logloglog R/loglogloglog R). This is smaller than the previous k~loglog R/logloglog R, but now at a guaranteed COMMON H~L².

If fewer than k events complete between reset and age H, the completed waits plus final idle split H into at most k intervals. At least one length is >=H/k. The actual calendar gives each completed full wait <=2qmin at its source and each final idle <2qmin, so that phase's center y has qmin(y)>=K0. It is reached by a signed word of length j<k following birth(x). The checked age bound gives all labels r<=Z0. Its cumulative gain g is a nonnegative even integer; y=x-g. The exact incoming pins of 4f654df give one CRT class if consistent,
    y+g=0 modp, y+g-g_i=1-s_i mod r_i,
    M=p * M_low, M_low=prod_{distinct r in word}r.
All labels in the word are below p, and M_low<=Z0^k=R^o(1); hence X~R/M is polynomially large uniformly. The forms
    (y+g+p)/p, y+g+p-2, y-1, y+1
have the first two R^theta-rough (theta=.198) and last two K0-rough. Their bad-prime product is bounded in factor B4 by
    C F4(p+g-1) prod_{ell|M_low, ell>=11}(1-4/ell)^(-1).
To check, coefficients divide M, denominators divide p; determinants after multiplication by denominators are M times the differences of the four undivided shifts. All shifts distinct for large R, since p≫kZ0. Other than 2, these differences divide the product of p+g-1 and its ±2 shifts. The low-modulus factor is <=(k+1)^C by ordering its at most k distinct primes and summing their reciprocals; this is l^o(1). No factor depending on the total number of possible small primes is introduced.

For fixed signed word, apply (3), then sum over p using (2) with shift g-1 independent of p. Bound for that word:
    O(R/[M_low L²(log K0)²] * (k+1)^C).
As in 4f654df the reciprocal weight of all signed words of length j is <=[2(H_Z+j)]^j, H_Z=sum_{3<=r<=Z0 prime}1/r=O(log log Z0)=O(l2). Repeated labels pay once in M_low. Summing j<k costs at most l^(c+o(1)): log(2(H_Z+k))<=log l2+O(1), and k~c l2/log l2. Thus the total number of reset roots with fewer than k completed events is
    B_few << R/L² * l^(-2+c+o(1)) = o(R/L²), c<2.           (6)
Here the two different sieve thresholds and averaging of F4 are both needed: using all forms only to K0 loses the L² source saving; using the previous uniform (log L)^4 bad-prime loss overwhelms the new (log K0)^2 gain. The proof counts an actual necessary phase from the partition of H, not assumed typical waiting times. It counts the final incomplete phase as well. Remove these o(R/L²) roots from the retained population in section 5. Still >>R/L² disjoint actual non-twin histories through H, each with at least k true additional events, with at least >>R k/L² distinct visited positions (not merely swept cuts). At the same H all such paths remain spatially within J by the exact height bound. This is unconditional and uses no independent-event model.

## 7. Order-free tradeoff and common original square-root elapsed age

Use (4) on F without the rough-neighborhood exclusions, now at any distance D0 between 1 and R. Make a graph on N roots, joining pairs counted in E(D0). The elementary independent-set bound alpha(G)>=N²/(N+2E) follows by random permutation selecting vertices earlier than all neighbors, then Cauchy-Schwarz. Since N>=aR/L², (4) implies a subset of roots with pairwise reset-center distances >D0 of size
    >> R/(L²+D0).                                            (7)
The inequality N²/(N+2E) is increasing in N and decreasing in E, so no additional upper for N is needed. For D0≫L², this reaches the natural packing order R/D0 of disjoint spatial intervals. It is not a bound on all actual collisions; the price of interval separation is reduction of population. For D0=O(L²), (5)-(6) gave the much stronger properties of almost-full-density retained population, clear neighborhoods, and event depth at a common small H.

For the square-root target let T=ceil(8 sqrt(2R+1)), D0=4T+20 (<=R eventually). By (7), retain >>R/T=>>sqrt R roots. Each first reset occurs by age R^.199/2=o(T). The entire original canonical history of A through COMMON ORIGINAL ELAPSED AGE T stays inside [A-2T-6,A] by the checked canonical gain bound. Because A=x+p-1 with p<=R^.199, this is contained in [x-2T-6,x+p-1], of length at most 2T+6+R^.199. Those envelopes for distinct retained reset centers are disjoint by D0 separation. Hence the entire actual visited position sets through age T are pairwise disjoint across roots, independent of their later labels, waits, height, gain ratio or whether a twin is reached. This includes all their initial sources, resets and postreset histories. They each have postreset elapsed time T-o(T). In particular at age T there are >>sqrt R distinct actual endpoint positions. If twin centers are finite, these histories for sufficiently large R necessarily remain non-twin because all centers stay >=R-2T-6. Without that hypothesis no non-twin guarantee or twin abundance is asserted here.

This is a common ELAPSED age theorem, not a theorem of all roots sharing the same signed clock or the same observation-window retirement. In particular separated roots at this scale may lie in different observation windows. The lower of >>sqrt R roots is not the desired >>R/L² at the common square-root horizon; the disjoint interval method only gives R/T at this scale. While the theorem removes ALL word-count costs for a sparse subpopulation, it has not solved the density-scale coalescence problem of the project or the .40 gain criterion. The next meaningful barrier is to permit overlapping displacement envelopes and bound actual contacts within them, instead of insisting on interval separation. Use the averaged near-pair estimate (4) as a local initial pair-energy input, then analyze actual common-clock first contacts with the height pins, aiming to recover logarithmic-density rather than spatial-packing lower. Previous .295 proof draft remains unchanged, no new 4.85 claim.

## 8. Verification and source record

Audit research/lean/negative_min_reset_buffer_packing_audit.mjs @5bfef1cce7337530e016dabae460201584061c38, blob 24df6a5415cd7946d216ab4a3dc3ee2931b36960, executed ECMAScript and exact pinned remote readback. Four finite slabs R=12000,48000,192000,768000. Use finite proxy p,v=1 mod12, target directly 11-rough, p>max(4J,K), J=4,6,10,16, K=17,23,31,43, H=floor(J/2) for proxy; not the asymptotic J, K or exact H=floor((J-6)/2). The proxy H envelope [x-J-6,x] stays inside the clear radius4J. 423 actual reset examples, 56364 initial/reset ticks, 24439 shifted roughness checks, 40572 nonzero determinant checks including long-offset pairs, 9563 checks of the two/four residue counts at individual good primes, 9998 exact expansion-majorant checks. Clear buffers retained only 8 finite roots (0,2,3,3); these finite samples are far from the asymptotic regime and do NOT test the claimed retained fraction. 45 common short-horizon ticks,5 events; 12 subsequent crossing events,69 ticks,90 distinct assigned cuts verified. The growing-depth asymptotic (6) is an analytic argument, not inferred from these small samples. 
At T=1240,2479,4958,9915 (square-root formula), 5652 near pairs including324 same-label pairs with positive offset multiple p. Greedy distance selection (equal-length interval packing) 34 roots total, 2,4,9,19 by slab, independent-set lower checked at finite sizes; independently trial-factored literal recurrence against factor-calendar 709 completed events,245403 actual ticks including final tails,743 visited-position checks, all pass. The actual finite samples may reach known twins. No evidence of a no-twin asymptotic universe. The audit checks local arithmetic and actual paths, not the proof of averaged sieve estimates.
Analytic inputs are the same elementary diagonal Selberg and Mertens arguments developed earlier (e51533d/4f654df), the previously derived unconditional BV linear-sieve source family e51533d section 4. No new external theorem invoked. No new Lean run, independent human review or modification of main/siblings. 4.85 remains unmet: the square-root theorem has sparse population only, and the terminal roughness/low-gain obstacle persists.
