# Dimension-two upper sieve for certified MIN returns

Continuation of the independent direct-arithmetic branch. Prior global roughness note restored at [bfdd0f9](https://github.com/tara-sooo/A166944-Lean/blob/bfdd0f957aa1b17777ae67c2fa3c596d106daa21/research/2026-11-26-min-direct-global-roughness.md). This strengthens the global necessary conditions without assuming a short return word or a reset. The only additional number theory is an elementary upper-bound sieve, proved below. No new assumption about prime pairs or their distribution; not a proof of twin infinitude or A166944.

## 1. A self-contained upper sieve

Let I be an interval of N consecutive integers. For each odd prime l<=z forbid rho(l) residues, with rho(l) in {1,2}. For squarefree odd d built from these primes define rho(d)=product rho(l), g(d)=rho(d)/d, h(d)=product (1-g(l))/g(l); all functions have value1 at d=1. Write D for the downward-closed set of odd squarefree d<=z. Let A_d(n) be 1 if n lies in a forbidden residue at every l|d, 0 otherwise. In particular A_1=1 and A_d A_e=A_lcm(d,e). CRT gives sum over n in I of A_d(n)=N*g(d)+O(rho(d)), with absolute error <=rho(d).

For real weights lambda_d with lambda_1=1, the surviving count is <= sum_I (sum_D lambda_d A_d(n))^2. Its main quadratic form is
    Q(lambda)=sum_{d,e in D} lambda_d lambda_e g(lcm(d,e))
             =sum_{r in D} h(r) (sum_{d in D:r|d} lambda_d g(d))^2.
Indeed g(lcm)=g(d)g(e)/g(gcd), and 1/g(gcd)=sum_{r|gcd}h(r) by multiplication. Set G(z)=sum_D 1/h(r) and y_r=mu(r)/(h(r)G). Invert the finite divisor sum by lambda_d*g(d)=sum_{r in D:d|r}mu(r/d)y_r. This has lambda_1=1, since sum_D mu(r)y_r=1. Its Q=1/G. For squarefree d|r, mu(r/d)mu(r)=mu(d), so
    abs(lambda_d) <= 1/(g(d)h(d)) = product_{l|d} 1/(1-g(l)) <= d.
The inequality follows since sum_{d|r}1/h(r) <= G/h(d), using r=d*s, gcd(d,s)=1. Each prime factor l>=3 and rho(l)<=2 gives 1/(1-g(l))<=l. Consequently the total error is <=(sum_{d in D} abs(lambda_d)rho(d))^2<=z^6, since rho(lcm)<=rho(d)rho(e), rho(d)<=d and sum_{d<=z}d^2<=z^3. The exact finite bound is
    S(I,z) <= N/G(z)+z^6.                              (1)

When rho(l)=2 everywhere write G_0(z). Then
    G_0(z) >= sum_{odd squarefree d<=z} 2^omega(d)/d
             >= (1/6) H_odd(floor sqrt(z))^2
             >= (log z)^2/96.                          (2)
For the middle bound, consider ordered odd a,b<=T=floor sqrt(z) with weight1/(ab). Exclude a divisible by l^2, b divisible by l^2, or both divisible by l. Their combined weighted mass for each odd prime l is <=3 H_odd(T)^2/l^2 by scaling. Sum over all odd primes: sum_{odd n>=3}1/n^2<=1/9+ integral_1^infty (2x+1)^(-2) dx=5/18. At least1/6 of the mass remains, on squarefree coprime pairs. Each d=ab<=z is counted at most2^omega(d) times. Finally H_odd(T)>=H_T/2>=log(T+1)/2>=(log z)/4. This proves (2), without PNT or Mertens.

If the forbidden residues are 0 and -h0 modulo l for a positive integer shift h0, then rho(l)=1 when l divides h0, 2 otherwise. Define J(h0)=product_{odd prime l|h0} l/(l-2). Splitting the squarefree summation in G_0 according to factors dividing h0 gives
    G_0(z)<= J(h0)*G(z).
Indeed the terms coprime to h0 have their original weights in G, while summing the complementary prime factors without the product cutoff multiplies by at most J(h0). With z=floor N^(1/12) (small N handled by a larger absolute constant), (1)-(2) give
    S(I,z) <= K N/log^2(2N)                             (3)
in the two-distinct-residue case, and <=K J(h0) N/log^2(2N) in the shift case, for one absolute K. Here z^6<=sqrt(N); log z comparable to log N for large N. No claim that K is the optimal sieve constant. The bound holds on an arbitrary translated interval, not only [1,N].

The shift product has bounded average:
    sum_{1<=h0<=D} J(h0)<= e D.                         (4)
Expand J(h0)=sum_{d|h0, odd squarefree} product_{l|d}2/(l-2), then use floor(D/d)<=D/d. The resulting Euler product is <=exp(sum_{odd l>=3}2/[l(l-2)])<=e because the sum over all odd integers telescopes as 1/(l-2)-1/l. This is an elementary bound, not a prime-pair asymptotic.

## 2. Application to certified events

As in the previous note, a certified large event in a block with all pre-horizons <=Y is defined by
    B=1+floor cbrt(512(Y+1)), C=floor sqrt(Y+1),
    p>B, 4w>=p-1.
Every prime factor of H+-1 is >(Y+1)^(1/3), the selected neighbor H-e=pq has prime q>=p, the opposite neighbor is pq+2e and is prime or semiprime. In particular q and pq+2e avoid 0 mod every odd prime l<=z whenever z<=(Y+1)^(1/3) and l<p. For fixed p and sign e, the two forbidden q residues are distinct: 0 and -2e/p mod l. This is precisely the two-residue sieve, not a twin-prime hypothesis.

For fixed p, q<=N=floor((Y+1)/p), and N>=p>B. The cutoff z=floor N^(1/12) is much smaller than p and (Y+1)^(1/3) for large Y. Also log N is between fixed positive multiples of log Y, since p<=C and p>B. Summing over the two signs gives
    number of certified occurrences of p <= O(Y/(p log^2 Y)),
    certified gain on p <= O(Y/log^2 Y).                (5)
The counts are of events in one contiguous path, not all roots. Each occurrence of the same p>=5 has strictly increasing q: after its jump the horizon grows by at least p-1 before the next such occurrence, while the sign changes by at most2. So no multiple counting of the same q is needed. In contrast the previous capacity bound based solely on prime q was O(Y/log Y) for gain.

The same argument applies with q fixed and p varying: take N=min(q,floor((Y+1)/q)). If there is any certified event on q then N>B, so log N comparable to log Y. Both p and qp+2e avoid the sieve residues; distinct p label choices count each physical event at most once for fixed q, by the previous strict monotonicity. Thus the total certified gain associated to one cofactor q is O(N^2/log^2 Y)<=O(Y/log^2 Y), uniformly. This observation does not require that the cofactor be a selected label anywhere else.

## 3. Stronger global alternative

Recall the preceding interval theorem. For a canonical ray with H0 fixed, in a crossed [X,16X], Y=16X, and X>=max(H0,256), either small labels p<=B have gain >=Y/88, or certified large events have gain >=Y/88. This follows from the elementary wait/envelope inequality 11(U+V)>=G-2d_start>=Y/4. Under finite twins every canonical adaptive ray starting beyond the last twin center crosses all such windows.

Small alternative unchanged: some p<=B is used Omega(Y^(1/3) log Y) times, by A(B)=sum_{odd prime p<=B}(p-1)=O(Y^(2/3)/log Y).

In the certified alternative, A(C)=O(Y/log Y). Discard labels with fewer than m=Y/(176 A(C)) certified events. Their gain is <=Y/176; the remaining gain >=Y/176. Each surviving label carries <=O(Y/log^2 Y) by (5). Therefore in EVERY such window either the small alternative holds or there are
    Omega((log Y)^2) DISTINCT selected primes,
    each with Omega(log Y) certified occurrences.      (6)
Moreover their associated prime cofactors include Omega((log Y)^2) DISTINCT primes, by the symmetric capacity bound in section2. This is a lower bound on the number of distinct cofactors, not on each cofactor's multiplicity. The original (weaker) logarithmic label-diversity theorem is thus improved by one full log factor, with no PNT. As usual both alternatives can hold.

## 4. Certified events near the square boundary cannot carry the large alternative alone

Define the diagonal gap h0=q-p>=0 at a certified event. For h0=0, the total gain over a path is at most A(C)=O(Y/log Y): each label p can occur with q=p at most once. For h0>=1 and fixed h0, p and p+h0 are both prime and greater than B, and p<=C. Sieve p in [1,C] with forbidden residues 0 and -h0, choosing z=floor C^(1/12) below B. Equation (3) in the shift case bounds the number of candidate p by O(J(h0) C/log^2 C). Both signs together give at most twice this count; in fact a p,q pair cannot recur on one path. Each event gains <=C. By (4), for every integer D>=1,
    gain of all certified events with 0<=q-p<=D
        <= O(Y/log Y + Y D/log^2 Y).                   (7)
This counts prime pairs, not just consecutive primes, and does not assume finite twins. We do not even need the opposite-neighbor roughness for this particular bound. The constant is absolute, uniform in D. For D=o(log^2 Y) this is o(Y). More quantitatively choose one sufficiently small absolute alpha>0 so the right side for D=floor(alpha log^2 Y) is eventually <=Y/176, using the absolute constant in (7). No numerical alpha is claimed. In the large alternative there remains >=Y/176 certified gain on events with q-p>D. Discard labels with fewer than Y/(352 A(C)) such remaining events; at least Y/352 gain remains. The same (5) gives (6) and the distinct-cofactor bound, now with EVERY counted event additionally satisfying
    q-p > alpha (log Y)^2 - 1.
Equivalently one can lower alpha slightly and omit the -1 for sufficiently large Y. So very near-square events (q-p bounded, or even o(log^2 Y)) cannot by themselves account for the required certified gain. This does NOT say that an unbounded path cannot also contain near-square events or twin witnesses, nor that near-square returns are impossible. It is a global obstruction to treating bounded-gap cofactor events as the principal carriers of horizon gain.

## 5. A local crowding bound on repeated certified p visits

For a fixed p in the certified range of a block, let m>=1 of its certified occurrences have cofactor span q_max-q_min=L-1 (including all integers between them). Apply (3) on that translated interval of length L, with z=floor L^(1/12) (use a large absolute constant for small L). Because L<=floor((Y+1)/p) and p>B, the sieve primes are still below p and the roughness bound. Thus
    m <= O(L/log^2(2L)).
As distinct q imply m<=L, this forces
    L >= Omega(m log^2(2m)).                           (8)
The associated pre-horizon span is >=p(L-1)-2. In particular a rich label with m>=c log Y has pre-horizon span Omega(p log Y (log log Y)^2) as Y tends to infinity. This refines the earlier same-label linear spacing bound without assuming finite twins or equal adjusted deficit. It says only that a large collection cannot be too closely packed, not that each successive q pair has a large gap. It neither forces a gap2 pair nor excludes one.

## 6. Verification and persistence

[Exact audit 6bb96a4](https://github.com/tara-sooo/A166944-Lean/blob/6bb96a43217ef06ef08b26868c868370084dd018/research/min_direct_global_sieve_audit.mjs), blob 1c7c09b4344df489d8865af34a22ed2d0f2d903a. Exact remote readback. Actual ECMAScript execution: 270 configurations (z=3,5,7,11,17,23,31,43,61; interval lengths100,1000,10000; fixed p/sign and positive shift cases), 2,730 weights and 43,350 quadratic summands, 999,000 integer residue checks. BigInt integer-scaled rational weights check lambda1, diagonalization, weight/error bounds, pointwise majorant, actual interval bound, harmonic-pair lower bound, and degenerate-shift comparison. Five bounded singular-product-average checks (display/comparison there uses floating point; (4) is proved exactly above). All passed; finite diagnostic is not empirical evidence for the unbounded asymptotic. Run from repository root:
    node research/min_direct_global_sieve_audit.mjs

Previous global note and both companion artifacts recovered with exact remote readback: note bfdd0f957aa1b17777ae67c2fa3c596d106daa21, audit 50a7a70259647c7be98bc7b628d2c434c5dd322d, results 64cd77e97c6c9f89b9ec481aaa9a6c6e3601e92b. No new trajectory scan is claimed this round; use the previous 3,636,351-event diagnostics for the underlying clock theorem. No Lean executable/formal verification. No web research or external novelty claim. Main and sibling branches unchanged.

## 7. Remaining problem

If twins are finite, all sufficiently large canonical rays are infinite, so the enhanced dichotomy holds throughout each. To obtain a contradiction it is still necessary to rule out the small-label concentration, or to use the actual clock/phase coupling across the many distinct repeated large prime labels and prime cofactors, not just count admissible prime pairs. The sieve bounds constrain every possible realization but do not force twin cofactors. In particular it would be incorrect to infer an unbounded family of minimal returns from (6). The next useful question is whether a single path can sustain the required rich-label set simultaneously with the local crowding bound (8) and phase congruences.
