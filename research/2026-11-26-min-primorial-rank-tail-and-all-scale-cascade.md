# Bounded-cofactor record rank tails and an all-scale relay cascade

2026-11-26 JST. Continuation of cd8164531eb2242232833a3123f5d4caa625b038, research/2026-11-26-min-primorial-multiscale-relay-cascade.md. Paper deductions and separately executed finite arithmetic audit. No Lean verification, novelty claim, or proof of twin infinitude.

## 1. Small cofactor classification at a large non-doubling record

Use the ordinary uncut universal offset MIN, with envelope u/2<=v<=u+1, next time n=v+w<=u+3, update U=u+p-1,V=n. Let u=kp+e where e=+1 for minus clock, e=-1 for plus clock, and k odd. Assume k>=3, p>max(k,5), so the selected label is a proper prime factor of a composite neighbor. Every odd factor of that neighbor has a clock with period 2q. A factor of k gives w<=2k. Write n=a p+c, c=0 for minus, c=2 for plus. The integer a is even for minus, odd for plus. The bounds n>v>=u/2 and n<=u+3 give (k+1)/2<=a<=k-1 for minus. For plus they give (k+1)/2<=a<=k, but a=k is forbidden: n=u+3 is a simultaneous clock of a smaller prime factor of k, so p would lose the tie. Hence plus has a<=k-2. These inequalities use p>=7.

In particular k=3 forces the minus clock and a=2. Thus

    u=3p+1, v=2p-w, 1<=w<=6,
    (U,V)=(4p,2p), d'=0.

A non-doubling first record p>r=X/2+1 reached at u<=A0 X (fixed A0) always has bounded k<=2A0+1 for large X, and k>=3: k=1 on the minus side cannot fire in the envelope for u>=6, and k=1 on the plus side is precisely a doubling. Thus the cofactor classification applies asymptotically uniformly in such a block. It does not assume that a false record actually exists.

## 2. A rational-line obstruction to a short high-label predecessor tail

Fix an event from section 1. Use Z=a u-k v and C=2(a+k). At its pre-state,

    Z=a e+k(w-c),   0<|Z|<=a+k(2k+2).

Nonzero follows since 0<a<k and e=+/-1. If this state is an arrival from a preceding event with label q, then q|gcd(u,v) for even v, and q|gcd(u+2,v-2) for odd v. Therefore

    q|Z (v even),   q|Z+C (v odd).

The odd case cannot have Z+C=0 since k is odd and u is even, so Z+C is odd. The only exceptional case is even v and Z=0. Away from that line,

    q<=M:=|Z|+C.

For k=3 one has a=2, Z=2+3w<=20, C=10, so the immediately preceding label is <=30 (if the pre-state is not the seed). The statement needs no distribution assumption on primes. The example (u,v)=(52,33) with p=17,w=1 is an actual local clock control of the non-doubling cofactor-3 event, not asserted reset-reachable.

For a predecessor (x,t) of (u,v) with label q and wait W, x=u-q+1, t=v-W, W<=2q. Set Z_old=a x-k t. Then

    Z_old=Z-a(q-1)+kW,
    |Z_old|+C <= H M, H=1+a+2k.

(The bound |Z_old-Z|<=a(q-1)+2kq suffices.) Thus along j reverse steps which do not encounter the singular line Z=0 at even v, all labels and total backward physical gain are O_k(H^j), and the same bound holds for |Z|+C. The actual initial reset (X,X/2+3) has Z_seed=(a-k/2)X-3k>=X/2-3k. Since a,k are bounded and k odd, this is macroscopically separated from the record corridor.

Consequently for any fixed 0<theta<1 and large X, every bounded-ratio non-doubling first record has the following alternative: within the final floor(theta log X/log H) preceding events it encounters the exact rational line a u=k v at even time; or the entire tail of that length exists and has all labels and total gain O_{A0}(X^theta). In the latter case it cannot already have reached the reset. The corridor is narrow in the linear coordinate as well. At a rank state itself one may write u=(k/g)t, v=(a/g)t for g=gcd(a,k), and an even arrival label divides t; the nonsingular estimate does not control that label. This identifies the singular-line ancestry as a separate obstruction. It does not exclude rank states or the long small-label tail.

## 3. Include all upward events, not just lag descents

Call an event upward when delta d=2w-(p-1)>0. In the pre-record portion of an arbitrary integer reset ray, all events are non-twin: at a twin center u>=X the selected label would be u+1>r. Since some neighbor is composite and all its prime factors have competing clocks, w<=2 sqrt(u+1). Upward events therefore have p-1<4 sqrt(u+1); all prime factors q of either neighbor satisfy q>=w/2>(p-1)/4. In a bounded-ratio segment all upward labels are O(sqrt X).

If the first record p>r is not at a twin center, its own wait is <=2 sqrt(u+1). Nonnegative post-deficit implies

    d_pre >= p-1-2w >= r+1-4 sqrt(A0 X+1).

In particular d_pre-6>=X/4 for all sufficiently large X. Since each positive increment is <=3p+1<=5(p-1), the total physical gain of upward pre-record events is at least X/20. Thus this population covers BOTH false-double and false-non-doubling alternatives, even when the latter has no macroscopic net lag collapse. The new bounds below apply to any marked subset of this upward population.

## 4. All-scale mixed CRT and sparse cascade

The bare CRT part of the previous mixed-scale result does not use descent roughness. Consider marked events with labels p>=7 and p<=C sqrt X for fixed C, chronological pairs p,r, intervening physical gain E, weights min(p-1,r-1), sum W, disjoint total relay R. For 0<beta<=1/2, short means E<=beta min(p,r). The repeat toll forces p!=r for short pairs. For fixed p,r,E and the two signs, source u is in one class modulo 2pr, so the count in a bounded-ratio horizon interval is O(1+X/(pr))=O(X/(pr)). This remains valid at and above constant multiples of sqrt X, since pr=O(X). Long-pair weight is <=R/beta.

Let P be the set of distinct marked labels. Sum only over p!=r, or over actual ordered transition types if these are available. Define m=min(p,r), M=max(p,r). The exact accounting gives

    W/X <= C1 (beta K0 + E0)+R/(beta X),
    K0=sum m/M, E0=sum 1/M.

This is the bare CRT bound in the preceding note, here used with the larger upward population, without the sub-square-root hypothesis. If P has J occupied dyadic bands with lower endpoints T_j and S_j<=C0 log^2(2T_j), minimum T_*, maximum T_max, then

    K0=O(J log^4(2T_max)),
    E0=O(log^4(2T_*)/T_*).

Indeed each ordered band pair contributes to K0 at most O(S_i S_j 2^(-|i-j|)); sum the geometric kernel using 2ab<=a^2+b^2. For E0 the contribution with j>=i is O(log^2(2T_i) log^2(2T_j)/T_j). For fixed j sum over i from the minimum occupied dyadic index to j, getting O((1+j-j_*) log^4(2T_j)/T_j). Summation over j>=j_* converges with the claimed bound by geometric decay, independently of J. These bounds do not assume that the occupied bands are adjacent. Write Kbar=J log^4(2T_max), eta=log^4(2T_*)/T_*; J>=1. Optimizing beta (clipped at 1/2) gives W/X<=C2(eta+sqrt(Kbar R/X)), with constants uniform over the bands. The clipping case follows since R/X is bounded on the whole segment.

Apply this independently to each suffix of the occupied bands in increasing scale order. Let G_j be marked physical gain in band j, R0 total nonmarked gain on the segment. The actual relay of suffix j is <=R0+sum_{i<j}G_i, not a sum across suffixes. As in the previous note G_j<=3W_j+2T_j. With s_j=R0/X+sum_{i<=j}G_i/X and a0=R0/X+eta+T_max/X, obtain

    G_j/X <= C3 (eta+sqrt(Kbar s_(j-1))+T_max/X).
    sum_j G_j/X <= C4 Kbar (2a0)^(2^(-J))        (a0<=1/2).

For the second line set y_j=s_j+a0; since the physical total is bounded, y_j<=C5 sqrt(Kbar y_(j-1)), y_0<=2a0, and iterate. Constants are independent of J. No overlapping relay totals are added.

For example if T_*>=X^epsilon, R0/X=O(X^(-c)) for fixed positive epsilon,c, and J<=(1-delta)log_2 log X for fixed delta>0, then a0<=X^(-c') for some c'>0 and Kbar=O(log^5 X). The right side tends to zero because 2^(-J)log X>=(log X)^delta. Therefore such sparse marked bands cannot carry macroscopic physical gain, even when some are at the square-root scale. Applied to section 3, a bounded-ratio false-record prefix cannot have this structure with polynomially scarce nonmarked gain. It would contradict the upward gain lower bound X/20 (unmarked upward gain is <=R0). This is a conditional exclusion of a larger class of false records than the lag-only cascade; dense support, small-scale labels and substantial relay gain remain possible. In particular the stronger relay scarcity hypothesis is needed to absorb the polylogarithmic cost of the bare CRT estimate; no assertion of an all-scale extension with merely R0=o(X) is made.

## 5. Near-square-root actual transition graph, even for dense support

Consider one marked band [T,KT] with T comparable to sqrt X and fixed K. Suppose its marked physical gain is >=rho X for fixed rho>0. Then W>>X since min(p_i-1,p_(i+1)-1) is comparable to each marked gain and the endpoint contributes O(T)=o(X). Let A be the number of DISTINCT actual ordered transitions (p,r) with p!=r among consecutive marked events (not the product of source and target supports).

For integer 0<=B<T-3, short pairs with E<=B have p!=r and a fixed (p,r,E,e,f) has O(1) candidates by CRT. Consequently their total weight is O(T A(B+1)). The long pairs have weight O(T R/(B+1)). Thus

    W << T A(B+1)+T R/(B+1).
    (A+1)(1+TR/X) >> T.

To derive the second line take B+1 a sufficiently large fixed multiple of 1+TR/X, so the long contribution is smaller than half the assumed macroscopic lower bound; if this cutoff is too large for B<T-3, the asserted conclusion already follows from 1+TR/X>>T. This estimate depends on the actual transition graph, not on S^2 as a substitute. If R=O(X/T), then A>>T. Even when the entire available prime band is used, its number of labels is O(T/log T) by Chebyshev, so some label must have Omega(log T) distinct outgoing target labels. A graph with uniformly bounded outdegree cannot carry such a near-square-root macroscopic population at this relay scale, no matter how dense its vertex set is. This is a necessary condition, not an ancestry-derived degree upper bound.

## 6. Executed audit

Source research/min_primorial_rank_tail_audit.py, commit 0b9640217245689a9721d8ce1a2271f59abc8d71, verified blob 5d3d37329a5f9320cbbd665457ebb910c9ce88db equals the locally executed source. Requires SymPy and sibling min_primorial_record_supply_audit.py. Run:

    python research/min_primorial_rank_tail_audit.py 100000

Executed on 16,666 integer resets r=7,13,...,99997 through their first label >r inclusive. Output:
- 334337 events, 16666 first records, zero non-doubling first records.
- 190400 pre-record upward events passed the competing-clock and scale bounds.
- 24840 short chronological upward pairs (p>=7, E<=min(p,r)/2), 24581 distinct ordered types counted separately by seed, 24836 fixed-tuple multiplicity checks, 13216 band-kernel comparisons.
- 30 actual reset-ray events with proper cofactor 3<=k<=19 and p>max(k,5), not first records. Their cofactor counts: k=5:1; 7:1; 13:6; 17:20; 19:2. Total 209 nonsingular reverse edges, 27 traces reaching the seed (others have empty ancestry); no singular-line hit recorded in these traces. All congruence and growth checks passed.
- 11 additional locally constructed cofactor-3 events (not claimed reset-reachable), giving 41 bounded-cofactor controls in total. Example (52,33,p=17,w=1). All passed the classification. The data include no false first record and hence do not directly demonstrate a long rank tail from a false first record.

## 7. Open target

The two false-record modes can now be treated through upward supply without a lag-collapse premise. Non-doubling records also have a bounded-cofactor terminal corridor with a singular rational-line exception. Neither result bounds the full path from an integer reset, nor establishes the existence of arbitrarily large seeds satisfying the earlier short-displacement certificate. An unconditional bound on relay gain/transition diversity or exclusion of the singular-rank ancestry would be a substantive further step; finite favorable trajectories are not a proof of any such bound.