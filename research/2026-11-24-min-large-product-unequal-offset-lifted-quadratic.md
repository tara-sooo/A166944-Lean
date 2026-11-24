# Unequal-offset large-product asynchronous matching: quotient determinant and lifted quadratic classes

2026-11-24 JST. Continues 5e5f1eb1ce0e9866c5516902d2bf54f0c1bb3262 on the same research/min-cycle-forest-2026-11-24 branch. Paper deductions and exact finite diagnostics; not Lean-checked. Full matching deficit and twin-prime conjecture remain open.

## 1. Integer quotient constraint

Keep the original MIN cutoffs, LOW7 L=210, B=ceil(sqrt(7X)), and the globally disjoint stopped-cohort matching of previous notes. At the first asynchronous projected contact (p,C), with distinct prime labels p,q,q', positive prior height indices k,k', lag j!=0, even error e, and unequal bounded even offsets s1,s2, write
    C+sigma=p a0, C+s1=q a1, C+s2=q' a2,
    kq-k'q'=d=2jp+e/2,
    Delta=s1-s2 !=0, t=sigma-s2.
Here |Delta|,|t|=O_L(1). Put l=k a2-k'a1. The preceding quotient identity yields
    d a2=l q+k'Delta.
We restrict to q,q'>=B^theta (fixed 0<theta<1), 1<=k,k'<=H=log^beta B, 1<=|j|<=H, r(C)<=z=ceil(log^gamma B), |e|<=7L+4z+6, and pqq'>X U, U=log^lambda B with lambda>max(beta,gamma). Thus p>=X U/B^2 >> H+z+L; for sufficiently large B, p>max(k,k',2|j|,|Delta|,|e|/2). Also p<=B. In particular d!=0 and p<=|d|<=O(Hp) eventually. Let D0=|d|. The new integer constraint gives
    g0=gcd(l,D0) divides k'Delta.
Consequently g0<=O_L(H) and p does not divide g0. This bounded gcd is special to the UNEQUAL offset case; if Delta=0 it cannot be inferred.

Eliminate a2 and q' from C+s2=q'a2. For the polynomial
    P_l(T)=(kT-d)(lT+k'Delta)+k'd t
we get
    P_l(q)=k'd(C+sigma)=p k'd a0.
Thus every candidate q satisfies BOTH
    lq+k'Delta=0 mod D0,
    P_l(q)=0 mod p D0.
We may discard the further necessary k' divisibility if useful, but will impose it in the two-prime sieve. The sign of d is irrelevant for congruences.

## 2. At most two residue classes modulo p D0/g0

Fix p,k,k',j,e,s1,s2,sigma,l satisfying the above numerical bounds. If g0 does not divide k'Delta there are no solutions. Otherwise the first congruence specifies one residue modulo D0/g0 (including trivial modulus 1). Restrict to q not divisible by p, as required by distinctness.

Case p does not divide d. Then modulo p the polynomial has degree at most two and is nonzero: if p divides l its linear coefficient k k'Delta is nonzero modulo p, and otherwise the leading coefficient k l is nonzero. Hence at most two roots modulo p. CRT with the first congruence gives at most two residue classes modulo p D0/g0. The second congruence modulo p D0 may impose more conditions; these cannot increase the candidate count.

Case p divides d. Since p>|e|/2 and p>2|j|, we must have e=0 and d=2jp with v_p(d)=1. From the first congruence and Delta!=0, p does not divide l. Modulo p, P_l(T)=k T(lT+k'Delta); the root T=0 is excluded and the unique other root is nonzero and simple. Its derivative is k l T !=0 mod p. Therefore there is at most one lift to a root modulo p^2: writing T=T0+p w gives a linear congruence with nonzero coefficient on w. Combine this with the first congruence modulo D0/(p g0), coprime to p. This gives at most one residue class modulo p D0/g0. No division by d modulo p is performed.

In either case all actual q lie in at most two classes modulo p D0/g0, of size at least c_L p^2/H. If needed, impose kq=d mod k' to ensure q'=(kq-d)/k' integral. Intersection with that congruence produces at most two classes with modulus a multiple of p D0/g0. Their candidates q and q' are affine linear integral forms in a common integer parameter. Both slopes nonzero, with nonzero determinant because d!=0.

## 3. Unequal-offset deletion in the square-separated regime

Fix theta,epsilon>0, theta<1, and retain the conditions in section 1. In addition suppose
    p^2 <= min(q,q')/B^epsilon,
    m(q,D)<=q W, m(q',D')<=q' W, W=log^delta_w B.
Here D and D' are the pre-horizons of the two executed prior high keys, not D0=|d|. The mass bounds hold automatically in the hybrid cap of the earlier note if theta exceeds its floor exponent; they may be imposed conditionally in other absorption rules. We prove, with fixed exponents,
    V_unequal_sep = O_(L,theta,epsilon)(X W H^4 (1+z)(log log B)^3/log B).
In particular choose beta=gamma=delta_w=1/8, lambda=1/4. Then this is O(X (log log B)^3/log^(1/4) B)=o(X). It bounds actual disjoint matching pairs of arbitrary ancestry depth, including first contacts at a proposed stop.

Proof. Orient the pair q<=q' (swap signs and indices as necessary). Partition into dyadic bands Q<=q<2Q, Q'<=q'<2Q', Q' >=Q, Q>=B^theta/2. For fixed p,k,k',j,e and bounded offsets, the integer l satisfies
    |l| <= (D0 a2+|k'Delta|)/q
        <= O_L(D0 X/(Q Q')).
We used a2=(C+s2)/q'=O(X/Q'), D0>=p>>H, and QQ'<=B^2=O(X). So there are O_L(D0 X/(Q Q')) values of l, including negative values and zero, if any are feasible.

For each l with g0|k'Delta, use the at most two progression classes in section2 and integrality of q'. On each class the parameter interval has length at most O(n), with n=Q g0/(p D0), and can be embedded in an interval of length comparable to n. We have
    n >= c Q/(H p^2) >= c B^epsilon/H.
The last inequality follows from p^2<=q/B^epsilon and q<2Q. Both actual primes are at least B^theta. Apply the usual dimension-two upper-bound sieve, as in the previous equal-offset note: choose level B^(min(theta,epsilon)/4), prime cutoff a sufficiently small fixed power of B. Outside primes dividing the nonzero product of the slopes and determinant, there are two distinct forbidden residues. That exceptional product, including 2 and the factors of k,k',d and the progression modulus, has magnitude B^O(1) since all slopes and d have polynomial size. Its exceptional factor is O((log log B)^2) by the earlier Mertens splitting argument. The residue error O(B^(min(theta,epsilon)/4)log B) is absorbed by n/log^2 B. All actual prime values exceed the cutoff. Uniformly in the fixed tuple the count is at most
    O_(theta,epsilon)(Q g0/(p D0) * (log log B)^2/log^2 B).
Imposing the extra q' integrality condition may shorten the interval but the same embedded interval upper bound applies. Each candidate determines q', a2=(lq+k'Delta)/d, C=q'a2-s2, and both preceding keys once g,g' and signs are fixed. Negative a2, C outside the window, etc. are harmless overcounts. Unlike the three-modulus CRT bound, this does not introduce a +1 per large-label triple.

Multiply by the degree-one matching bound <=2Q W, use g0<=O_L(H), and sum over l. This gives for fixed p, the parent bands and other coefficients,
    O_(theta,epsilon,L)(X W H (Q/Q') (log log B)^2/(p log^2 B)).
Sum over p using the harmonic prime bound O(log log B). Sum over Q'>=Q using the geometric factor Q/Q', and over O(log B) bands Q. Finally sum O_L(H^3(1+z)) tuples k,k',j,e and bounded LOW gains/signs. This proves the stated result. The current p need not have any prescribed mass or be executed. No independence or distribution of modular inverses is assumed.

A minor sharpening is available. For M=ceil(c_L D0 X/(QQ')) chosen >=D0, and admissible l in [-M,M], g0 divides gcd(D0,k'Delta). Using gcd(l,D0)=sum_{a|gcd(l,D0)} phi(a), bound the sum of g0 over the admissible l by
    sum_{a|gcd(D0,k'Delta)} phi(a)(2M/a+1)
       <=3M tau(gcd(D0,k'Delta)).
For any fixed nu>0, the elementary divisor bound tau(n)=O_nu(n^nu) gives O_L,nu(M H^nu). Thus the extra H factor above can be replaced by H^nu, yielding H^(3+nu) instead of H^4 in the theorem, with constants depending on nu. For the displayed exponents, any fixed nu<3 gives o(X); the simpler H^4 bound is sufficient here.

## 4. Exact finite tests

Extend the previous asynchronous quotient audit with the integer identity, gcd divisor, polynomial identity, and explicit residue enumeration modulo pD0/g0 for unequal-offset, distinct-label, large-product pairs with both positive parent indices. Run the saved function at X=256,1024,4096,16384,65536,262144 for uniform cap floor(B/4) and hybrid cap 4 max(ceil(sqrt B),p), preserving original cutoff tags, same sorted-half matching and all previous first-contact tests. In the finite diagnostic, the root-class enumeration applies only if p>max(|Delta|,k,k',2|j|,|e|/2), and modulus <=200000. The exact polynomial and gcd identities are checked regardless of this diagnostic bound.

At X262144 uniform: 656 unequal-offset large-product pairs, 289 both-positive indices, all 289 polynomial/gcd checks pass; 211 satisfy the coefficient bounds, 148 explicitly enumerate classes (63 skipped due to modulus cap), maximum two. Hybrid: 1605 unequal-offset pairs, 639 both-positive, all 639 polynomial/gcd checks pass; 411 satisfy coefficient bounds, 377 enumerate classes (34 skipped), maximum two. Across these tested windows the loose separation p^2<=min(q,q') holds for 0 uniform and 2 hybrid both-positive pairs, both at X65536. In particular it holds for NONE of the corresponding pairs at X262144. The actual asymptotic square separation is stronger; this theorem should not be described as removing the majority of the observed unequal-offset class.

A finite example with e=0 from X16384 hybrid: p13,q173,q'17,k=k'=1,j6,Delta10,l2110,d156,g0=2. The residue modulus is 1014, with only admissible nonzero-mod-p root class 173. This tests the repeated prime factor in the modulus. A separate exact synthetic enumeration across p=11,13,17,19, small signed coefficients, nonzero even Delta, l including multiples of p and zero, tests 21504 admissible gcd tuples (4608 with e=0); 17312 nonempty, 2948 two-class cases, maximum two, including 9216 cases with p|l. Enumeration tests the two necessary polynomial and integrality congruences, not MIN reachability. These results are checks of the algebra, not asymptotic evidence for concentration.

Executed function bodies and exact remote readback of research/min_asynchronous_unequal_quotient_audit.mjs and research/min_asynchronous_unequal_quotient_results.json at commit 42eb747f8db85463dd115dd734fe2afcec4e70a6.

## 5. Residual

The unequal-offset quotient argument recovers the missing factor 1/p in a regime where the congruence parameter length remains a positive power of B. When p^2 is comparable to or larger than min(q,q'), the new progression can be too short: the one-per-class term cannot be uniformly absorbed in Qg0/(pD0). Summing it over l returns the loss. A proof of the remaining unequal-offset regime would need cancellation/distribution across l, or a dynamical estimate reducing matched source mass there. Long lag, large height indices, reset/reset, small-label concentration and other prior residuals remain. No total matching bound or proof of twins is obtained. No new branch or main edit.
