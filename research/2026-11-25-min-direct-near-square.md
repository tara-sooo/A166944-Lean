# Near-square MIN resets: exact cofactor criterion, tight twin gate, and Fermat bounds

2026-11-25 JST. Independent direct-arithmetic continuation of [30538f5](https://github.com/tara-sooo/A166944-Lean/commit/30538f5ccd69237e827c84ed3b128fa2fa3ce504). Paper deductions and exact finite checks; no cost decomposition, ensemble estimates, source mergers, Lean validation, or external novelty claim. Twin-prime infinitude OPEN.

## 1. Near-square selected label forces a prime cofactor

Use the adaptive square-root MIN defined in the first note. Let C=0 mod4 be the pre-horizon and t=C/2+3 (canonical odd root M=C/2+1) or t=C/2 (even reset). Suppose the first selected event is on the minus/even side, with prime p=1 mod4, p>=53. Write its post-horizon as

    Z=C+p-1=p m,    C-1=p(m-1).

The exact clock table of the preceding note gives wait (p-7)/2 at a root or (p-1)/2 at a reset, hence the new state is (Z/2,Z), an even reset. Assume m<=2p (the near-square band), and set q=m-1. Since p^2<=C+1=pq+2, q>=p (integer), while m=0 mod4 gives q=3 mod4, so q>p. If q were composite, its least prime divisor r<=sqrt(q)<sqrt(2p) would be eligible on the same minus side, with next hit in at most 2r ticks. For p>=53,

    2 sqrt(2p) < (p-7)/2.

(The squared inequality is p^2-46p+49>0, increasing for p>=53.) Thus r would hit strictly before p. Contradiction. Therefore q is prime, p<q<2p, q-p=2 mod4, and the previous minus neighbor is a semiprime. This conclusion requires the root/reset phase, not an arbitrary prestate of the same horizon.

## 2. Exact first-hit condition in the near-square band

Conversely take primes p,q with p>=53, p=1 mod4, q=3 mod4, p<q<2p. Set C=pq+1 and root or reset time as above. The minus neighbor pq has only eligible factor p: q^2>pq+2 since q>=p+2. The plus neighbor is pq+2. Let b0=floor sqrt(pq+2). For any odd prime r<=b0 dividing pq+2, its clock does not precede the intended p clock precisely when

    r=1 mod4: r>=p-4;
    r=3 mod4: 3r>p-6.

Indeed at the root the plus gap is (r-1)/2 for r=1 mod4 (r>=5), or (3r-1)/2 for r=3 mod4 (including r=3, gap4). At the even reset the corresponding gaps increase by 3 except r=3 whose positive representative wraps to 1; it precedes p in either case. Comparison with the p wait gives r>=p-6 for the first class, equivalent to r>=p-4 by residues, and 3r>=p-6 for the second. Equality in the first would give r=3 mod4, and equality in the second would imply p=0 mod3. Hence there are no ties. This proves an exact iff, independent of trajectory costs, for the first event from either phase. It is not an iff for reaching that prestate from any other canonical source.

For p>=73 every prime divisor of pq+2 exceeds (p-6)/3 (including factors larger than b0). Since ((p-6)/3)^3>2p^2>pq+2, the plus neighbor is prime or semiprime. If semiprime, both factors are 1 mod4 or both 3 mod4. This is an exact necessary structural restriction on the prior plateau, not on Z itself.

## 3. Tightest adaptive quotient is already a twin gate

The smallest possible q is p+2, equivalently m=p+3. In this case

    C=(p+1)^2,    C+1=(p+1)^2+1,    Z=p(p+3).

For every prime p>=53 with p=1 mod4, the first selected event from the canonical root M=(p+1)^2/2+1 or the even reset at C is p on the minus side IF AND ONLY IF

    p+2 is prime AND (p+1)^2+1 is prime.                (T)

Necessity of p+2 prime follows from section 1. For the other necessity, suppose (p+1)^2+1 composite. Its least prime factor r<=p+1 is 1 mod4: -1 is a square modulo r, so 4 divides r-1 by the elementary order argument. It is not p (the value is 2 mod p); it cannot be p-4 because the value at p=4 mod r is 26 and r>=49. Thus r<=p-8 and violates section 2. Sufficiency: p+2 prime gives only eligible factor p of pq, while the prime plus neighbor supplies no eligible factor. The cutoff contains p. This gate does not assert infinitely many solutions of (T); that would be stronger than the twin-prime objective on this residue class.

Under finite twins, (T) can occur for only finitely many p. Every sufficiently large actual near-square first reset in the stated phases must have q>=p+6. Conversely, unbounded occurrence of the tightest quotient alone would prove twin infinitude, without any terminal twin or cost estimate. The missing point is to force those events; adaptive MIN's local arithmetic does not guarantee (T).

Moreover the tight event does NOT usually stop at its new center. Since p,p+2>3 are twins, p=2 mod3, hence Z=p(p+3)=1 mod3. The next eligible minus label 3 has reset gap4. No smaller earlier clock is possible: plus 3 absent; plus 5 gap5, and minus 5 cannot divide Z-1 because p^2+3p-1 has discriminant 13, a quadratic nonresidue mod5 (or enumerate five residues). For r>=7 the minimum relevant gap is >=4, and the only potentially equal case r=9 is not prime. Consequently the actual next event is exactly p'=3 at wait4 and new horizon Z+2=(p+1)(p+2), with recorded deficit 6.

For any near-square first reset from section 1, prime 3 would preempt p at the prior plus clock if pq=1 mod3. Thus pq=-1 mod3. If the new reset is quiet for at least four ticks, Z cannot be 1 mod3 (minus label3 would fire at tick4). The possibility q=1 mod3, p=2 mod3 would give Z=1 mod3. Therefore

    p=1 mod3, q=2 mod3, q-p=10 mod12.

So a long quiet tail in this family forces the gap q-p>=10, regardless of whether twins are finite. This explains why the tight case and long quiet terminal targets are distinct.

## 4. Thin near-square band: direct Fermat factor bounds

Let p=1 mod4 and m=0 mod4 as above. If

    (m-p)^2 < 2(p+m)-5,

then with S=(p+m+1)/2 (an odd integer),

    (S-1)^2 < Z-1 < Z+1 < S^2.

This follows by expanding the squares; the left difference is [2(p+m)-5-(m-p)^2]/4>0 and the right difference is [(m-p)^2+2(p+m)-3]/4>0. For either odd neighbor n=Z+/-1 that is composite, write n=ab with a its least prime factor, b>=a odd, and A=(a+b)/2 integer. Since A>=sqrt(n)>S-1, A>=S. The function A-sqrt(A^2-n)=n/(A+sqrt(A^2-n)) is decreasing for A>=sqrt(n). Therefore

    a <= S-sqrt(S^2-n) <= U := S-sqrt(S^2-(Z+1)).

The previous reset-clock table then supplies a stricter twin certificate:

    L >= floor((3U+5)/2)  and the first L ticks are quiet.

The proof uses the composite neighbor's least prime factor, eligible in the adaptive pool. For fixed bounded m-p, U=sqrt(Z)-sqrt(p)+O(1), so compared with the prior generic reset threshold this saves order Z^(1/4) ticks. The leading sqrt(Z) constant is unchanged.

Under the previous shorter-quiet structural criterion, if Z-1=ab is a semiprime with a=3 mod4, b=1 mod4, then A is even while S is odd, so A>=S+1. The stronger minus-side factor bound is

    a <= S+1-sqrt((S+1)^2-(Z-1)).

The plus semiprime (both factors 3 mod4) still has odd A and need only satisfy A>=S. These bounds restrict the possible obstruction; they do not show either neighbor is prime.

There is a related prior-plateau sharpening. Set h=(q-p)/2 (odd), A0=p+h (even), n=pq+2=A0^2-h^2+2. Suppose p>=73, h^2<2A0+1, p>4h+13. Then n>(A0-1)^2. Any prior plus semiprime having both factors 1 mod4 has odd factor mean A, so A>=A0+1. Its least factor satisfies

    a <= A0+1-sqrt(2A0+h^2-1) < p-4,

where the last comparison is equivalent to 2p>8h+26. This violates the exact first-hit condition. Hence in this thin prior band the prior plus neighbor must be prime or a semiprime with BOTH factors 3 mod4, each > (p-6)/3. The same geometry does not exclude the slow 3 mod4 clocks.

## 5. Actual counterexamples and finite coverage

The earlier abstract reset example is no longer the only obstruction. The following is a genuine first event from an all-odd canonical root in the near-square band:

    M=16206715, C=32413428, p=4261, q=7607, m=7608.
    C-1=4261*7607, C+1=32413429 (prime).
    Z=32417688, Z-1=2399*13513, Z+1=2699*12011.

The first event at relative tick (4261-7)/2=2127 selects p and resets at Z/2. Both final neighbors are composite with the structural classes from the preceding note. The next event is minus 2399 at gap3598, hence L=3597 quiet ticks, about 0.631756 sqrt(Z+1). The shorter structural inequalities hold. Literal per-tick adaptive parity GCD verifies both first hits. This refutes the blanket exclusion of the two-semiprime obstruction even for actual first reset paths with p<q<2p. It is NOT in the thin Fermat band, and M is composite. No prime-root two-semiprime counterexample is claimed.

An actual prime-root single-composite case:
    M=4559557 (prime), p=2269, q=4019, C=9119112,
    C+1=9119113 (prime), Z=9121380,
    Z-1=9121379 (prime), Z+1=1039*8779,
    next plus 1039 at gap1561, L=1560.
This is enough to refute automatic twin termination for prime roots in the wider near-square band under the shorter structural condition. It is not a refutation of the improved full quiet certificate.

A separate actual first-reset example with long relative quiet tail:
    M=52628767, p=9901, q=10631, Z=105267432,
    prior plus =6779*15527,
    Z-1=10247*10273, Z+1=105267433 (prime).
    L=15369, next minus 10247 at gap15370.
Here L/sqrt(Z+1)=1.4979544..., close to the previous generic coefficient 1.5. Not in the thin Fermat band; no asymptotic sharpness claim.

## 6. Reproducible audit and remaining goal

[Source at 36edd62](https://github.com/tara-sooo/A166944-Lean/blob/36edd62190fae767a284f6c47e272e1ae94fe3f7/research/min_direct_near_square_audit.mjs), blob 5d97907967ed0b389b131f925add08c555a4e10c, exact remote readback. Run:

    node research/min_direct_near_square_audit.mjs 12000

Executed the actual ECMAScript function, not a separate Node process. Sieve through sqrt(2P^2+100)+5 and exact trial factorization within the required bound. Prime pairs p=1 mod4, 53<=p<=12000, q=3 mod4, p<q<2p exhaustively checked. Clock comparisons at both root and reset phases; 645 composite-cofactor tests for p<=300; tight-square equivalence on 701 labels and 14 successful tight events, all followed by 3 at gap4; near-pair tests 183576 and actual winners 15847. 6198 nonterminal quiet>=4 cases satisfy the mod3 restriction. Thin-band candidates5737, winners464 (3 terminate at twins, 461 nonterminal factor/clock bounds); prior-thin tests681, 84 composite prior-plus cases all both3 mod4. In the wider band 59 actual paths meet the shorter structural condition with at least one composite neighbor (9 prime roots), including one both-composite path; literal first and next clock comparisons all pass. No such case in the tested thin band; that finite absence is not a universal exclusion.

This work gives a new concrete finite-twins consequence (no unbounded tight first resets), exact near-square eligibility, and sharper direct primality certificates. It also excludes the blanket wider-band semiprime-impossibility idea by actual paths. The next mathematical issue is whether MIN can force sufficiently tight arithmetic configurations on an unbounded family of roots. Merely showing p near sqrt(C) in a factor-two band is insufficient; even the stronger thin-band numerical absence is not a proof. Seek a deterministic construction or exclusion in the thin band, or a global reachability theorem forcing the tight quotient, without smuggling in a prime-pair or square-plus-one primality assumption. No solution of twin infinitude or the A166944 record conjecture; no Lean changes. Main and sibling branches untouched.
