# Arbitrary reset seeds, exact phase reachability, and finite-prefix obstructions

2026-11-26 JST. Continuation of e34065ffbc93d51eaea54f6df344b3871e7377c1, research/2026-11-26-min-primorial-record-displacement-and-supply.md. Paper deductions and executed Python audit; no Lean verification, proof of twin infinitude, or external novelty claim.

## 1. Remove the prior-twin and starting-threshold hypotheses

For every integer r>=7 with r=1 mod6, use the ordinary uncut offset MIN from (X,v0)=(2r-2,r+2). The initial offset is a positive multiple of 12 and the deficit is 6. Do not require r or r-2 to be prime, or claim that the seed is reached by the distinguished ray.

Let m(r) count events through the first label p>r inclusive, and G(r) denote displacement before that event. This event exists by the primorial no-crossing argument (otherwise all labels lie in the finite set of primes <=r). Every intermediate twin center would cause a record since u>=X>r. Thus the preceding paper's displacement certificate and event-count lower bound for a false record apply without modification: they use r=1 mod6, X=2r-2, d0=6 and the comparison with r, not primality of r or r-2.

Explicit threshold for the G certificate: if G<=X/4, a false doubling would require X/2-24<=6 sqrt(5X/4-1). For X>=276 this fails, since the difference of squares is X^2/4-69X+612>0 and X/2-24>0. A non-doubling record p>r requires G>=r+7>X/4. Hence for EVERY integer r=1 mod6 with r>=139,

    G(r)<=X/4  ==>  the first label >r is a genuine twin record.

There is no unknown starting threshold in this statement. The older event-count certificate also has an explicit threshold: r>=31 and m(r)<=sqrt(r)/4 exclude a false record by 2m>sqrt(4r-3)-sqrt(2r+5). Indeed sqrt(4-3/r)-sqrt(2+5/r) is increasing for r>3 and exceeds 1/2 at r=31.

It now suffices to prove either short bound along ANY unbounded sequence of integers r=1 mod6, with no input twin primes. A finite ray starting at such an arbitrary reset is not claimed to be a canonical prefix; the resulting actual integer twin center suffices for twin infinitude in its own right. The upper bounds remain unproved.

## 2. Exact reverse ancestry and the phase-set recursion

For a nonseed arrival state (u,v), possible preceding labels p are constrained by
- even v: p divides gcd(u,v);
- odd v: p divides gcd(u+2,v-2).
The predecessor offset is x=u-p+1. For L=u+3-v, the sharper phase restrictions are L=3 mod2p for even v, L=p-1 mod2p for odd v. In particular p<=L+1 (using the earlier general envelope v<=x+3 at the event). At a false double with L<=q+4 and q the least prime factor of u-1, the predecessor label is <=q+5. The old local control (66,67) has L=2, is not a seed, and cannot be an arrival: its odd predecessor label would have to be <=3 and divide 68.

Define A_x to be the union of active ticks for the odd prime factors of x-1 and x+1, with their exact even and odd clock residues. Let b_x(n) be the greatest active tick strictly less than n. For any active tick n let p_x(n) be the least label active at n. For every integer t in [b_x(n),n-1], the next tick and label from (x,t) are exactly (n,p_x(n)); no other t has that next event.

Let T(u) denote the set of event times reachable from any seed (X,X/2+3) with X a positive multiple of 12. At each u include seed u/2+3 if 12 divides u. For other arrivals test the candidate p and x from above, require p=p_x(v), and require

    T(x) intersect [b_x(v),v-1] != empty.

These are necessary and sufficient conditions, since x<u and every event strictly increases u. Thus exact finite reachability is an acyclic recursion; equivalent forward implementation merges equal states from all seeds. Future seeds above u cannot enter its ancestry. A potential route is to bound the reachable clock-phase sets rather than the deficit scalar. This recursion does not itself imply a uniform sparsity bound.

## 3. Convex-hull abstraction fails even with exact one-step clocks

At each offset keep [min T,max T], propagate from all integers in the interval, and take the integer interval hull of all arrivals and seeds at each new offset. For fixed x and an interval [a,b], the set of possible next active ticks is exactly A_x intersect [F_x(a),F_x(b)], where F_x(t)=min{n in A_x:n>t}. For intermediate ticks n<=b+1 choose t=n-1; the last tick F_x(b) can be attained by t=b. This yields exact one-step images before the new interval hull is taken. At every clock the true least-label tie rule is used, including within the relaxed hull.

This stronger relaxation is distinct from merely allowing any eligible label before F_x(b). Its finite failure is attributable to filling phase holes across arrivals, not to omitting the tie rule. The executed audit in section 6 finds false doubling candidates in the hull abstraction starting at u=152310 despite zero actual false doubles up to 10^6. Therefore this particular interval invariant cannot exclude false doubles even on that finite range. It does not rule out every possible scalar or interval invariant.

## 4. Finite-prefix translation obstructs a uniformly bounded record time

Fix a finite prefix of m events from seed r0=7 (X=12,v0=9). The raw gcd at relative tick j and relative gain G is gcd(r+2+j,7+2j-G) on even absolute ticks and gcd(r+j,1+2j-G) on odd absolute ticks. This follows by writing u=2r-2+G, n=r+2+j and subtracting u±1 from twice the clock argument. The second argument is always odd and nonzero. If its absolute value is <=B at all ticks in the finite prefix, then every seed r congruent to r0 modulo Q=2P_B (P_B product of odd primes <=B, B>=7) has exactly the same prefix, by induction on ticks. All raw gcd prime sets are preserved, and parity and r=1 mod6 are preserved. Choose r>B so none of the first m labels is a record >r.

There are arbitrarily large such seeds for every m, indeed a full arithmetic progression. More quantitatively, the base prefix satisfies u_i<=12*2^i and v_{i+1}<=u_i+3. Therefore B may be chosen <=12*2^(m-1)+7, taking the maximum of the absolute defects across its plateaus (negative odd defects have absolute value <=3). Set r_m=7+(B+1)Q. By Chebyshev log Q=O(B), so log log r_m<=m log2+O(1). The maximum label on the base ray tends to infinity and B can be taken nondecreasing and unbounded. Consequently for an unbounded sequence of integer seeds,

    m(r_m)>m >= log_2(log r_m)-O(1).

Here log_2 means logarithm to base 2, and inner log natural. This is an obstruction to a uniform constant bound (and to certain extremely slow bounds), not to the required square-root bound. There is no claim that these lifted seeds are twin-derived.

## 5. Almost all large integer seeds have no record within any fixed event count

Take natural densities relative to r=1 mod6. For any fixed displacement G and cutoff z>=5, the density of r for which both 2r-2+G±1 have no factor among odd primes 5<=q<=z is exactly

    D(z)=product_{5<=q<=z prime}(1-2/q).

Each q excludes two distinct residues of r, and the CRT is independent of the mod6 constraint. D(z)->0 by divergence of the reciprocal prime sum. Fix any event count k and error eta>0. Inductively bound the first i labels by a constant K_i outside an exceptional set of upper density at most i eta/k. For a good prefix the displacement and deficit are bounded by constants depending only on i and K_i, using w<=2p. In particular only finitely many G are possible. Choose z large enough that the union, over those G, of the above rough conditions has density at most eta/k. For each remaining seed a prime q<=z divides a neighbor, hence the next w<=2z. The selected p divides the relative defect, so p<=d+4z+1 (or p=3 in the negative-defect case). This bounds the next label by another constant independent of r. The induction proves that for all sufficiently large r outside an exceptional set of upper density <=eta, none of the first k labels exceeds r. Let eta tend to zero. Thus

    density{r=1 mod6 : m(r)<=k}=0 for every fixed k.

A fixed-length prefix has a periodic cylinder description by the same relative-defect argument in section 4. The tightness argument just given makes the finite-prefix limit distribution over residue cylinders well-defined. This statement concerns all integer reset seeds, not the conditional density among twin primes.

The first-event wait itself has a heavy tail in this limit. The event w>W depends only on finitely many prime residues (relative defects up to 2W+7). Since w<=2q for every neighboring factor q, and p<=2w+7 from d0=6, the limiting density obeys for W>=10

    D(2W+7) <= density{w>W} <= D(floor(W/2)).

The omitted prime 3 never divides either initial neighbor. Mertens' reciprocal-prime-product theorem and convergence of sum 1/q^2 give D(z) asymp 1/(log z)^2. Hence the first-wait tail is Theta(1/log^2 W) and its limiting mean diverges. Since w<=2p and p<=2w+7, the first-label distribution has the same tail order. This is not an asymptotic independence assumption between successive events. In particular a finite-mean iid approximation for the full uncut reset clocks is inappropriate. The result neither proves nor refutes the short macroscopic displacement bound.

## 6. Executed finite audit

Source research/min_primorial_reset_reachability_audit.py at f894556505e5536b1236d6b0f72697b46972b631, remote blob c8441b517e4c61cf1fc72d190be51573cac86578 matches the executed source (git hash-object). Uses the sibling record-supply audit and SymPy. Run:

    python research/min_primorial_reset_reachability_audit.py 1000000 100000

- All 16,666 integer seeds r=7,13,...,99997 (no primality condition), first record search with cap 100000 events: zero incomplete, zero false records. Maximum m=188 at r=75667, G=3288, next p=154621. Maximum G/X for r>=1000 was 330/2220 at r=1111; for r>=10000 it was 1794/23376 at r=11689.
- Exact union of ALL reachable states from positive multiples-of-12 reset offsets, with pre-offset <=10^6: 233225 occupied offsets, 446860 states, maximum 11 times per offset, 54573 same-offset merges (distinct times with identical next state, counted as excess inputs), 116288 noninterval time sets, first hole u=60 with T(60)={33,48}. Maximum d=6150 at u=814902. Zero false doubles. This scan covers complete ancestry in the offset domain but not beyond its cap. It does not track first-record thresholds of all ancestral seeds.
- Exact-one-step interval-hull relaxation with the true least-label tie rule: 1871 distinct false-double offsets, first at u=152310, relaxed time interval [76158,152100], firing tick 152313. Maximum interval width 499916. A looser earlier exploratory relaxation (ignoring some ties, filling down to u/2) had 2282 false candidates; do not conflate these counts.
- Literal GCD replay of three translated finite prefixes from r0=7 for m=5,10,15: defect bounds B=67,67,319; lifted seeds of 83,83,433 bits; largest selected labels 61,61,313. Every tick agrees, and none is a record >r.
- First waits from 166666 integer seeds r<=10^6: sample mean 20760.785 (includes rare very large immediate double waits), tail counts for W=10,30,100,300,1000 respectively 53329,30445,18055,11618,7845. These finite observations are not the proof of the limiting tail theorem.

## 7. Open target

The arbitrary-reset formulation removes the previous twin-seed threshold problem. The new exact phase recursion and explicit failure of interval hulls identify a possible ancestry-sensitive route; the next step is a uniform structural bound on the phase sets (or on surviving no-record paths across a macroscopic displacement). Density and translation theorems rule out expecting bounded-length finite-prefix information to settle that task. No asymptotic upper bound on G(r) or m(r), no proof of twin infinitude, and no Lean verification have been obtained.
