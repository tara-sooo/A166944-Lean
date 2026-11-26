# Direct reset mergers: unbounded multiplicity but finite limiting moments

2026-11-26 JST. Continuation of bb469545c6174bab58fcfaf110d9a70e0288aa61 (rank lines and crossing mergers). Ordinary uncut offset MIN, arbitrary deficit-6 integer seeds, and pre-first-record paths. Paper deductions and executed finite audit, not Lean-verified. No novelty or twin-infinitude claim. No formal target or canonical branch changed.

## 1. Exact direct reset predecessors

Write target reset (U,V)=(2r-2,r+2), r>=7, r=1 mod6. A direct predecessor that is itself an integer reset (x,t) must have

    x=2r-p-1, t=x/2+3, w=(p-1)/2.

Both offsets are multiples of 12, so p=1 mod12. The target time V is odd, hence this is a plus event and p divides gcd(U+2,V-2)=r. Conversely for any such prime divisor p of r, the displayed source and wait are forced, and they give a direct merger iff the true first-clock/least-label event has that wait and label. Restrict to PRE-FIRST-RECORD edges of the source seed: p=r is excluded because p exceeds the source threshold r-(p-1)/2. If p<r, then r/p is odd >=3, and p<=r-(p-1)/2 automatically. The source has positive offset for sufficiently large r (indeed for p<r, r>=7 and p=1 mod12). Denote by D(r) the number of these true direct reset predecessors, and by D_T(r) the number with p>=T. They count distinct reset origins, not arbitrary incoming states.

## 2. Arbitrarily large direct indegree, on positive-density progressions

For any fixed m>=1 choose distinct primes p_i>max(2m+3,5), p_i=1 mod12, recursively such that p_i is 1 modulo every odd prime <=2m and every preceding p_j, and p_i>p_j+2 for j<i. Dirichlet applies to each finite reduced residue class.

Impose r=1 mod6 and r=0 mod each p_i. At the source x_i=2r-p_i-1, the prime p_i divides x_i+1. Each other selected p_j is excluded from x_i±1, since neither p_i nor p_i+2 is divisible by p_j: if j<i use the nested congruence (p_i+2=3 mod p_j), and if j>i use the strict size inequality. Let B=max p_i+6. For every unselected odd prime q<=B exclude r residues with 2r=p_i or p_i+2 mod q, for all i. For q<=2m choose r=1 mod q, since all p_i=1 mod q. For q>2m at most 2m residues are forbidden and at least one remains. The q=3 constraint is satisfied by r=1 mod6. CRT combines these choices, including parity, into a nonempty arithmetic progression.

At seed (x_i,x_i/2+3), the intended odd tick V=r+2 has raw gcd equal to p_i: the odd clock argument is r and the plus neighbor is 2r-p_i, giving gcd(r,2r-p_i)=p_i. This is its first eligible p_i clock since w_i=(p_i-1)/2<2p_i. At all earlier relative ticks j the nonzero odd raw defects are 2j+7 (even absolute tick) or 2j+1 (odd absolute tick), bounded in absolute value by p_i+6. Thus no unselected prime >B can fire there and all smaller competitors were excluded. This proves exact first-event selection at every source. Choosing sufficiently large r in the progression gives p_i<r and hence genuine pre-record edges. All m distinct seeds reach the same deficit-6 state in one event. In particular the limiting lower density of D(r)>=m among r=1 mod6 is positive, for every fixed m; there is no uniform constant upper bound even for this one-step ancestry class. This does not assert that the first crossing of a high rational slope has large basin, nor does it compare these constructed multiplicities to log^2 of a future crossing label.

## 3. High direct mergers have small mean supply

Fix target r in [Y,2Y] and a true pre-record direct incoming p. Set r=pk, k odd >=3. The source neighbors are p(2k-1) and p(2k-1)-2. Since w=(p-1)/2 and every odd neighboring prime factor q has a competing clock within 2q, all these factors satisfy q>=(p-1)/4. In particular (p-1)<=4(2k-1), using a prime factor of the proper cofactor 2k-1. Hence p^2+3p<=8r<=16Y. For fixed p, both 2k-1 and p(2k-1)-2 have no odd prime divisor <=p/8 for p sufficiently large. Their two roots modulo any odd prime ell<p/8 are distinct and the leading coefficients invertible.

Apply the two-form Selberg upper sieve proved in research/2026-11-26-min-primorial-record-displacement-and-supply.md, section 3, with parameter k in an interval of length O(Y/p), enlarged if necessary to [1,ceil(2Y/p)]. This length is >>p by the scale bound. The same cutoff floor(p^(1/10)), error O(p^(3/5)), and Euler-product lower bound yield O(Y/(p log^2 p)) targets for each p, uniformly, with bounded p handled by the trivial bound. Sum over primes p>=T using Chebyshev and dyadic bands (each band's contribution O(Y/log^3 T_j)):

    sum_(Y<=r<=2Y,r=1 mod6) D_T(r) << Y/log^2 T       (T>=13).

In particular the fraction of targets in that slab with ANY pre-record direct incoming label >=T is O(1/log^2 T), with an absolute implied constant. Taking T=13 bounds the average D(r). This is an incoming-degree statistic at reset states, not a basin-size estimate for arbitrary states.

## 4. All fixed moments are uniformly bounded

Let k>=1 be a fixed integer moment order and average over r=1 mod6 in [Y,2Y]. We prove E_Y[D(r)^k]=O_k(1). The number of targets is comparable to Y for large Y. Set P0=Y^(1/(2k)). The exceptional targets with any direct incoming label >P0 have fraction O_k(1/log^2 Y) by section 3. Since D(r)<=omega(r), the ordinary number of distinct prime factors, and E_Y[omega(r)^(2k)]<<_k (1+log log(3Y))^(2k), Cauchy-Schwarz bounds their contribution by

    O_k((1+log log(3Y))^k/log Y)=o(1).

The elementary omega moment bound follows by expanding powers into sums over ordered tuples of distinct prime divisors: for product P<=2Y the number of multiples in the slab is <=1+Y/P<=3Y/P; products >2Y cannot occur; Mertens bounds the reciprocal-prime sum. The same upper bound holds upon restricting to the residue class.

For the remaining targets expand D^k into sums over tuples of j DISTINCT direct incoming labels, 1<=j<=k, each <=P0, with only moment-dependent coefficients. Fix such a tuple p_1<...<p_j=p and P=product p_i<=sqrt Y. Then r=P h, and the largest incoming label p requires the two forms

    2(P/p)h-1,    p[2(P/p)h-1]-2

to avoid all odd primes <=p/8. Omit sieve primes dividing P (at most k of them); all remaining odd primes below the cutoff have exactly two distinct roots. Parameter h has interval length O(Y/P), which is at least a constant times sqrt Y and hence at least a constant times p. The same explicit two-form Selberg argument gives

    O_k(Y/(P log^2 p))

possible targets. Omitting at most k primes costs only a k-dependent bounded factor in the truncated Euler product (each factor (1-2/ell)^(-1)<=3 for ell>=3); residue counting and the error are unchanged. Bounded p again handled trivially. Summing over the smaller tuple labels gives at most (sum_(q<p)1/q)^(j-1). Therefore the normalized tuple count is bounded by

    C_k sum_(p prime >=13) (1+log log(3p))^(j-1)/(p log^2 p) < infinity.

Convergence follows from Chebyshev in dyadic bands or partial summation. Sum over j to prove the moment bound. The argument works uniformly over slabs and extends to averages up to Y by dyadic decomposition, with the finitely many small r contributing a bounded amount.

For fixed cutoff T, D restricted to p<T is an eventually periodic function of r: eligibility p|r, seed parity, and the first w=(p-1)/2 tick tests involve only prime divisors of the odd relative defects of size <=p+6. All are fixed finite congruences, as in section 2. The exclusion p=r concerns only finitely many r. Thus each truncated distribution has a natural density. Section 3 gives a uniform tail probability O(1/log^2 T) in limsup as Y->infinity, so the full integer-valued D has a limiting distribution (both on [Y,2Y] and on [7,Y]). All its fixed moments are finite and converge: for any moment order k, Cauchy-Schwarz with the bounded 2k-th moment and the probability of a label >=T gives a uniform O_k(1/log T) bound for the contribution of the differing targets. In particular for each fixed k the upper density of D>=m is O_k(m^(-k)); combined with section 2 its support is unbounded. This controls the rarity of large one-step mergers, not repeated-merger basin sizes. No independence of successive mergers is assumed or proved.

## 5. Executed finite audit

Source research/min_primorial_reset_merger_audit.py at 7447c430d809e8c2cbcf29c2047dc1d0d955bcb6, blob 7f554736794e0648b33dfbb052cf764b15af530d. Remote content exactly verified; after aligning one blank line, the exact blob was independently rerun locally and hash checked. Requires SymPy and sibling record-supply audit. Run:

    python research/min_primorial_reset_merger_audit.py 1000000 100000

CRT controls (all literal GCD ticks):
- Labels (13,61), target r=10814547277439034186424081, modulus 7858321551080267055879090; 36 ticks.
- Labels (13,61,73,109), target r=32273174190789302777780684879126882182644542071, modulus 31610054640417607788145206291543662493274686990; 126 ticks.
These use explicit compatible finite label sets rather than the recursively chosen sequence of section 2. No primality of the target r is required.

Direct incoming edges on all 166666 targets r=7,13,...,999997: 58131 candidate prime-divisor edges, 13268 actual pre-record direct reset edges. Counts D=0:153588; D=1:12891; D=2:184; D=3:3. Maximum witnesses r=394693 labels [13,97,313], r=528541 labels [13,109,373], r=931801 labels [13,229,313]. Sum D^2=13654. Number of targets with at least one incoming p>=13,31,61,127,257,1021 respectively 13078,3594,2538,1187,707,47.

Independent full pre-record path multiplicity scan on 16666 seeds r<=100000 (including initial and terminal pre-states, not executing the first label >r):
- 334337 seed-state visits, 84217 distinct states, 4244 distinct terminal pre-states, no false first records.
- Maximum basin 104, for example at reset state (102132,51069), and at terminal (102198,51109). This counts all visited origins, not just direct predecessors. Unordered state-origin collision incidences sum binom(b,2)=2419013; a given pair of origins can be counted at several different common states.
- First observed positive-to-nonpositive crossings of slopes (K+1)/(2K), for K=3,5,9,19,39,99, before record: numbers of origins 2,7,29,84,264,1020; distinct destinations 2,6,13,41,89,308; maximum per-destination multiplicities 1,2,15,9,23,25. Seeds already on the high side at start are not automatically counted as crossings. The populations across slopes overlap.

All direct incoming identities, clock checks and scale bounds passed. No inference of the limiting law from sample frequencies; the moment and density arguments above are separate paper deductions.

## 6. What remains

The first-crossing state supply bound from the preceding note needs control of the WHOLE pre-crossing basin, not just immediate reset predecessors. This work establishes unbounded local merging even for exact deficit-6 origins, and a uniform averaged tail for this particular source of merging. The full basin may accumulate many mergers over many events, including nonreset arrival states. No bound on that accumulation, no upper bound on first-record displacement G(r), and no Lean verification are obtained. The user-directed exploratory branch is unchanged outside the two new research artifacts; no assigned child issue is claimed completed.
