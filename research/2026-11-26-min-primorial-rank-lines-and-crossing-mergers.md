# Rational rank lines: exact local words and a crossing-state supply bound

2026-11-26 JST. Continuation of d93e614a6758060e1e05269be12caecc8409358e, research/2026-11-26-min-primorial-rank-tail-and-all-scale-cascade.md. Paper deductions and finite experiments on the ordinary uncut offset MIN. No Lean verification, novelty claim, or proof of twin infinitude. Distinguish local envelope-valid histories from histories originating at deficit-6 integer resets.

## 1. Rank states and their exact predecessor/departure identities

Fix coprime positive A,K, with K odd and 1/2<A/K<1, and set Z=A u-K v. A rank state is u=K t, v=A t; t is even because u is even. The exact reachable-state union in section 5 shows that rank states cannot be excluded just by requiring origin at an arbitrary deficit-6 reset. In particular seed (36,21) has next event p=7,w=7, reaching (42,28) on 2u=3v.

If a rank state has incoming label q, the arrival time is even, hence q divides gcd(u,v)=t. Write t=bq with b even. Its predecessor has x=(K b-1)q+1, time A b q-W. For a macroscopic incoming q>=eta X with u<=C X, the cofactor k'=K b-1 is bounded in terms of C,eta, and W<=2k' by the competing-clock argument. The predecessor is in the new corridor

    A' x-k' v_prev=A'+k' W,    A'=A b.

The slope A'/k' is strictly larger than A/K; for sufficiently large X it is strictly less than 1, since the event time is <=x+3, and A' and k' have opposite parity. Reducing the fraction preserves an odd denominator. This is an exact way to continue reverse rank analysis across a macroscopic singular arrival, rather than treating it as an arbitrary loss of all phase information. It does not handle all intermediate-size singular arrivals, or prove an upper bound on the time spent in a corridor.

For departures from u=K t,v=A t, the relative clock congruences are

    p|K w+A          (minus, w even),
    p|K w-A-2K       (plus, w odd),

in addition to p dividing the corresponding neighbor (and p not dividing K, automatic). Neither expression can vanish for integer w>=1, as 0<A<K. Thus for any prescribed finite waiting horizon W the entire departure competition depends on finitely many primes <=K W+A+2K. This follows directly by multiplying the clock congruence by K and substituting Kt=+/-1 mod p; it is also sufficient given neighbor eligibility and parity.

A rank-preserving event satisfies K w=A(p-1), so K divides p-1, the quotient (p-1)/K is even, and w is even. Hence the event is minus-side, with p=1 mod 2K. Conversely an eligible such prime has its indicated first clock at w=A(p-1)/K< p; it preserves rank if it wins the true competition. This gives a one-dimensional local transition system on t -> t+(p-1)/K, with explicit competitors. Rank preservation is not automatic just from divisibility.

## 2. Arbitrarily long exact rank-preserving words ending at a cofactor-3 false event

Specialize to A=2,K=3. At a rank state (3t,2t) with t even, the two relative clock defects are 3w+2 and 3w-8. In particular, if t=3 mod5 and P=t+1 is prime >5, the next two events are exactly

    (3t,2t) --(p=5,w=1)--> (3P+1,2P-1)
             --(p=P,w=1)--> (4P,2P).

For the first event 5 divides the plus neighbor and the odd clock argument 2t-1; 3 cannot divide that neighbor, so the least prime is 5. For the second, the even clock argument is 2P and the minus neighbor is 3P, with gcd exactly P. This ends in the cofactor-3 non-doubling event and deficit zero; the source neighbors are not twins because one is 3P.

For every prescribed m>=1 we can construct arbitrarily large local envelope-valid histories of m exact rank-preserving events followed by these two terminal events. Choose distinct primes p_i>max(7,2m+2,E_(i-1)+3), where E_i=sum_(j<=i)(p_j-1), E_0=0. Let Q0 be the product of odd primes <=2m+2 other than 3,5. For i<m choose p_i=1 mod 30 Q0 product_(j<i) p_j; for i=m impose p_m=7 mod30 and p_m=1 mod Q0 product_(j<m)p_j. These are reduced residue classes, so Dirichlet supplies the primes. All p_i=1 mod6. Earlier gains E_i are multiples of 30, and the final gain is 6 mod30.

Take initial t even, seek offsets u_i=3t+E_i, times v_i=2t+2E_i/3. Require t=1 mod5, so all source plateaus i<m avoid 5 on both neighbors and the final rank parameter t+E_m/3=3 mod5. At selected p_i impose 3t+E_(i-1)=1 mod p_i. At earlier plateaus this offset is 1 minus a positive even gain difference >=6 and <p_i-3, so not +/-1. At later plateaus the offset is 0 mod p_i by the nested label congruences; the terminal prime candidate P=t+E_m/3+1 is therefore 1 mod p_i.

For all unselected odd primes q<=C0=2 max_i p_i+8 other than 3,5, exclude the residues of t giving 3t+E_j=+/-1 mod q for j<m, and also exclude P=0 mod q. For q<=2m+2 use t=0 mod q (all E_j divisible q); otherwise at most 2m+1 residues are forbidden, fewer than q. For q=3 the source offsets already avoid both neighbors' divisibility by 3; choose t to ensure P is not 0 mod3. For q=5 the terminal P=4 mod5. All these conditions combine with t even by CRT, and leave P in a reduced residue class modulo the resulting modulus. Dirichlet in this single progression gives arbitrarily large P prime.

The intended i-th event has w_i=2(p_i-1)/3, an even positive integer less than p_i. It is the first eligible p_i clock and preserves the rank line. Selected primes are absent at other pre-plateaus and unselected primes <=C0 have been excluded; any prime >C0 cannot fire before w_i by the two nonzero relative defects 3w+2 and 3w-8. This establishes the exact MIN selection including all quiet ticks and tie competition. The terminal two events were checked above. All states satisfy the time envelope when t is sufficiently large. P can exceed any prescribed bound and every earlier selected label.

This is stronger than a mere local rank-state example: there are legal histories of arbitrarily many events on the exceptional line, ending in a large non-twin non-doubling event. These histories begin with deficit t, not 6. They are not counterexamples to reset-origin first-record conjectures, nor claims of actual canonical A166944 recurrence ancestry. Fixed-depth ancestry tests, even with exact rank constraints, cannot exclude all such local terminal words.

## 3. Global supply of high-label upward crossings of a fixed rank line

Take a fixed rational slope A/K as in section 1 and any envelope-valid non-twin event with pre-offset in [X,C X], C>1 fixed, crossing from Z=A u-K v>0 to Z'=A U-K V<=0. It need not be the first crossing on a ray. The following counts DISTINCT destination states across ALL legal source times, not just one ray.

The crossing implies K w>A(p-1), so w>(p-1)/2. All odd factors ell of either neighbor satisfy 2ell>=w. Hence all are > (p-1)/4, and by a composite neighbor's small factor p-1<4 sqrt(u+1). This is a subset of the earlier upward-event population.

The arrival identities give Z'=h p for even V, and Z'+2(A+K)=h p for odd V. Since w<=2p, Z>0 and Z'<=0,

    -2K <= h <= 2(A+K)/p.

Thus for fixed source offset, label, and arrival parity there are only O_K(1) possible destination times, regardless of how many source times lead there. Away from the even singular case Z'=0, the incoming crossing label is actually unique among primes >2(A+K): the nonzero integer Z' or Z'+2(A+K) has form hp with bounded |h|, and all its other prime factors are <=2(A+K). In the even singular case the candidates divide t=gcd(U,V), so the number >=T is at most log(O_C(X))/log T. Odd singularity is impossible by parity (K odd).

For fixed p and sign write the source selected neighbor as p k0. Both k0 and p k0+/-2 avoid odd prime factors <=p/8 for p sufficiently large. The exact two-form Selberg upper sieve from research/2026-11-26-min-primorial-descent-support-sieve.md applies with a smaller roughness constant: p<=O_C(sqrt X), so the multiplier interval of length O(X/p) is at least a constant times p. Taking sieve cutoff floor(p^(1/10)) gives O_C(X/(p log^2 p)) source offsets. The finitely many possible destination times introduce only a slope-dependent constant.

For T>=7, sum this upper bound over primes p>=T and p<=O_C(sqrt X). In each dyadic band [2^j T,2^(j+1)T), Chebyshev's prime upper bound gives contribution O(X/log^3(2^j T)). The sum over j>=0 is O(X/log^2 T) by integral comparison. Consequently the set of distinct destination states reached by any such non-twin upward crossing with p>=T has cardinality

    O_(A,K,C)(X/log^2 T).

This is a bound over the union of all possible legal source states in the horizon slab, not a sum over rays or a claim about the number of ancestral seeds. It does not bound the number of crossings with small labels. It gives a many-seed merging constraint in the next section.

## 4. Consequence for false-record families and a missing basin bound

Take arbitrary integer resets with X in [Y,2Y] (X a positive multiple of 12). Consider those whose first label >r=X/2+1 is not twin-derived and whose pre-offset satisfies u<=C X. All earlier events are non-twin. The earlier record deficit bound gives d_pre>=r+1-4sqrt(C X+1), hence d_pre>=X/3 for large X. At the pre-record state v/u>=1/2+1/(6C). Choose a fixed coprime A,K with K odd and 1/2<A/K<1/2+1/(8C). The initial reset has v/u=1/2+3/X below that slope for large X. Thus there is a first upward crossing of this line strictly before the false record. Its pre-offset lies in [Y,2C Y]. This applies to both false-record modes.

Suppose N of these seeds have first-crossing label >=T. Partition them by their exact destination state at that first crossing; forward dynamics after each destination coincide. The number M of nonempty classes is O_(A,K,C)(Y/log^2 T) by section 3. If their sizes are b_i, then

    sum b_i^2 >= N^2/M >> N^2 log^2 T/Y.

In particular if N>=rho Y for fixed rho>0, some destination must collect Omega(log^2 T) different reset origins, and the number of ordered distinct-origin collisions is Omega(Y log^2 T) as T tends to infinity. This is a necessary merging burden if a positive fraction of reset seeds realize the bounded-ratio, high-first-crossing false-record mode. A uniform o(log^2 T) bound on the number of such reset origins per destination would exclude that mode at positive density. Neither such a basin-size bound nor a lower bound forcing the first-crossing label to grow has been proved. Small-label crossings and mergers along long actual ancestries are unresolved; the union-state upper bound alone does not show that any individual ray cannot cross. No claim of twin infinitude.

## 5. Executed finite audit

Source research/min_primorial_rank_line_audit.py at 36e68da898c56657627c273874d32b231f407a9a; remote blob c0bb3331e92bfa3bf022ca120889205861c8647e matches the locally executed source (git hash-object, final whitespace-aligned rerun). Requires SymPy and sibling record-supply audit. Run:

    python research/min_primorial_rank_line_audit.py 1000000

- Full reachable-state union from every positive multiple-of-12 offset reset, cap 10^6: 446860 distinct states. Among even arrival times, reduced rank slopes 1/2<A/K<1, K odd and 3<=K<=19, 29 rank states, all with a witnessed nonseed incoming event. Counts: (K,A)=(3,2):1; (5,3):4; (5,4):1; (7,4):3; (9,5):3; (11,6):4; (13,7):1; (15,8):4; (17,9):2; (17,11):1; (19,10):5. Largest offset 9006, v4740. No uniform rarity bound follows from this finite data.
- For nine slopes A/K=(K+1)/(2K), K=3,5,...,19, the audit counted all positive-to-nonpositive crossing edges within the cap, not necessarily the first crossing of each origin. Counts 2,6,14,13,20,27,32,33,44, with 191 non-twin crossing edges in total; distinct destination counts 2,6,14,13,20,27,31,32,43. All modular overshoot, competing-factor, and scale checks passed. No rank-preserving edge on these nine lines observed within this domain. Rank states themselves are not globally forbidden.
- Local CRT examples, not reset-origin: p-list (7), terminal P=29283829, deterministic prime test within 64 bits; states (87851478,58567652)->(87851484,58567656)->(87851488,58567657)->(117135316,58567658), labels 7,5,P, waits 4,1,1. Literal GCD of every tick checked. Second p-list (31,37), terminal P=17752791184473730509101043072029, probable-prime test (not a primality certificate); labels 31,37,5,P and waits 20,24,1,1, literal GCD replay passed. The arbitrary-length theorem uses Dirichlet, not the large probable-prime example. The finite examples need not use the exact recursively nested prime-selection scheme of section 2; their CRT exclusions and all clocks were checked separately.

## 6. Remaining target

The exact rank corridor is not an impossible local state, and arbitrary fixed reverse depth will not rule out its legal words. The new result separates entering a high-rank region from spending time in it. A possible next step is a basin-size estimate for the first-crossing map across arbitrary reset origins, retaining actual incoming time intervals rather than scalar reachability. The other unresolved alternatives are small-label first crossings, unbounded first-record displacement, and mesoscopic singular arrivals. No Lean kernel verification was run; no canonical branch or formal theorem was changed.