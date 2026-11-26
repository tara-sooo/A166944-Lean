# Ordered descent pairs: five-condition hyperbola sieve and four-condition CRT relay toll

2026-11-26 JST. Continuation of 774dfb6c0aab1613a6349b89f272114a20ab2d3e (lag-descent support sieve). Uses the elementary hyperbola distribution and explicit Selberg quadratic-form arguments in research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md at inherited direct-arithmetic 14c6176473bd6b30599d06a02e49cc2679c227ae, and the two-form Selberg construction in research/2026-11-26-min-primorial-record-displacement-and-supply.md. Paper deductions and separately executed finite local/trajectory audits; not Lean verified, no external novelty or twin-infinitude claim.

## 1. Pair setup and repeat toll

Consider a single actual envelope-valid uncut offset MIN segment with pre-offsets in [X,A0 X], A0>1 fixed. A descent is an event with w>=p, i.e. strictly decreasing lag L=u+3-v. From the previous paper, all odd prime factors of either neighbor at a descent are >=p/2, and p<=2 sqrt(A0 X+1). Choose T tending to infinity and a fixed K>1. Mark the descent events with labels in [T,KT] and pair consecutive marked events, including all intervening events (not necessarily descents) in their relay. A subset of these pairs is also allowed. More generally the counting bounds hold for any unique-source ordered pairs with disjoint relay interiors; we use consecutive marked events for the relay conclusions.

Write source and target pre-offsets x=pq+e, y=rs+f, signs e,f in {-1,1}, and E=y-x-(p-1) for the intervening physical gain. It is an even nonnegative integer. Set D=p+E-1, a=E+e-1-f. Exactly,

    rs=p(q+1)+a, y=x+D.

If p=r then E=f-e+1 mod p. For p>=5 the smallest nonnegative even representative is p+f-e+1, at least p-1. Consequently short pairs E<=B<T-3 have p!=r; also a is odd, nonzero and |a|<p. This repeat toll uses only parity, divisibility and the intervening gain, not the wait comparison.

## 2. Five local conditions and exact common singular factor

For every sieve prime 5<ell<T/2, the two descents imply

    r!=0, s!=0, rs!=p+a, rs!=p+a-2e, rs!=-2f (mod ell).

The first is selected target primality and the second is target cofactor roughness. The last three are the two source-neighbor roughness conditions and the target other-neighbor roughness condition, using the product relation. Neither multiplier is assumed prime. Define

    nu_ell=2*1_(ell|D)+1_(ell|D-2)+1_(ell|D+2).

The three integers D,D-2,D+2 are positive for p>=7 and differ pairwise by 2 or 4; for ell>5 at most one is divisible by ell. For each of the four choices of e,f, direct substitution shows that the number h of DISTINCT NONZERO residues among p+a,p+a-2e,-2f is exactly 3-nu_ell. (If D=0 mod ell, one residue is zero and the other two coincide; if D=+/-2 mod ell, there is just one loss.) Thus the number of forbidden pairs in F_ell^2 is

    rho(ell)=2ell-1+(3-nu_ell)(ell-1),
    g(ell)=rho(ell)/ell^2=(5-nu_ell)/ell-(4-nu_ell)/ell^2.

The axes contribute 2ell-1, and each distinct nonzero product contributes ell-1 further pairs. In particular the generic density is 5/ell-4/ell^2; even in the degenerate cases the formula is exact. Define the finite factor

    S(p,E)=product_(ell>5) (1-1/ell)^(-nu_ell).

For fixed K and 0<=E<T, D(D-2)(D+2)=O_K(T^3). Uniformly S(p,E)<<_K (log log T)^2: split at y0=log(3T); each small prime has exponent <=2, and Mertens gives the product bound, while for the large prime divisors the sum of reciprocals is at most log(D(D-2)(D+2))/(y0 log y0)=O_K(1). We only use T sufficiently large.

A stronger averaged bound, uniformly for p in [T,KT] and integer B<T-3, is

    sum_(0<=E<=B, E even) S(p,E) <<_K B+1+(log log T)^4.          (1)

To see this, drop parity for an upper bound and again discard the large-prime factor at constant cost. For each ell<=y0, ell>5, write (1-1/ell)^(-nu_ell)=1+b_ell(E). This nonnegative function is supported on three residue classes, and its sum over all ell residues is

    A_ell=((1-1/ell)^(-2)-1)+2*((1-1/ell)^(-1)-1)
         =4/ell+O(ell^(-2)).

Expand the finite product. By CRT, for a squarefree product d of these primes, the sum of product b_ell(E) over the interval is at most ((B+1)/d+1) product_(ell|d) A_ell. Summing over d bounds it by

    (B+1) product(1+A_ell/ell)+product(1+A_ell)
    << B+1+(log y0)^4.

The first product converges uniformly, and the second uses Mertens. Set

    M(B,T)=min((B+1)(log log T)^2, B+1+(log log T)^4).

Both the pointwise and averaged estimates are valid for each source prime.

## 3. Five-condition hyperbola upper sieve, all descent scales

Fix p,e,f,E with E<=B<T-3. Every candidate (r,s) lies on rs=a mod p, in a rectangle of r length O_K(p) and s length O_A0(N), N=X/T. Since p is comparable to T and T<=2sqrt(A0 X+1), N>>_(A0,K) p. Thus the long-rectangle congruence bound in the inherited direct paper applies: for each residue pair modulo squarefree d coprime to p, its count is N0/d^2+O_(A0,K)(N p^(-1/4) log^2(2p)), where N0=O_(A0,K)(N). That proof uses Fourier expansion and the elementary nonzero Kloosterman bound O(p^(3/4)); we do not introduce a new exponential-sum assumption.

Take z=floor(T^(1/64)), sieve primes 5<ell<=z, and squarefree sieve indices d<=z. With the local rho of section 2, counts of all forbidden residue pairs modulo d have main term N0 g(d) and error O(rho(d) N p^(-1/4) log^2(2p)). The explicit Selberg weights from the cited papers have lambda_1=1, |lambda_d|<=d, and main quadratic form 1/G(z), G(z)=sum_(d<=z) product_(ell|d) g(ell)/(1-g(ell)). The error in the expanded square is

    O(N p^(-1/4) log^2(2p) z^8)=O_(A0,K)(N T^(-1/8) log^2 T),

since rho(lcm(d,e))<=lcm(d,e)^2 and sum_(d<=z)d^3=O(z^4). The weight bound holds since ell>=7 and 1/(1-g(ell))<=ell.

For the lower bound on G, truncate the Euler product to primes ell<=z^eta with eta a sufficiently small fixed positive constant. Its total squarefree weight is product(1-g(ell))^(-1). In the normalized distribution of those weights each prime occurs with probability g(ell)<=5/ell, so the mean log d is O(log(z^eta)) by Chebyshev and partial summation. At least half of the weight lies at d<=z by Markov. The factorization

    1-g(ell)=(1-1/ell)(1-(4-nu_ell)/ell)

and Bernoulli give (1-g(ell))^(-1)>=(1-1/ell)^(-(5-nu_ell)). By Mertens, G(z)>>log^5 T/S(p,E). The error is negligible compared to the main upper bound. Therefore for each fixed p,e,f,E the number of actual pairs is at most

    O_(A0,K)(X S(p,E)/(T log^5 T)).                              (2)

Each integer solution (r,s) fixes the target offset and, by y=x+D, the source offset, which occurs at most once on the monotone segment. No additional path counting or distribution assumption is required. For arbitrary pair weights in [0,K_w T] and S1 distinct source labels, summing signs and E using (1) yields

    F_short(B) << X S1 M(B,T)/log^5 T.                          (3)

This extends the earlier three-condition source-only sieve by two powers of log, apart from the explicitly controlled singular factor. It exploits BOTH events descending, and so does not assert an analogous gain for arbitrary first high successors.

## 4. Both labels fixed: CRT with four-condition sieve

Fix p,r,e,f,E for a short pair. By section 1, p!=r. The source offset x belongs to one class modulo 2pr, from x even, x=e mod p, x+D=f mod r. Hence the bare candidate count is O_(A0,K)(1+X/T^2)=O_(A0,K)(X/T^2), since T<=2sqrt(A0 X+1). For ell<T/2, ell>5, the progression step is invertible mod ell. In its progression parameter the four roughness conditions x±1,x+D±1 avoid exactly 4-nu_ell residues, with the SAME nu_ell as section 2: the residues in x are +/-1,-D+/-1. This supplies a one-dimensional sieve with g(ell)=(4-nu_ell)/ell.

Let N2=max(1,X/T^2) and H=min(log(2T),log(2+N2)). Uniformly over the full scale range the pair count for the fixed tuple is

    O_(A0,K)(N2 min(1,S(p,E)/H^4)).                             (4)

Indeed use the trivial count when the cutoff is bounded. Otherwise choose z=floor(min(T^(1/64),N2^(1/12))), so log z is comparable to H. On the progression interval, residue counts are length*g(d)+O(rho(d)) with rho(d)<=d. The same Selberg diagonalization and |lambda_d|<=d give error O(z^6)<=O(sqrt(N2)), absorbed by O(N2/H^4) as N2 grows. The truncated Euler-product argument now gives G(z)>>H^4/S(p,E), since g<=4/ell and 1-g<=(1-1/ell)^(4-nu_ell). This proves (4), without treating a short progression as uniformly equidistributed beyond its length.

For S1 distinct source and S2 distinct target labels, weighted summation gives two bounds

    F_short(B) << X S1 S2 (B+1)/T,
    F_short(B) << X S1 S2 M(B,T)/(T H^4).                       (5)

In particular if T<=X^(1/2-eps), eps>0 fixed, H>>_eps log T. The four-condition sieve on the CRT progression then supplies a full four powers of log (with the averaged singular factor), unlike the bare CRT bound. Near the square-root scale H can be bounded and (3) is a separate all-scale bound. The two sieve bounds apply to the same actual pairs and may be minimized, not added as if they were independent populations.

## 5. Ordered relay consequences

Pair consecutive marked descents in [T,KT]. Let F be their source-weight sum (each source weight between zero and K_w T) and R the total physical gain of nonmarked events in their disjoint relay interiors. In particular for E>B the weight of all such pairs is <=K_w T R/(B+1). Thus for every integer 0<=B<T-3,

    F << X min( S1 M(B,T)/log^5 T,
                 S1 S2 (B+1)/T,
                 S1 S2 M(B,T)/(T H^4) )
          + K_w T R/(B+1).                                    (6)

Constants depend only on A0,K,K_w. A macroscopic marked positive lag-loss sum gives F>=rho X for some fixed rho>0 by choosing each source weight w-(p-1) and dropping only the last marked event (O_K(T)=o(X)). Alternatively use source physical gain p-1. Equation (6) requires only F>=rho X for the conclusions below; it does not assume a global event-count bound.

(a) If S1<=C0 log^2 T and F>=rho X, take B=floor(c log^3 T) for small fixed c>0. The first term in (6), via (1), is <=rho X/2 eventually. Hence R>>X log^3 T/T. If R=O(X/T) instead, choose B a sufficiently large fixed integer; then the first term forces S1>>log^5 T/(log log T)^2. These bounds may be weaker than the CRT constraint when both label sets are small, but allow only a small SOURCE support.

(b) Let S be the distinct label count of the whole marked band, so S1,S2<=S. The bare CRT bound implies S^2(1+TR/X)>>T. To prove it take B+1 comparable to a sufficiently large fixed multiple of 1+TR/X, paying the tail by rho X/2. If this cutoff is >=T/2, the conclusion is already trivial since S>=1. Otherwise the first bound in (5) applies. Thus for S=O(log^2 T) one necessarily has R>>X/log^4 T (the term 1 in 1+TR/X is negligible). For R=O(X/T), the same-band support must be Omega(sqrt(T)), stronger than the source-only sieve.

(c) Main sparse-band conclusion below the square-root scale: if T<=X^(1/2-eps) and S<=C0 log^2 T, F>=rho X forces R>>X. In fact choose B=floor(c T) with 0<c<1/2 sufficiently small depending on A0,K,K_w,eps,C0,rho. From the second bound in (5) and (1),

    F_short(B) << X (B+1+(log log T)^4)/T <=rho X/2

for large T. The long relay tail then requires R>=c' X. More generally the conclusion holds for S=O(H^2) by the same proof. This is a macroscopic relay requirement for a macroscopic descent band with sparse support; unlike earlier support-size lower bounds it concerns the physical gain of the intervening events. It neither excludes larger support nor proves such a dominant descent band must exist in a false-double path.

## 6. Executed audit

Source research/min_primorial_ordered_descent_audit.py at 17600e8f4858f902851153d9cd0d411537daaac6, remote blob aec505ab65a20c8089d95966ae63f1bea469df5e matches the locally executed file (git hash-object). Run (requires SymPy and sibling record-supply audit):

    python research/min_primorial_ordered_descent_audit.py 100000

Local brute enumeration: 7136 finite-field density comparisons, 5300 with h=3, 1228 h=2, 608 h=1. Every five-condition density matched brute enumeration, and every exact degeneracy count and four-condition CRT residue count matched. 92 repeat-minimum tests passed.

All 16666 arbitrary integer reset seeds r=7,13,...,99997 up to their first label >r: 317671 pre-record events, 140738 descents. For six bands [T,6T] the audit counted consecutive marked descents (overlapping band populations, not independent trajectories):

 T     pairs    repeats    E<T-3    E=0    local exclusion checks
 7     29762    6174       5801      3607   0
 13    11255    871        2792      1040   0
 31    4118     119        1012      240    3036
 61    1945     35         635       81     4445
 127   553      8          278       38     4170
 257   31       0          30        0      840

Total 47664 pairs, 7207 repeated labels, 10548 short pairs, 5006 zero-relay pairs and 12491 local exclusion checks; all passed. Each short pair also passed the exact product identity and nonzero odd shift test. The audit checks the finite arithmetic ingredients, not the asymptotic sieve inequalities or a bound on first-record displacement.

## 7. Remaining issue

The new pair bounds connect lag descent with ordered relay gain. A low-support band cannot supply macroscopic lag loss without macroscopic relay gain in the sub-square-root regime. However, the total displacement G(r) is still not bounded above: an orbit may distribute lag loss and relay gain across many scales, or use large support in a single band. Controlling that multi-scale alternative or deriving a genuinely unconditional source-support bound from reset ancestry remains necessary. Neither the finite audit nor (6) proves the existence of arbitrarily large r with the short-displacement criterion. Twin infinitude remains open.
