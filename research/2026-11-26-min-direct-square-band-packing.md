# Square-band packing, primorial filtering, and the exact bridge phase lattice

Continuation of [3e47b8d](https://github.com/tara-sooo/A166944-Lean/commit/3e47b8d04171ec244e01bce15b1f0f7e38a0aab5), independent direct-arithmetic branch. We first check what additional information the two clocks give for a fixed bridge. The main new global theorem comes from the elementary integer square geometry and a fixed-pool product barrier. It needs neither the long-wait certification nor any prime-pair estimates, finite-support run complexity, or historical cost decomposition. The square-root eligibility is essential. Twin infinitude and A166944 remain open; paper proofs, not Lean kernel verification.

## 1. Exact phase lattice for a fixed bridge

At an adaptive event let H=pq+e, q odd >=p, e=+1 even/-1 odd, I=(1-e)/2, n winning tick, Z=H+p-1, D=2n-Z-6I. For p>=5, D is a nonnegative multiple of 2p. The clock relation is
    n-2I = [p(q+1)+D]/2.
Thus once H, p, side and D are specified with consistent parity, the winning clock divisibility is automatic. It is NOT an independent extra congruence in q.

For two chronological events with distinct labels p,r>=5, endpoint signs e,f, endpoint indicators I,J, let s=H_2-H_1-(p-1) be intervening gain (all intermediate events), T=n_2-n_1>0. Their exact phase identity is
    2T=s+r-1+D_2-D_1+6(J-I).
Because every intermediate wait is <=3 times its gain, T<=3(s+r-1). Fixing p,r,s,e,f,T fixes the first pre-horizon H_1 modulo 2pr: H_1=e mod p, H_1+p-1+s=f mod r, H_1 even. It also fixes n_1 modulo 2pr: the two absolute clocks fix n_1 modulo 2p and n_1+T modulo 2r. Equivalently, D_1 is 0 mod 2p and s+r-1-2T+6(J-I) mod 2r. Inconsistent parity gives no solution.

For repeated instances of that signed time-pattern on one path,
    Delta H_1 = 2pr*u, Delta n_1 = 2pr*v,
    Delta D_1 = 2pr*(2v-u).
If the two adjusted deficits differ by less than 2pr in absolute value they are equal, and the positive horizon difference is a multiple of 4pr. These are exact necessary lattice conditions. They do not square the previous CRT capacity: the time coordinate is not fixed by the horizon unless further information controls the deficit. Even on an equal-deficit stratum, the improvement in spatial spacing is a factor 2, not another factor pr. Thus no upper bound on the total transition-pattern diversity follows just by multiplying the two congruences.

## 2. Integer square bands and separation

For every adaptive event p, write
    x=(p+q)/2, k=(q-p)/2 >=0.
Then x,k integers, p=x-k, q=x+k, H=x^2-k^2+e.
The inequality q>=p follows directly from eligibility p^2<=H+1: on odd side p^2<=pq; on even side p^2<=pq+2, excluding odd q<=p-2.

Fix 0<eps<1. Call an event near if k^2<=eps*x and x>=X_eps=ceil(16/(1-eps)^2). All sufficiently high events satisfying the band inequality automatically meet this center threshold. Otherwise call it far (for high horizons this means k^2>eps*x). Its pre-horizon is in
    [x^2-eps*x-1, x^2+1],
whose width is eps*x+2. Since k<=sqrt(x) and (1-eps)x>=4sqrt(x) at the chosen threshold, the gain p-1=x-k-1 exceeds this width. Consequently at most ONE near event on a strictly increasing trajectory can have any given center x. These bands are ordered and disjoint for x>=X_eps, so centers of successive near events strictly increase, even if their labels do not.

For two successive near events, write x'=x+j, j>=1, and second parameters k',f. Then intervening gain s=H_2-H_1-(p-1) is exactly
    s=(2j-1)x+j^2+k^2-k'^2+k+1+f-e.                   (1)
Moreover H_2>= (x+1)^2-eps*(x+1)-1 and H_1<=x^2+1, so
    s >= (1-eps)x+k-eps.                             (2)
In particular with fixed eps, s is at least a positive constant times p. In a sharper band k^2=o(x), k'^2=o(x') along an unbounded sequence, if s<=K0 p for a fixed K0, the band bounds show x'~x and j=O_K0(1). Equation (1) then gives
    s/p=2j-1+o(1).
Thus the normalized intervening gain approaches the set of positive odd integers. For fixed eps, the error from the two k^2 terms is at most eps+o(1), since both squares are nonnegative and at most eps*x or eps*x'; the other terms are o(p). This quantization is conditional on the two events being near, not all certified bridges.

## 3. Half-gain packing bound

Consider any finite contiguous event block with pre-horizons in [A,Y], 8<=A<=Y. Every near center lies between
    lo=ceil sqrt(A-1),
    hi=floor((eps+sqrt(eps^2+4(Y+1)))/2),
from x^2>=H-1 and x^2-eps*x-1<=H. Define
    J0=max(0,hi-lo+1), S0=sum_{lo<=j<=hi} j
(with S0=0 when empty). One event per center and p-1<=x give exact bounds
    count_near <= J0, gain_near <= S0.                (3)
Uniformly in A<=Y, J0=O(sqrt(Y)) and S0<=(Y-A)/2+O(sqrt(Y)), since lo=sqrt(A)+O(1), hi=sqrt(Y)+O(1). No prime condition on q, waits, or reset phases is used.

For a crossed [X,Y] with Y=lambda*X for fixed lambda>1, use the block from first horizon >=X to first >=Y, with pre-horizons in [X,Y]. The start overshoot <=sqrt(X+1) by eligibility, so total gain G>=Y-X-sqrt(X+1). Therefore at least
    (Y-X)/2-O(sqrt(Y))
gain comes from far events. Unlike earlier near-diagonal sieve bounds, this works on the much wider band q-p<=2sqrt(eps*x), of order H^(1/4) near the square boundary. It gives a half-gain upper bound, not an o(Y) upper bound, so the older sieve estimate for very narrow certified bands is not superseded in its own range.

## 4. Product barrier and filtering out small labels

For integer R>=3 define K_R=2 product_{3<=l<=R, l prime} l. At any even multiple J of K_R, a run restricted to labels p<=R cannot cross from H<=J to H'>J. Indeed H=J has no active such label. For H<J with H=e mod p, J-H is positive even, congruent to -e mod p, so it is at least p-1 (e=+1) or p+1 (e=-1). The jump p-1 cannot cross J. Choosing the next multiple of K_R at or above the run's start shows every such run has gain <=K_R. This is an elementary absolute bound and does not require the previous uniform support-length theorem. One may replace K_R by any proven smaller run-gain bound.

In a contiguous block as in section3, partition events into low labels p<=R (gain U), near labels p>R (gain N), far labels p>R (gain F). All gains nonnegative and G=U+N+F. The number of high near events <=J0, and number of high far events <=F/(R-1), since their gains >=R-1. Low runs, separated by high events, number at most J0+F/(R-1)+1. Therefore
    U <= K_R*(J0+F/(R-1)+1).
Combining with N<=S0 proves the exact finite inequality
    (1+K_R/(R-1))*F >= G-S0-K_R*(J0+1).              (4)
This is stronger than a double-loss estimate obtained by applying (2) separately to every near-to-near interval. For comparison, (2) also implies if both near endpoint labels are sufficiently large and every intermediate label <=R then s<=K_R, impossible. Thus long near-only high-label paths cannot be sustained by finite-pool intermediates, regardless of clock phase.

## 5. Global far-from-square theorem

For any infinite adaptive ray and any fixed lambda>1, every sufficiently large [X,lambda X] is crossed. All near events then have centers above X_eps automatically. Let Y=lambda X; G-S0 >=(Y-X)/2-O(sqrt(Y)). Fix R>=3. In (4) the term K_R*(J0+1)=O_R(sqrt(Y)) is lower order, yielding
    F >= Omega_(eps,lambda,R)(X).
Thus for EVERY fixed R and every fixed eps in (0,1), a positive fraction of horizon-scale gain in EVERY sufficiently large crossed window comes from events p>R with
    q-p=2k>2sqrt(eps*x)>=2sqrt(eps*p).                 (5)
This is unconditional on the primality of q; it is also independent of finite-twin assumptions beyond using them to obtain infinite canonical rays. In particular, if outside a fixed finite set of labels all sufficiently late events satisfy the near-band inequality, the adaptive trajectory MUST terminate. The union of a finite small-label pool and an arbitrary unbounded sequence of near-square labels is not enough for an infinite trajectory.

More quantitatively K_R <=2 exp(4(log 2)R), by the elementary dyadic-binomial bound theta(R)<=4(log 2)R (already proved in the absolute-scale note). For fixed 0<eta<1/2 put
    R(X)=floor(eta log X/(4 log 2)).
For large X, R>=3, K_R<=2 X^eta, K_R*(J0+1)=O(X^(eta+1/2))=o(X), and 1+K_R/(R-1)=O(X^eta/log X). Equation (4) yields
    F >= Omega_(eps,lambda,eta)(X^(1-eta) log X),
    number of these far events >= Omega_(eps,lambda,eta)(X^(1/2-eta) log X).
The count follows because each jump <=sqrt(Y+1). In particular eta=1/4 gives a logarithmically growing lower cutoff R~log X/(16 log 2), far gain Omega(X^(3/4) log X), and at least Omega(X^(1/4) log X) far events in each large crossed window. Alternatively R=floor(log log X/(4 log 2)) gives K_R<=2 log X and far gain Omega(X log log X/log X). No assumption of finite total multiplicity of each fixed prime is needed. These estimates use no PNT or sieve.

Under finite twin primes, any canonical adaptive ray above the last twin center is infinite, so these necessary conditions apply to all such rays. They are a new direct global stopping criterion, excluding an eventual near-square regime plus bounded labels. They do not say that the far events have prime cofactors, or that their cofactors differ by two. In particular they do not exclude the small-label concentration alternative of the earlier global roughness theorem, since it can coexist with far events. Nor is the earlier proposed upper bound A^2 T=o(Y^(1/3)) proved.

## 6. Exact diagnostics and status

[Audit 47deb5a](https://github.com/tara-sooo/A166944-Lean/blob/47deb5a03a55b3ebe6406a2b794c1346985ba90d/research/min_direct_square_band_packing_audit.mjs), blob a6d898136e8ac6615c14f41c5db41b910264d8d2; exact remote readback. Run:
    node research/min_direct_square_band_packing_audit.mjs 150000 180

Actual ECMAScript function executed in tool runtime (not separate Node process). All odd canonical M=5..150000, at most180 nonunit events, 1,630,951 actual events, 73,479 nonempty paths, zero range truncation, 1,787 independent literal parity-GCD comparisons. For eps=1/4,1/2,3/4 with their respective center thresholds, near-event incidences 1633/2231/1854, successive near-pair checks 19/19/12; 220,437 packing interval checks. Example M64419, p359,q359,H128880,e=-1, then near p353,q367,H129552,e=+1, centers359 and360, k0 and7, intervening gain314; actual events not adjacent. For R=3,5,7 also verified 220,437 uniform-support filtering checks and 36 between-near filter checks (using previous bounds L=2,5,11). For independent primorial K_R at R=3,5,7,11,13: 5,096,823 low-event barrier checks, 367,395 block/filter checks and 367,395 stronger linear-loss bound (4) checks, plus 361,869 checks of weaker two-stage bound when its size hypotheses hold. Phase lattice checked 437,937 adjacent distinct-label pairs p,r>=5, 3704 repeated signed-time-pattern pairs, 753 low-deficit-difference cases, all pass. No claim that asymptotic far-gain estimates have been observed on a large crossed window. All finite examples are source incidences, not independent physical trajectories.

No Lean executable/kernel verification or final twin proof. Main and sibling branches unchanged. Next: seek a direct obstruction to the many far-from-square events, possibly by combining their mandatory gain with timing and cofactor structure; in particular distinguish large far events with short waits from those whose waits certify cofactors. The phase lattice itself supplies no multiplicative improvement without further coupling.
