# Bandwise overlap caps, source-local common origins, and physical phase transfer

2026-11-25 JST. Continuation of 40d101b608145d2dac29c9dfdaef03e18bcc89a6. Enlarges the previous overlap cap by budgeting the square root of each band's arithmetic pair count separately. Further removes thin source-cell portions of arbitrarily heavy intersection sets. An exact normalized pair ledger then partitions residual common origins by physical synchronization before, during, or after the repeat segment. Provides a sufficient medium energy-transfer criterion, not a proof of the residual moments. No Lean compilation or novelty assertion.

## 1. Setup

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u). Freeze actual medium events y<p<Q (or subset after paid previous marks), selected prime p, least eligible prime r(C)<=p. Attach each LOW block to its preceding nonLOW anchor, w_r=r+1.5L, L<=ell^.25 as in 711a0db. Initial and high-attached LOW and first k=floor(u^.25) per root/r/aligned cell A_r=ceil(w_r² u^1.5) paid o(NT). All repeat pair counts refer to the frozen medium list before first-k deletion. The high definition and earlier high-energy arguments are unchanged.

For dyadic P<=r<2P, r<Q, write l_P=log(2P), e_P=1+log l_P, lambda_P=sqrt(P/Q) log Q/l_P. In 40d101b, the band Cauchy coefficient C_P<<NH P/(u^1.5 l_P). The short gap D_r=max(1,floor(r u^1.5 log²(2+min(r,u))/ell^1.5)) contribution to sum sqrt(C_P Z_P) is o(NT), independent of overlap. For each long pair C<E in the same aligned r-cell and r(C)=r(E)=r, V_r(C,E) counts actual common origins with both medium hits. Each unordered pair incidence contributes two to Z_P. Previous caps c'_r=max(1,floor(max(1,floor(log^6 r))/lambda_P)) have negligible weighted moment. For any remaining weighted moment W, its clock contribution is bounded by sqrt(O(NXB/u^3.75) W), by sum C_P/lambda_P. Here and below splitting a moment is not a disjoint linear deletion of endpoints.

## 2. A larger bandwise cap

Let K_P be the total number of arithmetic same-r horizon pairs in the band, including short and long, ignoring alignment if convenient. The earlier least-factor four-form sieve in 711a0db gives
    K_P << X u^1.5 P e_P^4/l_P^5,                  P>=u².
Indeed per r the bound is X u^1.5 (1+loglog r)^4/log^4 r and the number of primes in the band is O(P/l_P). For P<u² (including a band crossing u²), use instead the elementary congruence h=0 or +/-2 mod r, with A_r/r²=O(u^1.5 (1+L/P)^2):
    K_P << X u^1.5 (1+L/P)^2 P/l_P.
Both bounds count possible keys, not source pairs or physical states.

Define b_P=max(1,floor(b_P^*)) where
    b_P^*=(B/P)^2 u^(-1.5) sqrt(P/Q) * f_P,
    f_P=l_P^6/e_P^4 if P>=u²,
    f_P=l_P²/(1+L/P)^2 otherwise.
The cap is defined for all nonempty bands P<Q. Uniformly the minimum b_P^* grows faster than u^.25: for P>=u², on P>=sqrt(Q) use l_P~u and B/P>=B/Q, giving >>u^6.5/ell^4; below sqrt(Q) the power of Q in (B/P)^2 sqrt(P/Q) dominates any logarithms. For P<u² the bound likewise dominates every fixed power of u. Floors and min1 do not affect the limiting estimates. For top P~Q, b_P is of order u^6.5/ell^4, compared with old order u^6. For lower P the power of P in the cap, ignoring logarithms and L, is -3/2 versus old -1/2. For fixed P the new order is B^1.5/u times l_P²/(P^1.5(1+L/P)^2), using Q~B/u. The exact expression above governs all scales.

For all long keys with V<=b_P, Z_P^cap<=2 b_P K_P. The product of Cauchy coefficient and support cancels all band logarithms:
    C_P b_P K_P << NH X B² u^-1.5 sqrt(P/Q).
Therefore
    sum_P sqrt(C_P Z_P^cap)
      << sqrt(NH X B²/u^1.5) sum_P (P/Q)^.25
      = O(NT/u^.125)=o(NT).                         (1)
Use N~X/u, H~T~X/u^.25, B²~X and the bounded geometric sum. This proof does NOT claim that this cap's weighted moment is o(NBu³); it pays directly in the bandwise clock sum. Union with the old cap by sqrt(a+b)<=sqrt a+sqrt b. The new cap can be used even without the old cap.

## 3. Source-cell density at both horizons

For a fixed long key (r,C,E), all its common sources satisfy C-H<2M-2<=C. In particular they occupy an interval of length <H/2. For each scale d_j=ceil(H/2^j), 0<=j<=floor((log_2 u)/4), partition the entire source range into fixed aligned half-open cells [X+id_j,X+(i+1)d_j). Let V_i count actual common tags at C AND E in cell i. At most J_d=ceil(H/(2d))+2 cells can occur for each key. Use cell cap
    m_{P,d}=max(1,floor(b_P/J_d)).
The min1 is immaterial for large X, since b_P>>u^.25 uniformly and J_d=O(u^.25). For each key, the total number of tags in occupied cells with V_i<=m_{P,d} is <=J_d m_{P,d}<=b_P. Thus the band moment of these thin portions is <=2b_P K_P, EVEN IF V is arbitrarily large. This is a new stronger condition than a cap on entire V. It requires neither physical synchronization nor any bound on individual horizon marginal masses.

Use all O(ell) scales at once, defining the cells and masses on the frozen original intersection at that key, not recomputing after other marks. The union of thin portions has Z_P<=O(ell b_P K_P), so by (1) its clock contribution is O(NT sqrt(ell)/u^.125)=o(NT). The earlier cap and first-use and short-gap terms are separately paid. Every residual tag belongs to a source cell at EACH scale with >m_{P,d} original roots sharing both C,E. These are intersection masses, not merely thickness at one of the two horizons. Different scales may use different companions. No claim that the surviving tag count in the cell itself exceeds the cap after union deletion.

One could instead use any fixed family of source cells whose maximum overlap count per key is bounded and sum of the corresponding cap budgets is o in (1). The stated ladder is a definite parameter choice; no dynamic modification of MIN.

## 4. Exact physical-phase partition of the residual

Fix one of the stated scales (e.g. finest) and a long key/cell. Let A be the FULL frozen common-source set in that cell, n=|A|; let S be those tags that remain after the cap union and all thin-cell tests. If S is nonempty, n>m_{P,d} and n>=2. All A visit C and E with actual physical times t_M(C), t_M(E). Partition A by the first time t at C, and separately by the second time s at E. Define a_t and b_s to be the corresponding group sizes. The first partition refines the second: if two roots have the same t at C, they follow identical deterministic suffix until either stops. Since both visit E, their times at E are equal. This statement uses original paths and remains true on any frozen incidence subset. It does not identify equal projected horizons with physical synchronization.

For each M in S with endpoint times t,s, its n-1 OTHER common-source partners in A split exactly into
    a_t-1                 (already physically synchronized at C),
    b_s-a_t               (first physical meeting in (C,E]),
    n-b_s                 (still physically asynchronous at E).
All three are nonnegative and sum to n-1. The last class has never physically met before E; if they had, deterministic suffix would force equal times while both are present. Define three weighted moments by summing respectively 2 lambda_P times each of these counts divided by n-1 over every residual key/cell/tag in S. Denote W_early, W_new, W_async. Then exactly
    W_res=W_early+W_new+W_async,
    W_res=2 sum_{remaining key tags} lambda_P.         (2)
This directed normalized counting is important: partners are from the full A and need not themselves survive. Each focal surviving tag gets total weight 2lambda_P, no double counting of its own moment. An unordered source pair can supply both directions when both are focal tags; the formula accounts for that. None of these is the previous high off-diagonal energy; they count repeat segments with two sources.

## 5. Sufficient transfer to medium endpoint energies

There is also a useful upper bound that removes the normalization at the price of a cell-dependent coefficient. Set
    U_r = const * A_r/(r log²(2r)).
For any fixed r-horizon C, there are <=U_r other r-horizons in its aligned cell, using the uniform two-form sieve with quotient length O(A_r/r), sieve level r^1/8, and bounded-r cases by the trivial progression count. The error r^.75 is absorbed because A_r/r>=r u^1.5. The same holds when fixing E and looking backward. U_r is an upper envelope, not a claim of uniform distribution of actual events.

At a horizon C and source cell i, count ORDERED distinct source pairs with both frozen medium hits at C: S_{r,i}(C) counts those with equal physical times, A_{r,i}(C) those with different times. Define weighted endpoint energies
    H_sync = sum_{r,i,C} (lambda_P U_r/(r m_{P,d})) r S_{r,i}(C),
    H_async = sum_{r,i,C} (lambda_P U_r/(r m_{P,d})) r A_{r,i}(C).
Here sums use the fixed scale d in (2), r=r(C)<Q. These are medium energies with an explicitly r-dependent coefficient. Since n-1>=m_{P,d}, a directed pair at C with equal physical time is counted at most U_r times over all possible later E (same r, same aligned horizon cell); similarly at E for the new-sync or async class over earlier C. Focal and partner must both be medium tags at both endpoints, so relaxing the other endpoint only increases the bound. It follows that
    W_early <=2 H_sync,
    W_new   <=2 H_sync,
    W_async <=2 H_async.                              (3)
One could retain the exact normalized weights of (2) instead, which is usually sharper. Equations (2)-(3) give an explicit connection to physical-suffix and asynchronous endpoint techniques, but do NOT bound H_sync or H_async at the required scale. In particular no transfer from high-energy smallness to medium-energy smallness without further proof is asserted.

## 6. Joint residual

Combining the previous short-gap/first-use and old cap estimates, (1), cell union, and the previous weighted Cauchy coefficient,
    R_med,rem << o(NT)+sqrt(O(NXB/u^3.75) W_res).
Thus a new sufficient medium condition is W_res=O(NBu³) or o(NBu^3.25), equivalently the corresponding bound for the sum in (2). A sufficient (potentially stronger) condition is H_sync+H_async=O(NBu³). The previous high residual condition E_phys,admitbad+E_async,bad=o(T²Bu) remains independent and OPEN. These two conditions on the same unbounded dyadic windows would give the gain-prefix contradiction R=o(NT) without twin terminals. No actual residual estimate or twin-prime proof. Next: control the actual three classes, e.g. use first physical meeting tail ledgers with the medium repeat-clock weights, or reverse-phase constraints on pairs that stay asynchronous across the whole long gap. The cell caps give actual shared source clusters at both endpoints.

## 7. Audit

Standalone ECMAScript research/min_prime_root_band_cap_audit.mjs, exact remote readback at 3c5b95eb3451a91c4f59f2f3c3453d432293c132, blob 64f4ee3073f540cd45b12b242a60faba82c31654. Run:
    node research/min_prime_root_band_cap_audit.mjs 256 1024 4096 16384 65536 262144
Executed its audit function in available ECMAScript runtime, not a separate Node process. All 18 runs (three modes x six windows) passed. Inherited literal parity-GCD checks at X256/1024 (short1183,wide1707,analytic1719), LOW, band and overlap ledger; long keys store exact (M,t(C),t(E)) triples. Checks source locality cell envelope, thin-cap counting, disjoint old/band/cell union, original-cell phase refinement and exact three-class normalized weights with floating tolerance. Does not independently audit endpoint upper bound (3), which follows from the counting proof, asymptotic sieve constants, or cumulative previous marks.

Analytic mode uses b_P as stated (finite floor/min1), source widths ceil(H), ceil(H/u^.125), ceil(H/u^.25) (not the full increasing dyadic ladder). Every old-heavy pair is covered by b_P in all tested analytic windows; the finite residual-phase check is therefore vacuous in that mode. Diagnostic short/wide use old finite caps multiplied by 2 sqrt(Qm/P), widths ceil(H),ceil(H/2),ceil(H/4), subcap=max(1,floor(b/J_d)). The diagnostics deliberately reduce thresholds to exercise nonempty residuals; not estimates of asymptotic removal rates. With min1 at finite sizes the cell bound is m*actual cells, not necessarily b; the paper b bound is eventual. Fixed finite LOW y3,L6. 

Largest analytic X262144: old weighted long-heavy 30582.0582, unweighted80386; all 80386 covered by b_P. Largest wide: old-heavy66 all band-covered. Largest short X262144: old-heavy5440, additional band5310, thin-cell2, final128 (64 focal tags at 5 long keys). Weighted final78.2409901367 = early31.3712299324 + new34.0588040331 + async12.8109561711. 17 cell checks and 64 coarsening/phase checks on surviving cells. At short X65536, old-heavy1154, extra band1124, final30 (15 focal tags, one key), weighted16.6847053214 all early sync. Earlier short windows and wide residual empty. These are diagnostic partitions, not a limiting result. Main and other branches unchanged.
