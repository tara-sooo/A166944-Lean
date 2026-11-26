# Multiband weighted deficit-coordinate sieve with short-range baseline

Continuation of [bc3b10b](https://github.com/tara-sooo/A166944-Lean/blob/bc3b10b88fe25e845935164e571bed5f650ace87/research/2026-11-26-min-direct-low-scale-localized-deficit-sieve.md). Use one selected list across all label bands, not a separately filtered list in each band. Attach a horizon bin of length T*L to an edge ending in the label band [L,2L), assigning it by the FIRST horizon even when its endpoint lies outside that bin. Count deficit coordinates in shorter padded ranges than T. The geometric endpoint weights control the repeated variation budgets across bands, and relay gain is charged only once globally. This gives a multiband necessary supply condition and a stronger polynomial tradeoff when ordinary variation is particularly small. It remains conditional on the selected gain, caps or small normalized budgets; it does not eliminate the full small/middle crossing branch.

## 1. Setup

Let X tend to infinity, Y=lambda X with fixed lambda>1, C=floor sqrt(Y+1). Take a contiguous actual MIN block with pre-horizons in [X,Y], gain G=O_lambda(X). Choose integer thresholds T,R with T->infinity, 7<=T<=R<=C, and R<=K_R T^b for fixed K_R,b>=1. Select an arbitrary subset of nonreset events with p in [T,R] in ONE physical list. At each event p, g=p-1, side I, e=1-2I, ordinary post-deficit d', coordinate x=(d'-6I)/2=hp>0. Initially impose x<=K T^beta for fixed K>0, 1<=beta<2. In particular x<T^2 eventually, so there is at most one distinct prime divisor >=T of x. Each selected x uniquely determines its label.

For consecutive selected events p,r, first pre-horizon H, second H2, write E=H2-H-(p-1), v=d2'-d1', c=x2-x1=v/2-3(J-I). Close means E<=B and |v|<=A for nonnegative integer cutoffs B<T-1 and Q=floor(A/2)+3<=T/2. Then |c|<=Q, p!=r by exact repeated-label spacing, and c!=0 by uniqueness of the large divisor. No long-clock, prime cofactor, crossing or finite-twins assumption is used.

Set m=1+floor(log_2(R/T)), so the ending label bands [L,2L), L=T*2^j for 0<=j<m, cover [T,R]. Fix nu=1 or2, with nu(beta-1)<1, and choose a fixed real theta with
    nu(beta-1)<theta<1, theta>0.
Set W0=ceil(T^theta). In contrast to the previous theorem, W0 is strictly smaller than T in order of magnitude. The smaller padding is still enough for a uniform sieve in the allowed multiplier range.

## 2. Assign edges by their ending band and starting horizon

For an edge ending with r in [L,2L), assign its FIRST pre-horizon H to the half-open bin [j T L,(j+1) T L), j integer. It is immaterial whether H2 is in that bin. Keep only close edges with both coordinates capped. For fixed ending coordinate x2, signed c, E, and sides I,J, both labels are uniquely determined by x1=x2-c and x2. The necessary horizon conditions
    H=e mod p, H+p-1+E=f mod r
give a single residue modulo pr>=T L, since p!=r. Thus at most one H per bin for these data. On one fixed actual filtered list H determines at most one starting event and one next selected event. The counting weight is r-1<2L. No cross-bin or cross-band edges need to be discarded. We use neither independence nor any bound on the number of possible trajectories across roots.

In each nonempty edge group (L,j), take the range R_(L,j) of its ending x2 coordinates and W_(L,j)=max(W0,R_(L,j)+1). For fixed c count possible ending x2 in the corresponding translated interval of length W=W_(L,j).

For nu=1, impose only the ending prime condition x2=kr with r in [L,2L). If a=min x2>=W, then k in [a/(2L),2a/L], positive, and k<=K T^(beta-1). For fixed k pad the prime interval to N=ceil(W/k)+1. Since W/k>>T^(theta-beta+1), its logarithm is comparable to log T from below. Also W=O_K(T^beta), so the earlier one-dimensional Selberg sieve cutoff N^(1/12) is below T for large T. The count is O((W/k)/log T), and sum 1/k over the bounded-ratio interval is O(1). If a<W, cover [T,min(2W,K T^beta)] by dyadic shells [D,2D), D=T*2^i; total shell widths O(W). The same argument on each shell works since D>=T>=W0 eventually. Thus the candidate count per fixed c is O(W/log T). The ignored first prime condition is still necessary and its label is unique when it holds, so omitting that test does not increase the number of horizons per tuple.

For nu=2, impose also x1=hp=x2-c with p in [T,R]. In the away-origin interval, |c|<=T/2<=a/2, so h in [a/(2R),3a/T] and k in [a/(2L),2a/L], both <=K T^(beta-1). Write g=gcd(h,k)|c, a0=h/g,b0=k/g,c0=c/g. Compatible simultaneous congruences for x2 give a line x2=x0+(hk/g)z. The two required prime forms (x2-c)/h and x2/k have integer slopes b0,a0 and determinant of absolute value |c0|. Parameter interval padded length N=ceil(Wg/(hk))+1 is polynomially large, since Wg/(hk)>>T^(theta-2(beta-1)). The same two-dimensional Selberg estimate with omitted slope and determinant primes is
    O((Wg/(hk)) J(a0)J(b0)J(abs(c0))/log^2 T),
where J(n)=prod_(odd prime f|n) f/(f-2). At fixed g, the harmonic sum of J(b0)/b0 is O(1) on its bounded-ratio range, and that of J(a0)/a0 is O(m), since its endpoint ratio is O(R/T). These also hold if a lower endpoint is below 1, by the same bounded mean of J. Summing gcd and signed displacement as in bc3b10b gives a total O(W (A+1)m/log^2 T): indeed sum_(c<=Q) sum_(g|c) J(c/g)/g=O(Q). The near-origin dyadic shells give the same bound with sum of widths O(W). All sieve constants depend on fixed K,beta,theta,nu, not on R/T, X or the baseline deficit.

Combining both dimensions, summing E and sides, and weighting the ending gain gives for each group
    F_(L,j) << L W_(L,j) (A+1)(B+1) m^(nu-1)/log^nu T. (1)
The factor m in the two-dimensional case comes only from the larger starting-multiplier range; in dimension one there is no such loss.

## 3. Geometric weighting of local ranges and one global relay budget

For each fixed ending band L, the number of its nonempty bins is O_lambda(X/(T L)): T L<=Y+1, and starting horizons are in [X,Y]. Within each bin group consider the physical interval from its first ending POST state to its last ending POST state. These intervals are disjoint for different bins of the SAME ending band because the order of first horizons is the order of their successor visits. Let V_(L,j) denote their ordinary absolute variation. Then
    R_(L,j)<=V_(L,j)/2+3,
    W_(L,j)<=W0+V_(L,j)/2+4,
    sum_j V_(L,j)<=V_d,
where V_d is total physical ordinary variation on the block. Across different ending bands these intervals can overlap; do not assert their disjointness. Instead use the exact geometric bound sum_L L<=2R:
    sum_(L,j) L W_(L,j)
        = O_lambda(X W0 m/T+ R V_d).
This avoids a factor m multiplying the variation term from repeated endpoint-band accounting. Summing (1) gives the new multiband supply bound
    F_close << (X W0 m/T+R V_d)(A+1)(B+1)
                        m^(nu-1)/log^nu T.             (2)
All close edges of the ONE selected list are included, not just within-band edges. If the list is uncapped, (2) still bounds the close edges with both endpoints capped: uniqueness holds for these endpoints, and the actual ending-state intervals retain their ordering even when other edges are omitted.

Let F be total selected gain, U_out=G-F. All consecutive selected relay intervals are disjoint over the entire list, sum E<=U_out. Similarly their post-to-post variation intervals are disjoint, sum |v|<=V_d. These are GLOBAL budgets, not sums of separately filtered same-band relay gains. The first vertex costs <=R, and ending vertices of edges with E>B or |v|>A have gain <=R. In the capped case we obtain
    F <= R + O((X W0 m/T+R V_d)(A+1)(B+1)m^(nu-1)/log^nu T)
                   + R U_out/(B+1)+R V_d/(A+1).         (3)
No loss from cross-bin boundaries occurs. This replaces the former single-band estimate with one valid for arbitrary mixing of the specified labels and smaller padded deficit range.

## 4. Refined multiband tradeoff

Write
    y=R V_d/X, z=R U_out/X,
    e_T=m W0/T, L_T=log^nu T/m^(nu-1).
With R<=K_R T^b we have m=O(log T), e_T=o(1), and L_T >> log T (for either nu, up to constants). Suppose F>=rho X for fixed rho>0. Then
    (e_T+y)(1+y)(1+z) >>_(lambda,K,K_R,b,beta,theta,rho) L_T. (4)
If the product is already >=L_T there is nothing to prove. Otherwise y,z<=L_T/e_T=O(T^(1-theta) log^2 T)=o(T). Choose A=ceil(K0 y), B=ceil(K0 z) with fixed K0 sufficiently large depending on rho. Both cutoffs are o(T), hence meet the close conditions. The last terms in (3) are <=2X/K0, R<=C=o(X), and the close term is O(X(e_T+y)(1+y)(1+z)/L_T). Rearrange to prove (4).

Since e_T=o(1), this implies the less precise familiar product (1+y)^2(1+z)>>L_T, hence U_out+V_d=Omega((X/R)L_T^(1/3)). The improvement is strongest for small y: if y<=1, then (1+z)(e_T+y)>>L_T. For any fixed 0<delta<1-theta, if V_d=O((X/R)T^(-delta)), then e_T=o(T^(-delta)), and
    U_out = Omega((X/R) T^delta L_T).                   (5)
In particular flat or very narrow variation does not allow a macroscopic capped population that is nearly consecutive even when spread across label bands. The scale R, not T, appears in normalized budgets because the ending gains of exceptional edges can be as large as R. This distinction is essential for wide bands. For bounded R/T, L_T is comparable to log^nu T, reproducing the earlier balanced-budget lower bound but improving the very-low-variation regime. For polynomial R/T, dimension two can lose one logarithm; no claim of the full two-log saving uniformly across all bands.

## 5. Uncapped alternative

Without any x cap keep the ONE selected list, F>=rho X, with labels in [T,R]. For a chosen cap K T^beta with nu(beta-1)<theta<1, count close edges with both coordinates capped using (2). All other close endings have x2>K T^beta-Q, since |x2-x1|<=Q. Therefore if F_high denotes gain with x>K T^beta-Q,
    F_high >= F-R
      -O((X W0 m/T+R V_d)(A+1)(B+1)m^(nu-1)/log^nu T)
      -R U_out/(B+1)-R V_d/(A+1).                      (6)
If (e_T+y)(1+y)(1+z)=o(L_T), choose a slowly growing L0 such that L0^2 times that product is still o(L_T) and A=ceil(L0 y), B=ceil(L0 z) are o(T). The latter is possible by the preceding polynomial upper bound for y,z. Then Q=o(T), all errors in (6) are o(X), and gain at x>(K-o(1))T^beta is >=F-o(X). With nu=1, choose theta in (beta-1,1) for each fixed beta<2. Thus the high-deficit escape applies to a multiband population, not only a dominant single band. The smallness condition depends on theta,beta and the chosen range; no automatic escape for every low-count alternative is implied.

In particular the prior pin-only count alternative does not force a macroscopic gain among the selected nonresets in [T,R], nor small U_out,V_d, nor a cap on x. This work handles the multiband aggregation bottleneck in the conditional supply estimate but leaves the actual forcing of its hypotheses, the high-deficit population, resets and the small/middle crossing counts open. No final contradiction is obtained. The next useful target is an actual upper bound on variation or high-deficit nonreset supply using the MIN rule, rather than another conditional change of label scales.

## 6. Diagnostics and preservation

[Audit ef959df](https://github.com/tara-sooo/A166944-Lean/blob/ef959df5647b10024d2f647601d604e1b09b92db/research/min_direct_multiband_deficit_sieve_audit.mjs), blob f2338e90341231df2e1303613df75ccbb4785afc, exact remote readback. Run node research/min_direct_multiband_deficit_sieve_audit.mjs 40000. Actual ECMAScript executed in tool runtime, not a separate Node process. 19998 odd canonical roots through40000,352451 events,0 unresolved cap180.154848 finite capped/uncapped block controls,458805 selected incidences,303957 consecutive pairs,16048 capped close edges incl6008 cross-band and2292 crossing the assigned horizon-bin boundary.65843 controls with multiple selected bands.14914 nonempty edge groups,1134 multi-edge groups,14520 ending-band range checks,32096 unique divisor checks,16048 exact CRT and tuple uniqueness tests.154848 global relay/variation partitions and weighted local range budgets,81902 uncapped controls,8181 high-escape incidences. Independent controls:9996 abstract CRT tests,16265 synthetic groups and6000 synthetic same-band variation bounds. Example T11,p11,r23,x44->46,H978->990,E2,v-2,ending band L22,bin length242. Counts overlap across controls. Finite caps floor(T^1.45), floor(T^1.8) and padding ceil(T^.95); the audit exercises arithmetic and budgets, not the analytic prime-line sieve constants or asymptotic tradeoffs. All assertions passed. No Lean executable/kernel verification, external novelty claim or twin-infinitude contradiction. Main and sibling branches unchanged.
