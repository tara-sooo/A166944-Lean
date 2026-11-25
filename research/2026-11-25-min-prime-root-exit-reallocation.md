# Exit-group reallocation for sparse medium repeat costs

2026-11-25 JST. Continuation of 0ce6427caa7d6ba32c2c0946fdd879b3a69d9378 on research/min-prime-root-repeat-energy-2026-11-25. A new accounting choice for the residual sparse quota: use large groups sharing an actual physical successor as partner pools; for the remaining small groups, discard a small relative pool or use its own normalized partner ledger. This pays all retained near-exit-time interactions at o(NT) and leaves only far asynchronous interactions and two types of physical formation. The original uniform-partner asynchronous component need not be small: reallocation changes the partition but preserves the actual clock cost. No Lean compilation or proof of residual estimates.

## 1. Setup and inherited quota

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime roots M in [X,2X), Q=ceil(B/u). Original gain-stopped MIN prefixes, including terminal vertices, are unchanged. Freeze medium incidences y<p<Q, possibly after already-paid marks. For the least eligible odd prime r=r(E)<=p at a medium hit E, write P<=r<2P for its dyadic band, l_P=log(2P), and w_r=r+1.5L with L<=ell^.25 the earlier LOW primorial. The actual clock-plus-attached-LOW cost a_M(E) lies in [r,w_r]. The total such cost is O(NH).

In the sparse quota of 0ce6427, each root/r/aligned horizon cell of width A_r=ceil(w_r² u^1.5) pays the first k_P hits, with
    k_P=ceil(u^1.5/ell^1.25 + u^1.5 l_P (1+L/P)(P/Q)^.25/ell).
Each subsequent medium hit E assigns a_M(E)/k_P to each of its last k_P preceding hits C in the same list and cell. First-use, short gap, bandwise sparse-overlap cap b_P, and thin source-cell tests are already paid o(NT). Use the same finest fixed source-cell width d=ceil(H/2^floor(log2(u)/4)), J_d=ceil(H/(2d))+2. Its mass cap m_P=max(1,floor(b_P/J_d)). The original cap is
    b_P=max(1,floor((B/P)^2 u^-1.5 sqrt(P/Q) f_P)),
    f_P=l_P^6/(1+log l_P)^4 for P>=u²,
        l_P²/(1+L/P)^2 otherwise.
For each remaining long key (r,C,E) in a fixed source cell, A is the FULL original sparse common-source set of size n>m_P and S is the surviving focal subset. Each A tag has one quota edge at this key; some partners in A may have already been paid. Across all these full cells and keys, the sum of their original allocated costs (including paid tags) is at most the total original medium cost. It is important to use this full sparse set, not recompute masses after exclusions.

The previous uniform allocation a_M(E)/(k_P(n-1)) was one way to account for each remaining focal edge. We replace it in this note. Neither the original medium hits nor the previous arithmetic cap tests are changed.

## 2. Successor groups and bounded near-time degree

At a fixed E, the actual next physical state of a medium tag is (s,E+p-1), where p is the actual selected prime in [r,Q) and s is the next tick after its current time t. Partition A by this successor key (s,p). Different selected labels cannot have the same output tick at E, by the lexicographic MIN tie rule. Each eligible odd p divides exactly one of E-1,E+1, determining a progression of ticks with period 2p (0 or p+2 mod 2p). The number of eligible primes >=P is O(u/l_P), since their product divides (E-1)(E+1)=O(X²) and each is >=P. Hence, for any given successor time s, the number of possible distinct successor keys with |s'-s|<=D, including the given key, is at most
    Delta_P(D) << (1+D/P) u/l_P.                       (1)
For each p, at most floor(D/p)+1 ticks occur in the interval of width 2D. This is independent of the actual source masses or of the existence of other keys. No prime distribution or CRT independence assumption is needed.

Set
    K_P=ceil(u^(1/8) u/l_P),
    U=u^(1/32),
    D_P=floor(P u^(1/16)).
Call an exit group large if its mass g is >=n/K_P, otherwise small. Let s_0 be the total mass of all small groups; use a different symbol from the actual tick s. Uniformly m_P/K_P grows without bound by the estimates in section 4, so every large group eventually contains at least two tags. At finite sizes we use max(2,n/K_P) for the large test and treat a pool of fewer than two tags as tiny; the asymptotic definitions are unaffected.

## 3. Reallocation and unconditional close-time bound

For each focal M in S, with assigned cost a_M(E)/k_P, apply exactly one rule:

A. If its exit group is large, distribute the entire cost uniformly among its g-1 OTHER tags in that same group, including paid partners if present. Every such pair already shares a physical state at E or synchronizes at its actual next physical state. There is no far asynchronous contribution from this focal edge.

B. If its group is small and s_0<n/U, pay the entire focal cost as a tiny-pool exclusion. Across a key/cell the sum of all these costs is <=w_r s_0/k_P <= (w_r/r) U^-1 times the full original allocated cost of A. Uniformly w_r/r=O(1+L), so summing full cells and keys pays
    R_tiny << NH(1+L)/U=o(NT).                         (2)
This is not a bound on the size of all small groups; only on cells where their aggregate fraction is small.

C. Otherwise, for a focal in a small group distribute its cost uniformly among the s_0-1 OTHER tags of the full small-group pool. Its partners with output tick within D_P belong to at most Delta_P(D_P) groups, each of mass <n/K_P. As s_0-1>=n/(2U) eventually, their fraction is
    <=2 Delta_P(D_P) U/K_P = O(u^(1/16+1/32-1/8))
    = O(u^(-1/32)).
The sum of these close contributions, including possible same exit keys in this small pool, is at most
    R_close=O(NT/u^(1/32))=o(NT).                     (3)
This is a direct fractional-clock estimate and does not need a bound on the actual graph products. All remaining contributions from rule C have different output ticks with gap >D_P. Such pairs are physically asynchronous at E, since equal input state forces equal successor. Both actual waits lie in [1,2r], so for their input times t,t' and outputs s,s',
    ||s-s'|-|t-t'||<2r<=4P.
Their input gap is >D_P-4P, in particular >D_P/2 eventually. The residual also has both exit-group masses <n/K_P and aggregate small-pool mass >=n/U. These are properties of the full frozen sparse set at the key, not necessarily of the surviving focal set.

Every focal cost has been preserved exactly except for the paid parts. In particular the new synchronous cost can exceed the old synchronous allocation, because a focal that formerly paid asynchronous partners can now choose same-successor partners. The proof does NOT assert that the old uniform-partner asynchronous moment is o(NT).

## 4. Later endpoint transfer with bounded loss

For a directed source pair M,M' and fixed later medium horizon E, the focal M has at most k_P selected predecessors C. In rule A, g-1>=n/(2K_P)>=m_P/(2K_P); in rule C, s_0-1>=n/(2U)>=m_P/(2U). Thus the sum of its assigned contributions at E is at most
    2 max(K_P,U) a_M(E)/m_P
       <= W_r := 2 max(K_P,U) w_r/m_P.                (4)
This bound applies to either class separately and to their union, since there are at most k_P predecessor choices in TOTAL. Rule A vs C can vary between different keys, but the physical class of any pair retained at this endpoint is fixed: same successor with equal input times (already synchronized), same successor with different input times (immediate synchronization), or distinct successors (far). Some edges can instead be paid. The cancellation of k_P in (4) is why we work with sparse quotas.

Uniformly
    m_P / ((1+L/P) max(K_P,U)) >> u^(49/8)/ell^4
                               = m_*/u^(1/8),
    m_*=u^(25/4)/ell^4.
Indeed for P>=sqrt Q one has l_P~u, so K_P=O(u^.125), U<=K_P eventually, and b_P>=c u^6.5/ell^4. Divide by J_d=O(u^.25) and the additional O(u^.125). For P<sqrt Q the factor B²/(P^1.5 sqrt Q) is at least of polynomial order in B, dominating all the displayed powers of u and L; this handles both small-band and four-form band definitions. Floors/min1 do not affect this assertion. Consequently
    W_r << r u^.125/m_*,
    sum natural medium W_r along any root <= O(H u^.125/m_*). (5)
Here natural medium means all original medium events without root-specific accounting marks. This bound uses the original total r-cost <=1.5H. In particular the per-hit upper bound is O(Q u^.125/m_*). The weighted natural suffix is deterministic at a shared physical state until either path stops, irrespective of whether the two allocated LOW costs are equal.

## 5. Separate physical merger exclusions

Retain the disjoint fixed finest source cells as in 0ce6427. Every reallocated pair belongs to a single cell. At any physical vertex let n_v be the full original visiting mass restricted to that cell, and a_i the immediate predecessor branch sizes (a starting root is a singleton). The truncated convex quadratic f_m(n)=n² up to m and 2mn-m² thereafter has increment D_v=f_m(n_v)-sum f_m(a_i)>=0. Including expirations, sum D_v<=2mN over the disjoint restricted forests. At n_v<=m the increment is the ordered first-pair count. Thus there are <=mN unordered first physical meeting pairs in those cells and states. This uses all original vertices, not the thinned key set.

Already synchronized at E: a pair's total charge from this class is bounded by twice the common natural W_r suffix after its first physical meeting, by (4), hence O(H u^.125/m_*). With m_a=max(1,floor(u^6/ell^4)), small cell-local first meetings n_v<=m_a therefore pay
    O(N m_a H u^.125/m_*)=O(NT/u^.125)=o(NT).          (6)
The same natural tail-layer and hierarchical admission extensions as in 0ce6427 remain available, with adjusted weight scale (5); not independently audited here.

Immediate synchronization: distinct times at E but same successor give a first common physical vertex at the next step. A pair can have at most ONE such E, across all bands/keys, since any earlier physical meeting would force equal times at E while both continue. The charge at E is before the first common state, not a part of the common post-merger tail. By (4)-(5), its total over all selected predecessor keys and both directions is O(Q u^.125/m_*). We can therefore choose the much larger first-merger cutoff
    m_b=max(1,floor((H/Q) m_a)).
The cell-local first physical meetings with n_v<=m_b account for at most m_b N unordered pairs, hence their entire pre-merger immediate synchronization charge is
    O(N m_b Q u^.125/m_*)=O(NT/u^.125)=o(NT).          (7)
The first meeting can be terminal in either original prefix. This is valid because the actual selected event exists on both paths. The two thresholds apply to different costs of a pair, so overlapping pair sets cause no problem. In particular a pair can contribute once in the immediate class and many times in the already-synchronized class, and we do not discard all future costs using m_b. This is a substantially larger allowable first-merger mass for the pre-merger charge only.

## 6. Result and remaining estimates

Let R_already,bad be the assigned large-exit-group charge from pairs already synchronous at E whose original cell-local first-meeting mass exceeds m_a; let R_immediate,bad be the assigned immediate-synchronization charge whose first meeting mass exceeds m_b. Let R_far be the remaining small-pool charge with output lag >D_P, necessarily input lag >D_P-4P. From inherited sparse accounting and (2)-(7),
    R_med <= o(NT)+R_already,bad+R_immediate,bad+R_far.
In particular no close asynchronous energy estimate is needed separately for this NEW accounting. The unresolved far class has many original sparse common sources at two horizons, both successor groups relatively small, and widely different actual clock phases. This is not a bound on all far interactions, nor does it prove the new physical residuals small. The original high definition and high residual are unchanged. Joint OPEN sufficient conditions on unbounded dyadic windows:
    R_already,bad+R_immediate,bad+R_far=o(NT),
    E_phys,admitbad+E_async,bad=o(T²Bu).
They imply R=o(NT) and the prior gain-prefix contradiction absent twin terminals. The result is a reallocation-based sufficient reduction, not a proof of the conjecture. Next: bound actual large cell-local physical formation and far asynchronous small-pool pairs, potentially use differing successor clocks at both ends of a selected long quota segment. No need to estimate the old uniform-partner phase partition itself.

## 7. Reproducible audit

Standalone ECMAScript research/min_prime_root_exit_reallocation_audit.mjs, exact remote readback at e3133006143eb7cfeabbdfe6946ba631fa0afa11, blob df9d056240f7764da7c8c34c9bbf25866ecccfc5. Earlier audit commits ca06f8449b201d75da303ed775946493f2d5bd48 and 1de43b8fab3fff8c21f1c33c71d1c2ab9ddf44c2. Executed its function in available ECMAScript runtime, not separate Node process. All final 30 runs (five modes x six windows X256..262144) passed. Run node research/min_prime_root_exit_reallocation_audit.mjs 256 1024 4096 16384 65536 262144.

Inherited exact canonical MIN, literal parity-GCD checks at X256/1024, LOW and quota partitions. Store each actual later successor tick/horizon/label. Checks unique selected label at a tick, actual wait, exact local exit-degree envelope, heavy/tiny/small-pool allocations and near/far partition, far input lag inequality, total per-directed-endpoint multiplicity and weighted cap, exact first physical meeting scan for already-synchronous charged pairs, natural tail upper bound, and two restricted-cell potential telescopes. The finite analytic settings have no residual after band caps, so the allocation is tested in diagnostic modes. Immediate synchronization was not present in the retained large-exit class in any of these finite runs; an independent full-original-medium scan checks uniqueness and common actual successor for such pairs, not a nonzero immediate quota-charge example. The asymptotic estimates are paper proofs, not numerically inferred. No cumulative prior optional masks, no full growing ladder, no Lean compilation.

Modes inherited from 0ce6427: analytic, short, wide, phase. Diagnostic K=3 short,4 wide/phase, U=2, D=1 short and floor(P/2) otherwise, ma4 short/8 others, mb=3ma; these differ from the asymptotic powers and are deliberately finite tests. Stress is phase (T4B,Qm=ceil(B/8), k3, width ceil((r+9)^2/2)) with band cap2, cell cap1, K2, U4, D1 to exercise nonempty small pools; this is NOT a regime justifying the asymptotic close bound. Analytic uses the stated powers and original b_P, max(2,n/K) large test, min1 finite floors, three approximate widths.

At largest X262144:
- Short: prior quota residual5886. New tiny374, large-exit allocation5512 (all already synchronous), small-pool close/far0. First-merger small already780.9269841, remaining4731.0730159. Prior old async636.1778 is no longer a residual under this new ledger; not a statement that the old async quantity is negligible. 57 large and7 tiny focal edges, 286 pair tail checks. Restricted ma4 potential71443=91833-20390; mb12 potential122255=142645-20390. Independent oracle42069 immediate source pairs across full medium list,31611 same source cell.
- Phase: prior residual294, all large-exit already synchronized, small first-merger15.6559140, residual278.3440860; max endpoint multiplicity2. At phase X16384, prior656.6667 -> tiny20 + already636.6667, small first-merger437.7667, residual198.9; max multiplicity3. Wide and analytic retained residual0.
- Stress: original medium6414220, first6385246, short4864, long24110, band5421.6667, thin164.9999, remaining18523.3333. Tiny291.3333, close312.1481481, far178.5185185, large-exit already17741.3333. Small already first-merger10255.7259896, large already7485.6073437, final7664.1258622. 854 keys,1140 actual exit groups/degree checks,7226 large focal edges,215 small-pool,118 tiny,93640 partner checks,14159 distinct synchronous pair tail checks, max multiplicity3. Oracle53666 immediate pairs,41993 in same cell; immediate selected charge0. The graph max observed near-key count is1 at D1 (same group included); near pool fraction can be1 in this artificial diagnostic, not evidence of an asymptotic saving.

| X | stress pre-reallocation residual | tiny | close | far | final after first-merger exclusions |
|---:|---:|---:|---:|---:|---:|
|4096|186.3333|0|12|30|30|
|16384|1747.3333|0|190.4141|93.2525|362.3747|
|65536|4682|93.3333|89.8333|33.8333|1409.1973|
|262144|18523.3333|291.3333|312.1481|178.5185|7664.1259|

Main and other branches unchanged by this checkpoint.
