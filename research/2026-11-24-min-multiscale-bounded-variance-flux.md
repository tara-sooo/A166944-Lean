# Multiscale bounded spatial variance: exact merge/split ledger and far-flow lower bound

2026-11-24 JST. Continues 24b2cde3cb225ed761ab1dbdb149fcb16973fa21 on the SAME research/min-cycle-forest-2026-11-24 branch. New elementary Hilbert-space variance identities, quantitative near-flow deletion and all-depth arithmetic local-flow bounds; finite diagnostics. No Lean compilation. The complete anti-concentration bound and twin-prime conjecture remain open.

## 1. Keep all original stopped tags rather than permanently merging packets

Canonical MIN, odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original individual cutoffs, LOW7 L=210. Use the already-defined source-preserving projected-key absorption, e.g. uniform T=B. Let S be the number of stopped original tags, J the number of distinct stopped keys, and T_min the minimum stop threshold. Thus J<=S/T_min; on no-twin windows S=N-o(X) by the prior arithmetic prefix budget. Restrict the following accounting graph to these S stopped tags, using their ORIGINAL paths and no changed trajectories. A vertex v=(p,C) is any proposed high key visited by a stopped tag, including its original stop. Directed edges connect consecutive high keys of each tag, with the intervening low-only segment compressed. Each original tag starts with an injection at its first high key and ends at its own stop. The graph is acyclic in C. At each vertex let A_v be its set of tags, m_v=|A_v|. Incoming edge sets A_e partition A_v together with singleton root injections; outgoing edge sets partition A_v if v is not a stop. A stop has no outgoing sets. Edges retain actual original identities. Projected vertices may split into many outgoing groups; no non-splitting assumption is made. On an edge use the same set of tags at both ends.

## 2. Bounded distance kernels and exact variance

For D>=1, assign the original odd root M a vector in a real Hilbert space. A convenient first choice is the normalized interval indicator
    phi_M(t)=1_[M,M+D](t)/sqrt(2D), in L^2(R).
Its squared pair distance is K_D(M,M')=min(|M-M'|/D,1). For any nonempty set A of original tags define
    F_D(A) = sum_(i in A) ||phi_i - mean_A(phi)||^2
           = (1/|A|) sum_(i<j in A) K_D(i,j).
Set F_D(empty)=0. If disjoint A_a partition A and n_a=|A_a|, m=|A|, mu_a=mean_(A_a) phi, then the ordinary variance decomposition is
    F_D(A)-sum_a F_D(A_a)
        = sum_a n_a ||mu_a-mu||^2
        = (1/m) sum_(a<b) n_a n_b ||mu_a-mu_b||^2 >=0.
This follows by expanding squares in the Hilbert inner product. Jensen gives
    n_a n_b ||mu_a-mu_b||^2
        <= sum_(i in A_a,j in A_b) K_D(i,j).
Use the left-hand difference on the incoming partition at v to define merge increment G_D(v), and on the outgoing partition at a non-stop v to define split decrement L_D(v). Singleton injections have F_D=0. Sum over vertices; each internal edge potential cancels once in each direction. Exactly
    sum_v G_D(v) - sum_(v non-stop) L_D(v) = sum_(v stop) F_D(A_v).
This handles arbitrary projection splitting and repeated encounters. Neither monotonic growth of each original key mass nor an irreversible merging of historical contacts is assumed.

Define the nonnegative cross-donor proxy flux
    P_D(v) = (1/m_v) sum_(a<b incoming groups) sum_(i in A_a,j in A_b) K_D(i,j).
Then G_D(v)<=P_D(v). Consequently total P_D is at least terminal variance PLUS the full split decrement. For two fixed distinct previous high keys a,b, their contribution at v is <= n_a(v)n_b(v)/m_v <= min(n_a(v),n_b(v)) since K_D<=1. Summed over all possible current keys v, it is <= min(m_a,m_b), because the outgoing edge subsets at each parent partition its original tags. This is an exact all-depth mass control even without globally disjoint matching, and also for arbitrary subsets of cross-donor pairs. At a fixed v, total P_D(v)<=m_v/2. For a particular parent pair or coefficient tuple the stronger min-donor bound can be used, regardless of actual clocks, actual stop overshoot or previous pair encounters. This is a proxy upper bound for the true variance increment; it is not asserted to be equal to it.

## 3. Smooth kernel improves near-distance deletion to the two-thirds scale

Use instead the normalized triangular hat translates
    phi_M(t) = sqrt(3/(4D)) max(0,1-|t-M|/D).
Their squared norms are 1/2. Set x=|M-M'|/D. Their squared distance is
    K_D^hat(x) = 3x^2/2-3x^3/4          for 0<=x<=1,
                 1-(2-x)^3/4            for 1<=x<=2,
                 1                     for x>=2.
The formula follows by integration of the two piecewise-linear hats: their unscaled overlap integral for separation x in unit coordinates is 2/3-x^2+x^3/2 for x<=1, (2-x)^3/6 for 1<=x<=2, and 0 otherwise. In particular 0<=K<=1, K>=3/4 for x>=1, and K<=3x^2/2 for all x (also follows from the L^2 derivative translation inequality). Use this kernel in all the preceding exact variance identities.

Terminal lower bound: suppose 1<=D<=T_min and a stopped cohort has m>=T_min tags. Sort roots M_1<...<M_m. The pair separation for index gap >=ceil(m/2) is at least m>=D, since distinct roots are odd with spacing 2. There are floor(m/2)(floor(m/2)+1)/2 >= m(m-2)/8 such pairs. Therefore
    F_D(A_v) >= (3/32)(m-2).
In particular summing stops gives terminal variance >=(3/32)(S-2J). For large T_min and S proportional to X this is Omega(X), UNIFORMLY for all D<=T_min. The same lower bound holds for the interval-indicator kernel.

Near-distance upper bound: restrict P_D(v) to pairs with original |M-M'|<=d. For each root at most one root lies in each direction at distance 2j. Counting unordered pairs and bounding by all such pairs (not just different donor groups),
    P_D^near(v) <= (1/m_v) m_v sum_(1<=j<=d/2) (3/2)(2j/D)^2
                 = O(d^3/D^2).
This bound is independent of mass, heights, clock lags and the number of predecessors. The total number of projected high keys, occupied or not, is O(X sum_(p<=B prime)1/p)=O(X log log(3B)), by p|C+/-1, length O(X) and p<=B. Hence
    P_D^near <= O(X d^3 log log(3B)/D^2).
For the nonsmooth interval kernel the corresponding bound is O(X d^2 log log(3B)/D); this is why the smooth hat is useful.

Take the original uniform cap T=B, D=B, d=B^(2/3)/(log B)^(1/3) (integer rounding harmless). Then P_D^near=O(X log log B/log B)=o(X). On hypothetical no-twin windows the variance identity now forces
    P_D^far >= (3/32)(S-2J) + sum_v L_D(v) - o(X)
             >= (3/32-o(1))N.
Here far means original root distance >d, and P_D^far is a WEIGHTED cross-donor flow of actual tags, not a cardinality of distinct matched pairs. The bound holds for any d=o((D^2/log log B)^(1/3)). It is not a claim of linearly many globally disjoint far pairs or distinct merge vertices. Repeated encounters are included in the flux and actual splitting is explicitly subtracted. In particular distant pairs from the two arms cannot simply be counted as a permanent coalescence.

The same estimate holds at EVERY scale D<=T_min tending to infinity fast enough for d to grow. For example for T_min=B and fixed 0<a<1, take dyadic D in [B^a,B], and d_D=D^(2/3)/(log B)^(1/3); the errors o(X) are uniform. Summing gives Omega(X log B) required total far weighted flux over these scales in no-twin windows. This is a multiscale ledger, not independent new pairs at each scale. The same actual encounter may supply flux at several scales, and the kernels must be kept when counting their weighted sum.

## 4. All-depth low-only formation does not supply the required far flux

For any low cutoff y use the already proved LOW barrier L_y=2 product_(3<=p<=y prime) p. A root that has executed only labels <=y before reaching a proposed high key at C has gain C-C0<L_y. If both arms of a cross-donor pair have that property, their original root distance is <L_y/2, because C0=2M-2. Thus all such two-unexposed-root pairs are near whenever L_y/2<=d_D. This includes repeated visits, old matching prefixes, and paths that have split, with arbitrary actual masses. By Chebyshev's bound sum_(p<=y) log p=O(y), for D=B choose y=c log B for any sufficiently small absolute c>0 so that L_y<=B^(1/2). Then their ENTIRE proxy flux is o(X) by section3. Hence the required far flux must involve at least one tag that already executed a prime >y. Unlike the previous greedy first-crossing theorem, no small residual cap on actual tags is used here; this is a deletion of a contribution to a bounded spatial variance ledger, not a claim that few tags have crossed y. A repeatedly used large-exposed tag may supply many units of flux, so a bound on distinct exposed tags alone is not enough.

## 5. Transfer previous lag-free arithmetic deletion to this all-depth flux

This is a direct use of 2c5864bda3a26b9203ac0d087280581ff5b64e6a and 24b2cde3cb225ed761ab1dbdb149fcb16973fa21, with a different counting operation. Consider contributions to P_D(v) from actual tag pairs in distinct incoming high donor groups (q,D_prev),(q',D'_prev), with both preceding high events, prior indices k,k'<=H=log^beta B, cheap current r(C)<=z=ceil(log^gamma B), current p>=P=log^lambda B, and distinct p,q,q'. The two arms retain their individual residues and nonnegative current indices:
    2kq=(2K+1)p+e1, 2k'q'=(2K'+1)p+e2,
    |e_i|<=7L+4z+7, e_i odd.
For large B, if lambda>beta+gamma, root-only and reset arms are impossible at these p, and the same-parent-label parity obstruction of the previous note applies to distinct preceding keys; equality p=q or p=q' is impossible by the consecutive horizon congruence. Thus all three labels are distinct whenever the two prior indices are bounded and the current prime and clock meet these eventual separation conditions. No lag bound is imposed. These facts are local and do not require first projected contact.

Assume that for each qualifying tuple of previous and current projected keys the weight of qualifying cross-donor tag pairs, with the kernel and denominator m_v included, is <=p W, W=log^delta B (fixed multiplicative factors harmless). This follows if either executed parent mass is <=pW, OR if actual current whole mass is <=pW. More generally the bound may be applied to a restricted subflow of pairs using just the corresponding smaller subgroup. Multiple clock choices within a fixed tuple do not require summing clock multiplicities: for any fixed coefficient tuple the sum of its actual normalized pair weights is bounded by n_a(v)n_b(v)/m_v<=min(n_a(v),n_b(v))<=min(m_a,m_b). One can overcount coefficient tuples in the same way as before. Actual tags are retained, including at a stop. Unlike degree-one matching, a source may occur in the proxy at many vertices; the inequality per tuple does not require it to be globally matched only once.

For completeness, fix p,k,k',e1,e2, finite low gains and divisor signs. The previous one-dimensional upper-bound sieve gives for each arm's residue class
    A_p=O((1+B/p)/(1+log(B/p))), 
    S_p=O((H+1+log log(3B))/p)
where the harmonic sum is over q>=p/(4H) as forced by the individual equation; similarly A'_p,S'_p. Count C by O(1+X/(pqq')) from CRT, then multiply by the tuple weight pW and sum independently over q,q'. The +1 part totals O(X W/log B) summed over p, since sum_p 1/[p(1+log(B/p))^2]=O(1/log B); the volume part is O(X W (H+1+log log(3B))^2/P) by sum_(p>=P)1/p^2=O(1/P). Multiply by O_L(H^2(1+z)^2) coefficient choices. Hence for either kernel, every scale D, even with multiple encounters and splitting, the qualifying total proxy flux is
    O_L(X W H^2(1+z)^2 [(H+1+log log(3B))^2/P + 1/log B]) = o(X)
provided 4beta+2gamma+delta<lambda and 2beta+2gamma+delta<1. For beta=gamma=delta=1/8, lambda=1, this is O(X/log^(1/8) B). No matching threshold or global disjointness is needed. The bounds are uniform in D since K<=1.

Two useful cases that DO NOT require a whole current mass bound, and remain valid at arbitrary stop overshoots:
- Original uniform cap T=B: for current p>=B/log^alpha B every executed parent mass <=B<=p log^alpha B. Thus use W=log^alpha B, and the all-depth qualifying flux is o(X) for alpha=beta=gamma=1/8, lambda=1. Current keys may have larger mass. 
- Hybrid cap ceil(W0 max(B^eta,q)), W0=log^delta0 B, eta fixed in (0,1): at p>=B^eta, if at least one prior label q<=p log^alpha B then its mass is <=O(p log^(alpha+delta0) B). Use W=log^(alpha+delta0) B in the same theorem. E.g. alpha=delta0=beta=gamma=1/8 and lambda=2 gives o(X). No bound on the other parent's label or actual current mass is necessary. This treats some downward and upward transfers in an all-depth, split-aware flow setting.

These are deletions from the new proxy flux, not new asymptotic statements about the total number of global witness pairs or the count of roots. They do not remove large-index, small-current-label, expensive-clock, large normalized donor mass at small p, or low-history/large-history mixed interactions in general. The far-flow lower bound plus this local deletion leaves a genuine residual of cross-donor flux.

## 6. Exact finite diagnostics

Saved and executed both scripts at X=256,1024,4096,16384,65536,262144, original diagnostic caps uniform floor(B/4) and hybrid 4 max(ceil(sqrt B),p), using original per-root cutoffs. Reconstruct the projected DAG of ALL stopped-root paths, with source-specific actual event times checked during replay. Verify integer in/out flow partition counts; root conservation; stop sizes; per-vertex merge nonnegativity, split nonnegativity and Jensen proxy bound; global variance telescoping within numerical tolerance (the pair kernel numerators are integers, variance ratios are floating point); separation of near and far weighted contributions and pointwise near bound; and 80 direct brute checks of each optimized pair kernel in each run. The hat numerator is 4D^3 times K: for distance t<=D, 6D t^2-3t^3; for D<t<2D, 4D^3-(2D-t)^3; for t>=2D, 4D^3. The optimized sorted-array prefix-moment computation is checked to have safe integer total. For each D also record illustrative local flux where both positive prior indices<=4, distinct prior labels, p>=31,r<=31, and distinguish actual restricted stopped-tag mass m_v<=4p from its complement. This finite diagnostic does NOT require all asymptotic separation hypotheses, and uses stopped-tag subset mass, not total original process mass. If m_v<=4p the tuple bound holds for this ledger regardless of larger full-process mass; it is not a claim the full mass is capped. Exact remote readbacks: interval script/data at 1c9ce8039f59168fca33376c2b23a44444653ec0, hat script/data at e118b64c5dd40a7b2447d369c4301cc124ccbdb1.

At X262144, B1355, uniform diagnostic T338, S11112, J30, 6332 occupied projected keys, 6831 distinct internal edges. There are 3856 keys with positive merge variance and 481 with positive split variance. At D338, hat kernel:
    terminal variance = 3989.707 (rounded)
    total merge increment = 5528.169
    total split decrement = 1538.462
    total cross-donor proxy flux = 9497.854
    near proxy d=48 = 29.662; far = 9468.192.
    near proxy d=338 = 1851.979; far = 7645.876.
    finite local capped flux = 18.777; finite local uncovered flux = 34.152.
For interval kernel at same D, terminal4427.180, merge5934.637, split1507.457, proxy11200.128. These demonstrate that splitting is non-negligible and cannot simply be omitted as a trajectory description, while both exact ledgers telescope.

Hybrid diagnostic at X262144, S34194,J192, minimum threshold148, 18729 keys,19954 internal edges, 11742 merge keys,1280 split keys. At D148 hat kernel, terminal12671.291, merge15534.289, split2862.998, proxy26280.108, near d27=128.617, far26151.491. For D=T_min the toy finite cutoffs floor(D^(2/3)) are illustrative; the analytic deletion includes the logarithmic factor in d. These finite ratios do not prove asymptotic smallness of the remaining proxy flux.

## 7. Remaining obstruction and next concrete task

This ledger is a different route from the greedy early matching: it uses EVERY stopped-root path and makes no irreversible packet or non-splitting hypothesis. The lower bound has a genuine growing distance scale B^(2/3)/log^(1/3) B for the uniform B stop rule, and repeated local near encounters cannot by themselves supply the needed bounded spatial variance. The task is now to bound the remaining far cross-donor normalized flux (or more efficiently the net merge-minus-split variance) below the required constant fraction of N. A natural next estimate is on transport of far-separated source populations across large labels to small labels, especially how much of their apparent merge variance is returned by subsequent projected splits; a direct signed estimate may be better than bounding all positive cross-donor contributions. The above does not establish that estimate or a full stopping deficit. No new branch, no main edits, no Lean compilation.
