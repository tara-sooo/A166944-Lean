# Clock-refined non-splitting forest: exact asynchronous cancellation and harmonic near-flow deletion

2026-11-24 JST. Continues b15525de4c59c7fbb4b858e433bcf2e8676131ba on the same research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions and finite audit. Not Lean-checked. Full stopping deficit and twin-prime conjecture remain open.

## 1. Physical clock refinement and one terminal virtual union

Use the preceding source-preserving projected-key absorption process, canonical odd roots M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original individual cutoffs and fixed LOW7 L=210. Let S denote stopped roots, J stopped projected keys, T_min minimum stop threshold, with J<=S/T_min. Retain only the actual paths of those S roots. No original trajectory or cutoff is altered.

Refine each proposed high key (p,C) by the actual proposed event clock n, obtaining physical high vertex w=(p,C,n). For executed vertices the post-state (n,C+p-1) determines the entire subsequent MIN trajectory up to an individual cutoff. If two of the stopped tags share w and w is not a projected stop, both must have a subsequent high key: otherwise the tag lacking one would terminate without stopping. Their next high vertex is identical by the deterministic MIN rule and horizon/time monotonicity; different original cutoffs can truncate a path but cannot change its first admissible next event into a different earlier event. This proves unique successor among retained stopped tags. If w is a projected stop, its successor is defined to be the single virtual terminal vertex v=(p,C) representing the union of all its clock classes. Every root is injected as a separate singleton leaf at its first high vertex. Every edge strictly increases the horizon except the final virtual edge, which is terminal. All vertices, except the virtual sinks, have unique successor; all their actual tags move together to that successor. This is a directed forest, even though the original projected graph can split. Distinct physical high vertices with different labels may have the same post-state; their high-suffix paths then agree if continued, but the refinement need not contract that additional equality.

Every pair of distinct stopped roots sharing a terminal cohort has a unique first common vertex in this augmented forest. It is either a physical clock vertex or the virtual terminal. Pairs in different terminal cohorts cannot meet in this refined forest. In particular the cross-incoming-group pair proxy counts each pair at most once, regardless of projected re-encounters. The number of branching vertices (at least two nonempty incoming groups including singleton injections) is <=S-J by the ordinary finite rooted-tree leaf count, even if many unary vertices occur. We need not count all possible physical states by sieve here.

## 2. Exact local and global signed cancellation

Retain any Hilbert-space variance F(A) of the preceding note, especially the hat kernel K_D. For projected vertex v, let its clock partition be A_(v,n), and define its between-clock variance
    A(v)=F(A_v)-sum_n F(A_(v,n)) >=0.
For a projected edge e from v to v', partition its actual tags into physical subedges, and define
    A(e)=F(A_e)-sum_(physical subedges f of e) F(A_f)>=0.
All physical tags at a given clock vertex have the same successor, so the physical subedges of e are whole physical outgoing vertex groups (which may merge on arrival). Each singleton root injection has no between-clock variance.

Let G_proj(v), L_proj(v) be the previous incoming merge and outgoing split terms. Let G_phys(w) be the incoming merge term within physical vertex w. Direct subtraction of the two variance partitions gives the exact local identities
    G_proj(v)=sum_(w refining v) G_phys(w) + A(v) - sum_(e entering v) A(e),
    L_proj(v)=A(v)-sum_(e leaving v) A(e)       (non-stop v).
The latter holds because no physical clock group splits. Thus L_proj(v)<=A(v), and
    G_proj(v)-L_proj(v)=sum_w G_phys(w)
                       +sum_out A(e)-sum_in A(e).
The between-clock edge terms telescope on summation, and at a projected stop the remaining A(v) is precisely the virtual merge variance G_virt(v). Therefore
    F_terminal = sum_(physical w) G_phys(w) + sum_(virtual stops v) G_virt(v).
This also follows directly from the non-splitting forest variance decomposition. Intermediate asynchronous variance has canceled EXACTLY through these edge terms, not necessarily by the very next projected split. We do not assert that all intermediate clock dispersion is immediately lost or that the terminal asynchronous term is small.

Define physical and virtual cross-donor proxy P(w) exactly as before: divide the sum of K_D over pairs from distinct incoming groups by the size m_w of that vertex. Both actual merge increments are <=their proxies. Physical contributions now count only same-clock actual high-event merges; low-only paths are compressed. The virtual contribution is only at the original stops.

## 3. Harmonic near-flow deletion at almost the stopping scale

Use the preceding smooth hat kernel, with 0<=K_D(t)<=min(1,3t^2/(2D^2)). For any root i and distance cutoff d>=1, consider the other roots j within distance d that have a common vertex with i in the augmented forest. There are at most floor(d) such roots because origins are odd and separated by at least 2. List them in the order in which they first join i's physical/virtual cluster along the unique successor chain, with arbitrary order within a simultaneous merge. If j has rank a in this list, the first common vertex w has m_w>=a+1: all previously joined roots remain in its cluster. This is true even when other, more distant roots have merged as well. Therefore
    sum_(j:0<|M_i-M_j|<=d, common vertex) 1/m_first(i,j)
         <= sum_(a<=floor d) 1/a = H_floor(d).
The proxy counts each unordered pair only once, at that first common vertex. Summing the preceding inequality over i, dividing by two, then multiplying by the kernel bound yields
    P_near(D,d) <= (3/4) S (d/D)^2 H_floor(d)
                = O(S (d/D)^2 log(2d)).
The estimate includes all physical and final virtual near contributions, not just actual physical coalescences. It does not require any sieve, height restriction, clock-lag restriction, or per-key mass cap. The previous projected-DAG bound was O(X d^3 log log B/D^2), because pairs could re-encounter. For uniform stop threshold T=B and D=B, choose d=floor(B/log B). Then
    P_near=O(X/log B)=o(X).
More generally any d with (d/D)^2 log(2d)=o(1) works. Thus d=D/log^(1/2+epsilon) B for arbitrary fixed epsilon>0 suffices for D<=B. This advances the deleted near-distance scale from B^(2/3)/log^(1/3) B to almost B. It is the near contribution that is excluded over this larger range; the remaining far pairs are correspondingly more distant. No claim that the far proxy is small follows merely from the harmonic estimate.

## 4. Sharper terminal lower bound

The hat kernel is increasing in distance. Write K(x) for the dimensionless kernel of the preceding note:
    K(x)=3x^2/2-3x^3/4 for 0<=x<=1,
         1-(2-x)^3/4 for 1<=x<=2,
         1 for x>=2.
In a terminal cohort of m>=T_min>=D distinct odd origins, the distance between entries with index gap k is >=2k. Therefore
    F_D(A)/m >= (1/m) sum_(k=1..m-1) (1-k/m) K(2k/m).
Indeed D<=m and K is increasing. The function (1-u)K(2u) on [0,1] has a bounded Lipschitz constant, so the Riemann sum differs from its integral by O(1/m), uniformly. Direct integration gives
    integral_0^(1/2) (1-u)(6u^2-6u^3) du = 1/10,
    integral_(1/2)^1 (1-u)(1-2(1-u)^3) du = 9/80.
Thus the sum integral is 17/80, and
    F_terminal >= (17/80) S - O(J).
This improves the earlier 3/32 constant. The calculation uses the precise hat, not the interval-indicator kernel. Under no twins in unbounded windows and uniform T=B, the existing prefix budget implies S=N-o(X); J<=N/B. Combining with section3 gives
    P_phys^far + P_virt^far >= (17/80-o(1))N
at d=B/log B. One can also use actual G_virt instead of its proxy to obtain
    P_phys^far + G_virt >= (17/80-o(1))N
because G_phys<=P_phys and its near part is o(X). This latter form separates the actual asynchronous terminal obstruction from the physical far-merge proxy.

For each virtual stop v, let its clock-class sizes be m_1,...,m_l, m=sum m_i. Let m_max be the largest. By the centroid variance formula, G_virt(v)=sum_i m_i||mu_i-mu||^2 is no larger than sum_i m_i||mu_i-mu_max||^2, because the combined mean minimizes the squared sum. Jensen and K<=1 imply every squared difference of two class means <=1. Hence
    G_virt(v)<=m-m_max.
Define total terminal minority mass M_clock=sum_v(m-m_max). Then the following genuine necessary inequality holds on no-twin windows:
    P_phys^far + M_clock >= (17/80-o(1))N.
In particular a proof that P_phys^far=o(X) and M_clock=o(X), or even that their sum has liminf ratio to N strictly below 17/80, suffices. If physical far flux is small, a positive fraction of tags must stop outside their cohort's largest clock class. We have not proved either required upper bound. Minority mass is an upper bound for virtual variance, not its exact value, and virtual merging is an accounting operation rather than actual physical coalescence.

## 5. Root deletion stability, without repeated-incidence costs

For any set A and additional root i, the variance update is
    F(A union {i})-F(A) = |A|/(|A|+1) ||phi_i-mean_A phi||^2
between 0 and 1 by Jensen and K<=1 (empty A is trivial). Consequently removing an arbitrary set of b original roots from all terminal cohorts decreases total terminal variance by at most b. Restrict the whole refined forest to surviving original tags; deterministic successor property and all previous inequalities remain valid. Stop mass lower bound m>=T_min need not hold after deletion: use the original terminal lower bound minus b, not the Riemann-sum argument on the trimmed cohorts. This avoids needing to bound the total repeated positive proxy flux caused by the deleted roots.

For example the preceding height budget h_hyp<=6+4R_i+4B, with uniform stop cap T=B and total R_pre=O(X^2/log^3 B), implies deleting all roots that ever have proposed high post-height >=A=X/log^2 B costs O(X/log B)=o(X) roots. This is exactly the earlier extreme-height estimate, now compatible with the forest ledger and terminal variance without any multiplicity penalty. The remaining forest has all attained high heights bounded by A and still needs (17/80-o(1))N far physical plus virtual proxy. Deleting arbitrary o(X) exceptional-root sets obtained in future estimates is likewise legitimate, even if each would otherwise participate in many projected meetings. This does not establish the much smaller logarithmic bounds on high-height indices needed in earlier local arithmetic deletions.

## 6. Finite diagnostics and exact readback

Executed the saved research/min_physical_clock_variance_forest_audit.mjs at X=256,1024,4096,16384,65536,262144 for the previous uniform diagnostic cap floor(B/4) and hybrid 4 max(ceil(sqrt B),p). Reconstruct every stopped tag's unchanged high path; verify physical successor uniqueness and exact edge mass, singleton injections, virtual stop union and root conservation, branching count<=S-J, per-vertex variance decomposition and nonnegativity, global physical+virtual gain equality with terminal variance, virtual gain<=minority, harmonic near bound (also unweighted), and terminal variance loss<=deleted source count for two height diagnostics. Reuse the integer hat numerator and 80 brute kernel checks per run from the preceding audit; variance ratios and telescoping use floating-point tolerances. The local projected signed edge identities of section2 are mathematical deductions; the current script checks global physical/virtual telescoping and between-clock terminal equality, not each projected edge-variance identity separately. Exact remote script and JSON readback at 487e58eb58e65e3046868b82facec5bd95f5258c.

At X262144,B1355, uniform diagnostic T338, S11112, J30:
    physical vertices8094, terminal clock classes116, maximum clocks per stop7, one-clock stops1, largest terminal clock class357, total minority3763, branching nodes3993.
    D338: terminal3989.706959 = physical gain3069.234852 + virtual gain920.472107.
    physical proxy4683.720281, virtual proxy2026.122354, total6709.842635 (preceding projected proxy9497.854).
    Sum of between-clock variance over interior projected vertices4896.351423 (not a net contribution); terminal920.472107.
    d46=floor(D/log B): near physical26.027872, near virtual0.572214, total26.600087; unweighted near sum5720.792437, harmonic bound24539.114339.
    deleting roots ever proposed high height>=5041:1 root, terminal loss0.330490. At height>=B:3535 roots, loss1513.908705. These thresholds are finite diagnostics.
Hybrid diagnostic W4, S34194,J192,T_min148:
    physical vertices23693, terminal classes676, maximum clocks8, one-clock stops20, largest class243, minority9956, branching nodes12157.
    D148: terminal12671.290836 = physical9930.536122 + virtual2740.754714.
    physical proxy15252.470315, virtual5760.904643, total21013.374958 (previous projected proxy26280.108).
    d20=floor(D/log B): near physical76.115459, near virtual1.378993.
    height>=5041:1 removed root, terminal loss0.676015.
The finite virtual contribution is substantial, so it would be incorrect to omit the terminal clock union. The improved analytic far-distance scale is asymptotic; finite d values need not be much larger than the earlier D^(2/3) cutoff. The finite diagnostics do not prove a global far flux deficit.

## 7. Remaining proof task

The clock-refined forest removes repeated intermediate asynchronous encounters from the signed target, and the harmonic estimate excludes near flux at nearly the full stopping scale. The precise remaining quantities are physical far first-coalescence flow and terminal between-clock variance (or its minority bound). The latter includes roots whose physical trajectories never merge before their common projected stop. The next natural target is the distribution of actual clock-class masses at the projected stops and its dependence on the original-root distance; bounding just the number of classes or showing that the interior projected graph splits does not imply a small terminal minority. Alternatively a direct bound on the sum of physical and virtual far proxy would suffice. No full twin-prime proof, no main edit, no new branch, no Lean compilation.
