# Common-cutoff reset forest: low-component contraction and single-high cut capacity

2026-11-24 JST. Continues ea0e4efdb2fc71c86ae4986cb07a70adf8775874 on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions using the established MIN clock/barrier lemmas and upper-bound sieve; two exact finite audits. Not Lean-checked. No proof of the full concentration bound or twin-prime infinitude.

## 1. A narrower common-cutoff family and exact one-dimensional renewal forest

Let X be sufficiently large dyadic, B=ceil(sqrt(7X)), K=floor((7X-1)/4). Select original canonical odd sources M in [X,5X/4), of count N=X/8 for dyadic X>=8. Initial t=M+2 and C=2M-2 as before. Use the common cutoff K, which is <= the original K(M) for every such source. This is an intentional restriction for a sufficient twin-prime argument, NOT a modification claimed to preserve the original full-window statistics. Since K-t0>=X/2-O(1), any non-twin terminal has required executed elapsed >=X/2-O(B). A genuine twin terminal in any such window suffices (smaller prime >=2X-1). The proof of the terminal certificate uses C<=2t, r(C)<=B if either C-1,C+1 composite, and the 2B quiet-tail bound. The same certificate holds starting from any reset vertex below, even those not canonical odd sources.

Define b(u)=0 for even u and 6 for odd u, C_u=2u-b(u). At every integer u in I=[X+3,K] define a hypothetical reset state (u,C_u). Include ALL these vertices, not merely reached vertices. Starting there, run deterministic MIN until the first subsequent reset (height 2t-C=b(t), regardless of selected prime, including low events) or the terminal under common cutoff. If the next reset is v, define rho(u)=v>u; otherwise u is a sink of the reset graph, with a terminal excursion that may have further nonreset events. Denote by e(u) the executed excursion (including its endpoint reset event if present), by c(u) its sum of r(C) costs, by l(u) its elapsed time from u to last executed event (zero if no event), by H(u) its count of p>7 selections. No final quiet tail is included. For a reset edge u->v, l(u)=v-u and exact total gain
    C_v-C_u=2(v-u)+b(u)-b(v)>0.
Each event increments by p-1 and r<=p<=3(p-1)/2. Thus c(u)<=3(C_v-C_u)/2 and l(u)<=2c(u). For terminal excursions the same cost-vs-gain inequality holds with actual terminal horizon. All edges strictly increase time and horizon; each vertex has at most one outgoing edge. Consequently the weak components of this finite graph are rooted directed trees oriented toward their unique sinks. There are no undirected cycles: an undirected cycle would have a smallest-time vertex with two outgoing edges. This is exact for the common cutoff. Unlike the earlier projected high-key graph, the physical reset graph has NO splitting of incoming source tags or expiration at differing cutoffs.

Let I_0(u)=1 if u=M+2 for the restricted original odd family, 0 otherwise. Define m(u)=I_0(u)+sum_{w:rho(w)=u}m(w) in increasing u. This is precisely the number of original sources arriving at u, with disjoint incoming sets. Each source has one injection, follows the graph to its sink, and executes that sink's terminal excursion. In particular
    sum_sink m(u)=N,
    R=sum_u m(u)c(u),
    sum_{reset edges u->v}m(u) = total source-tag reset-transition count.
These equalities use the common cutoff, not a scalar recurrence that drops original cutoff tags on the full window.

## 2. Contract complete low-only components, not individual short gaps

Fix y>=7, L_y=2 product_(3<=p<=y prime)p. Retain only reset edges whose entire excursion selects primes <=y, deleting the other edges temporarily. Call the retained components short components, regardless of elapsed length. Every such component is again a directed tree with one sink w. Every path to w consists entirely of low-selected events, with NO interruption by a high event at the intermediate reset boundaries. The even-multiple barrier from the previous notes applies to the concatenation, so for every reset vertex u in this component,
    0<=C_w-C_u<L_y.
Thus all component horizons span <L_y. There are at most 2 reset times per even horizon (from the two formulas for C_u); in particular the component has O(L_y) vertices. The original injection horizons are spaced by 4, so the number b(A) of injected original sources in a component A satisfies
    b(A)<=A_y=floor(L_y/4)+1.
This is independent of the number of reset-to-reset edges in the component. Also, any reset edge with length <=(y-7)/2 is retained, because every selected prime p has p-1<=C_v-C_u<=2(v-u)+6<=y-1. Hence runs of such short reset intervals cannot extend indefinitely: the SAME low barrier bounds their cumulative horizon gain.

Contract every retained component to its sink. Every nonretained edge originates at a component sink and joins a strictly later component; the quotient is again a directed forest with outdegree <=1. Its injection at component A is b(A); its mass at the sink equals the full m at that physical reset vertex. Incoming ancestor component sets are disjoint. If a contracted vertex has mass m and a(v) distinct ancestor quotient edges (include edges from components with zero injected roots), its ancestor tree has a(v)+1 components, so
    m <= A_y (a(v)+1).
More strongly it has at least ceil(m/A_y) distinct components that contain original roots. For two disjoint incoming components of a merger, the corresponding ancestor trees are disjoint, and the two lower bounds on the required nonretained-edge counts apply separately. A large reset mass cannot be generated by one long chain of low-only transitions. This is a structural lower bound on necessary high-containing reset transitions, not an upper bound on the sizes of the ancestor trees.

Choose y growing slowly with L_y<=B^eta for fixed eta<1, as allowed by the earlier primorial bound. Then a reset mass >=B requires Omega(B/L_y) distinct prior high-containing quotient edges. With fixed LOW7, a(v)>=m/53-1; the finite LOW7 ceiling 34 from the older complete residue audit can sharpen 53 to 9 (the paper proof here uses L=210). The quotient bound avoids the time-free reverse search's overcount of different histories through the same physical reset state.

## 3. A genuine unconditional sieve estimate for first excursions with at most one high selection

Fix LOW7 L=210. At any hypothetical reset u, suppose its first high event has p>7. Its pre-horizon is C=2u-b(u)+g, where 0<=g<L even is the preceding low-only gain. By post-height nonnegativity, the time t of the high event satisfies
    2(t-u) >= p-1-b(u)+g >= p-7.
The preceding low prefix takes <=3L time. Thus the wait since the last low event or the reset start is >=(p-7)/2-3L. As this wait is <=2r(C), we get
    r(C) >= (p-7)/4-3L/2.
In particular for all sufficiently large p (fixed L), r(C)>=p/8. This is the earlier first-high delay argument, here applied to every reset-origin excursion with its own first reset endpoint.

For fixed parity b, low gain g and sign, p|2u-b+g +/-1 picks a progression of u mod p. Along it the two linear forms C-1 and C+1 have two distinct forbidden residues modulo each odd ell<=p^c other than p, for small fixed c. The roughness r(C)>=p/8 gives the necessary exclusion. The available progression interval length comparable to X/p>=c_0 B is sufficient for the same uniform dimension-two upper-bound sieve used earlier (choose small power of p as level; O(p^(1/4)log(2p)) remainder negligible). The count for each p is therefore O_L(X/(p log^2 p)), including bounded p by enlarging the constant. This reuses the first-high sieve, no independence of source masses.

If H(u)=1 then c(u)<=p+3L and l(u)<=2p+6L, because there are at most two low-only blocks. If it ends at a reset, then
    v-u = (p-1+g+g'+b(v)-b(u))/2 <= p/2+L+3,
where g'<L is the low suffix gain. Also if p>2L+10 the high event ITSELF must be the final reset event: a nonreset high post-height is >=2p (or 6+2p) and a low-only suffix can reduce height by less than L, so it cannot reach height 0 or 6. No later low event can be the first reset in that case.

Summing over all possible reset starts,
    sum_{u:H(u)=0} c(u) = O_L(X),
    sum_{u:H(u)=1} c(u) = O_L(X B/log^3 B),
    sum_{u:H(u)<=1} l(u) = O_L(X B/log^3 B).
For the second inequality multiply O(X/(p log^2 p)) by O_L(p), then sum over primes and use the prime-counting bound as in the first-heavy note. These estimates include terminal excursions as well as reset edges, and ALL reset start vertices, not only reached ones. Thus the zero-high and single-high parts of the unweighted first-excursion cost are controlled. The multiple-high part is not bounded by this argument.

## 4. Pointwise time-cut capacity for complete one-high excursions

Fix an integer time cut J with max original start < J < K-2B. A complete first excursion from u crosses J if u<=J< u+l(u). The zero-high crossings have u within 3L of J, so there are O_L(1) candidate vertices. For an excursion with exactly one high p, its origin lies within 2p+6L of J by the preceding bound, and the first high pre-horizon is 2u-b(u)+g. For fixed p,b,g and side, the congruence modulo p gives O_L(1) possibilities for u in that interval. Thus uniformly in J,
    #crossing reset-origin excursions with H<=1 = O_L(1+pi(B)) = O_L(B/log B).
This is independent of source mass, and includes terminal excursions whose executed portion crosses the cut. No two-dimensional sieve is necessary for the pointwise count.

Now stop all tags at a reset vertex with m(u)>=T=B (or T=B log^alpha B, fixed alpha<1), before executing its whole next excursion. Each executed departure then has original-tag mass <T, and no tag re-enters. All original sources remain unchanged up to stop. The weighted capacity of crossings of J in H<=1 excursions is
    O_L(T B/log B) = o(X).
If no twin terminal exists in the window, every original source not stopped at or before J has executed path crossing J: any non-twin terminal's last event must be within 2B of K. Its unique crossing excursion departed at or before J, and was not stopped. Therefore, writing S_{<=J} for cumulative reset stops,
    N <= S_{<=J} + O_L(T B/log B)
               + T * #{u: H(u)>=2, u<=J<u+l(u)}.
The final unweighted crossing count is an overcount over ALL hypothetical reset origins. This is a new cut-capacity inequality for the restricted common-cutoff family, not a bound on the multiple-high crossings. It shows that if S_{<=J}=o(X), then a no-twin window requires Omega(X/T) multiple-high reset-origin excursions crossing EVERY such cut. A sufficient pair of open conditions is (i) positive-fraction escape from reset mass saturation, and (ii) existence of a cut J after all injections and before K-2B with multiple-high crossing count o(X/T). Neither condition is claimed.

Integrating the pointwise inequality over J in [5X/4+2,3X/2] gives a convenient sufficient unweighted moment:
    sum_{u:H(u)>=2} l(u) = o(XB)    (T=B).
Indeed the total crossings over this interval are <=sum l(u); the interval has length Theta(X), so some J has crossing count o(B)=o(X/T). Equivalently, the zero/one-high sieve and this unweighted moment would make total executed elapsed o(X^2) under the reset cap, so non-twin unstopped sources number o(X). This replaces full source-weighted excursion transport by two separate problems: an unweighted FIRST-excursion moment and a reset forest saturation bound. The unweighted moment here counts only the next reset OR terminal, not the full suffix from each reset; therefore it is different from the older all-time full-future-moment condition that already included the original full source paths.

An alternative independent target: let E be the number of reset vertices u<=5X/4+2 which are sinks (no subsequent reset before K). If there are no twins, every such sink has l(u)>=K-u-2B>=X/2-O(B), and for large X must have H>=2. Hence
    E = O((sum_{H>=2}l(u))/X).
For example a proof of sum_{H>=2}l(u)=O(XB) and E/B->infinity on the same unbounded windows would suffice for twins, without ANY source-mass bound. This is a conditional route, and the required lower bound on early sinks is not established. Do not infer it from the finite number of early twin-terminating excursions; those already witness twins. The graph outdegree condition alone cannot prove the needed lower bound (a directed chain has one sink).

## 5. Exact finite reset-forest audit

Executed the saved JavaScript function bodies in the current runtime. First audit:
    node research/min_reset_contracted_forest_audit.mjs 256 1024 4096 16384 65536 262144
Constructs ALL reset-time vertices in [X+3,K] and every first-reset or terminal excursion using the actual MIN clocks. Injects the restricted N=X/8 canonical sources, propagates exact scalar mass, checks conservation and costs, independently replays every original root with the common cutoff, checks all reset counts and final classifications. For X<=1024, 1607 literal parity-GCD checks. Contracts low-only components at y=7,11,13; verifies every component horizon span <L_y, root injections <=A_y, exact component sink masses, quotient ancestor edge bound, and sink mass conservation. Script and complete results exact remote readback at 86e738194b0fbf93ab7e02892f7e932e2fcfa73b.

| X | original roots | largest reset mass | weighted reset transitions | largest LOW7 component root count |
|--:|--:|--:|--:|--:|
|256|32|4|23|2|
|1024|128|51|347|3|
|4096|512|45|1031|3|
|16384|2048|60|5027|3|
|65536|8192|225|31581|3|
|262144|32768|445|126608|3|

At X262144 the full hypothetical graph contains 196605 vertices, 164749 edges, of which 66924 have one high selection and 22926 have multiple highs. The reached graph has 39863 vertices, 31707 reset edges; 16425 one-high, 5663 multi-high, 9619 zero-high. Source-weighted reset transitions are 65551 one-high, 20614 multi-high, 40443 zero-high. R=23475259. All restricted original roots have twin terminals (X256 has 5 non-twin roots, larger tested windows zero). LOW7 contracted graph contains 121706 components, max vertex count 7, max horizon span 20, max root injection 3, max terminal basin root-containing component count 359, max ancestor nonretained edge count in any terminal basin 810. These last two maxima need not refer to the same basin as the max mass 445. At y11 and13 largest component root injection 6 and8 respectively, consistent with the much looser uniform barrier. These finite counts do not imply a uniform bound on reset ancestry.

## 6. Independent unweighted cut-capacity audit

    node research/min_reset_cut_capacity_audit.mjs 256 1024 4096 16384 65536 262144 1048576
Second audit enumerates all reset origins, records exact first-excursion elapsed and r-cost split by zero, one, or >=2 high events, including terminal excursions; difference arrays count exact crossing intervals on all integer cuts J in [5X/4+2,3X/2]. Verifies the first-high delay, LOW prefix gain, single-high cost bound, forced direct high reset for p>2L+10 on completed single-high excursions, and r>=p/8 for p>=12L+14. Exact script and JSON remote readback at df6eafb8c03a2ae90058b22a40f675ff10ac5262.

|X|B|sum multi-high elapsed|sum multi-high elapsed/(XB)|mean multi-high crossing count|early sinks|
|--:|--:|--:|--:|--:|--:|
|4096|170|69849|.100312|22.394|238|
|16384|339|468854|.084415|34.460|924|
|65536|678|3156454|.071038|66.255|2903|
|262144|1355|19065019|.053673|97.510|10829|
|1048576|2710|119004377|.041879|154.151|37612|

At X1048576, 786429 hypothetical reset origins, H=0/1/>=2 excursion counts 332094/284429/169906. Corresponding total elapsed 1043422/17002456/119004377, total r-cost 1900629/28114896/127783797. Mean zero/one/multiple-high crossing counts over the cut range 1.332/21.925/154.151; maxima 15/66/342; minima 0/0/25 (not necessarily at common cuts). Early sink counts by class 10904/4428/22280, all have twin terminals in this finite window. At p>2L+10, 17669 completed one-high excursions verified the high event itself is the reset. 270 one-high excursions checked the conservative large-p roughness threshold. Finite scale diagnostics only, no uniform rate or asymptotic lower bound for early sinks.

## 7. Next concrete proof task

The useful new simplification is a true forest on one time coordinate with no splitting, plus low-only contraction and the unconditional one-high pointwise capacity. To turn this into a proof, attack the multiple-high FIRST-excursion moment, not arbitrary long repeated reset trajectories. It is enough for the reset-cap route to prove sum l(u)=o(XB) for H>=2 and bound the stopped population; alternatively a sufficiently strong independent early-sink count plus the weaker O(XB) first-excursion moment would avoid source mass entirely. For multi-high excursions, use the exact nonreset height relation at every interior high event and the fact no intermediate reset is allowed. Enumerating fixed-depth words may permit upper-bound sieves/CRT, but a growing-depth tail bound is still needed; no such bound was derived here. The forest mass and component statements are deterministic partial results. No new branch or main edit.
