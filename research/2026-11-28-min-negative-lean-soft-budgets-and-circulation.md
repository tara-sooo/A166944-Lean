# Negative MIN: independent soft budgets, exact circulation rounding and relative support

2026-11-28 JST, independent issue #10. Base checkpoint 943848e0467c77bfa931c90379e97a3812837dec, core at 56970db8da07980b493376f6bb895e9349f35662. User requests continued research toward unconditional twin-prime infinitude, independent checking and Lean formalization. The actual MIN transition, roots, synchronized observation, full physical cap, irreversible prefix selection and the ultimate target are unchanged. No claim of a twin-prime proof or literature priority.

## 1. Individual budgets and finite ensembles (kernel checked)

For any root-dependent monotone completed-prefix expense c(A,k), c(A,0)=0, and a budget vector b(A), set d(A) to the maximal prefix within the original horizon with c(A,d(A))<=b(A). To include a tick at age i requires c(A,i+1)<=b(A). Exact deadlineClip applies even when the costs cease to be common after contact. It gives full physical capacity, including before observation, and each actual selected prefix has expense <=b(A).

For each observation bin v and budget vector omega, let X_v(omega) count full eligible roots, i.e. those satisfying the deadline at that physical state. The selected cumulative life is EXACTLY V(omega)=sum_v min(M,X_v(omega)). Total expense <=sum_A b(A).

Define HistoryLiveEstimate as the still OPEN uniform analytic inequality for the chosen cost:
    D live(d) <= D B0 M T twinCount + sum_A c(A,prefixAge(d,A)) + err
for all FullCapped policies. This is not an axiom; it is an explicit premise of the extraction theorem. For the multiscan cost it requires the preceding paper's upper sieve, suitable integer prices/rounding, and (for the joint latch) explicit monotonicity. It is not silently identified with the additive original WeightedEstimate.

For any finite equally weighted list of K budget vectors (repetitions allowed), summing the upper estimate gives
    D sum_omega V(omega) <= K(D B0 M T twinCount + err) + sum_omega sum_A b_omega(A).
A strict positive surplus after subtracting K err and budgets yields a TwinCenter above B when B+3T+6<R. No independence needed for the extraction.

Let S_v=sum X_v, Q_v=sum X_v^2 over the list. The existing clip_sharp applied separately to each bin gives
    M S_v^2 <= (sum_omega min(M,X_v)) ((M-1)S_v+Q_v).
A zero denominator contributes zero. Any integer local certificate l_v with l_v=0 or 0<den and l_v*den<=M*S_v^2 can be summed without penalizing all bins for a few very high concentrations. The exact sum exchange and conditional twin extraction are checked.

Checkpoint 29fbec0e7e2a8968e94042879a58efa920d2c5cf, CI 46043094443 success. Initial run 46042952958 failed on distributivity in the induction; fixed, not a mathematical counterexample. Key names individualHistoryClip_total, individualHistoryClip_live_exact, ensembleMass_swap, ensembleMass_local_lower, twin_above_of_local_ensemble_moments.

## 2. Independent budget law, local weak variance, rational cap (kernel checked)

Fix actual trajectories; only the exogenous budget choices are random. At one bin X=sum I_A, with mu=sum w_A, each w_A the probability the root is affordable. Independent choices give E X^2=mu+mu^2-sum w_A^2, so E X^2<=mu+mu^2. Pairwise nonpositive correlation suffices.

In integer form with K equally weighted samples, K Q<=K S+S^2. Multiplying clip_sharp by K, substituting this inequality and canceling S when positive gives
    M K S <= V (M K + S),   V=sum_omega min(M,X).
Thus E min(M,X) >= M mu/(M+mu) >= (1/2) min(M,mu). The half factor is uniform; it can also be improved to 1-e^(-1) by the elementary independent-product estimate, but that stronger constant is not needed for exponents.

The complete finite independent product is constructed by productBudgetEnsemble: each root is assigned its own list of allowed budget slots, including repetitions, independently of the others. historyBinBit depends only on that root's own budget; actual orbits are not randomized. Exact diagonal/off-diagonal indicator sums and pairwise identities prove the weak variance bound for every observation bin. No CRT independence assumption is involved.

Verified core checkpoints:
- 97fc11131a0e17ee7febefc164dd52662e45223d, CI 46043369325: clip_weak_variance_rational, ensembleSoftMass_lower, twin_above_of_soft_ensemble.
- 0e86509ea445ef4a189fa21525c96989a8095f0f, CI 46043933347: indicatorCounts_weak_variance, ensembleBin_pairwise_variance, productBudget_pairwise, productHistoryBudget_variance. 450 theorem declarations total at this point. Failed runs 46043572491 and 46043744532 were elaboration/rewrite issues, corrected. Key printed axioms are subsets of propext, Classical.choice, Quot.sound.

If every root has H slots, w_A(v) is the count of affordable slots and mu_v=sum_A w_A(v)/H. It is unnecessary to enumerate H^N budget vectors. The compressed certificate is
    U_H = sum_v min(M H, sum_A w_A(v)),
    B_H = sum_A sum_(j in choices(A)) j,
    2(H err+B_H)< D U_H.
This sufficient inequality follows from multiplying the expected cap and expense bounds by H. A further Lean implementation was attempted; see verification addendum, not an assumed result.

## 3. Arbitrary history-cost exact integer optimization (paper proof)

There is a stronger finite result that removes the 1/2 factor. It also addresses the original obstruction that the state-additive optimalNetDeath theorem cannot directly optimize history-dependent expense.

Each full physical state is a vertex (window, center, absolute clock). Its successor is deterministic and stays in its window until the common retirement. Use an artificial retirement sink per window; attach a unique leaf for each root to its birth state. The resulting directed graph is a forest pointing toward retirement (one outgoing edge per nonterminal; clocks increase). For each root A and prefix k>0, let P(A,k) consist of its birth-leaf edge and the k state edges corresponding to live pre-ticks, including before observation. Put capacity 1 on each birth-leaf edge and M on each state edge. The root option's weight is g(A,k)=D*l_A(k)-c(A,k); k=0 has zero profit and needs no edge.

A feasible fractional packing of options is equivalent to a circulation: add a return arc from the endpoint of each prefix P(A,k) to its own birth leaf, of capacity 1 and weight g(A,k), and put weight zero on the forward edges. Send the option mass along its forward path and return arc. Conversely for any circulation, the return-arc flows determine the forward flows uniquely, since their difference from the sum of option cycles is a circulation supported on a forest and must vanish. Thus every circulation encodes a feasible packing and vice versa.

Integrality has a direct constructive proof for rational flows. Scale by a common denominator H and regard each flow as a nonnegative integer numerator; capacities are multiples of H. At a vertex incident to a nonintegral edge (numerator not divisible by H), there must be at least two such incident edges by conservation modulo H. Their undirected multigraph therefore contains a cycle. Give the cycle signs according to its traversal relative to directed edges. Changing flows by these signed amounts preserves conservation. Choose the orientation with nonnegative objective slope; increase by the smallest positive distance of any cycle edge to its next multiple of H in that direction. This is strictly between 0 and H, preserves capacities, makes at least one more edge integral, and never changes an integral edge. Iteration terminates in finitely many steps, with no loss of objective. The root-leaf capacities imply at most one selected option per root. This proves exact equality of the rational fractional optimum and integral optimum for arbitrary root-history costs, not just state-additive ones. Equivalently the path incidence matrix is a network matrix (or use alternating signs along each ancestor chain in the Ghouila-Houri criterion). Standard integrality and dual integrality of network matrices are discussed in Lau, Ravi, Singh, Iterative Methods in Combinatorial Optimization, chapter 8, DOI 10.1017/CBO9780511977152.009, inspected 2026-11-28: https://www.cambridge.org/core/books/abs/iterative-methods-in-combinatorial-optimization/network-matrices/62DFF76A362F55690B507C582A8D91CB . The specific MIN circulation construction and above rounding proof are paper deductions, not Lean theorems.

Given rational budget choices, split each root into H copies, assign each copy one budget slot, and cap by M H. Deadline clipping still works on copy identities: absolute deadline and fixed identity priority, same monotonic contact property. It gives exact life U_H and total prefix expense <=B_H. Each root's total copy mass is at most H. Divide by H and round the circulation. Therefore there exists an actual integer capped policy with net >=(D U_H-B_H)/H, without factor 1/2. This controls NET, not the original separate cheap cost and lifetime simultaneously. For any uniform HistoryLiveEstimate the improved strict surplus H err+B_H<D U_H would force a twin. The fractional mean method also works simply by integrating the upper bound over integer policies in a convex decomposition. No assertion that the rounded policy obeys every assigned copy budget.

The LP dual gives an exact alternative mathematical target:
    V_opt = min_{tau_v>=0} [ M sum_v tau_v
       + sum_A max_{0<=k<=H_A}(D*l_A(k)-c(A,k)-sum_{v in P_A(k), physical} tau_v) ].
The maximization includes k=0 (hence nonnegative). Derivation: dualize physical cap rows with tau and root rows with y_A, then minimize y_A as the maximum residual prefix profit. This is the standard finite LP dual, with integer capacities and the proved primal integrality. This formulation allows research directly on arbitrary fields of state prices. Under a twin-free slab and uniform upper estimate, a small total price field must tax every profitable prefix; to contradict it, control how much cheap-prefix mass can be captured by a small price field. No such growing-scale estimate yet. This is a different lower-bound formulation rather than another cost upper bound. It is not enough to count price support without its mass or to ignore pre-observation states.

## 4. Heavier-tailed budgets improve the logarithmic lower-bound target (paper)

The preceding squared Pareto tail is unnecessarily costly in the exponent. Use dyadic budget levels b_j=b(2^j-1) for j>=0, with tail probabilities t_0=1 and t_j=2^{-j}/[j(j+1)] for j>=1. Truncate at a finite J large enough for all prefix costs in the slab. This gives rational slot probabilities t_j-t_{j+1}, with t_{J+1}=0. The mean budget is
    sum_{j=1}^J (b_j-b_{j-1}) t_j
      = (b/2) sum_{j=1}^J 1/[j(j+1)] <= b/2.
For cost c>0, take j=ceil(log_2(1+c/b)), assuming j<=J. Then w(c)=t_j obeys
    -log w(c) <= log(1+c/b)+2 log(1+log(1+c/b))+O(1).
At c=0 the weight is 1. This replaces the factor 2 in the leading logarithmic cost penalty by 1. One can take integer b and levels, after common scaling; if using real costs round the levels/expense to rational or integer and explicitly bound the rounding. No asymptotic real adapter is claimed checked.

Let c_A(t) be the actual expense through the NEXT completed tick for observation pair (A,t). At its bin v define mu_v=sum_A w(c_A(t)), and P(A,t)=-log w(c_A(t))+log^+(mu_v/M). Then
    U_H/(H N T) = E_{A,t} exp(-P).
This is exact for rational slot weights. For any subset E of all root-observation pairs with fraction s>0,
    U_H/(H N T) >= s exp(-E[P|E]).
No prefix closure of E is needed: it is only a lower bound on the sum of full-prefix affordable weights, not a change of the policy. Jensen and the heavier tail show that a sufficient new condition on actual slabs is, for some fixed delta>0,
    -log s + E[log(1+c_A(t)/b)+log^+(mu_v/M) | E]
      <= (1/4-delta) log L,
with b=o(L^-1/4). The extra mean log-log term is O(log log L) by concavity, since the first cost log is nonnegative and O(log L) in conditional mean. The expected expense is <=b/2. Under the preceding uniform paper upper estimate this would yield unbounded twins and, for the original M=L^2.1 scale, at least the R/L^2.35 quantitative lower bound on the good slabs.

A concrete tail variant: a population of fraction >=c L^-e for which c_A(t)<=b L^a and mu_v<=M L^d, with a,d,e>=0 and a+d+e<1/4, suffices. This permits costs beyond a fixed small hard budget and excludes atypical high-loss root-time pairs. The key remaining task is precisely this joint cost/physical-crowding estimate, or a price-field contradiction in section 3. No such population lower bound is proved here. In particular model probabilities of independent prime residues must not be substituted for actual roots; the budget independence above is an independent EXOGENOUS choice only.

## 5. Relative support count (paper, from preceding discussion, not Lean checked)

For an even positive Q, take base labels dividing Q and at most k distinct extra odd labels not dividing Q. Define F_Q(0)=0,
    b_k=F_Q(k-1)+1,
    F_Q(k)=Q [2+2(b_k+1)^k((b_k+1)Q+1)]^k-1.
This is an explicit bound on the number of extra events in a relaxed downward even-state word. A base-only interval has gain <Q by the wall property. Induct on k: consecutive uses of an extra label p enclose at most F_Q(k-1) extra events. At every pre-extra event and final state, record x mod Q and, for each extra label, its never-used/expired/active status, last source sign, count vector of extra labels since last use inclusive, and the intervening total base gain. Active means at most b_k extra events since last use. Its vector entries are <=b_k; base gain <(b_k+1)Q from the disjoint base runs. Number of possible signatures <=F_Q(k)+1. Equal signatures at two indices force each extra label used between them to be active in both (a never-used flag cannot recur, and a gap larger than b_k before its next use violates the induction bound). Equal count vectors, sign and base gain give equal current residues modulo that label. The base residues give divisibility by Q. Their positive even net gain Delta is divisible by all used labels; apply the wall to modulus Delta, contradiction. There are m+1 distinct signatures. Total nonzero events, including base, <=(F_Q(k)+1)(Q+1).

From the recurrence log(F_Q(k)+2) <= C k!(k+1)! log(Q+2), by dividing the log recurrence by k!(k+1)! and summing the summable lower-order terms. Thus if z=(log L)^theta, Q=2 product_{odd prime p<=z}p, and k<=c loglog L/logloglog L+O(1), theta+2c<1, the total-event bound is L^o(1). This decouples the growing base alphabet from the nonbase diversity and gives a potentially larger base cutoff than the prior z=D choice. The CRT count-vector enumeration in 943848e can use the total event bound, but every scan/sieve and the joint broad-word budget must be rechecked with the new z. The larger sieve of Gallagher and inverse variants (Green-Harper, GAFA 2014, DOI 10.1007/s00039-014-0288-1; https://wrap.warwick.ac.uk/id/eprint/107458/) require actual restrictions on the residue classes of inverse root sets; no such restriction for arbitrary long cheap histories follows simply from finite support, so no inverse-sieve transfer is asserted. Neither this support bound nor the new budget law proves the central lifetime lower bound.

## 6. Reproducibility

- research/lean/negative_min_history_ensemble_audit.mjs, commit 1f55762f071dce83933988b98b67712b5c7de4c1, blob c053d16a9c9e5eb1debfa6c877acbb237c7acff1. Executed in ECMAScript and fetched at the exact commit and reexecuted with identical output. Independent literal eligibility vs gcd tick: 14,757 checks; 703 canonical roots, 235 windows, 6,309 budget vectors over windows, 105,368 total assertions. Nine windows checked against exhaustive deterministic prefix selection including pre-observation capacity. Fixed proxies R=600,1200,2400, T=W=18, M=1, slots [0,1,4], D=3, cost=2*saturation+nonempty with z=3,Y=17, diversity trigger 2. Not a growing-scale test.
- research/lean/negative_min_circulation_rounding_audit.mjs, commit 0f80aad02fd96f905b9a2ec432d773a784a3c3ce. Same test domain, 242,746 assertions, 631 fractional cycle rounding steps in 235 windows, objective nondecrease, capacities and conservation verified at each step; rounded integer prefix choices reconstructed and cap checked. No independent human review or Lean rounding proof.
- At R=2400 expected clipped life/(NT)=0.6102901183255851, exact fractional life/(NT)=0.625150087743604, integer local moment lower/(NT)=0.5889083874675448, mean budget=5/3. These demonstrate the finite formulas and do not test the required asymptotic small budget.

The exact original real criterion/Mathlib bridge remains uncompiled. No full project build or new Mathlib dependency download; use standalone pinned Lean CI. Main and sibling branches unchanged. Issue #10 remains open. The analytical lower bound, the rigorous verification/formalization of the upper sieve, and the final extraction to conventional Mathlib twin primality are still required.

## 7. Independent replay and compressed implementation

The rounding audit was independently fetched at commit 0f80aad02fd96f905b9a2ec432d773a784a3c3ce, blob 7db826bbe3f3dd3f868f72b22f8099b46262699c, and executed again with exactly the same counts and numerical outputs. Both audits ran in an ECMAScript runtime, not a separately installed Node process. The circulation includes state capacities before observation as well as during it; the price field in the dual ranges over all such constrained state-time bins.

The compressed Lean implementation first failed in run 46044106690 (identity-map simplification and an unavailable tactic). Commit 3de46b29c9552e2ba7903bf4a2962df4c3413186 repairs those two points. The earlier independent-budget stage 0e86509ea445ef4a189fa21525c96989a8095f0f is verified by successful run 46043933347. The compressed stage requires its own successful run before being called verified.

**Final kernel check:** run 46044365996 completed successfully on 3de46b29c9552e2ba7903bf4a2962df4c3413186 (core blob b5dab2362e536a10028c69822f5689f9783afa4e, 457 theorem declarations, up from 416). `compressedSoftMass_exact`, `compressedBudgetSum_exact`, and `twin_above_of_compressed_soft` depend only on propext, Classical.choice, Quot.sound. In particular, the finite conditional compressed certificate now checks, with no exponential enumeration needed in the certificate expression itself. Its `HistoryLiveEstimate` hypothesis is explicit and remains open analytically; this is not a proof of twin-prime infinitude. No claim of a completed independent human review is made.
