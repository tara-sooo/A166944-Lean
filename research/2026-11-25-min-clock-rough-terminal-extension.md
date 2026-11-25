# Extended terminal-level matching and surviving common-cohort energy transport

2026-11-25 JST. Continues 629f56aa77521faf457883b9a39c873f4f7becf2. New paper deductions: extension matches previously terminal charges to *net recorded* downward deficit crossings, not the immediate true-tick cancellation inside the original wait; small surviving level and thin endpoint contributions have unconditional absolute budgets; high surviving levels admit a long-window projected energy transport with a coefficient tending to zero as reference length grows. Finite actual paths predominantly reach twin terminals, not compensating descents. No absolute upper bound for long-reference energy, no Lean compilation, twin infinitude OPEN.

## 1. Original occupation and extended reference

Keep original dyadic X, N=X/2 odd M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2, C0=2M-2, K(M)=floor((7M-1)/4), H=4B, a=2B, u=log B. The original recorded prefix includes the crossing post-state at/beyond relative H (if reached) or an earlier twin terminal. Write its last actual recorded time e_M. Its endpoint deficit satisfies 0<=d(e_M)<=12B+6 because e_M<=s_M+H+2B and C>=2M-2. Preserve all original natural weights and masks of 629f56a, particularly the delayed rough gate; no additional occupation is added to that energy. Each original charged pair shares a completed physical wait slot. Its supported root separation is <=H+3<5B eventually.

Use the two source partitions of width 10B shifted by 5B in ff58097e. Assign each unordered pair to partition 0 if both roots share its cell, else partition 1. For each cell, choose a common absolute reference end
    T=max_(M in cell) s_M + H+2B+W,
where W>=1 is an integer. Work eventually with 16B+W <= min_M(K(M)-s_M), which holds for W=ceil(B u^kappa) for any fixed kappa>0. For every root, continue the exact original fixed-cap MIN from its last recorded state to T or its first actual twin terminal, whichever comes first. If a final wait is clipped at T, retain only its actual stationary portion and no artificial event beyond T. The original recorded endpoint may be terminal already. Since C<=2t and T<=K(M)<7X/2, the two odd neighbors of any r(C)=0 horizon in this range are prime (they exceed 1 and their least prime factors, if composite, would be <=B). All these twins are >=2X-3. No reference goes beyond an original root-dependent cutoff or through a twin. The finite range gate matters: width 10B contributes to the needed available clock. 

For a pair in its assigned cell, after its original common slot departure v both original paths share actual deterministic recorded states through the earlier endpoint e=min(e_M,e_M'). If e is not a twin they continue together in the common-cell reference, even if the other original recorded prefix was longer. They have identical reference endpoint time and horizon. The common future slab [T-W,T) starts at/after BOTH original endpoints and is entirely shared if the pair survives actively to T. A terminal at T is counted as a twin, not an active survivor.

## 2. New exact terminal ledger and net-descent charge

In the previous delayed true-level allocation, every unordered pair/slot has original offdiagonal energy 2r w_M w_M'. Expand over the later-arrival tag and allocate half its tick contribution to each of the two integer levels crossed at the earlier stationary tick t-ell. Each such pair-level crossing is charged at most 1/2, across ALL original slots of that pair. Let d_min^+(v) be the minimum from slot post-state v through earlier recorded endpoint e. The old terminal energy T_old consists of charges at levels lambda<=d_min^+(v), so these levels remain occupied at e. Write m_ext=min of d over the common extension from e to the actual common reference end, including e and end. Only post-states need be checked for this minimum because stationary steps strictly increase d (also valid if the final wait is clipped).

Split every old terminal charge into exactly one class:
* M_ext: lambda>m_ext, newly matched by the first subsequent downward crossing.
* Q_ext: lambda<=m_ext and the common extension stops at a twin.
* T_surv: lambda<=m_ext and the common extension is still active at T.
Then exactly
    T_old = M_ext + Q_ext + T_surv.                           (1)
The twin class is not a small arithmetic error. Under the contradiction hypothesis of no twin pairs above a fixed threshold, for all sufficiently large X it is EMPTY; in finite experiments it may dominate. Reaching even one such terminal certifies an actual twin pair in the large window.

Important distinction from the original immediate cancellation: each level newly matched after e is below or equal to d(e). At its first future downcross, the preceding RECORDED post-state has deficit >=lambda (otherwise the first crossing already happened), and the next recorded post-state has deficit <lambda. Hence the matched crossing is on a genuinely negative NET recorded edge with decrement
    (d_pre-d_post)_+ = (p-1-2w)_+,
not just the true-tick decrement p-3. Both tags visit the common recorded edge. Different charged upward levels and slots of the same pair cannot use the same future pair-level downcross, because every old terminal level appears at most once per pair. Charge is at most 1/2 for each. If n_edge is the actual source mass on a completed recorded edge in a cell's ORIGINAL+extended reference (including original portions, since a pair's earlier stop may precede the other tag's original stop), then
    M_ext <= (1/2) sum_(partition,cell,edge) (d_pre-d_post)_+ binom(n_edge,2).  (2)
This is a valid bound in the earlier recorded negative-flux ledger, with longer reference scope; it is not an assertion that its right side is negligible. Using only edges beyond each tag's individual stop would miss the gap between the two original endpoints. The reference includes all original recorded edges for this reason. An exact allocation can retain only first subsequent downcrosses of actual charged levels instead of paying the loose envelope (2). The original immediate and later matched terms from 629f56a are unchanged.

## 3. Absolute low-level and thin endpoint payments

For every original pair, the total old terminal charges across ALL its original slots is <=d(e)/2<=6B+3: distinct unmatched upward levels at e cannot repeat without an intervening downcross, and each contributes at most 1/2. The source support |M-M'|<=H+3 gives O(XB) possible unordered original pairs. Thus for any h>=1 the entire surviving terminal charge at levels lambda<=h costs
    T_low <= O(XB h).
In particular take h=u^(5/2) to pay o(XB u^3). The same bound applies to any original or extended terminal class with this low level restriction. This is an absolute quadratic payment, not a linear tag deletion.

Next, at common cell reference endpoint let n_end be the number of actual active original tags sharing the same physical (T,C). For an active surviving pair, both tags are counted. In each partition, the endpoint groups are disjoint and their masses sum to at most N. The number of unordered pairs in groups of mass <=m is at most m N/2. Across both partitions, assigning each pair once, after low-level payment the additional thin endpoint charge is
    T_thin <= (6B+3) m N=O(XB m).
For m=u^(11/4), this too is o(XB u^3). This bound applies even if the pair had many previous shared rough slots. It uses a total terminal charge cap per pair, not a fresh cap at each original slot. No assumption about how large the group was at its first contact is needed. Use priority low-level then thin endpoint to keep payments disjoint. The remaining surviving terminal term T_heavy contains only levels >u^2.5 at active endpoint groups of mass >u^2.75.

## 4. Future projected-energy transport with vanishing coefficient

For each cell and root define v_M(C) as the length of its actual reference occupation at horizon C clipped to the common future slab [T-W,T), divided by 2r(C). Stop at twin terminals and use zero weight thereafter. This is an auxiliary future occupation, separate from original charged w_M. Let
    E_future=sum_(partition,cell,C) r(C) (sum_M v_M(C))^2.
A surviving pair shares its entire future slab with identical weights v_M=v_M'. Let its successive occupied wait pieces in that slab have lengths l_i and eligible r_i. Then sum l_i=W. All completed events ending inside the slab have gain p_i-1 and r_i<=1.5(p_i-1); the last incomplete wait costs at most B. The total completed gain in the slab is <=2W+d(T-W), by C<=2t. Since T-W<=s_M+16B and C>=2M-2, d(T-W)<=32B+6. Hence
    sum_i r_i <= 3W+49B+9 <= 3W+50B
for sufficiently large B, including first/last partial waits. The full ordered offdiagonal future pair energy satisfies the deterministic Cauchy lower bound
    e_future(M,M')=2 sum_i r_i (l_i/(2r_i))^2
       =sum_i l_i^2/(2r_i)
       >= W^2/[2(3W+50B)].                                   (3)
This does not require long individual waits or a lower bound on any selected p. It also includes arbitrary short waits after the original prefix, in contrast to replacing clock overlap by a single r-weighted product at one horizon.

For each surviving pair its remaining old terminal charge is <=6B+3. Its future pair contribution is counted once in the assigned partition's E_future; different original slots of that pair have already been aggregated in the charge cap. Combining with (3),
    T_heavy <= T_surv
      <= [(6B+3) 2(3W+50B)/W^2] E_future.                      (4)
For W=ceil(B u^kappa), the coefficient is O(u^(-kappa)). Thus under the no-large-twins hypothesis, a sufficient (OPEN) pair of upstream estimates for the old terminal term is
    M_ext=o(XB u^3),   E_future=o(XW u^3).
This is genuine relative transport to a DIFFERENT energy at a longer reference scale, not self-absorption by the original E. In particular a factor B/W alone does not solve the problem: the longer natural energy scale grows with W. The original immediate/later terms, heavy distinct slots, low-r shared anchors, and MED destination budget remain. Equation (4) also yields a lower bound on future collision energy from any large surviving terminal term, a quantitative obstruction that an independent long-window estimate would need to contradict.

An alternative pair-local version uses a continuation of W ticks beginning at the earlier original recorded stop e, inside both original cutoffs. Then d(e)<=12B+6, and the same sum-r bound is <=3W+22B eventually. For pairs surviving that local interval, (3) holds with 22B in place of 50B. Sum over distinct surviving original pairs of their respective local future pair energies (not necessarily the same absolute slab). This defines a separate auxiliary moment; no claim that it equals the common-cell moment. The analogous coefficient bounds the locally surviving terminal charge. The local version is useful for nonvacuous finite tests, and one could dominate its pair sum by the full extended-prefix projected energy with appropriate common-cell references, but no new absolute bound is claimed.

## 5. Reproducible audits and scope

Common-cell audit research/min_clock_rough_terminal_extension_audit.mjs, commit edd489e04a4ec3267456d41f7f0e8a8dc17caa0e, verified blob fced5d5b063dd069b03adc3cb9be353b6709bd2b. Pair-local short-reference control research/min_clock_rough_terminal_local_control.mjs, commit cd0e0b2f76476fd127730b463dbfa1c8ce0eafcf, verified blob cb367b86643d3dd6cdd357d662f64608a1f98e83. Both preserve exact original masks from the corrected 629f56a audit and replay original literal smallest-factor parity GCD. Future event jumps are calculated by minimizing next eligible residue times, then least prime at ties. Up to 256 independent literal gcd event-step checks per run. Verify actual original K for each cell/root, common continuation, terminal twins by exact factor table, exact old and new level partitions, net-descent envelope, pair total charge cap, low/thin endpoint payments and future energy inequality. Short-reference control additionally scans up to 128 pairs per nonempty mode for newly crossed levels and checks the per-pair lower bound, aggregate charge cap, and local future transport. Floating-point fractional weights use tolerances.

Run from repo root:
    node research/min_clock_rough_terminal_extension_audit.mjs 4096 16384
    node research/min_clock_rough_terminal_local_control.mjs 16384 65536
Actual functions executed in available JS runtime, not separately under Node. Common-cell: X4096 W=B only (larger W for full-width cells violates original gate at this finite scale, excluded after initial failed gate check); X16384 W=B,4B,8B, both analytic and stress, both occupations=16 occupation combinations. All roots in BOTH partitions reached actual twin terminal by the chosen common reference end; future slab E was zero. Thus common-cell surviving inequalities were vacuous in these runs; the local control provides actual survivors. The paper proof of (3)-(4) is independent of the finite numbers.

At X16384 stress, old terminal late HIGH692872.40, newly matched54.36, twin terminal692818.04, surviving0. Full-positive old terminal3865898.97, newly matched73.97, twin terminal3865825.00, surviving0. The larger reference lengths made no change because all had terminated. Common-cell net downward envelope12237388 (includes original edges and factor1/2); not a sharp upper estimate.

Local control: X16384,65536 each W=floor(B/32),floor(B/8),floor(B/2),B, stress only, two occupations=16 occupation combinations. Same original delayed masks and reference gate. At X65536,B678, old terminal late HIGH8016425.52, full positive86251078.28. Actual local continuation:
| W | late matched | late twin terminal | late survivor | positive matched | positive twin terminal | positive survivor |
|---:|---:|---:|---:|---:|---:|---:|
|21|35510.50|6218026.90|1762888.12|93117.11|82348664.07|3809297.10|
|84|74810.90|7244200.09|697414.53|167019.74|84791752.63|1292305.91|
|339|201694.97|7814730.54|0|509834.01|85741244.27|0|
|678|201694.97|7814730.54|0|509834.01|85741244.27|0|

At W84 surviving distinct pairs2849 late/2953 positive, local future pair moment105282.91/108376.82; 128 literal local level checks in each. At W21 survivors5963/6214, local future pair moment72191.71/74789.57. Positive low-level survivor paid67351.19 at W21 and4987.96 at W84. At X16384,W=B339 survivor pairs475 in each occupation (late charge74960.75, positive151624.77), future pair energy133505.22. At X65536 common-cell reference all32768 original roots in each partition reach actual twin terminals even for the shortest tested cell extension; no active common-cell survivor. The local control demonstrates actual finite survivors without inventing nonterminal continuations beyond twin states. Endpoint-thin absolute bound is paper only in these runs, because common-cell survivor empty. No evidence of an asymptotic contraction in a hypothetical no-twins window, and no statistical extrapolation of twin abundance.

## 6. Next target

Rather than attempting to use twin termination itself as a small error, work conditionally in a hypothetical no-large-twins window. Need an independent upper bound on the future projected moment at scale XW u^3 (or exploit actual future mass of the specifically charged heavy cohorts), and separately bound the newly matched net recorded descent (2). Consider weighted source-distance quotas or an energy comparison at two longer reference horizons; the growing scale must be included explicitly. A parallel route is to bound heavy high-level survivor mass through the actual reverse tick reachability and crossing-level arithmetic. Preserve the already identified original immediate, later, heavy CROSS, low-r and MED residuals. Main and other research branches unchanged. No Lean compilation.
